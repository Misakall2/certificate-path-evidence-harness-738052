// Copyright 2015 Matthew Holt
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package certmagic

import (
	"bytes"
	"crypto/tls"
	"crypto/x509"
	"crypto/x509/pkix"
	"math/big"
	"strings"
	"testing"
	"time"

	"go.uber.org/zap"
)

// TestCertificateSelectionPathAcrossReplacement locks down the security
// semantics of the certificate selection and cache path while a certificate
// is being renewed. During renewal the cache can legitimately hold two
// certificates for the same name (the one being replaced and its
// replacement), so the important guarantees are:
//
//   - the queried name is normalized before the cache is consulted, and a
//     certificate for another name is never selected, no matter how much
//     longer it is valid;
//   - validity (NotBefore/NotAfter) only decides between candidates that
//     already matched the queried name, and when two candidates are valid at
//     the same instant the existing priority rule decides which one is
//     served;
//   - the same Config/Cache keeps moving forward as the cache changes: when
//     the old entry is unusable and the replacement is already effective, the
//     replacement is served, and adding a replacement that is not effective
//     yet does not evict the usable old entry;
//   - another name's cached selection is unaffected by the renewal;
//   - when no candidate applies, the pre-existing failure/fallback result is
//     returned without relying on issuance;
//   - every selection comes from the cache as it is at the time of the
//     query; a previous handshake's result is never reused.
//
// Everything runs against one fixed, in-memory cache entry point: no
// maintenance goroutine, no wall-clock waiting, no listening socket, and no
// issuer or storage is configured, so nothing can reach a certificate
// authority.
func TestCertificateSelectionPathAcrossReplacement(t *testing.T) {
	t.Run("hostname is normalized and other names never enter selection", func(t *testing.T) {
		f := newCertificateSelectionFixture(t, true)
		f.cache.cacheCertificate(f.old)
		f.cache.cacheCertificate(f.control) // same query family, far longer validity

		// SNI is normalized (lower-cased, trimmed) before the lookup, so all
		// of these spellings must land on the same certificate.
		for _, sni := range []string{"example.com", "Example.COM", "EXAMPLE.COM"} {
			cert, err := f.cfg.GetCertificate(selectionClientHello(sni))
			if err != nil {
				t.Fatalf("GetCertificate(%q): %v", sni, err)
			}
			requireServedCertificate(t, cert, f.old, "SNI "+sni)
		}

		// One selection per handshake, each reading exactly the one cached
		// certificate for the queried name; the control certificate, which is
		// valid for years longer, must not appear in any of those reads.
		if len(f.reads.reads) != 3 {
			t.Fatalf("expected exactly one selection read per handshake (3 total), got %d", len(f.reads.reads))
		}
		for i, read := range f.reads.reads {
			if len(read.hashes) != 1 || read.hashes[0] != f.old.hash {
				t.Fatalf("read %d for %q had choices %v, want only the certificate for example.com", i, read.serverName, read.hashes)
			}
			if containsString(read.hashes, f.control.hash) {
				t.Fatalf("read %d for %q included the certificate for %s", i, read.serverName, f.control.Leaf.Subject.CommonName)
			}
		}

		// The control name still resolves to its own certificate, and that
		// selection does not include example.com's certificate either.
		f.reads.reset()
		cert, err := f.cfg.GetCertificate(selectionClientHello("control.example.net"))
		if err != nil {
			t.Fatalf("GetCertificate(control.example.net): %v", err)
		}
		requireServedCertificate(t, cert, f.control, "control name")
		if len(f.reads.reads) != 1 || len(f.reads.reads[0].hashes) != 1 || f.reads.reads[0].hashes[0] != f.control.hash {
			t.Fatalf("control selection read %v, want only its own certificate", f.reads.reads)
		}
	})

	t.Run("two valid candidates follow the existing first-indexed priority", func(t *testing.T) {
		// Both certificates are valid at the reference instant; the existing
		// rule is "first client-supported, unexpired choice in cache-index
		// order", not "newest certificate wins". Lock both directions so the
		// rule is pinned rather than accidentally relying on insertion order
		// that happens to look like newest-first.
		first := newCertificateSelectionFixture(t, true)
		first.cache.cacheCertificate(first.old)
		first.cache.cacheCertificate(first.renewed)
		cert, err := first.cfg.GetCertificate(selectionClientHello("example.com"))
		if err != nil {
			t.Fatalf("GetCertificate: %v", err)
		}
		requireServedCertificate(t, cert, first.old, "old indexed first")
		if len(first.reads.reads) != 1 || len(first.reads.reads[0].hashes) != 2 {
			t.Fatalf("expected one read with both candidates, got %v", first.reads.reads)
		}

		second := newCertificateSelectionFixture(t, true)
		second.cache.cacheCertificate(second.renewed)
		second.cache.cacheCertificate(second.old)
		cert, err = second.cfg.GetCertificate(selectionClientHello("example.com"))
		if err != nil {
			t.Fatalf("GetCertificate: %v", err)
		}
		requireServedCertificate(t, cert, second.renewed, "renewed indexed first")
	})

	t.Run("expired entry hands the same config to the effective replacement", func(t *testing.T) {
		f := newCertificateSelectionFixture(t, true)

		// The renewal window: the entry that has been served is expired, and
		// its replacement is already effective and cached beside it.
		f.cache.cacheCertificate(f.expired)
		f.cache.cacheCertificate(f.renewed)
		f.reads.reset()
		cert, err := f.cfg.GetCertificate(selectionClientHello("example.com"))
		if err != nil {
			t.Fatalf("GetCertificate: %v", err)
		}
		requireServedCertificate(t, cert, f.renewed, "expired alongside effective replacement")
		if len(f.reads.reads) != 1 || len(f.reads.reads[0].hashes) != 2 {
			t.Fatalf("expected one read with both candidates, got %v", f.reads.reads)
		}

		// Once the replacement is swapped in, the very same Config/Cache must
		// serve it, and the expired entry must be gone from cache and index.
		f.cache.replaceCertificate(f.expired, f.renewed)
		f.reads.reset()
		cert, err = f.cfg.GetCertificate(selectionClientHello("example.com"))
		if err != nil {
			t.Fatalf("GetCertificate after replacement: %v", err)
		}
		requireServedCertificate(t, cert, f.renewed, "after replacement")
		if len(f.reads.reads) != 1 || len(f.reads.reads[0].hashes) != 1 || f.reads.reads[0].hashes[0] != f.renewed.hash {
			t.Fatalf("after replacement the read should see only the replacement, got %v", f.reads.reads)
		}
		if hashes := f.cache.getAllMatchingCerts("example.com"); len(hashes) != 1 || hashes[0].hash != f.renewed.hash {
			t.Fatalf("expected only the replacement for example.com, got %d certificates", len(hashes))
		}
		f.cache.mu.RLock()
		_, expiredStillCached := f.cache.cache[f.expired.hash]
		f.cache.mu.RUnlock()
		if expiredStillCached {
			t.Fatal("expired certificate is still in the cache after replacement")
		}
	})

	t.Run("adding a not-yet-effective entry does not displace the usable one", func(t *testing.T) {
		f := newCertificateSelectionFixture(t, true)

		// The usable certificate is cached first, then an update arrives that
		// only adds a replacement whose validity starts in the future. It must
		// be cached alongside the old one, not replace it.
		f.cache.cacheCertificate(f.old)
		f.cache.cacheCertificate(f.pending)
		f.reads.reset()
		cert, err := f.cfg.GetCertificate(selectionClientHello("example.com"))
		if err != nil {
			t.Fatalf("GetCertificate: %v", err)
		}
		requireServedCertificate(t, cert, f.old, "usable entry alongside pending replacement")

		if len(f.reads.reads) != 1 || len(f.reads.reads[0].hashes) != 2 {
			t.Fatalf("expected one read with both candidates, got %v", f.reads.reads)
		}
		choices := f.reads.reads[0].hashes
		if !containsString(choices, f.old.hash) || !containsString(choices, f.pending.hash) {
			t.Fatalf("read choices %v do not contain both the usable and the pending certificate", choices)
		}
		if hashes := f.cache.getAllMatchingCerts("example.com"); len(hashes) != 2 {
			t.Fatalf("expected both certificates to remain cached, got %d", len(hashes))
		}

		// The same two entries with the not-yet-effective one indexed first:
		// the effective boundary must still be honored, so the usable entry is
		// served rather than the one whose validity has not begun.
		reverse := newCertificateSelectionFixture(t, true)
		reverse.cache.cacheCertificate(reverse.pending)
		reverse.cache.cacheCertificate(reverse.old)
		cert, err = reverse.cfg.GetCertificate(selectionClientHello("example.com"))
		if err != nil {
			t.Fatalf("GetCertificate (pending indexed first): %v", err)
		}
		requireServedCertificate(t, cert, reverse.old, "pending indexed first")
	})

	t.Run("another name's selection is unaffected by the renewal", func(t *testing.T) {
		f := newCertificateSelectionFixture(t, true)
		f.cache.cacheCertificate(f.old)
		f.cache.cacheCertificate(f.control)

		before, err := f.cfg.GetCertificate(selectionClientHello("control.example.net"))
		if err != nil {
			t.Fatalf("GetCertificate(control) before renewal: %v", err)
		}
		requireServedCertificate(t, before, f.control, "control before renewal")
		beforeRead := f.reads.reads[len(f.reads.reads)-1]

		// Renew example.com under the same Config/Cache.
		f.cache.replaceCertificate(f.old, f.renewed)
		cert, err := f.cfg.GetCertificate(selectionClientHello("example.com"))
		if err != nil {
			t.Fatalf("GetCertificate(example.com) after renewal: %v", err)
		}
		requireServedCertificate(t, cert, f.renewed, "renewed example.com")

		f.reads.reset()
		after, err := f.cfg.GetCertificate(selectionClientHello("control.example.net"))
		if err != nil {
			t.Fatalf("GetCertificate(control) after renewal: %v", err)
		}
		requireServedCertificate(t, after, f.control, "control after renewal")
		afterRead := f.reads.reads[len(f.reads.reads)-1]

		if len(beforeRead.hashes) != 1 || len(afterRead.hashes) != 1 ||
			beforeRead.hashes[0] != afterRead.hashes[0] || beforeRead.hashes[0] != f.control.hash {
			t.Fatalf("control selection changed across the renewal: before %v, after %v", beforeRead.hashes, afterRead.hashes)
		}
	})

	t.Run("no candidate applies to the queried name: existing failure, no issuance", func(t *testing.T) {
		// No CertSelection here: a custom selector may be handed every cached
		// certificate when a name has no match, which would mask this result.
		f := newCertificateSelectionFixture(t, false)
		f.cache.cacheCertificate(f.old)
		f.cache.cacheCertificate(f.renewed)
		f.cache.cacheCertificate(f.control)

		before := cachedCertificateCount(f.cache)
		cert, err := f.cfg.GetCertificate(selectionClientHello("other.example.net"))
		if err == nil {
			t.Fatalf("expected no certificate to be available for an unmatched name, got %d DER certificates", len(cert.Certificate))
		}
		if !strings.Contains(err.Error(), "no certificate available for 'other.example.net'") {
			t.Fatalf("unexpected error for an unmatched name: %v", err)
		}
		if cert != nil && len(cert.Certificate) != 0 {
			t.Fatalf("expected an empty certificate on failure, got %d DER certificates", len(cert.Certificate))
		}

		// Neither candidate was re-cached, and nothing was issued: no
		// OnDemand config, issuers, or storage exist in the fixture.
		if after := cachedCertificateCount(f.cache); after != before {
			t.Fatalf("cache size changed from %d to %d while serving an unmatched name", before, after)
		}
		if f.cfg.OnDemand != nil || len(f.cfg.Issuers) != 0 || f.cfg.Storage != nil {
			t.Fatal("fixture unexpectedly has a way to issue certificates")
		}
	})

	t.Run("no candidate is valid at the reference time: existing last-resort result", func(t *testing.T) {
		f := newCertificateSelectionFixture(t, false)

		// At the reference instant one candidate has expired and the other is
		// not yet effective. DefaultCertificateSelector's documented behavior
		// with a cached match is to fall back to the last client-supported
		// choice rather than fail; the point of this regression is that no
		// issuance is attempted and the cache is left alone.
		f.cache.cacheCertificate(f.expired)
		f.cache.cacheCertificate(f.pending)
		before := cachedCertificateCount(f.cache)

		cert, err := f.cfg.GetCertificate(selectionClientHello("example.com"))
		if err != nil {
			t.Fatalf("GetCertificate: %v", err)
		}
		requireServedCertificate(t, cert, f.pending, "last-resort selection")
		if after := cachedCertificateCount(f.cache); after != before {
			t.Fatalf("cache size changed from %d to %d with no issuance possible", before, after)
		}
		if f.cfg.OnDemand != nil || len(f.cfg.Issuers) != 0 || f.cfg.Storage != nil {
			t.Fatal("fixture unexpectedly has a way to issue certificates")
		}
	})

	t.Run("each handshake selects from the current cache, never the previous result", func(t *testing.T) {
		f := newCertificateSelectionFixture(t, true)
		f.cache.cacheCertificate(f.old)
		f.cache.cacheCertificate(f.control)

		for i := 0; i < 2; i++ {
			cert, err := f.cfg.GetCertificate(selectionClientHello("example.com"))
			if err != nil {
				t.Fatalf("GetCertificate #%d: %v", i+1, err)
			}
			requireServedCertificate(t, cert, f.old, "before renewal")
		}
		// Two handshakes are two independent reads of the cache.
		if len(f.reads.reads) != 2 {
			t.Fatalf("expected two independent selection reads, got %d", len(f.reads.reads))
		}
		for i, read := range f.reads.reads {
			if len(read.hashes) != 1 || read.hashes[0] != f.old.hash {
				t.Fatalf("read %d was %v, want only the old certificate", i, read.hashes)
			}
		}

		// After the cache changes, the next query must observe the change
		// instead of reusing what the previous handshake selected.
		f.cache.replaceCertificate(f.old, f.renewed)
		cert, err := f.cfg.GetCertificate(selectionClientHello("example.com"))
		if err != nil {
			t.Fatalf("GetCertificate after replacement: %v", err)
		}
		requireServedCertificate(t, cert, f.renewed, "after replacement")
		lastRead := f.reads.reads[len(f.reads.reads)-1]
		if len(lastRead.hashes) != 1 || lastRead.hashes[0] != f.renewed.hash {
			t.Fatalf("the post-replacement read was %v, want only the replacement", lastRead.hashes)
		}
		if lastRead.hashes[0] == f.reads.reads[0].hashes[0] {
			t.Fatal("selection reused the previous handshake's result instead of reading the current cache")
		}

		// A query for another name must not inherit the last result either.
		cert, err = f.cfg.GetCertificate(selectionClientHello("control.example.net"))
		if err != nil {
			t.Fatalf("GetCertificate(control): %v", err)
		}
		requireServedCertificate(t, cert, f.control, "control name after renewal")
		controlRead := f.reads.reads[len(f.reads.reads)-1]
		if len(controlRead.hashes) != 1 || controlRead.hashes[0] != f.control.hash {
			t.Fatalf("control read was %v, want only the control certificate", controlRead.hashes)
		}
	})
}

// certificateSelectionFixture is the single fixed entry point used by the
// regression: an in-memory Cache and Config with no maintenance goroutine, no
// storage, no issuers, and no OnDemand, so nothing waits, listens, or issues.
type certificateSelectionFixture struct {
	cfg   *Config
	cache *Cache
	reads *selectionReadLog

	// Two certificates for the same name (the one being replaced and its
	// replacement), a not-yet-effective replacement, an expired one, and a
	// control certificate for a different name with a much longer validity.
	old, renewed, pending, expired, control Certificate
}

func newCertificateSelectionFixture(t *testing.T, observe bool) *certificateSelectionFixture {
	t.Helper()

	// reference is the one instant certificate validity is expressed against;
	// the tests never wait for the wall clock.
	reference := time.Now()
	f := &certificateSelectionFixture{
		cache: &Cache{
			cache:      make(map[string]Certificate),
			cacheIndex: make(map[string][]string),
			logger:     zap.NewNop(),
		},
	}
	f.cfg = &Config{
		Logger:    zap.NewNop(),
		certCache: f.cache,
		OCSP:      OCSPConfig{DisableStapling: true},
	}
	if observe {
		f.reads = &selectionReadLog{}
		f.cfg.CertSelection = f.reads
	}

	f.old = issueSelectionFixtureCert(t, "example.com", 7001,
		reference.Add(-72*time.Hour), reference.Add(24*time.Hour))
	f.renewed = issueSelectionFixtureCert(t, "example.com", 7002,
		reference.Add(-1*time.Hour), reference.Add(2160*time.Hour))
	f.pending = issueSelectionFixtureCert(t, "example.com", 7003,
		reference.Add(6*time.Hour), reference.Add(2160*time.Hour))
	f.expired = issueSelectionFixtureCert(t, "example.com", 7004,
		reference.Add(-720*time.Hour), reference.Add(-time.Hour))
	f.control = issueSelectionFixtureCert(t, "control.example.net", 7005,
		reference.Add(-72*time.Hour), reference.Add(8760*time.Hour))
	return f
}

func issueSelectionFixtureCert(t *testing.T, name string, serial int64, notBefore, notAfter time.Time) Certificate {
	t.Helper()

	_, key, certPEM := mustIssueTestCertificate(t, &x509.Certificate{
		SerialNumber: big.NewInt(serial),
		Subject:      pkix.Name{CommonName: name},
		DNSNames:     []string{name},
		NotBefore:    notBefore,
		NotAfter:     notAfter,
		KeyUsage:     x509.KeyUsageDigitalSignature,
		ExtKeyUsage:  []x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth},
	}, nil, nil)
	keyPEM, err := PEMEncodePrivateKey(key)
	if err != nil {
		t.Fatalf("encoding fixture private key: %v", err)
	}
	cert, err := makeCertificate(certPEM, keyPEM)
	if err != nil {
		t.Fatalf("building fixture certificate: %v", err)
	}
	return cert
}

// selectionReadLog is a CertificateSelector that records the candidates the
// cache lookup handed to selection, then applies the default selection rules.
// Recording the choices is how the tests observe which cache entries were read
// for a query.
type selectionReadLog struct {
	reads []selectionRead
}

type selectionRead struct {
	serverName string
	hashes     []string
}

func (log *selectionReadLog) SelectCertificate(hello *tls.ClientHelloInfo, choices []Certificate) (Certificate, error) {
	read := selectionRead{serverName: hello.ServerName}
	for _, choice := range choices {
		read.hashes = append(read.hashes, choice.hash)
	}
	log.reads = append(log.reads, read)
	return DefaultCertificateSelector(hello, choices)
}

func (log *selectionReadLog) reset() { log.reads = nil }

func selectionClientHello(serverName string) *tls.ClientHelloInfo {
	hello := testClientHello() // modern client hello over the test connection
	hello.ServerName = serverName
	return hello
}

func requireServedCertificate(t *testing.T, got *tls.Certificate, want Certificate, context string) {
	t.Helper()
	if got == nil || got.Leaf == nil {
		t.Fatalf("%s: got no certificate, want serial %s", context, want.Leaf.SerialNumber)
	}
	if !bytes.Equal(got.Leaf.Raw, want.Leaf.Raw) {
		t.Fatalf("%s: served certificate serial %s (SANs %v), want serial %s",
			context, got.Leaf.SerialNumber, got.Leaf.DNSNames, want.Leaf.SerialNumber)
	}
}

func containsString(haystack []string, needle string) bool {
	for _, s := range haystack {
		if s == needle {
			return true
		}
	}
	return false
}

func cachedCertificateCount(cache *Cache) int {
	cache.mu.RLock()
	defer cache.mu.RUnlock()
	return len(cache.cache)
}
