import ImbalancedChen.Certificates.PairedCertificateChecker

/-! Deterministic data import; run verification/part2/import_paired_v2.py.
Frozen manuscript commit: ba6ec11d800eccc54406490631895e174de85766
Source path: verification/data/corpus-renewal-paired-certificate-v2-20261010.json
Source git blob: 49499697cca96de5f7b779e95077874ce5f9d119
Source SHA256: f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7
The Q160 endpoints below are provenance only. The new certificate uses
independent rational logarithm checks and proves its own weaker bounds.
-/

namespace ImbalancedChen.Certificates.PairedV2

def firstGroup : String := "E0"
def firstOrdinal : ℕ := 0
def firstTIndex : ℕ := 422
def firstUIndex : ℕ := 510
def a : ℚ := 417 / 5000
def h : ℚ := 19 / 125
def d : ℚ := 59 / 250
def mu : ℚ := 25 / 128
def K : ℚ := 8452171 / 1250000

def tLower (i : ℕ) : ℚ := mu + (d - mu) * i / 512
def tUpper (i : ℕ) : ℚ := mu + (d - mu) * (i + 1) / 512
def uLower (j : ℕ) : ℚ := a + (h - a) * j / 512
def uUpper (j : ℕ) : ℚ := a + (h - a) * (j + 1) / 512

def firstZ : ℚ := 76088109 / 532480000
def firstDiscardedQ80 : ℕ := 0
def firstStoredLowerQ160 : ℤ := 46334240358131757333311787501124513918660
def firstStoredUpperQ160 : ℤ := 46334240358131757333311787501124513918662

def firstCertificate : PairedIntegralCertificate where
  K := K
  a := a
  tl := tLower firstTIndex
  tr := tUpper firstTIndex
  ul := uLower firstUIndex
  ur := uUpper firstUIndex
  Z := firstZ
  logT :=
    { argument := 1875373 / 1874722
      terms := 1
      lower := 347191204489 / 1000000000000000
      upper := 347191214953 / 1000000000000000 }
  logU :=
    { argument := 388777 / 388434
      terms := 1
      lower := 176528638941 / 200000000000000
      upper := 882643366613 / 1000000000000000 }
  logZ :=
    { argument := 25362703 / 14802944
      terms := 6
      lower := 538453624463727 / 1000000000000000
      upper := 538453686055971 / 1000000000000000 }
  lower := 31703 / 1000000000000
  upper := 31704 / 1000000000000

end ImbalancedChen.Certificates.PairedV2
