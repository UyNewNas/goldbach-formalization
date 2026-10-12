import ImbalancedChen.Certificates.PairedV2Data

/-!
Deterministic adopted-source import. Regenerate with
`verification/part2/generate_paired_prefix.py --count 4`.
Frozen manuscript: ba6ec11d800eccc54406490631895e174de85766
Original source: verification/data/corpus-renewal-paired-certificate-v2-20261010.json
Original SHA256: f6d31386f93cf77888ea4771ffa549a1cf61dca700bac618ff7646566a02f9b7
Original git blob: 49499697cca96de5f7b779e95077874ce5f9d119
Selected source ordinals: 0..3; all E0, all discarded Q80 = 0.
Selected row stream SHA256: 96df956686f3617d69cb0f72e510258991e7f21d10c36c635915f8cc0a573235
The stored Q160 bounds are provenance in the source/report, not proof premises.
-/

namespace ImbalancedChen.Certificates.PairedV2.Prefix4

def rowIndices (i : Fin 4) : ℕ × ℕ :=
  match i.val with
  | 0 => (422, 510)
  | 1 => (422, 511)
  | 2 => (423, 509)
  | _ => (423, 510)

def rowZ (i : Fin 4) : ℚ :=
  match i.val with
  | 0 => 76088109 / 532480000
  | 1 => 1170333 / 8192000
  | 2 => 9511851 / 66560000
  | _ => 9509793 / 66560000

def rowOrdinal (i : Fin 4) : ℕ := i.val

def certificate0000 : PairedIntegralCertificate where
  K := K
  a := a
  tl := tLower 422
  tr := tUpper 422
  ul := uLower 510
  ur := uUpper 510
  Z := 76088109 / 532480000
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
  lower := 634063221377 / 20000000000000000000
  upper := 3170317936341 / 100000000000000000000

def certificate0001 : PairedIntegralCertificate where
  K := K
  a := a
  tl := tLower 422
  tr := tUpper 422
  ul := uLower 511
  ur := uUpper 511
  Z := 1170333 / 8192000
  logT :=
    { argument := 1875373 / 1874722
      terms := 1
      lower := 347191204489 / 1000000000000000
      upper := 347191214953 / 1000000000000000 }
  logU :=
    { argument := 389120 / 388777
      terms := 1
      lower := 2755827571 / 3125000000000
      upper := 35274599767 / 40000000000000 }
  logZ :=
    { argument := 1950555 / 1138688
      terms := 6
      lower := 538237220351071 / 1000000000000000
      upper := 134559320408441 / 250000000000000 }
  lower := 1582705120377 / 50000000000000000000
  upper := 126616482467 / 4000000000000000000

def certificate0002 : PairedIntegralCertificate where
  K := K
  a := a
  tl := tLower 423
  tr := tUpper 423
  ul := uLower 509
  ur := uUpper 509
  Z := 9511851 / 66560000
  logT :=
    { argument := 1876024 / 1875373
      terms := 1
      lower := 347070704593 / 1000000000000000
      upper := 173535357523 / 500000000000000 }
  logU :=
    { argument := 388434 / 388091
      terms := 1
      lower := 3450870867 / 3906250000000
      upper := 883423114317 / 1000000000000000 }
  logZ :=
    { argument := 3170617 / 1850368
      terms := 6
      lower := 26927083162251 / 50000000000000
      upper := 269270862481803 / 500000000000000 }
  lower := 1586437652383 / 50000000000000000000
  upper := 1586438569309 / 50000000000000000000

def certificate0003 : PairedIntegralCertificate where
  K := K
  a := a
  tl := tLower 423
  tr := tUpper 423
  ul := uLower 510
  ur := uUpper 510
  Z := 9509793 / 66560000
  logT :=
    { argument := 1876024 / 1875373
      terms := 1
      lower := 347070704593 / 1000000000000000
      upper := 173535357523 / 500000000000000 }
  logU :=
    { argument := 388777 / 388434
      terms := 1
      lower := 176528638941 / 200000000000000
      upper := 882643366613 / 1000000000000000 }
  logZ :=
    { argument := 3169931 / 1850368
      terms := 6
      lower := 134581319546397 / 250000000000000
      upper := 538325339594069 / 1000000000000000 }
  lower := 1583981804581 / 50000000000000000000
  upper := 3167965434447 / 100000000000000000000

def certificates (i : Fin 4) : PairedIntegralCertificate :=
  match i.val with
  | 0 => certificate0000
  | 1 => certificate0001
  | 2 => certificate0002
  | _ => certificate0003

def lowerBound : ℚ := 12676565261567 / 100000000000000000000
def upperBound : ℚ := 12676572571081 / 100000000000000000000

end ImbalancedChen.Certificates.PairedV2.Prefix4
