import ImbalancedChen.Certificates.PairedV2FullMask

namespace ImbalancedChen.Certificates.PairedV2.FullMask

open scoped BigOperators

/-- Integer endpoints at the two fixed positive scales.  The interpretation
below uses the real fourfold-integral checker already proved sound. -/
structure Approximation where
  tLo : ℕ
  tHi : ℕ
  uLo : ℕ
  uHi : ℕ
  zLo : ℕ
  zHi : ℕ
  lower : ℕ
  upper : ℕ
  deriving Inhabited

def makeCertificate (r : Row) (v : Approximation) : PairedIntegralCertificate where
  K := K
  a := a
  tl := tLower (indices r).1
  tr := tUpper (indices r).1
  ul := uLower (indices r).2
  ur := uUpper (indices r).2
  Z := cutoff r
  logT := ⟨tUpper (indices r).1 / tLower (indices r).1, 1,
    v.tLo / 1000000000000000, v.tHi / 1000000000000000⟩
  logU := ⟨uUpper (indices r).2 / uLower (indices r).2, 1,
    v.uLo / 1000000000000000, v.uHi / 1000000000000000⟩
  logZ := ⟨cutoff r / a, 6,
    v.zLo / 1000000000000000, v.zHi / 1000000000000000⟩
  lower := v.lower / 100000000000000000000
  upper := v.upper / 100000000000000000000

/-- Uniform soundness of a complete adopted-mask check.  The certificate
coordinates and K/80 normalization are fixed by the actual adopted row,
so a generator cannot replace an integral by a stored output. -/
theorem full_integral_bounds_of_checked (v : Row → Approximation)
    (hc : ∀ r : Row, (makeCertificate r (v r)).check = true) :
    ((∑ r : Row, (makeCertificate r (v r)).lower : ℚ) : ℝ) ≤ integral ∧
      integral ≤ ((∑ r : Row, (makeCertificate r (v r)).upper : ℚ) : ℝ) := by
  simpa only [makeCertificate, integral] using
    PairedIntegralCertificate.sum_check_sound Finset.univ
      (fun r => makeCertificate r (v r)) (fun r _ => hc r)

end ImbalancedChen.Certificates.PairedV2.FullMask
