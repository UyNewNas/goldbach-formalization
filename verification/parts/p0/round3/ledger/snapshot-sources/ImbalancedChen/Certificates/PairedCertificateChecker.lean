import ImbalancedChen.Certificates.PairedFibreIntegral
import ImbalancedChen.Certificates.RationalLogCertificate
import Mathlib.Data.Rat.BigOperators

/-!
Verification status: uncompiled candidate. See `docs/part2/HANDOFF.md`.

# A sound checker for the adopted paired-fibre integral

Acceptance checks rational endpoints, three proved logarithm enclosures,
and the outward arithmetic for the actual fourfold integral. Soundness
concludes an inequality about `pairedLocalIntegral`, whose definition
contains the manuscript kernel and no certificate output.

This is the local positive-fibre numerical interface. Membership in an
adopted mask and inheritance of the restrictable arithmetic parent remain
separate from this analytic calculation; the concrete data module binds
the former, while Part 5 must supply the latter in its counting argument.
-/

namespace ImbalancedChen.Certificates

open scoped BigOperators

structure PairedIntegralCertificate where
  K : ℚ
  a : ℚ
  tl : ℚ
  tr : ℚ
  ul : ℚ
  ur : ℚ
  Z : ℚ
  logT : RationalLogCertificate
  logU : RationalLogCertificate
  logZ : RationalLogCertificate
  lower : ℚ
  upper : ℚ
  deriving DecidableEq, Repr

def PairedIntegralCertificate.bracketLower (c : PairedIntegralCertificate) : ℚ :=
  1 / c.a - (1 + c.logZ.upper) / c.Z

def PairedIntegralCertificate.bracketUpper (c : PairedIntegralCertificate) : ℚ :=
  1 / c.a - (1 + c.logZ.lower) / c.Z

def PairedIntegralCertificate.productLower (c : PairedIntegralCertificate) : ℚ :=
  (c.K / 80) * c.logT.lower * c.logU.lower * c.bracketLower

def PairedIntegralCertificate.productUpper (c : PairedIntegralCertificate) : ℚ :=
  (c.K / 80) * c.logT.upper * c.logU.upper * c.bracketUpper

def PairedIntegralCertificate.Valid (c : PairedIntegralCertificate) : Prop :=
  0 < c.K ∧ 0 < c.a ∧ c.a ≤ c.Z ∧
    0 < c.tl ∧ c.tl ≤ c.tr ∧ 0 < c.ul ∧ c.ul ≤ c.ur ∧
    c.logT.argument = c.tr / c.tl ∧
    c.logU.argument = c.ur / c.ul ∧
    c.logZ.argument = c.Z / c.a ∧
    c.logT.check = true ∧ c.logU.check = true ∧ c.logZ.check = true ∧
    0 ≤ c.logT.lower ∧ 0 ≤ c.logU.lower ∧ 0 ≤ c.bracketLower ∧
    c.lower ≤ c.productLower ∧ c.productUpper ≤ c.upper

instance (c : PairedIntegralCertificate) : Decidable c.Valid := by
  unfold PairedIntegralCertificate.Valid
  infer_instance

def PairedIntegralCertificate.check (c : PairedIntegralCertificate) : Bool :=
  decide c.Valid

/-- The complete local certificate is about the literal fourfold integral,
not a comparison between two stored JSON fields. -/
theorem PairedIntegralCertificate.check_sound (c : PairedIntegralCertificate)
    (hcheck : c.check = true) :
    (c.lower : ℝ) ≤ pairedLocalIntegral (c.K : ℝ) c.a c.tl c.tr c.ul c.ur c.Z ∧
      pairedLocalIntegral (c.K : ℝ) c.a c.tl c.tr c.ul c.ur c.Z ≤ (c.upper : ℝ) := by
  have hv : c.Valid := of_decide_eq_true hcheck
  rcases hv with ⟨hK, ha, haZ, htl, ht, hul, hu, heT, heU, heZ,
    hcT, hcU, hcZ, hnT, hnU, hnB, hlo, hhi⟩
  have hKR : (0 : ℝ) < (c.K : ℝ) := by exact_mod_cast hK
  have haR : (0 : ℝ) < (c.a : ℝ) := by exact_mod_cast ha
  have haZR : (c.a : ℝ) ≤ (c.Z : ℝ) := by exact_mod_cast haZ
  have htlR : (0 : ℝ) < (c.tl : ℝ) := by exact_mod_cast htl
  have htR : (c.tl : ℝ) ≤ (c.tr : ℝ) := by exact_mod_cast ht
  have hulR : (0 : ℝ) < (c.ul : ℝ) := by exact_mod_cast hul
  have huR : (c.ul : ℝ) ≤ (c.ur : ℝ) := by exact_mod_cast hu
  have hzR : (0 : ℝ) < (c.Z : ℝ) := haR.trans_le haZR
  have hT := c.logT.check_sound hcT
  have hU := c.logU.check_sound hcU
  have hZ := c.logZ.check_sound hcZ
  rw [heT, Rat.cast_div] at hT
  rw [heU, Rat.cast_div] at hU
  rw [heZ, Rat.cast_div] at hZ
  have hnTR : (0 : ℝ) ≤ (c.logT.lower : ℝ) := by exact_mod_cast hnT
  have hnUR : (0 : ℝ) ≤ (c.logU.lower : ℝ) := by exact_mod_cast hnU
  have hnBR : (0 : ℝ) ≤ (c.bracketLower : ℝ) := by exact_mod_cast hnB
  have hBL : (c.bracketLower : ℝ) ≤
      1 / (c.a : ℝ) - (1 + Real.log ((c.Z : ℝ) / c.a)) / c.Z := by
    simp only [PairedIntegralCertificate.bracketLower, Rat.cast_sub,
      Rat.cast_div, Rat.cast_add, Rat.cast_one]
    exact sub_le_sub_left
      (div_le_div_of_nonneg_right (add_le_add (le_refl (1 : ℝ)) hZ.2) hzR.le) _
  have hBU : 1 / (c.a : ℝ) - (1 + Real.log ((c.Z : ℝ) / c.a)) / c.Z ≤
      (c.bracketUpper : ℝ) := by
    simp only [PairedIntegralCertificate.bracketUpper, Rat.cast_sub,
      Rat.cast_div, Rat.cast_add, Rat.cast_one]
    exact sub_le_sub_left
      (div_le_div_of_nonneg_right (add_le_add (le_refl (1 : ℝ)) hZ.1) hzR.le) _
  have hc0 : (0 : ℝ) ≤ (c.K : ℝ) / 80 := by positivity
  have hTL : (c.K : ℝ) / 80 * c.logT.lower ≤
      (c.K : ℝ) / 80 * Real.log ((c.tr : ℝ) / c.tl) :=
    mul_le_mul_of_nonneg_left hT.1 hc0
  have hTU : (c.K : ℝ) / 80 * Real.log ((c.tr : ℝ) / c.tl) ≤
      (c.K : ℝ) / 80 * c.logT.upper :=
    mul_le_mul_of_nonneg_left hT.2 hc0
  have hLprod : (c.productLower : ℝ) ≤
      (c.K : ℝ) / 80 * Real.log ((c.tr : ℝ) / c.tl) *
        Real.log ((c.ur : ℝ) / c.ul) *
        (1 / (c.a : ℝ) - (1 + Real.log ((c.Z : ℝ) / c.a)) / c.Z) := by
    have htwo := mul_le_mul hTL hU.1 hnUR (mul_nonneg hc0 (hnTR.trans hT.1))
    have hthree := mul_le_mul htwo hBL hnBR
      (mul_nonneg (mul_nonneg hc0 (hnTR.trans hT.1)) (hnUR.trans hU.1))
    simpa [PairedIntegralCertificate.productLower] using hthree
  have hUprod : (c.K : ℝ) / 80 * Real.log ((c.tr : ℝ) / c.tl) *
      Real.log ((c.ur : ℝ) / c.ul) *
      (1 / (c.a : ℝ) - (1 + Real.log ((c.Z : ℝ) / c.a)) / c.Z) ≤
      (c.productUpper : ℝ) := by
    have htwo := mul_le_mul hTU hU.2 (hnUR.trans hU.1)
      (mul_nonneg hc0 (hnTR.trans (hT.1.trans hT.2)))
    have hthree := mul_le_mul htwo hBU (hnBR.trans hBL)
      (mul_nonneg (mul_nonneg hc0 (hnTR.trans (hT.1.trans hT.2)))
        (hnUR.trans (hU.1.trans hU.2)))
    simpa [PairedIntegralCertificate.productUpper] using hthree
  have hloR : (c.lower : ℝ) ≤ (c.productLower : ℝ) := by exact_mod_cast hlo
  have hhiR : (c.productUpper : ℝ) ≤ (c.upper : ℝ) := by exact_mod_cast hhi
  rw [pairedLocalIntegral_eq (c.K : ℝ) haR haZR htlR (htlR.trans_le htR)
    hulR (hulR.trans_le huR)]
  exact ⟨hloR.trans hLprod, hUprod.trans hhiR⟩

/-- Checked finite rows bound the sum of their actual fourfold integrals.
The hypotheses are individual finite checks. This theorem neither asserts
that the adopted rows have all passed, nor identifies a union integral
without the separate ownership/disjointness proof. -/
theorem PairedIntegralCertificate.sum_check_sound {ι : Type*}
    (s : Finset ι) (c : ι → PairedIntegralCertificate)
    (hchecks : ∀ i ∈ s, (c i).check = true) :
    ((∑ i ∈ s, (c i).lower : ℚ) : ℝ) ≤
        ∑ i ∈ s, pairedLocalIntegral ((c i).K : ℝ)
          (c i).a (c i).tl (c i).tr (c i).ul (c i).ur (c i).Z ∧
      (∑ i ∈ s, pairedLocalIntegral ((c i).K : ℝ)
          (c i).a (c i).tl (c i).tr (c i).ul (c i).ur (c i).Z) ≤
        ((∑ i ∈ s, (c i).upper : ℚ) : ℝ) := by
  constructor
  · simpa only [Rat.cast_sum] using
      (Finset.sum_le_sum (s := s)
        (fun i hi => ((c i).check_sound (hchecks i hi)).1))
  · simpa only [Rat.cast_sum] using
      (Finset.sum_le_sum (s := s)
        (fun i hi => ((c i).check_sound (hchecks i hi)).2))

end ImbalancedChen.Certificates
