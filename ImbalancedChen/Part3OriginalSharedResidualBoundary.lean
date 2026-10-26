import ImbalancedChen.Part3OriginalMaskedWExplicitBoundary
import ImbalancedChen.Part3SharedFirstFactorDispersion

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26, phase 4.

Transfer to the ACTUAL shared-first-factor residual. Saturating both
finite masks recovers the full nonzero source exactly. The previously
proved original Schwartz bound is applied to genuine admissible point
mass slices; each p is then summed on the original primitive carrier.
This is a residual norm bound, not an equality of unshared and shared W.
The outside beta/gamma1 moments and primitive zero/V/U payments are left
for their existing public suppliers. Full spectral 7/32 remains OPEN.
-/

namespace ImbalancedChen.Part3.OriginalSharedResidualBoundary20261026b
noncomputable section
open Classical Finset TransposedGCDPoissonMask
open OriginalMaskedWExplicitBoundary20261026b
open scoped BigOperators

theorem original_saturated_small_masks_eq_full_nonzero
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    d.transposedAtom.commonSmallBetaModulusGCDNonzeroPart (2*d.U) d.physicalFactorCap false =
      d.transposedAtom.complexCRTSmoothNonzeroPart := by
  rw [complexCRTSmoothNonzeroPart_eq_betaPairs]
  unfold MediumAtom.commonSmallBetaModulusGCDNonzeroPart
  apply Finset.sum_congr rfl
  intro n1 hn1
  apply Finset.sum_congr rfl
  intro n2 hn2
  change n1 ∈ factorCarrier d.U at hn1
  have hceil : 1 ≤ Nat.ceil d.U := by exact_mod_cast hd.1.trans (Nat.le_ceil d.U)
  have hn1pos : 0 < n1 := by have hh := (Finset.mem_Icc.mp hn1).1; omega
  have hgn : n1.gcd n2 ≤ n1 := Nat.le_of_dvd hn1pos (Nat.gcd_dvd_left _ _)
  have hn1hi : (n1 : ℝ) ≤ 2*d.U :=
    (show (n1 : ℝ) ≤ (Nat.floor (2*d.U) : ℝ) by
      exact_mod_cast (Finset.mem_Icc.mp hn1).2).trans (Nat.floor_le (by linarith [hd.1]))
  have hy : ¬ 2*d.U < (n1.gcd n2 : ℝ) := by
    have hh : (n1.gcd n2 : ℝ) ≤ n1 := by exact_mod_cast hgn
    linarith
  simp only [if_neg hy]
  congr 1
  unfold MediumAtom.commonModulusGCDNonzeroWeight MediumAtom.commonFactorPairNonzeroWeight
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hqa := Finset.mem_Ioc.mp (d.physicalFactorModuli_subset_cap hd
    (Finset.mem_image_of_mem _ ha))
  have hgd : (complexFactorModulus a).gcd (complexFactorModulus b) ≤
      complexFactorModulus a := Nat.le_of_dvd hqa.1 (Nat.gcd_dvd_left _ _)
  have hcap0 : 0 ≤ d.physicalFactorCap := zero_le_one.trans (d.one_le_physicalFactorCap hd)
  have hqaR : (complexFactorModulus a : ℝ) ≤ d.physicalFactorCap :=
    (show (complexFactorModulus a : ℝ) ≤ (Nat.floor d.physicalFactorCap : ℝ) by
      exact_mod_cast hqa.2).trans (Nat.floor_le hcap0)
  have hD : ¬ d.physicalFactorCap <
      ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ) := by
    have hh : ((complexFactorModulus a).gcd (complexFactorModulus b) : ℝ) ≤
        complexFactorModulus a := by exact_mod_cast hgd
    linarith
  simp [hD]

theorem original_full_nonzero_boundary :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d →
        ‖d.transposedAtom.complexCRTSmoothNonzeroPart‖ ≤ C*d.U^2*d.physicalFactorCap^4/d.V := by
  obtain ⟨C,hC,hbound⟩ := original_bothSmall_nonzero_explicit_boundary
  refine ⟨C,hC,fun B sigma kappa c0 d hd => ?_⟩
  have h := hbound B sigma kappa c0 d hd (2*d.U) d.physicalFactorCap
  rw [original_saturated_small_masks_eq_full_nonzero hd] at h
  exact h

def sharedResidual (d : MediumAtom) : ℂ :=
  ∑ p ∈ d.primitiveFirstFactorCarrier,
    (d.q1SliceAtom p).transposedAtom.complexCRTSmoothNonzeroPart

/-- The actual p-carrier is summed after genuine admissible slice bounds.
No independent second first-factor variable is introduced. -/
theorem original_sharedResidual_boundary :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
      MediumAdmissible B sigma kappa c0 d →
        ‖sharedResidual d‖ ≤ C*d.Q1*d.U^2*d.physicalFactorCap^4/d.V := by
  obtain ⟨C,hC,hbound⟩ := original_full_nonzero_boundary
  refine ⟨2*C,by positivity,fun B sigma kappa c0 d hd => ?_⟩
  have hV : 0 < d.V := zero_lt_one.trans_le hd.2.1
  have hpCard : (d.primitiveFirstFactorCarrier.card : ℝ) ≤ 2*d.Q1 := by
    have hc := Finset.card_le_card (Finset.filter_subset
      (fun p : ℕ => p.Coprime d.residue.natAbs) (factorCarrier d.Q1))
    have hi := ElementaryTauTruncation.IntervalPayment.card_nat_ceiling_floor_le_length_add_one
      (a := d.Q1) (b := 2*d.Q1) (by linarith [hd.2.2.1]) (by linarith [hd.2.2.1])
    have hh : (d.primitiveFirstFactorCarrier.card : ℝ) ≤ ((factorCarrier d.Q1).card : ℝ) :=
      by exact_mod_cast hc
    change ((factorCarrier d.Q1).card : ℝ) ≤ 2*d.Q1-d.Q1+1 at hi
    linarith [hd.2.2.1]
  unfold sharedResidual
  calc
    _ ≤ ∑ p ∈ d.primitiveFirstFactorCarrier,
        ‖(d.q1SliceAtom p).transposedAtom.complexCRTSmoothNonzeroPart‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ d.primitiveFirstFactorCarrier, C*d.U^2*d.physicalFactorCap^4/d.V := by
      apply Finset.sum_le_sum
      intro p hp
      exact hbound B sigma kappa c0 (d.q1SliceAtom p) (mediumAdmissible_q1SliceAtom hd hp)
    _ = (d.primitiveFirstFactorCarrier.card : ℝ) * (C*d.U^2*d.physicalFactorCap^4/d.V) := by simp
    _ ≤ (2*d.Q1) * (C*d.U^2*d.physicalFactorCap^4/d.V) :=
      mul_le_mul_of_nonneg_right hpCard (by positivity)
    _ = (2*C)*d.Q1*d.U^2*d.physicalFactorCap^4/d.V := by ring

end
end ImbalancedChen.Part3.OriginalSharedResidualBoundary20261026b
