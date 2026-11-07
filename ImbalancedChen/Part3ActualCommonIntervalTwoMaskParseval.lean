import ImbalancedChen.Part3ActualCommonIntervalCompletionParseval
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED, 2026-10-24. Two masks on ONE common interval:
finite cross Parseval for the actual normalized DFT, exact overlap of the
clamped physical intervals, and a Gram identity that cancels the completed
phase only when both masks use the SAME completed phase.

The wrapped generalization has `sum_r occupancy_I(r)*occupancy_J(r)/q`.
Distinct masks are never contracted to their separate lengths or to zero.
No analytic/spectral return is inferred from this finite identity.
-/

namespace ImbalancedChen.Part3.ActualCommonIntervalTwoMaskParsevalSourceOnly
noncomputable section
open Classical Finset
open scoped BigOperators ComplexConjugate
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ImbalancedChen.Part3.ActualCommonMaskSourceOnly
open ImbalancedChen.Part3.ActualCommonIntervalCompletionSourceOnly
open ImbalancedChen.Part3.ActualCommonIntervalCompletionL1SourceOnly
open ImbalancedChen.Part3.ActualCommonIntervalCompletionParsevalSourceOnly

variable {ι : Type*}

private theorem char_star {q : ℕ} [NeZero q] (x : ZMod q) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hn : ‖ZMod.stdAddChar x‖ = 1 := by
    simpa only [ZMod.stdAddChar_apply] using Circle.norm_coe (ZMod.toCircle x)
  have hneg : ZMod.stdAddChar (-x) * ZMod.stdAddChar x = 1 := by
    rw [← ZMod.stdAddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hstar : star (ZMod.stdAddChar x) * ZMod.stdAddChar x = 1 := by
    rw [mul_comm]
    change ZMod.stdAddChar x * conj (ZMod.stdAddChar x) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn, one_pow,
      Complex.ofReal_one]
  exact (eq_inv_of_mul_eq_one_left hstar).trans
    (eq_inv_of_mul_eq_one_left hneg).symm

/-- Cross Parseval for the same complete additive-character convention as
`ZMod.dft`. The order of conjugation fixes the orientation of the Gram. -/
theorem finite_dft_cross (q : ℕ) [NeZero q] (f g : ZMod q → ℂ) :
    (∑ h : ZMod q, star (ZMod.dft f h) * ZMod.dft g h) =
      (q : ℂ) * ∑ r : ZMod q, star (f r) * g r := by
  have hpoint (h : ZMod q) :
      star (ZMod.dft f h) * ZMod.dft g h =
        ∑ r : ZMod q, ∑ s : ZMod q,
          star (f r) * g s * ZMod.stdAddChar (h * (r - s)) := by
    rw [ZMod.dft_apply, ZMod.dft_apply, star_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    apply Finset.sum_congr rfl
    intro s _hs
    simp only [smul_eq_mul]
    calc
      star (ZMod.stdAddChar (-(r * h)) * f r) *
          (ZMod.stdAddChar (-(s * h)) * g s) =
        star (f r) * g s *
          (star (ZMod.stdAddChar (-(r * h))) *
            ZMod.stdAddChar (-(s * h))) := by
        rw [star_mul]
        ring
      _ = star (f r) * g s * ZMod.stdAddChar (h * (r - s)) := by
        rw [char_star, ← ZMod.stdAddChar.map_add_eq_mul]
        congr 1
        ring
  calc
    (∑ h : ZMod q, star (ZMod.dft f h) * ZMod.dft g h) =
        ∑ h : ZMod q, ∑ r : ZMod q, ∑ s : ZMod q,
          star (f r) * g s * ZMod.stdAddChar (h * (r - s)) := by
      apply Finset.sum_congr rfl
      intro h _hh
      exact hpoint h
    _ = ∑ r : ZMod q, ∑ s : ZMod q,
          star (f r) * g s *
            (∑ h : ZMod q, ZMod.stdAddChar (h * (r - s))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _hr
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _hs
      rw [Finset.mul_sum]
    _ = _ := by
      simp_rw [ImbalancedChen.Part3.sum_stdAddChar_mul_eq]
      simp only [sub_eq_zero]
      simp [Finset.mul_sum, mul_assoc]

theorem finite_dft_normalized_cross (q : ℕ) [NeZero q]
    (f g : ZMod q → ℂ) :
    (∑ h : ZMod q,
      star ((q : ℂ)⁻¹ * ZMod.dft f h) *
        ((q : ℂ)⁻¹ * ZMod.dft g h)) =
      (q : ℂ)⁻¹ * ∑ r : ZMod q, star (f r) * g r := by
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q
  simp only [star_mul, map_inv₀, star_natCast]
  calc
    _ = ((q : ℂ)⁻¹ * (q : ℂ)⁻¹) *
          ∑ h : ZMod q, star (ZMod.dft f h) * ZMod.dft g h := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _hh
      ring
    _ = _ := by rw [finite_dft_cross]; field_simp [hq]

/-- General wrapped two-interval occupancy dot product. The intervals may
wind around the same modulus any number of times. -/
theorem wrapped_two_mask_cross (L₁ U₁ L₂ U₂ q : ℕ) [NeZero q] :
    (∑ h : ZMod q,
      star ((q : ℂ)⁻¹ * wrappedIntervalCoeff L₁ U₁ q h) *
        ((q : ℂ)⁻¹ * wrappedIntervalCoeff L₂ U₂ q h)) =
      (q : ℂ)⁻¹ * ∑ r : ZMod q,
        (wrappedOccupancy L₁ U₁ q r : ℂ) *
          (wrappedOccupancy L₂ U₂ q r : ℂ) := by
  let f : ZMod q → ℂ := fun r => (wrappedOccupancy L₁ U₁ q r : ℂ)
  let g : ZMod q → ℂ := fun r => (wrappedOccupancy L₂ U₂ q r : ℂ)
  have hfi (h : ZMod q) : wrappedIntervalCoeff L₁ U₁ q h = ZMod.dft f h := by
    rw [wrappedIntervalCoeff_eq_occupancy_dft, ZMod.dft_apply]
    simp only [f, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro r _hr
    congr 1
    ring
  have hfj (h : ZMod q) : wrappedIntervalCoeff L₂ U₂ q h = ZMod.dft g h := by
    rw [wrappedIntervalCoeff_eq_occupancy_dft, ZMod.dft_apply]
    simp only [g, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro r _hr
    congr 1
    ring
  simp_rw [hfi, hfj]
  simpa only [f, g, star_natCast] using finite_dft_normalized_cross q f g

private theorem commonInterval_subset_range (P : PacketData ι) (a b q : ℕ)
    (hperiod : P.hi < q) : commonInterval P a b ⊆ Finset.range q := by
  intro m hm
  have hmP := (Finset.mem_inter.mp hm).2
  exact Finset.mem_range.mpr
    ((Finset.mem_Ico.mp hmP).2.trans hperiod)

/-- Directly counts the intersection of the two actual cyclic indicators.
The common period gate makes every physical m its own residue. -/
private theorem cyclicIndicator_cross_overlap (P : PacketData ι)
    (a b c d q : ℕ) [NeZero q] (hperiod : P.hi < q) :
    (∑ r : ZMod q,
      star (cyclicIndicator P a b q r) * cyclicIndicator P c d q r) =
        ((commonInterval P a b ∩ commonInterval P c d).card : ℂ) := by
  have hterm (r : ZMod q) :
      star (cyclicIndicator P a b q r) * cyclicIndicator P c d q r =
        if r.val ∈ commonInterval P a b ∩ commonInterval P c d then
          (1 : ℂ) else 0 := by
    simp only [cyclicIndicator, Finset.mem_inter]
    split_ifs <;> simp_all
  simp_rw [hterm]
  rw [sum_zmod_val_reindex q (fun m =>
    if m ∈ commonInterval P a b ∩ commonInterval P c d then (1 : ℂ) else 0)]
  rw [← Finset.sum_filter]
  have hsub : commonInterval P a b ∩ commonInterval P c d ⊆ Finset.range q :=
    (Finset.inter_subset_left).trans (commonInterval_subset_range P a b q hperiod)
  have hfilter : (Finset.range q).filter
      (fun m => m ∈ commonInterval P a b ∩ commonInterval P c d) =
        commonInterval P a b ∩ commonInterval P c d := by
    ext m
    simp only [Finset.mem_filter]
    constructor
    · exact fun hm => hm.2
    · exact fun hm => ⟨hsub hm, hm⟩
  rw [hfilter]
  simp

/-- Exact cross Parseval for the two ACTUAL normalized masks. The same
physical phase is still in the shifted packet sums, not in these DFT masks. -/
theorem actual_two_mask_cross (P : PacketData ι) (a b c d q : ℕ)
    [NeZero q] (hperiod : P.hi < q) :
    (∑ h : ZMod q,
      star (normalizedFourierCoeff P a b q h) *
        normalizedFourierCoeff P c d q h) =
      ((commonInterval P a b ∩ commonInterval P c d).card : ℂ) / q := by
  simp only [normalizedFourierCoeff, finiteFourierCoeff]
  rw [finite_dft_normalized_cross,
    cyclicIndicator_cross_overlap P a b c d q hperiod]
  ring

/-- The overlap as a single explicit endpoint expression. Both intervals
use the same underlying `P.mCarrier`. -/
theorem commonInterval_overlap_card (P : PacketData ι) (a b c d : ℕ) :
    (commonInterval P a b ∩ commonInterval P c d).card =
      min (completionHi P a b) (completionHi P c d) -
        max (completionLo P a b) (completionLo P c d) := by
  rw [commonInterval_eq_Ico, commonInterval_eq_Ico]
  have he : Finset.Ico (completionLo P a b) (completionHi P a b) ∩
      Finset.Ico (completionLo P c d) (completionHi P c d) =
      Finset.Ico (max (completionLo P a b) (completionLo P c d))
        (min (completionHi P a b) (completionHi P c d)) := by
    ext m
    simp only [Finset.mem_inter, Finset.mem_Ico]
    omega
  rw [he]
  simp

theorem actual_two_mask_cross_endpoints (P : PacketData ι) (a b c d q : ℕ)
    [NeZero q] (hperiod : P.hi < q) :
    (∑ h : ZMod q,
      star (normalizedFourierCoeff P a b q h) *
        normalizedFourierCoeff P c d q h) =
      ((min (completionHi P a b) (completionHi P c d) -
        max (completionLo P a b) (completionLo P c d) : ℕ) : ℂ) / q := by
  rw [actual_two_mask_cross P a b c d q hperiod,
    commonInterval_overlap_card]

/-- Disjoint actual intervals are orthogonal after the *complete* frequency
sum. This is not a claim about any one frequency or packet sum. -/
theorem actual_two_mask_cross_zero_of_disjoint (P : PacketData ι)
    (a b c d q : ℕ) [NeZero q] (hperiod : P.hi < q)
    (hdisj : Disjoint (commonInterval P a b) (commonInterval P c d)) :
    (∑ h : ZMod q,
      star (normalizedFourierCoeff P a b q h) *
        normalizedFourierCoeff P c d q h) = 0 := by
  rw [actual_two_mask_cross P a b c d q hperiod,
    Finset.disjoint_iff_inter_eq_empty.mp hdisj]
  simp

/-- Exact Gram entry for two possibly different physical phases. It is
*not* replaced by overlap cardinal unless the two phases are identical. -/
theorem common_mask_physical_gram (P : PacketData ι) (a b c d : ℕ)
    (k k' : D4 → ℤ) :
    (∑ m ∈ P.mCarrier,
      star (commonMaskWeight P a b k m) * commonMaskWeight P c d k' m) =
      ∑ m ∈ commonInterval P a b ∩ commonInterval P c d,
        star ((P.completed k).weight m) * (P.completed k').weight m := by
  have hset : commonInterval P a b ∩ commonInterval P c d =
      P.mCarrier.filter (fun m => m ∈ Finset.Ico a b ∧ m ∈ Finset.Ico c d) := by
    ext m
    simp only [commonInterval, Finset.mem_inter, Finset.mem_filter]
    tauto
  rw [hset, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _hm
  by_cases hI : m ∈ Finset.Ico a b <;>
    by_cases hJ : m ∈ Finset.Ico c d <;>
      simp [commonMaskWeight, hI, hJ]

/-- The same completed phase cancels pointwise on the intersection. This
does not assert cancellation between different masks or different phases. -/
theorem common_mask_same_phase_overlap (P : PacketData ι) (a b c d : ℕ)
    (k : D4 → ℤ) :
    (∑ m ∈ P.mCarrier,
      star (commonMaskWeight P a b k m) * commonMaskWeight P c d k m) =
        ((commonInterval P a b ∩ commonInterval P c d).card : ℂ) := by
  rw [common_mask_physical_gram]
  have hpoint (m : ℕ) (hm : m ∈ commonInterval P a b ∩ commonInterval P c d) :
      star ((P.completed k).weight m) * (P.completed k).weight m = 1 := by
    have hmP : m ∈ P.mCarrier :=
      (Finset.mem_inter.mp (Finset.mem_inter.mp hm).1).2
    have hn := P.completed_weight_norm_mem k m hmP
    change conj ((P.completed k).weight m) * (P.completed k).weight m = 1
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn,
      one_pow, Complex.ofReal_one]
  calc
    (∑ m ∈ commonInterval P a b ∩ commonInterval P c d,
        star ((P.completed k).weight m) * (P.completed k).weight m) =
        ∑ _m ∈ commonInterval P a b ∩ commonInterval P c d, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact hpoint m hm
    _ = _ := by simp

end
end ImbalancedChen.Part3.ActualCommonIntervalTwoMaskParsevalSourceOnly
