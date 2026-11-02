import ImbalancedChen.Part3OriginalLinearDiscardModulusBinding
import ImbalancedChen.Part3OriginalS2NativePhysicalRange
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The preliminary LINEAR discard has the original inclusive smooth tail
on its complete physical modulus. This is a support theorem for the
independently defined discardedFactorGamma, not an S2 mixed-tail model.
-/

namespace ImbalancedChen.Part3.OriginalLinearDiscardSmoothSupport20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open MediumActualPreliminaryCauchy20261028 MediumGlobalDyadicOwnership20261028
open MediumReceiverCutoffArithmetic20261028 MediumCanonicalFixedBlock20261028
open OriginalLinearDiscardModulusBinding20261028
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3OriginalS2SmoothModulusValuationBridge
open ImbalancedChen.Part3OriginalS2NativePsiGeometry
open ImbalancedChen.Part3OriginalS2NativePhysicalRange

theorem original_factorCarrier_bounds {Q : ℝ} (hQ : 1 ≤ Q) {q : ℕ}
    (hq : q ∈ factorCarrier Q) : 0 < q ∧ Q ≤ (q : ℝ) ∧ (q : ℝ) ≤ 2 * Q := by
  obtain ⟨hlo, hhi⟩ := mem_Icc.mp hq
  have hlow : Q ≤ (q : ℝ) := (Nat.le_ceil Q).trans (by exact_mod_cast hlo)
  exact ⟨by exact_mod_cast (zero_lt_one.trans_le (hQ.trans hlow)), hlow,
    (show (q : ℝ) ≤ (Nat.floor (2 * Q) : ℝ) by exact_mod_cast hhi).trans
      (Nat.floor_le (by linarith))⟩

private theorem original_gamma_norm_le_one {B : ℕ} {σ κ c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B σ κ c0 atom)
    {r : ℕ × ℕ × ℕ} (hr : r ∈ atom.complexFactorLabels) :
    ‖atom.complexFactorGamma r‖ ≤ 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3⟩ := hA
  obtain ⟨h1r, h23⟩ := mem_product.mp hr
  obtain ⟨h2r, h3r⟩ := mem_product.mp h23
  rw [MediumAtom.complexFactorGamma, norm_mul, norm_mul]
  calc
    _ ≤ 1 * 1 * 1 := mul_le_mul
      (mul_le_mul (h1 _ h1r).1 (h2 _ h2r).1 (norm_nonneg _) zero_le_one)
      (h3 _ h3r).1 (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

/-- A fixed ordinary-divisor majorant, with all ordered physical labels
still counted. No one-bounded grouped-coefficient premise is used. -/
theorem discardedFactorGamma_norm_le_tau_cube {B : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (hA : MediumAdmissible B σ κ c0 atom)
    (receiver y : ℝ) (ell : ℕ) (hell : 0 < ell) :
    ‖discardedFactorGamma atom receiver y ell‖ ≤ (ell.divisors.card : ℝ) ^ 3 := by
  have hcard : (atom.physicalFactorFiber ell).card ≤
      (ell.divisors ×ˢ (ell.divisors ×ˢ ell.divisors)).card := by
    apply card_le_card_of_injOn (fun r : ℕ × ℕ × ℕ => r)
    · intro r hr
      have heq := (mem_filter.mp hr).2
      have h1 : r.1 ∣ ell := ⟨r.2.1 * r.2.2, by
        rw [← heq]; unfold complexFactorModulus; ring⟩
      have h2 : r.2.1 ∣ ell := ⟨r.1 * r.2.2, by
        rw [← heq]; unfold complexFactorModulus; ring⟩
      have h3 : r.2.2 ∣ ell := ⟨r.1 * r.2.1, by
        rw [← heq]; unfold complexFactorModulus; ring⟩
      exact mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨h1, hell.ne'⟩,
        mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨h2, hell.ne'⟩,
          Nat.mem_divisors.mpr ⟨h3, hell.ne'⟩⟩⟩
    · intro r hr s hs hrs
      exact hrs
  calc
    _ ≤ ∑ r ∈ atom.physicalFactorFiber ell,
        ‖if ¬Retained receiver y (r.2.1, r.2.2) then atom.complexFactorGamma r else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _r ∈ atom.physicalFactorFiber ell, (1 : ℝ) := by
      apply sum_le_sum
      intro r hr
      split_ifs
      · exact original_gamma_norm_le_one hA (mem_filter.mp hr).1
      · norm_num
    _ = ((atom.physicalFactorFiber ell).card : ℝ) := by simp
    _ ≤ ((ell.divisors ×ˢ (ell.divisors ×ˢ ell.divisors)).card : ℝ) := by
      exact_mod_cast hcard
    _ = _ := by simp only [card_product, Nat.cast_mul]; ring

theorem nonzero_discardedFactorGamma_has_original_label (atom : MediumAtom)
    (receiver y : ℝ) (ell : ℕ)
    (hne : discardedFactorGamma atom receiver y ell ≠ 0) :
    ∃ r ∈ atom.physicalFactorFiber ell,
      ¬Retained receiver y (r.2.1, r.2.2) ∧ atom.complexFactorGamma r ≠ 0 := by
  by_contra h
  push_neg at h
  apply hne
  unfold discardedFactorGamma
  apply sum_eq_zero
  intro r hr
  by_cases hb : ¬Retained receiver y (r.2.1, r.2.2)
  · exact (if_pos hb).trans (h r hr hb)
  · exact if_neg hb

private theorem inclusive_smooth_pos (z : ℝ) (q : ℕ) : 0 < zSmoothPart z q := by
  unfold zSmoothPart
  apply prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos _

private theorem inclusive_smooth_le_of_dvd (z : ℝ) {q ell : ℕ}
    (hq : 0 < q) (hell : 0 < ell) (hdiv : q ∣ ell) :
    zSmoothPart z q ≤ zSmoothPart z ell := by
  have hsdiv : zSmoothPart z q ∣ ell :=
    (show zSmoothPart z q ∣ q from
      ⟨zRoughPart z q, (zSmoothPart_mul_zRoughPart hq z).symm⟩).trans hdiv
  have hsmooth : ∀ p : ℕ, z < (p : ℝ) → (zSmoothPart z q).factorization p = 0 := by
    intro p hp
    simp only [factorization_zSmoothPart, if_neg (not_le.mpr hp)]
  exact Nat.le_of_dvd (inclusive_smooth_pos z ell)
    (smooth_divisor_dvd_smooth_multiple z (inclusive_smooth_pos z q) hell hsmooth hsdiv)

/-- The deleted original q2 or q3 smooth part divides the complete
modulus's smooth part. This includes p=z and repeated prime powers. -/
theorem nonzero_original_linear_discard_has_collapsed_smooth_support
    {B : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom)
    (hA : MediumAdmissible B σ κ c0 atom) (z : ℝ) (hz : 0 ≤ z)
    (ell : ℕ) (hell : 0 < ell)
    (hne : discardedFactorGamma atom (strictReceiverCutoff z) (roughY atom.scale) ell ≠ 0) :
    roughY atom.scale < (zSmoothPart z ell : ℝ) := by
  obtain ⟨r, hr, hb, hγ⟩ :=
    nonzero_discardedFactorGamma_has_original_label atom _ _ ell hne
  obtain ⟨h1r, h23⟩ := mem_product.mp (mem_filter.mp hr).1
  obtain ⟨h2r, h3r⟩ := mem_product.mp h23
  have h2 := (original_factorCarrier_bounds hA.2.2.2.1 h2r).1
  have h3 := (original_factorCarrier_bounds hA.2.2.2.2.1 h3r).1
  have hmod := (mem_filter.mp hr).2
  have h2div : r.2.1 ∣ ell := ⟨r.1 * r.2.2, by
    rw [← hmod]; unfold complexFactorModulus; ring⟩
  have h3div : r.2.2 ∣ ell := ⟨r.1 * r.2.1, by
    rw [← hmod]; unfold complexFactorModulus; ring⟩
  have hbad : roughY atom.scale < (zSmoothPart z r.2.1 : ℝ) ∨
      roughY atom.scale < (zSmoothPart z r.2.2 : ℝ) := by
    by_contra h
    push_neg at h
    apply hb
    exact ⟨h2.ne', h3.ne',
      by simpa only [← originalSmooth_eq_receiver z hz] using h.1,
      by simpa only [← originalSmooth_eq_receiver z hz] using h.2⟩
  rcases hbad with hb2 | hb3
  · exact hb2.trans_le (by exact_mod_cast inclusive_smooth_le_of_dvd z h2 hell h2div)
  · exact hb3.trans_le (by exact_mod_cast inclusive_smooth_le_of_dvd z h3 hell h3div)

theorem physicalFactorModulus_le_native_cap {B : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (hA : MediumAdmissible B σ κ c0 atom)
    {ell : ℕ} (hell : ell ∈ atom.physicalFactorModuli) :
    0 < ell ∧ ell ≤ nativePhysicalCap atom := by
  have hcap := mem_Ioc.mp (atom.physicalFactorModuli_subset_cap hA hell)
  refine ⟨hcap.1, hcap.2.trans ?_⟩
  apply Nat.floor_mono
  unfold MediumAtom.physicalFactorCap
  have h1 : 0 ≤ atom.Q1 := zero_le_one.trans hA.2.2.1
  have h2 : 0 ≤ atom.Q2 := zero_le_one.trans hA.2.2.2.1
  have h3 : 0 ≤ atom.Q3 := zero_le_one.trans hA.2.2.2.2.1
  nlinarith [mul_nonneg (mul_nonneg h1 h2) h3]

/-- Original range (7) and the actual nonzero discarded coefficient
jointly discharge both gates of the already proved arithmetic tail (8). -/
theorem actual_linear_discard_modulus_mem_collapsed_filter
    {B : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom)
    (hA : MediumAdmissible B σ κ c0 atom) (hσ : 0 ≤ σ) (hc0 : 0 < c0)
    (hx : (10 : ℝ) ^ (10 : ℕ) ≤ atom.scale) (z : ℝ) (hz : 0 ≤ z)
    {ell : ℕ} (hell : ell ∈ atom.physicalFactorModuli)
    (hne : discardedFactorGamma atom (strictReceiverCutoff z) (roughY atom.scale) ell ≠ 0) :
    ell ∈ (Icc 1 (Nat.floor (atom.scale ^ ((4 : ℝ) / 5)))).filter
      (fun ell => roughY atom.scale < (zSmoothPart z ell : ℝ)) := by
  obtain ⟨hellpos, hcap⟩ := physicalFactorModulus_le_native_cap atom hA hell
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hellpos,
    hcap.trans (nativePhysicalCap_le_original_range hA hσ
      (residue_ne_zero_of_original_c0 hA hc0) hx)⟩,
    nonzero_original_linear_discard_has_collapsed_smooth_support atom hA z hz ell hellpos hne⟩

end
end ImbalancedChen.Part3.OriginalLinearDiscardSmoothSupport20261102
