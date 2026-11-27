import ImbalancedChen.P3OriginalU5JointPrimeWallPayment
import ImbalancedChen.P3OriginalU5PhysicalRawRank

/-!
The joint finite-cell lower coefficient has an arbitrarily small
pre-attachment density loss on the complete original pair carrier.
The width and threshold precede every target and every finer rounding.
-/

namespace ImbalancedChen.P3OriginalU5JointRoughRoundingPayment

noncomputable section
open scoped Classical BigOperators
open P2OriginalPairSourceReceiver (PairRange)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P3OriginalU5JointCellCoefficient
open P3OriginalU5JointPrimeWallPayment
open P3OriginalU5PhysicalRawRank (physical_raw_level_and_rank)
open P3OriginalU5RoundedModulusCap (rawRank)
open P5OriginalU5CausalFinite (pairSupport cutoff)
open P5OriginalU5PlateauPrimeBV (fullModulus)

/-- An actual good member of the joint fine cell bounds the rank of the
charged row, including when the charged row itself was rejected. -/
theorem gap_rank_le (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (hb : 0 ≤ b) (m : ℕ) {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (he : 0 < epsilon) (tau : ℝ) {x : Point} (hx : x ∈ carrier N epsilon)
    (hne : coefficient R bank b m N epsilon tau x ≠ rawCoefficient R bank b m N epsilon x) :
    x.2.primeFactorsList.length ≤ rawRank epsilon := by
  obtain ⟨y, hy, hd⟩ := retained_difference_of_coefficient_ne_raw R bank b m N epsilon tau hx hne
  by_cases hret : retained R bank b m N epsilon x
  · exact (physical_raw_level_and_rank R bank b hb m epsilon he hN
      (Finset.mem_product.mp hx).1 (Nat.ceil (cutoff N)) hret).2
  · have hyret : retained R bank b m N epsilon y := by
      by_contra hnot
      exact hd (iff_of_false hret hnot)
    obtain ⟨hysrc, hlabel⟩ := Finset.mem_filter.mp hy
    have hlen := same_rough_length R m N tau hlabel
    rw [← hlen]
    exact (physical_raw_level_and_rank R bank b hb m epsilon he hN
      (Finset.mem_product.mp hysrc).1 (Nat.ceil (cutoff N)) hyret).2

/-- Exact decomposition of the existing absolute loss, retaining the
two exterior marks in the denominator at each rank. -/
theorem roundingLoss_eq_sum_ranks (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (hb : 0 ≤ b) (m : ℕ) {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (he : 0 < epsilon) (he8 : epsilon < 1 / 8) (tau : ℝ) :
    roundingLoss R bank b m N epsilon tau =
      ∑ i : Fin (rawRank epsilon + 1), rankRoundingLoss R bank b m N i.val epsilon tau := by
  let M := rawRank epsilon
  let cf := coefficient R bank b m N epsilon tau
  let raw := rawCoefficient R bank b m N epsilon
  let f (x : Point) := |cf x - raw x| * rowWeight x
  have hs (x : Point) (hx : x ∈ carrier N epsilon) :
      f x = ∑ i : Fin (M + 1), if x.2.primeFactorsList.length = i.val then f x else 0 := by
    by_cases hr : x.2.primeFactorsList.length ≤ M
    · let j : Fin (M + 1) := ⟨x.2.primeFactorsList.length, by omega⟩
      rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
      · exact (if_pos rfl).symm
      · intro i _ hi
        exact if_neg (fun hh => hi (Fin.ext hh.symm))
    · have hzero : cf x = raw x := by
        by_contra hne
        exact hr (gap_rank_le R bank b hb m hN he tau hx hne)
      simp [f, hzero]
  calc
    _ = ∑ x ∈ carrier N epsilon, |cf x - raw x| / (Nat.totient (fullModulus x.1 x.2) : ℝ) := by
      simp only [roundingLoss, carrier, Finset.sum_product, cf, raw]
    _ = ∑ x ∈ carrier N epsilon, f x := by
      apply Finset.sum_congr rfl
      intro x hx
      dsimp only [f]
      rw [rowWeight_eq_full hN he he8 hx]
      ring
    _ = ∑ x ∈ carrier N epsilon, ∑ i : Fin (M + 1),
        if x.2.primeFactorsList.length = i.val then f x else 0 := Finset.sum_congr rfl hs
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [rankRoundingLoss, Finset.sum_filter, f, cf, raw]

/-- The pre-attachment comparison uses a fixed positive presieve
exponent and the one chosen physical policy on all original pairs. -/
theorem exists_joint_rough_rounding_payment (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (b : ℚ) (hb : 0 ≤ b) (m : ℕ) {epsilon : ℝ} (he : 0 < epsilon)
    (he8 : epsilon < 1 / 8) {eta : ℝ} (heta : 0 < eta) :
    ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ {N : ℕ}, N0 ≤ N → ∀ {tau : ℝ}, 0 < tau → tau ≤ tau0 →
        roundingLoss R bank b m N epsilon tau < eta := by
  let M := rawRank epsilon
  let e := eta / ((M : ℝ) + 2) / 2
  have hepos : 0 < e := by dsimp [e]; positivity
  have heach (i : Fin (M + 1)) := exists_joint_charged_row_payment R bank b m i.val he he8 hepos
  choose width hwidth threshold _hthreshold hpay using heach
  let widths := insert (1 : ℝ) (Finset.univ.image width)
  have hn : widths.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let tau0 := widths.min' hn
  have htau0 : 0 < tau0 := by
    have hm : tau0 ∈ widths := Finset.min'_mem _ _
    rcases Finset.mem_insert.mp hm with h | h
    · rw [h]
      exact zero_lt_one
    · obtain ⟨r, _, h⟩ := Finset.mem_image.mp h
      exact h ▸ hwidth r
  have hle (i : Fin (M + 1)) : tau0 ≤ width i :=
    Finset.min'_le widths (width i)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
  refine ⟨tau0, htau0, max 2 (Finset.univ.sup threshold), le_max_left _ _, ?_⟩
  intro N hN tau ht ht'
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hsum : (∑ i : Fin (M + 1), rankRoundingLoss R bank b m N i.val epsilon tau) ≤
      ∑ _i : Fin (M + 1), 2 * e := by
    apply Finset.sum_le_sum
    intro i _
    have hi : threshold i ≤ N := (Finset.le_sup (f := threshold) (Finset.mem_univ i)).trans
      ((le_max_right _ _).trans hN)
    exact (rankRoundingLoss_le R bank b m i.val hN2 epsilon tau).trans
      (mul_le_mul_of_nonneg_left (hpay i hi ht (ht'.trans (hle i))).le (by norm_num))
  have hbound : (∑ i : Fin (M + 1), rankRoundingLoss R bank b m N i.val epsilon tau) ≤
      ((M : ℝ) + 1) * (2 * e) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one] using hsum
  have hreserve : ((M : ℝ) + 1) * (2 * e) < eta := by
    calc
      _ = (((M : ℝ) + 1) * eta) / ((M : ℝ) + 2) := by dsimp only [e]; ring
      _ < eta := (div_lt_iff₀ (by positivity : 0 < (M : ℝ) + 2)).mpr (by nlinarith only [heta])
  rw [roundingLoss_eq_sum_ranks R bank b hb m hN2 he he8 tau]
  exact hbound.trans_lt hreserve

end
end ImbalancedChen.P3OriginalU5JointRoughRoundingPayment
