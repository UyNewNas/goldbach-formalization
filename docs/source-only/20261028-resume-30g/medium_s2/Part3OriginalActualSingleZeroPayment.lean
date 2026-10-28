import ImbalancedChen.Part3OriginalActualSingleZeroCounting
import ImbalancedChen.Part3OriginalS2NativePhysicalRange
import Mathlib.Tactic

/-! Genuine first/second single-zero restoration payment at
Rcal*(N+Y)*x^epsilon, on the unchanged original primitive paired source.
All divisor envelopes in the finite count are discharged by the existing
classical subpower theorem. SOURCE ONLY / UNCOMPILED / ZERO CREDIT. -/

namespace ImbalancedChen.Part3OriginalActualSingleZeroPayment

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalActualSingleZeroSource
open ImbalancedChen.Part3OriginalSingleZeroPolynomialTau
open ImbalancedChen.Part3OriginalActualSingleZeroCounting
open ImbalancedChen.Part3OriginalS2NativePhysicalRange
open ImbalancedChen.Part3OriginalS2ActualKeyCoefficients
open ImbalancedChen.Part3OriginalS2ActualTailTransfer
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3OriginalCanonicalS2Stages
open ImbalancedChen.Part3OriginalS2RoughScalePayment
open ImbalancedChen.Part3OriginalS2ActualBlockGeometry
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumLiteralS3Deleted20261028
open ImbalancedChen.Part3.MediumDeletedIndicatorShift20261028
open ImbalancedChen.Part3.MediumSingleZeroFiber20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3.OriginalMediumS1SeparatedDivisorMean
open ImbalancedChen.Part3.OriginalGevreyFinalPsi20261028
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
open Classical Finset
open scoped BigOperators

noncomputable section

theorem actual_first_zero_term_norm_le_lambda_square
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key)
    (H : ℕ)
    (hλ : ∀ small ∈ dyadicWindow k.d, ∀ r ∈ dyadicWindow k.w,
      ‖lambdaTrim d z y k small r‖ ≤ (H : ℝ))
    (t : PairIndex) (ht : t ∈ pairedCarrier d k) :
    ‖firstZeroTerm d z y k t‖ ≤ (H : ℝ) ^ 2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAlpha, _, _, _, _, _⟩ := hd
  have houter := (Finset.mem_filter.mp (Finset.mem_product.mp ht).1).1
  have hdwin := (Finset.mem_product.mp (Finset.mem_product.mp houter).2).1
  have hij := Finset.mem_product.mp (Finset.mem_product.mp ht).2
  have hi := Finset.mem_product.mp hij.1
  have hj := Finset.mem_product.mp hij.2
  have hψq := paperPsi_le_one ((t.1.1 : ℝ) / d.Q1)
  have hψm := paperPsi_le_one ((t.1.2.2 : ℝ) / d.V)
  have hψq0 := paperPsi_nonneg ((t.1.1 : ℝ) / d.Q1)
  have hψm0 := paperPsi_nonneg ((t.1.2.2 : ℝ) / d.V)
  have hΨ : ‖(jointPsi d t.1 : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (jointPsi_nonneg d t.1)]
    exact (by simpa only [jointPsi, paperQWeight,
      ImbalancedChen.Part3.OriginalGevreySharedRowDictionary20261028.paperMWeight, one_mul] using
      mul_le_mul hψq hψm hψm0 (by norm_num : (0 : ℝ) ≤ 1))
  have hzero := zeroIndicator_norm_le_one d.residue (oldIndex t).n1 (oldIndex t).m
  have hdel := deletedIndicator_norm_le_one d.residue
    (((oldIndex t).q * (oldIndex t).d) * (oldIndex t).s) (oldIndex t).n2 (oldIndex t).m
  unfold firstZeroTerm pairCoefficient
  simp only [norm_mul, norm_star]
  calc
    _ ≤ 1 * (H : ℝ) * H * 1 * 1 * 1 * 1 := by
      gcongr <;> first | exact hΨ | exact hλ _ hdwin _ hi.1 |
        exact hλ _ hdwin _ hj.1 | exact hAlpha _ hi.2 | exact hAlpha _ hj.2 |
        exact hzero | exact hdel | positivity
    _ = _ := by ring

theorem actual_first_zero_norm_le_dischargable_integer_budget
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key) (H : ℕ)
    (ha : 0 < d.residue.natAbs) (hA : d.residue.natAbs.divisors.card ≤ H)
    (hshift : ∀ m ∈ paperPsiNaturalCarrier d.V,
      ∀ n ∈ Finset.Ico (Nat.ceil d.U) (Nat.floor (2 * d.U) + 1),
        (otherShiftAbs m n d.residue.natAbs).divisors.card ≤ H)
    (hλ : ∀ small ∈ dyadicWindow k.d, ∀ r ∈ dyadicWindow k.w,
      ‖lambdaTrim d z y k small r‖ ≤ (H : ℝ)) :
    ‖actualFirstZero d z y k‖ ≤
      24 * singleZeroR k * (d.U + singleZeroY d k) * (H : ℝ) ^ 4 := by
  rw [actualFirstZero_eq_active]
  calc
    _ ≤ ∑ t ∈ firstActive d z y k, ‖firstZeroTerm d z y k t‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ firstActive d z y k, (H : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      exact actual_first_zero_term_norm_le_lambda_square hd z y k H hλ t
        (firstActive_data hd z y k t ht).1
    _ = ((firstActive d z y k).card : ℝ) * (H : ℝ) ^ 2 := by simp
    _ ≤ (24 * singleZeroR k * (d.U + singleZeroY d k) * (H : ℝ) ^ 2) * (H : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (actual_first_zero_card_le hd z y k H ha hA hshift) (by positivity)
    _ = _ := by ring

/-- The integer H in the source count is now a specific floor of a
proved uniform divisor bound. There is no unproved hSingleZero budget. -/
theorem exists_actual_singleZeros_subpower_budget
    (kappa epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : ℕ) (sigma c0 : ℝ) (d : MediumAtom) (k : Key) (z : ℝ),
        MediumAdmissible B sigma kappa c0 d → 0 ≤ sigma → 0 < c0 → 0 ≤ z →
        ‖actualFirstZero d (strictReceiverCutoff z) (roughY d.scale) k‖ +
          ‖actualSecondZero d (strictReceiverCutoff z) (roughY d.scale) k‖ ≤
        C * (singleZeroR k * (d.U + singleZeroY d k) * d.scale ^ epsilon) := by
  let eta := epsilon / 4
  have heta : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨C0, hC0, hbound⟩ := exists_uniform_polynomial_tau kappa eta heta
  have hC0pos : 0 < C0 := zero_lt_one.trans_le hC0
  refine ⟨48 * C0 ^ (4 : ℕ), by positivity, ?_⟩
  intro B sigma c0 d k z hd hsigma hc0 hz
  have hx : 1 ≤ d.scale := by
    dsimp [MediumAtom.scale]
    nlinarith [hd.1, hd.2.1]
  have hxpos : 0 < d.scale := lt_of_lt_of_le zero_lt_one hx
  let H := Nat.floor (C0 * d.scale ^ eta)
  have hHreal : (H : ℝ) ≤ C0 * d.scale ^ eta := Nat.floor_le (by positivity)
  have hHone : 1 ≤ H := Nat.le_floor (by
    have hp := Real.one_le_rpow hx heta.le
    nlinarith)
  have hapos : 0 < d.residue.natAbs :=
    Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr (residue_ne_zero_of_original_c0 hd hc0))
  have hxK : d.scale ≤ d.scale ^ (max 1 (1 + kappa)) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (le_max_left 1 (1 + kappa))
  have haK : (d.residue.natAbs : ℝ) ≤ d.scale ^ (max 1 (1 + kappa)) :=
    hd.2.2.2.2.2.2.2.1.trans
      (Real.rpow_le_rpow_of_exponent_le hx (le_max_right 1 (1 + kappa)))
  have hAtau : d.residue.natAbs.divisors.card ≤ H := Nat.le_floor
    (hbound d.scale d.residue.natAbs hx hapos (by nlinarith [Real.rpow_nonneg hxpos.le (max 1 (1 + kappa))]))
  have hshift : ∀ m ∈ paperPsiNaturalCarrier d.V,
      ∀ n ∈ Finset.Ico (Nat.ceil d.U) (Nat.floor (2 * d.U) + 1),
        (otherShiftAbs m n d.residue.natAbs).divisors.card ≤ H := by
    intro m hm n hn
    by_cases hzero : otherShiftAbs m n d.residue.natAbs = 0
    · simpa [hzero] using (Nat.zero_le H)
    · exact Nat.le_floor (hbound d.scale (otherShiftAbs m n d.residue.natAbs) hx
        (Nat.pos_of_ne_zero hzero) (actual_single_zero_shift_polynomial_bound hd m n hm hn))
  have hλ : ∀ small ∈ dyadicWindow k.d, ∀ r ∈ dyadicWindow k.w,
      ‖lambdaTrim d (strictReceiverCutoff z) (roughY d.scale) k small r‖ ≤ (H : ℝ) := by
    intro small hsmall r hr
    by_cases hzero : lambdaTrim d (strictReceiverCutoff z) (roughY d.scale) k small r = 0
    · simp [hzero]
    have hK : keyKept d d.scale z k small r ≠ 0 := by
      rw [keyKept_eq_actual_lambdaTrim hd d.scale z hz k small r hsmall]
      exact hzero
    have hsupp := nonzero_labelSubset_support d z small r
      (fun v => keyPredicate z k v ∧
        ImbalancedChen.Part3OriginalS2SmoothYRankinStart.individualSmoothWithinY d.scale z v) hK
    have hp : 0 < small * r := Nat.mul_pos
      (dCarrier_pos d z small hsupp.1) (roughFiber_pos d z small r hsupp.2)
    have hprod := small_mul_rough_le_four hd z small r hsupp.2
    have h23 := Q2_mul_Q3_lt_scale hd hsigma
    have hpoly : ((small * r : ℕ) : ℝ) ≤ 8 * d.scale ^ (max 1 (1 + kappa)) := by
      nlinarith
    have hτ : (small * r).divisors.card ≤ H := Nat.le_floor (hbound d.scale (small * r) hx hp hpoly)
    exact (lambdaTrim_norm_le_tau d (strictReceiverCutoff z) (roughY d.scale) k small r hd).trans
      (by exact_mod_cast hτ)
  have hfirst := actual_first_zero_norm_le_dischargable_integer_budget hd
    (strictReceiverCutoff z) (roughY d.scale) k H hapos hAtau hshift hλ
  have hpow : (d.scale ^ eta) ^ (4 : ℕ) = d.scale ^ epsilon := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    congr 1
    dsimp [eta]
    ring
  rw [actualSecondZero_norm_eq_first]
  calc
    _ ≤ 2 * (24 * singleZeroR k * (d.U + singleZeroY d k) * (H : ℝ) ^ 4) := by linarith
    _ ≤ 2 * (24 * singleZeroR k * (d.U + singleZeroY d k) *
        (C0 * d.scale ^ eta) ^ 4) := by
      gcongr
    _ = _ := by rw [mul_pow, hpow]; ring

end
end ImbalancedChen.Part3OriginalActualSingleZeroPayment
