import ImbalancedChen.Part3FixedMarkEulerMajorant

/-! Uncompiled source. All local prime tails are estimated before global
summability is obtained by bounding finite smooth-number sums. -/
noncomputable section
namespace ImbalancedChen.Part3.FixedMarkTail
open Classical Finset OriginalSmoothPoissonTail
open scoped BigOperators
attribute [local instance] Classical.propDecidable

private def ratio (δ : ℝ) (p : ℕ) := (p:ℝ)^(-1+δ)

private def bad (m : ℤ) (δ : ℝ) (p : ℕ) : ℝ :=
  if (p:ℤ) ∣ m then ratio δ p else 0

private def envelope (m : ℤ) (δ : ℝ) (p : ℕ) : ℝ :=
  bad m δ p + 2*(p:ℝ)^(-5/4+δ) +
    (1-ratio δ 2)⁻¹ * (p:ℝ)^(2*(-1+δ))

private theorem ratio_nonneg (δ : ℝ) (p : ℕ) : 0 ≤ ratio δ p := by
  unfold ratio; positivity

private theorem ratio_lt {δ : ℝ} (hδ : δ<1/4) {p : ℕ} (hp : p.Prime) :
    ratio δ p < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

private theorem envelope_nonneg (m : ℤ) {δ : ℝ} (hδ : δ<1/4) (p : ℕ) :
    0 ≤ envelope m δ p := by
  have h : 0 < 1-ratio δ 2 := sub_pos.mpr (ratio_lt hδ Nat.prime_two)
  have hbad : 0 ≤ bad m δ p := by unfold bad; split_ifs <;> simp [ratio_nonneg]
  unfold envelope
  positivity

private theorem envelope_summable {m : ℤ} (hm : m ≠ 0) {δ : ℝ} (hδ : δ<1/4) :
    Summable (envelope m δ) := by
  have hbad : Summable (bad m δ) := by
    apply summable_of_ne_finset_zero (s := Finset.range (m.natAbs+1))
    intro p hp
    have hnot : ¬ (p:ℤ) ∣ m := by
      intro hd
      exact hp (Finset.mem_range.mpr (by
        have h := Nat.le_of_dvd (Int.natAbs_pos.mpr hm) (Int.natCast_dvd.mp hd)
        omega))
    simp [bad, hnot]
  have h₁ := (Real.summable_nat_rpow.mpr (by linarith : -5/4+δ < -1)).mul_left 2
  have h₂ := (Real.summable_nat_rpow.mpr (by linarith : 2*(-1+δ) < -1)).mul_left (1-ratio δ 2)⁻¹
  exact (hbad.add h₁).add h₂

private theorem local_sum (m : ℤ) {δ : ℝ} (hδ : δ<1/4) {p : ℕ} (hp : p.Prime) :
    Summable (fun k : ℕ => price m δ (p^k)) ∧
      (∑' k : ℕ, price m δ (p^k)) ≤ 1 + envelope m δ p := by
  have hr := ratio_lt hδ hp
  have hr₀ := ratio_nonneg δ p
  have hg := summable_geometric_of_lt_one hr₀ hr
  have he (k : ℕ) : price m δ (p^(k+2)) = ratio δ p ^ 2 * ratio δ p ^ k := by
    simpa only [ratio, pow_add, mul_comm] using price_higher m δ hp k
  have ht : Summable (fun k : ℕ => price m δ (p^k)) := by
    apply (summable_nat_add_iff 2).mp
    simpa only [he] using hg.mul_left (ratio δ p ^ 2)
  refine ⟨ht, ?_⟩
  have hfirst : price m δ p ≤ bad m δ p + 2*(p:ℝ)^(-5/4+δ) := by
    rw [price_prime m δ hp]
    unfold bad ratio
    split_ifs
    · exact le_add_of_nonneg_right (by positivity)
    · simp
  have hr₂ : ratio δ p ≤ ratio δ 2 :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)
  have hi : (1-ratio δ p)⁻¹ ≤ (1-ratio δ 2)⁻¹ :=
    inv_anti₀ (sub_pos.mpr (ratio_lt hδ Nat.prime_two)) (by linarith)
  have hsquare : ratio δ p ^ 2 = (p:ℝ)^(2*(-1+δ)) := by
    unfold ratio
    rw [← Real.rpow_mul_natCast (by positivity)]
    congr 1 <;> ring
  rw [← ht.sum_add_tsum_nat_add 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
    price_one, he, tsum_mul_left, tsum_geometric_of_lt_one hr₀ hr]
  unfold envelope
  rw [← hsquare]
  nlinarith [mul_le_mul_of_nonneg_left hi (sq_nonneg (ratio δ p))]

/-- The uniform tilt in the original weight-two arithmetic series. There is
no regularization or Petersson supplier among the hypotheses. -/
theorem summable_majorant_price {m : ℤ} (hm : m ≠ 0) {δ : ℝ} (hδ : δ<1/4) :
    Summable (price m δ) := by
  have henv := envelope_summable hm hδ
  apply summable_of_sum_range_le (c := Real.exp (∑' p : ℕ, envelope m δ p))
    (price_nonneg m δ)
  intro N
  have hsm := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (price_one m δ) (fun h => price_coprime m δ h)
    (fun {p} hp => by
      have hh (k : ℕ) : ‖price m δ (p^k)‖ = price m δ (p^k) :=
        Real.norm_of_nonneg (price_nonneg _ _ _)
      simp only [hh]
      exact (local_sum m hδ hp).1) N).2
  have hnat := hasSum_subtype_iff_indicator.mp hsm
  have hid (d : ℕ) (hd : d ∈ Finset.range N) :
      (N.smoothNumbers.indicator (price m δ)) d = price m δ d := by
    by_cases h : d = 0
    · subst d
      by_cases hN : 0 ∈ N.smoothNumbers <;> simp [hN, price_zero]
    · exact Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero h)
        (Finset.mem_range.mp hd)) _
  calc
    _ = ∑ d ∈ Finset.range N, N.smoothNumbers.indicator (price m δ) d :=
      Finset.sum_congr rfl (fun d hd => (hid d hd).symm)
    _ ≤ ∏ p ∈ N.primesBelow, ∑' k : ℕ, price m δ (p^k) :=
      sum_le_hasSum _ (fun d _ => by
        by_cases h : d ∈ N.smoothNumbers <;> simp [Set.indicator, h, price_nonneg]) hnat
    _ ≤ ∏ p ∈ N.primesBelow, (1 + envelope m δ p) := by
      apply Finset.prod_le_prod
      · intro p _; exact tsum_nonneg (fun k => price_nonneg _ _ _)
      · intro p hp; exact (local_sum m hδ (Nat.prime_of_mem_primesBelow hp)).2
    _ ≤ Real.exp (∑ p ∈ N.primesBelow, envelope m δ p) :=
      Real.prod_one_add_le_exp_sum _ (envelope_nonneg m hδ)
    _ ≤ _ := Real.exp_le_exp.mpr (henv.sum_le_tsum _ (fun p _ => envelope_nonneg m hδ p))

/-- Positive-modulus series with independently varying unit twists and
second markings; the n=0 term in the nat indexing is explicitly suppressed. -/
theorem physical_twisted_summable {m : ℤ} (hm : m ≠ 0) (u n : ℕ → ℤ)
    (hu : ∀ d, 0 < d → IsUnit (u d : ZMod d)) {δ : ℝ} (hδ : δ<1/4) :
    Summable (fun d : ℕ => if d=0 then 0 else
      ‖kloosterman d (m*u d) (n d)‖ * (d:ℝ)^(-2+δ)) := by
  apply Summable.of_nonneg_of_le _ _ (summable_majorant_price hm hδ)
  · intro d; split_ifs <;> positivity
  · intro d
    by_cases hd : d=0
    · simp [hd, price_zero]
    · letI : NeZero d := ⟨hd⟩
      simp only [price, if_neg hd]
      exact mul_le_mul_of_nonneg_right
        (physical_unit_le_majorant _ _ _ (hu d (Nat.pos_of_ne_zero hd))) (by positivity)

end ImbalancedChen.Part3.FixedMarkTail
