import ImbalancedChen.Part3E1GevreyWindow

/-!
# Carrier and coefficient bounds for the medium Gevrey tail

The cardinality uses the supported q carrier, the closed split-divisor
block, and the original rough and alpha carriers with their multiplicity.
-/

namespace ImbalancedChen.Part3

open Finset Filter
open scoped BigOperators

/-- The q carrier remaining after zero Gevrey weights are discarded. -/
noncomputable def mediumGevreyS2SupportedQ (d : MediumAtom) (Q : Finset ℕ) : Finset ℕ :=
  Q.filter fun q => GevreyCutoff.cutoff ((q : ℝ) / d.Q1) ≠ 0

/-- The supported q carrier lies in the physical smooth interval. -/
theorem mediumGevreyS2_supportedQ_bounds {d : MediumAtom} (hQ₁ : 1 ≤ d.Q1)
    {Q : Finset ℕ} {q : ℕ} (hq : q ∈ mediumGevreyS2SupportedQ d Q) :
    0 < q ∧ d.Q1 / 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 5 * d.Q1 / 2 := by
  have hQ₁pos := zero_lt_one.trans_le hQ₁
  have h := GevreyCutoff.cutoff_tsupport_subset (subset_closure (mem_filter.mp hq).2)
  have hlo := (le_div_iff₀ hQ₁pos).mp h.1
  have hhi := (div_le_iff₀ hQ₁pos).mp h.2
  have hqPos : (0 : ℝ) < (q : ℝ) := by linarith
  exact ⟨Nat.cast_pos.mp hqPos, by linarith, by linarith⟩

private theorem real_card_le_of_pos_of_le (S : Finset ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hS : ∀ j ∈ S, 0 < j ∧ (j : ℝ) ≤ L) : (S.card : ℝ) ≤ L := by
  have hsub : S ⊆ Ioc 0 ⌊L⌋₊ := fun j hj =>
    mem_Ioc.mpr ⟨(hS j hj).1, Nat.le_floor (hS j hj).2⟩
  have hcard : S.card ≤ ⌊L⌋₊ := by
    simpa only [Nat.card_Ioc, Nat.sub_zero] using card_le_card hsub
  exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le hL)

private theorem e1FactorCarrier_pos_and_upper {D : ℝ} (hD : 1 ≤ D)
    {k : ℕ} (hk : k ∈ factorCarrier D) : 0 < k ∧ (k : ℝ) ≤ 2 * D := by
  obtain ⟨hlo, hhi⟩ := e1FactorCarrier_bounds (zero_le_one.trans hD) hk
  exact ⟨Nat.cast_pos.mp ((zero_lt_one.trans_le hD).trans_le hlo), hhi⟩

/-- The split divisor and the rough factor are positive on the original
closed dyadic carriers. -/
theorem mediumGevreyS2_rough_bounds {D R : ℝ} (hD : 1 ≤ D) (hR : 1 ≤ R)
    {k r : ℕ} (hk : k ∈ factorCarrier D) (hr : r ∈ factorCarrier R) :
    0 < k ∧ 0 < r ∧ (r : ℝ) ≤ 2 * R :=
  ⟨(e1FactorCarrier_pos_and_upper hD hk).1, e1FactorCarrier_pos_and_upper hR hr⟩

/-- The original divisor coefficient bounds give a common linear
envelope for the trimmed rough coefficients. -/
theorem mediumGevreyS2_trim_le {B : ℕ} {σ κ c0 : ℝ} {d : MediumAtom}
    (hσ : 0 ≤ σ) (hX : 1 ≤ d.scale) (hd : MediumAdmissible B σ κ c0 d)
    {k r : ℕ} {R : ℝ} (hR : 1 ≤ R) (hprod : (k : ℝ) * R ≤ 4 * d.Q2 * d.Q3)
    (hr : r ∈ factorCarrier R) {z : ℂ} (hz : ‖z‖ ≤ ((k * r).divisors.card : ℝ)) :
    ‖z‖ ≤ 8 * d.scale := by
  have hlength := (medium_e1_factorLengths_le_scale hσ hX hd).2
  have hrhi := (e1FactorCarrier_pos_and_upper hR hr).2
  calc
    _ ≤ ((k * r).divisors.card : ℝ) := hz
    _ ≤ ((k * r : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.card_divisors_le_self _)
    _ = (k : ℝ) * (r : ℝ) := Nat.cast_mul _ _
    _ ≤ (k : ℝ) * (2 * R) := mul_le_mul_of_nonneg_left hrhi (by positivity)
    _ = 2 * ((k : ℝ) * R) := by ring
    _ ≤ 8 * d.scale := by nlinarith only [hprod, hlength]

/-- The original subpower split scale is eventually below the full scale,
uniformly before the choice of any medium atom. -/
theorem eventually_mediumGevreyS2_splitScale_le_scale :
    ∀ᶠ X : ℝ in atTop, (X ^ (1 / Real.log (Real.log X))) ^ 2 ≤ X := by
  filter_upwards [eventually_e1SplitScale_reserve (σ := 2) (by norm_num)] with X hX
  norm_num at hX
  simpa only [one_div] using hX.1

/-- A polynomial envelope for the complete medium S2 tail multiplier.
The two rough and alpha labels are counted independently. -/
theorem mediumGevreyS2_card_envelope {B : ℕ} {σ κ c0 : ℝ} {d : MediumAtom}
    (hσ : 0 ≤ σ) (hX : 1 ≤ d.scale) (hd : MediumAdmissible B σ κ c0 d)
    {D : ℝ} (hD : 1 ≤ D) (hDX : D ≤ d.scale)
    (Q : Finset ℕ) (R : ℕ → ℝ) (Rs : ℕ → Finset ℕ)
    (hR : ∀ k ∈ factorCarrier D, (Rs k).Nonempty →
      1 ≤ R k ∧ (k : ℝ) * R k ≤ 4 * d.Q2 * d.Q3 ∧ Rs k ⊆ factorCarrier (R k)) :
    (8 * d.scale)^2 * ((mediumGevreyS2SupportedQ d Q).card : ℝ) * (d.alphaCarrier.card : ℝ)^2 *
      (∑ k ∈ factorCarrier D, ((Rs k).card : ℝ)^2) ≤ 81920 * d.scale ^ 8 := by
  have hX0 := zero_le_one.trans hX
  have hU := hd.1
  have hV := hd.2.1
  have hQ₁ := hd.2.2.1
  obtain ⟨hQ₁X, hQ₂Q₃X⟩ := medium_e1_factorLengths_le_scale hσ hX hd
  have hDU : ((factorCarrier D).card : ℝ) ≤ 2 * d.scale := by
    refine (real_card_le_of_pos_of_le _ (L := 2 * D) (by positivity) ?_).trans
      (mul_le_mul_of_nonneg_left hDX (by norm_num))
    exact fun k hk => e1FactorCarrier_pos_and_upper hD hk
  have hQU : ((mediumGevreyS2SupportedQ d Q).card : ℝ) ≤ 5 * d.scale / 2 := by
    refine (real_card_le_of_pos_of_le _ (L := 5 * d.Q1 / 2) (by positivity) ?_).trans (by linarith)
    intro q hq
    obtain ⟨hqpos, _, hqhi⟩ := mediumGevreyS2_supportedQ_bounds hQ₁ hq
    exact ⟨hqpos, hqhi⟩
  have hUX : d.U ≤ d.scale := le_mul_of_one_le_right (zero_le_one.trans hU) hV
  have hNU : (d.alphaCarrier.card : ℝ) ≤ 2 * d.scale := by
    refine (real_card_le_of_pos_of_le _ (L := 2 * d.U) (by positivity) ?_).trans
      (mul_le_mul_of_nonneg_left hUX (by norm_num))
    exact fun n hn => e1FactorCarrier_pos_and_upper hU (mem_filter.mp hn).1
  have hRU (k : ℕ) (hk : k ∈ factorCarrier D) : ((Rs k).card : ℝ) ≤ 8 * d.scale := by
    by_cases hS : (Rs k).Nonempty
    · obtain ⟨hRk, hkr, hsub⟩ := hR k hk hS
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (e1FactorCarrier_pos_and_upper hD hk).1
      have hRx : R k ≤ 4 * d.scale := by
        refine (le_mul_of_one_le_left (zero_le_one.trans hRk) hk1).trans ?_
        linarith only [hkr, hQ₂Q₃X]
      refine (real_card_le_of_pos_of_le _ (L := 2 * R k) (by positivity) ?_).trans (by linarith)
      exact fun r hr => e1FactorCarrier_pos_and_upper hRk (hsub hr)
    · simp only [not_nonempty_iff_eq_empty.mp hS, card_empty, Nat.cast_zero]
      positivity
  have hsum : (∑ k ∈ factorCarrier D, ((Rs k).card : ℝ)^2) ≤
      2 * d.scale * (8 * d.scale)^2 := by
    calc
      _ ≤ ∑ _k ∈ factorCarrier D, (8 * d.scale)^2 :=
        sum_le_sum fun k hk => pow_le_pow_left₀ (by positivity) (hRU k hk) 2
      _ = ((factorCarrier D).card : ℝ) * (8 * d.scale)^2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hDU (by positivity)
  calc
    _ ≤ (8 * d.scale)^2 * (5 * d.scale / 2) * (2 * d.scale)^2 *
          (2 * d.scale * (8 * d.scale)^2) := by gcongr
    _ = _ := by ring

end ImbalancedChen.Part3
