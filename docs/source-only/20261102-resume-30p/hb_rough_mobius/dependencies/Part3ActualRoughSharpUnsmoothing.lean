import ImbalancedChen.Part3RoughSlotPerronTruncation
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals

-- SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
-- Positivity belongs to the ORIGINAL normalized smoothing window nu.
-- The arithmetic coefficient can be complex and signed; no order assertion
-- about the rough one/Mobius character sum is used.

namespace ImbalancedChen.Part3.ActualRoughSharpUnsmoothing20261027
noncomputable section
open Classical Set Complex Real MeasureTheory
open RoughSlotSmoothedPerron20261026b RoughSlotPerronTruncation20261026b

def integerWindow (X w : ℝ) : Finset ℕ :=
  Finset.Icc (⌊X⌋₊ - ⌈w⌉₊) (⌊X⌋₊ + ⌈w⌉₊ + 1)

theorem mem_integerWindow {X w : ℝ} (hX : 0 ≤ X) (n : ℕ)
    (hn : |(n : ℝ) - X| ≤ w) : n ∈ integerWindow X w := by
  have h := abs_le.mp hn
  have hf := Nat.floor_le hX
  have hf' := Nat.lt_floor_add_one X
  have hc := Nat.le_ceil w
  have hlo : ⌊X⌋₊ ≤ n + ⌈w⌉₊ := by
    exact_mod_cast (show (⌊X⌋₊ : ℝ) ≤ (n : ℝ) + (⌈w⌉₊ : ℝ) by linarith)
  have hhi : n ≤ ⌊X⌋₊ + ⌈w⌉₊ + 1 := by
    exact_mod_cast (show (n : ℝ) ≤ (⌊X⌋₊ : ℝ) + (⌈w⌉₊ : ℝ) + 1 by linarith)
  simp only [integerWindow, Finset.mem_Icc]
  constructor <;> omega

theorem integerWindow_card_le {X w : ℝ} (hw : 0 ≤ w) :
    ((integerWindow X w).card : ℝ) ≤ 2 * w + 4 := by
  have hcard : (integerWindow X w).card ≤ 2 * ⌈w⌉₊ + 2 := by
    simp only [integerWindow, Nat.card_Icc]
    omega
  have hcast : ((integerWindow X w).card : ℝ) ≤ 2 * (⌈w⌉₊ : ℝ) + 2 := by
    exact_mod_cast hcard
  have hc := Nat.ceil_lt_add_one hw
  linarith

-- This pointwise estimate is where the original nonnegative envelope is used.
-- Its transition lies in [1-log(2)epsilon,1+2log(2)epsilon].
theorem sharp_sub_Smooth1_norm_le {ν : ℝ → ℝ}
    (hnonneg : ∀ x > 0, 0 ≤ ν x)
    (hmass : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) :
    ‖(((if x ≤ 1 then 1 else 0 : ℝ) - Smooth1 ν ε x : ℝ) : ℂ)‖ ≤ 1 := by
  have h0 := Smooth1Nonneg hnonneg hx hε
  have h1 := Smooth1LeOne hnonneg hmass hε hx
  rw [Complex.norm_real, Real.norm_eq_abs]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

theorem originalWindow_error_eq_zero {ν : ℝ → ℝ}
    (hsupp : support ν ⊆ Icc (1/2) 2)
    (hmass : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {ε X : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hX : 0 < X)
    {n : ℕ} (hn : n ≠ 0)
    (hout : n ∉ integerWindow X (2 * Real.log 2 * ε * X)) :
    (if (n : ℝ) ≤ X then 1 else 0 : ℝ) - Smooth1 ν ε ((n : ℝ)/X) = 0 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hwindow : 0 ≤ Real.log 2 * ε * X := by positivity
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have habs : 2 * Real.log 2 * ε * X < |(n : ℝ) - X| := by
    exact lt_of_not_ge (fun h => hout (mem_integerWindow hX.le n h))
  by_cases hle : (n : ℝ) ≤ X
  · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at habs
    obtain ⟨c, _, hc, hbelow⟩ := Smooth1Properties_below hsupp hmass
    have hy : (n : ℝ)/X ≤ 1 - c*ε := by
      rw [div_le_iff₀ hX, hc]
      nlinarith
    rw [if_pos hle, hbelow ε ((n : ℝ)/X) hε (div_pos hnpos hX) hy]
    ring
  · have hgt := lt_of_not_ge hle
    rw [abs_of_nonneg (sub_nonneg.mpr hgt.le)] at habs
    obtain ⟨c, _, hc, habove⟩ := Smooth1Properties_above hsupp
    have hy : 1 + c*ε ≤ (n : ℝ)/X := by
      rw [le_div_iff₀ hX, hc]
      nlinarith
    rw [if_neg hle, habove ε ((n : ℝ)/X) ⟨hε,hε1⟩ hy]
    ring

-- The error is bounded by the original positive window's lattice mass.
-- No bound on the signed sharp or smoothed character sum is a hypothesis.
theorem norm_finite_sharp_sub_smooth_le (S : Finset ℕ) (a : ℕ → ℂ)
    (ha0 : a 0 = 0) (ha : ∀ n, ‖a n‖ ≤ 1) {ν : ℝ → ℝ}
    (hnonneg : ∀ x > 0, 0 ≤ ν x)
    (hsupp : support ν ⊆ Icc (1/2) 2)
    (hmass : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {ε X : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hX : 0 < X) :
    ‖∑ n ∈ S, a n * (((if (n : ℝ) ≤ X then 1 else 0 : ℝ) -
      Smooth1 ν ε ((n : ℝ)/X) : ℝ) : ℂ)‖ ≤
      4 * Real.log 2 * ε * X + 4 := by
  let W := integerWindow X (2 * Real.log 2 * ε * X)
  let f : ℕ → ℂ := fun n => a n *
    (((if (n : ℝ) ≤ X then 1 else 0 : ℝ) - Smooth1 ν ε ((n : ℝ)/X) : ℝ) : ℂ)
  have hz (n : ℕ) (hn : n ∉ W) : f n = 0 := by
    by_cases hn0 : n = 0
    · simp [f, hn0, ha0]
    · simp only [f, originalWindow_error_eq_zero hsupp hmass hε hε1 hX hn0 hn,
        ofReal_zero, mul_zero]
  have hb (n : ℕ) : ‖f n‖ ≤ 1 := by
    by_cases hn0 : n = 0
    · simp [f, hn0, ha0]
    · have hnpos : 0 < (n : ℝ)/X := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hn0) hX
      have hi : ((if (n : ℝ) ≤ X then 1 else 0 : ℝ) - Smooth1 ν ε ((n : ℝ)/X)) =
          (if (n : ℝ)/X ≤ 1 then 1 else 0 : ℝ) - Smooth1 ν ε ((n : ℝ)/X) := by
        rw [div_le_one hX]
      dsimp only [f]
      rw [norm_mul, hi]
      exact (mul_le_mul (ha n) (sharp_sub_Smooth1_norm_le hnonneg hmass hε hnpos)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hrestrict : ∑ n ∈ S, f n = ∑ n ∈ S ∩ W, f n := by
    symm
    apply Finset.sum_subset (Finset.inter_subset_left)
    intro n hn hnot
    exact hz n (fun hmem => hnot (Finset.mem_inter.mpr ⟨hn,hmem⟩))
  calc
    _ = ‖∑ n ∈ S ∩ W, f n‖ := by change ‖∑ n ∈ S, f n‖ = _; rw [hrestrict]
    _ ≤ ∑ n ∈ S ∩ W, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ S ∩ W, (1 : ℝ) := Finset.sum_le_sum (fun n _ => hb n)
    _ = ((S ∩ W).card : ℝ) := by simp
    _ ≤ (W.card : ℝ) := by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : S ∩ W ⊆ W)
    _ ≤ 2 * (2 * Real.log 2 * ε * X) + 4 :=
      integerWindow_card_le (by positivity)
    _ = 4 * Real.log 2 * ε * X + 4 := by ring

def sharpCarrier (X : ℝ) : Finset ℕ := Finset.range (⌊X⌋₊ + 1)

variable {q : ℕ} [NeZero q]

def roughSharpSum (useMu : Bool) (χ : DirichletCharacter ℂ q)
    (z τ U X : ℝ) : ℂ :=
  ∑ n ∈ sharpCarrier X, coefficient useMu χ z τ U n

theorem roughSharpSum_eq_Ioc (useMu : Bool) (χ : DirichletCharacter ℂ q)
    (z τ U X : ℝ) :
    roughSharpSum useMu χ z τ U X =
      ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, coefficient useMu χ z τ U n := by
  change (∑ n ∈ sharpCarrier X, coefficient useMu χ z τ U n) = _
  symm
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_Ioc, sharpCarrier, Finset.mem_range] at *
    omega
  · intro n hn hnot
    have hn0 : n = 0 := by
      simp only [Finset.mem_Ioc, sharpCarrier, Finset.mem_range] at *
      omega
    simp [hn0]

theorem roughSharpSum_sub_eq_Ioc (useMu : Bool) (χ : DirichletCharacter ℂ q)
    (z τ U : ℝ) {X Y : ℝ} (hXY : X ≤ Y) :
    roughSharpSum useMu χ z τ U Y - roughSharpSum useMu χ z τ U X =
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊, coefficient useMu χ z τ U n := by
  have hsets : Finset.Ioc ⌊X⌋₊ ⌊Y⌋₊ = Finset.Ico (⌊X⌋₊+1) (⌊Y⌋₊+1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hsets, Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ (Nat.floor_mono hXY))]
  rfl

-- A genuinely signed unsmoothing estimate for the literal rough coefficient.
-- In particular χ need not be principal, real or nonnegative.
theorem norm_roughSharpSum_sub_smoothed_le (useMu : Bool)
    (χ : DirichletCharacter ℂ q) (z τ U : ℝ) {ν : ℝ → ℝ}
    (hnonneg : ∀ x > 0, 0 ≤ ν x)
    (hsupp : support ν ⊆ Icc (1/2) 2)
    (hmass : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {ε X : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hX : 0 < X) :
    ‖roughSharpSum useMu χ z τ U X - roughSmoothedSum useMu χ z τ U ν ε X‖ ≤
      4 * Real.log 2 * ε * X + 4 := by
  let S := sharpCarrier X ∪ smoothCarrier ν ε X
  let a := coefficient useMu χ z τ U
  have hsharp : (∑ n ∈ S, a n * ((if (n : ℝ) ≤ X then 1 else 0 : ℝ) : ℂ)) =
      roughSharpSum useMu χ z τ U X := by
    symm
    calc
      _ = ∑ n ∈ sharpCarrier X, a n * ((if (n : ℝ) ≤ X then 1 else 0 : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn' : n ≤ ⌊X⌋₊ := by simpa only [sharpCarrier, Finset.mem_range, Nat.lt_succ_iff] using hn
        have hnX : (n : ℝ) ≤ X := (by exact_mod_cast hn').trans (Nat.floor_le hX.le)
        simp [a, hnX]
      _ = _ := by
        apply Finset.sum_subset (Finset.subset_union_left)
        intro n _ hn
        have hn' : ⌊X⌋₊ < n := by
          simpa only [sharpCarrier, Finset.mem_range, not_lt, Nat.add_one_le_iff] using hn
        simp only [if_neg (not_le.mpr (Nat.lt_of_floor_lt hn')), ofReal_zero, mul_zero]
  have hsmooth : roughSmoothedSum useMu χ z τ U ν ε X =
      ∑ n ∈ S, a n * Smooth1 ν ε ((n : ℝ)/X) := by
    rw [roughSmoothedSum_eq_finite useMu χ z τ U hsupp hε hε1 hX]
    apply Finset.sum_subset (Finset.subset_union_right)
    intro n _ hn
    have hn' : ⌈(1+2*Real.log 2*ε)*X⌉₊+1 ≤ n := by
      simpa only [smoothCarrier, Finset.mem_range, not_lt] using hn
    have hy : (1+2*Real.log 2*ε)*X ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_of_succ_le hn')
    obtain ⟨c, _, hc, habove⟩ := Smooth1Properties_above hsupp
    have hcut : Smooth1 ν ε ((n : ℝ)/X) = 0 := by
      apply habove ε _ ⟨hε,hε1⟩
      rw [hc]
      exact (le_div_iff₀ hX).2 hy
    simp only [hcut, ofReal_zero, mul_zero]
  rw [← hsharp, hsmooth, ← Finset.sum_sub_distrib]
  simpa only [ofReal_sub, mul_sub] using
    norm_finite_sharp_sub_smooth_le S a
      (coefficient_zero useMu χ z τ U) (coefficient_norm_le_one useMu χ z τ U)
      hnonneg hsupp hmass hε hε1 hX

theorem norm_roughSharpSum_le_smoothed (useMu : Bool)
    (χ : DirichletCharacter ℂ q) (z τ U : ℝ) {ν : ℝ → ℝ}
    (hnonneg : ∀ x > 0, 0 ≤ ν x)
    (hsupp : support ν ⊆ Icc (1/2) 2)
    (hmass : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {ε X : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hX : 0 < X) :
    ‖roughSharpSum useMu χ z τ U X‖ ≤
      ‖roughSmoothedSum useMu χ z τ U ν ε X‖ + 4 * Real.log 2 * ε * X + 4 := by
  have h := norm_roughSharpSum_sub_smoothed_le useMu χ z τ U
    hnonneg hsupp hmass hε hε1 hX
  have ht := norm_add_le (roughSharpSum useMu χ z τ U X -
    roughSmoothedSum useMu χ z τ U ν ε X) (roughSmoothedSum useMu χ z τ U ν ε X)
  rw [sub_add_cancel] at ht
  linarith

-- Arbitrary original individual intervals follow by prefix subtraction.
-- The endpoints and the full Mellin phase are retained literally.
theorem norm_sharp_interval_le_two_smoothed (useMu : Bool)
    (χ : DirichletCharacter ℂ q) (z τ U : ℝ) {ν : ℝ → ℝ}
    (hnonneg : ∀ x > 0, 0 ≤ ν x)
    (hsupp : support ν ⊆ Icc (1/2) 2)
    (hmass : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {ε X Y : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hX : 0 < X) (hY : 0 < Y) :
    ‖roughSharpSum useMu χ z τ U Y - roughSharpSum useMu χ z τ U X‖ ≤
      ‖roughSmoothedSum useMu χ z τ U ν ε Y‖ +
      ‖roughSmoothedSum useMu χ z τ U ν ε X‖ +
      4 * Real.log 2 * ε * (X + Y) + 8 := by
  have hx := norm_roughSharpSum_le_smoothed useMu χ z τ U hnonneg hsupp hmass hε hε1 hX
  have hy := norm_roughSharpSum_le_smoothed useMu χ z τ U hnonneg hsupp hmass hε hε1 hY
  have ht := norm_sub_le (roughSharpSum useMu χ z τ U Y) (roughSharpSum useMu χ z τ U X)
  nlinarith

end
end ImbalancedChen.Part3.ActualRoughSharpUnsmoothing20261027
