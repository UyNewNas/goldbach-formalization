import ImbalancedChen.Part3CompletedReciprocalWeil
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Smooth reciprocal-phase completion

A complex Schwartz profile is dilated at its physical scale and summed on
a finite natural carrier containing its sampled support. Poisson
summation preserves the residue character and separates the exact
Ramanujan term before the nonzero frequencies are bounded.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Finset MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped BigOperators ContDiff SchwartzMap FourierTransform

private def dilatedSchwartzProfile (w : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (LinearEquiv.smulOfNeZero ℝ ℝ t⁻¹ (inv_ne_zero ht.ne')).toContinuousLinearEquiv w

private theorem dilatedSchwartzProfile_apply (w : 𝓢(ℝ, ℂ)) {t : ℝ}
    (ht : 0 < t) (x : ℝ) :
    dilatedSchwartzProfile w t ht x = w (x / t) := by
  change w (t⁻¹ * x) = w (x / t)
  rw [div_eq_mul_inv, mul_comm]

private theorem dilatedSchwartzProfile_fourier (w : 𝓢(ℝ, ℂ)) {t : ℝ}
    (ht : 0 < t) (y : ℝ) :
    (𝓕 (dilatedSchwartzProfile w t ht)) y = t • (𝓕 w) (t * y) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
    Real.fourier_real_eq, Real.fourier_real_eq]
  have hphase (x : ℝ) : x / t * (t * y) = x * y := by field_simp
  calc
    _ = ∫ x : ℝ, Real.fourierChar (-(x / t * (t * y))) • w (x / t) := by
      simp only [hphase, dilatedSchwartzProfile_apply]
    _ = |t| • ∫ x : ℝ, Real.fourierChar (-(x * (t * y))) • w x :=
      MeasureTheory.Measure.integral_comp_div
        (fun x : ℝ => Real.fourierChar (-(x * (t * y))) • w x) t
    _ = _ := by rw [abs_of_pos ht]

private theorem smoothProfile_affine_poisson (w : 𝓢(ℝ, ℂ)) {N D : ℝ}
    (hN : 0 < N) (hD : 0 < D) (b : ℝ) :
    (∑' z : ℤ, w ((b + D * (z : ℝ)) / N)) =
      ∑' j : ℤ, ((N / D) • (𝓕 w) ((N / D) * (j : ℝ))) *
        fourier j ((b / D) : UnitAddCircle) := by
  have hscale (z : ℤ) : (b / D + (z : ℝ)) / (N / D) = (b + D * (z : ℝ)) / N := by
    field_simp
  convert (dilatedSchwartzProfile w (N / D) (div_pos hN hD)).tsum_eq_tsum_fourier (b / D)
      using 1
  · exact tsum_congr fun z => by rw [dilatedSchwartzProfile_apply, hscale]
  · exact tsum_congr fun j => by rw [dilatedSchwartzProfile_fourier]

private theorem smoothProfile_finite_progression_eq_affine
    (w : 𝓢(ℝ, ℂ)) {N : ℝ} (hN : 0 < N) (S : Finset ℕ)
    (hneg : ∀ x : ℝ, x < 0 → w x = 0)
    (hS : ∀ n : ℕ, w ((n : ℝ) / N) ≠ 0 → n ∈ S)
    {q : ℕ} (hq : 0 < q) (b : ℤ) :
    (∑ n ∈ S, if Int.ModEq q (n : ℤ) b then w ((n : ℝ) / N) else 0) =
      ∑' z : ℤ, w (((b : ℝ) + (q : ℝ) * (z : ℝ)) / N) := by
  classical
  let f : ℕ → ℂ := fun n =>
    if Int.ModEq q (n : ℤ) b then w ((n : ℝ) / N) else 0
  let g : ℤ → ℂ := fun z => w (((b : ℝ) + (q : ℝ) * (z : ℝ)) / N)
  have hnonneg (z : Function.support g) : 0 ≤ b + (q : ℤ) * z.val := by
    have hz : 0 ≤ ((b : ℝ) + (q : ℝ) * (z.val : ℝ)) / N := by
      exact le_of_not_gt (fun h => z.property (hneg _ h))
    have hr : 0 ≤ (b : ℝ) + (q : ℝ) * (z.val : ℝ) := by
      simpa only [zero_mul] using (le_div_iff₀ hN).mp hz
    exact_mod_cast hr
  let i : Function.support g → ℕ := fun z => (b + (q : ℤ) * z.val).toNat
  have hcast (z : Function.support g) : (i z : ℤ) = b + (q : ℤ) * z.val :=
    Int.toNat_of_nonneg (hnonneg z)
  have hi : Function.Injective i := by
    intro z z' he
    have hz := congrArg (fun n : ℕ => (n : ℤ)) he
    rw [hcast, hcast] at hz
    apply Subtype.ext
    exact mul_left_cancel₀ (by exact_mod_cast hq.ne') (add_left_cancel hz)
  have hcover : Function.support f ⊆ Set.range i := by
    intro n hn
    have hn' : Int.ModEq q (n : ℤ) b ∧ w ((n : ℝ) / N) ≠ 0 := by
      simpa only [f, Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] using hn
    obtain ⟨z, hz⟩ := Int.modEq_iff_dvd.mp hn'.1.symm
    have hiZ : b + (q : ℤ) * z = n := by linarith
    have hiR : (b : ℝ) + (q : ℝ) * (z : ℝ) = n := by exact_mod_cast hiZ
    have hg : z ∈ Function.support g := by
      simpa only [Function.mem_support, g, hiR] using hn'.2
    exact ⟨⟨z, hg⟩, by simp only [i, hiZ, Int.toNat_natCast]⟩
  have hvalues (z : Function.support g) : f (i z) = g z := by
    have hcongr : Int.ModEq q (i z : ℤ) b := by
      rw [hcast]
      exact Int.modEq_iff_dvd.mpr ⟨-z.val, by ring⟩
    have hr : (i z : ℝ) = (b : ℝ) + (q : ℝ) * (z.val : ℝ) := by
      exact_mod_cast hcast z
    simp only [f, if_pos hcongr, hr, g]
  calc
    _ = ∑' n : ℕ, f n := by
      symm
      apply tsum_eq_sum
      intro n hn
      have hw : w ((n : ℝ) / N) = 0 := by
        by_contra h
        exact hn (hS n h)
      simp [f, hw]
    _ = _ := tsum_eq_tsum_of_ne_zero_bij i hi hcover hvalues

private theorem smoothProfile_fourier_at_residue (q : ℕ) [NeZero q]
    (j : ℤ) (u : ZMod q) :
    fourier j (((u.val : ℝ) / (q : ℝ)) : UnitAddCircle) =
      ZMod.stdAddChar ((j : ZMod q) * u) := by
  have hu : ((j * (u.val : ℤ) : ℤ) : ZMod q) = (j : ZMod q) * u := by
    simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [← hu, ZMod.stdAddChar_coe, fourier_coe_apply]
  push_cast
  congr 1
  ring

/-- Exact completion on a single residue class. The same finite carrier
may be used in every class. The sign of the Fourier character is positive. -/
theorem smoothProfile_progression_eq_tsum (q : ℕ) [NeZero q] (u : ZMod q)
    {N : ℝ} (hN : 0 < N) (w : 𝓢(ℝ, ℂ)) (S : Finset ℕ)
    (hneg : ∀ x : ℝ, x < 0 → w x = 0)
    (hS : ∀ n : ℕ, w ((n : ℝ) / N) ≠ 0 → n ∈ S) :
    (∑ n ∈ S, if (n : ZMod q) = u then w ((n : ℝ) / N) else 0) =
      ∑' j : ℤ, ((N / (q : ℝ)) • (𝓕 w) ((N / (q : ℝ)) * (j : ℝ))) *
        ZMod.stdAddChar ((j : ZMod q) * u) := by
  have hclass (n : ℕ) : (n : ZMod q) = u ↔ Int.ModEq q (n : ℤ) (u.val : ℤ) := by
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
      (ZMod.intCast_eq_intCast_iff (n : ℤ) (u.val : ℤ) q)
  simp only [hclass]
  rw [smoothProfile_finite_progression_eq_affine w hN S hneg hS (NeZero.pos q),
    Int.cast_natCast, smoothProfile_affine_poisson w hN (by exact_mod_cast NeZero.pos q)]
  exact tsum_congr (fun j => by rw [smoothProfile_fourier_at_residue])

/-- Absolute convergence of the single-residue Fourier expansion. -/
theorem smoothProfile_progressionFourier_norm_summable
    (q : ℕ) [NeZero q] (u : ZMod q) {N : ℝ} (hN : 0 < N) (w : 𝓢(ℝ, ℂ)) :
    Summable (fun j : ℤ => ‖((N / (q : ℝ)) • (𝓕 w) ((N / (q : ℝ)) * (j : ℝ))) *
      ZMod.stdAddChar ((j : ZMod q) * u)‖) := by
  let t : ℝ := N / q
  have ht : 0 < t := div_pos hN (by exact_mod_cast NeZero.pos q)
  obtain ⟨C, hC, hdecay⟩ := schwartz_norm_le_rapidDecay (𝓕 w) 2
  let g := Function.update (fun j : ℤ => C * poissonNonzeroDecay t j) 0 (t * ‖(𝓕 w) 0‖)
  have hg : Summable g :=
    ((poissonNonzeroDecay_summable_tsum_le ht).1.mul_left C).update 0 _
  refine hg.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
  change ‖(t • (𝓕 w) (t * (j : ℝ))) * ZMod.stdAddChar ((j : ZMod q) * u)‖ ≤ g j
  simp only [norm_mul, norm_smul, Real.norm_eq_abs, abs_of_pos ht, stdAddChar_norm, mul_one]
  by_cases hj : j = 0
  · simp [g, hj]
  · simp only [g, Function.update_of_ne hj, poissonNonzeroDecay, if_neg hj]
    exact (mul_le_mul_of_nonneg_left (hdecay (t * (j : ℝ))) ht.le).trans_eq (by ring)


/-- The finite smooth reciprocal sum on the actual sample points. -/
def smoothReciprocalSum (q : ℕ) [NeZero q] (a : ℤ) (N : ℝ)
    (w : 𝓢(ℝ, ℂ)) (S : Finset ℕ) : ℂ :=
  ∑ n ∈ S, w ((n : ℝ) / N) * reciprocalPhase q a (n : ZMod q)

/-- The physical sum uses the original inverse phase and the coprime filter. -/
theorem smoothReciprocalSum_eq_signed_inverse (q : ℕ) [NeZero q] (a : ℤ) (N : ℝ)
    (w : 𝓢(ℝ, ℂ)) (S : Finset ℕ) :
    smoothReciprocalSum q a N w S =
      ∑ n ∈ S, if Nat.Coprime n q then
        w ((n : ℝ) / N) *
          fourier 1 (((a : ℝ) * (((n : ZMod q)⁻¹).val : ℝ) / (q : ℝ)) : UnitAddCircle)
      else 0 := by
  unfold smoothReciprocalSum
  apply sum_congr rfl
  intro n _
  rw [reciprocalPhase_nat_eq_fourier]
  split_ifs <;> simp

private theorem smoothReciprocalSum_eq_tsum (q : ℕ) [NeZero q] (a : ℤ)
    {N : ℝ} (hN : 0 < N) (w : 𝓢(ℝ, ℂ)) (S : Finset ℕ)
    (hneg : ∀ x : ℝ, x < 0 → w x = 0)
    (hS : ∀ n : ℕ, w ((n : ℝ) / N) ≠ 0 → n ∈ S) :
    smoothReciprocalSum q a N w S =
      ∑' j : ℤ, ((N / (q : ℝ)) • (𝓕 w) ((N / (q : ℝ)) * (j : ℝ))) *
        completeKloosterman q (j : ZMod q) a := by
  let t : ℝ := N / q
  let R (u : ZMod q) (j : ℤ) : ℂ :=
    reciprocalPhase q a u *
      ((t • (𝓕 w) (t * (j : ℝ))) * ZMod.stdAddChar ((j : ZMod q) * u))
  have hR (u : ZMod q) : Summable (R u) :=
    (smoothProfile_progressionFourier_norm_summable q u hN w).of_norm.mul_left _
  calc
    _ = ∑ u : ZMod q, reciprocalPhase q a u *
        ∑ n ∈ S, if (n : ZMod q) = u then w ((n : ℝ) / N) else 0 := by
      symm
      simp only [mul_sum]
      rw [sum_comm]
      unfold smoothReciprocalSum
      apply sum_congr rfl
      intro n _
      rw [sum_eq_single (n : ZMod q)]
      · simp only [if_true]
        exact mul_comm _ _
      · intro u _ hne
        simp only [if_neg (Ne.symm hne), mul_zero]
      · simp
    _ = ∑ u : ZMod q, ∑' j : ℤ, R u j := by
      apply sum_congr rfl
      intro u _
      rw [smoothProfile_progression_eq_tsum q u hN w S hneg hS]
      exact tsum_mul_left.symm
    _ = ∑' j : ℤ, ∑ u : ZMod q, R u j :=
      (Summable.tsum_finsetSum (fun u _ => hR u)).symm
    _ = _ := by
      apply tsum_congr
      intro j
      simp only [completeKloosterman, mul_sum]
      apply sum_congr rfl
      intro u _
      unfold R t
      ac_rfl

/-- The zero frequency of the exact completed sum is its Ramanujan
contribution. The remaining series excludes precisely the integer zero. -/
theorem smoothReciprocalSum_sub_zero_eq_tsum (q : ℕ) [NeZero q] (a : ℤ)
    {N : ℝ} (hN : 0 < N) (w : 𝓢(ℝ, ℂ)) (S : Finset ℕ)
    (hneg : ∀ x : ℝ, x < 0 → w x = 0)
    (hS : ∀ n : ℕ, w ((n : ℝ) / N) ≠ 0 → n ∈ S) :
    smoothReciprocalSum q a N w S -
        ((N / (q : ℝ)) • (𝓕 w) 0) * completeKloosterman q 0 a =
      ∑' j : ℤ, if j = 0 then 0 else
        ((N / (q : ℝ)) • (𝓕 w) ((N / (q : ℝ)) * (j : ℝ))) *
          completeKloosterman q (j : ZMod q) a := by
  let t : ℝ := N / q
  have ht : 0 < t := div_pos hN (by exact_mod_cast NeZero.pos q)
  let f (j : ℤ) :=
    (t • (𝓕 w) (t * (j : ℝ))) * completeKloosterman q (j : ZMod q) a
  obtain ⟨C, hC, hdecay⟩ := schwartz_norm_le_rapidDecay (𝓕 w) 2
  have hnonzero :=
    (completedReciprocal_nonzero_norm_le q a t ht _ C hC.le hdecay).1.of_norm
  have hs : Summable (Function.update f 0 0) := by
    apply hnonzero.congr
    intro j
    by_cases hj : j = 0 <;> simp [f, hj]
  rw [smoothReciprocalSum_eq_tsum q a hN w S hneg hS]
  change (∑' j : ℤ, f j) - _ = _
  rw [Summable.tsum_eq_add_tsum_ite' (f := f) 0 hs]
  simp only [f, t, Int.cast_zero, mul_zero, add_sub_cancel_left]

/-- Nonzero frequencies cost only the quadratic decay constant of the
actual profile and the stated Weil divisor factor. -/
theorem smoothReciprocalSum_sub_zero_norm_le (q : ℕ) [NeZero q] (a : ℤ)
    {N : ℝ} (hN : 0 < N) (w : 𝓢(ℝ, ℂ)) (S : Finset ℕ)
    (hneg : ∀ x : ℝ, x < 0 → w x = 0)
    (hS : ∀ n : ℕ, w ((n : ℝ) / N) ≠ 0 → n ∈ S)
    (C : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ x : ℝ, ‖(𝓕 w) x‖ ≤ C / (1 + |x|) ^ 2) :
    ‖smoothReciprocalSum q a N w S -
        ((N / (q : ℝ)) • (𝓕 w) 0) * completeKloosterman q 0 a‖ ≤
      2 * C * (q.divisors.card : ℝ) ^ 2 * Real.sqrt q := by
  rw [smoothReciprocalSum_sub_zero_eq_tsum q a hN w S hneg hS]
  exact (completedReciprocal_nonzero_norm_le q a (N / (q : ℝ))
    (div_pos hN (by exact_mod_cast NeZero.pos q)) _ C hC hdecay).2

/-- Equation (17) with an explicit decay constant and the actual profile's
separate zero mass. The profile is complex and the inverse frequency is signed. -/
theorem smoothReciprocalSum_norm_le (q : ℕ) [NeZero q] (a : ℤ)
    {N : ℝ} (hN : 0 < N) (w : 𝓢(ℝ, ℂ)) (S : Finset ℕ)
    (hneg : ∀ x : ℝ, x < 0 → w x = 0)
    (hS : ∀ n : ℕ, w ((n : ℝ) / N) ≠ 0 → n ∈ S)
    (C : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ x : ℝ, ‖(𝓕 w) x‖ ≤ C / (1 + |x|) ^ 2) :
    ‖smoothReciprocalSum q a N w S‖ ≤
      2 * C * (q.divisors.card : ℝ) ^ 2 * Real.sqrt q +
        (N / (q : ℝ)) * ‖(𝓕 w) 0‖ * (q.gcd a.natAbs : ℝ) := by
  let t : ℝ := N / q
  let z : ℂ := (t • (𝓕 w) 0) * completeKloosterman q 0 a
  have ht : 0 ≤ t := div_nonneg hN.le (Nat.cast_nonneg _)
  have hz : ‖z‖ ≤ t * ‖(𝓕 w) 0‖ * (q.gcd a.natAbs : ℝ) := by
    simp only [z, norm_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left (completeKloosterman_zero_left_norm_le_gcd q a)
      (mul_nonneg ht (norm_nonneg _))
  calc
    _ = ‖(smoothReciprocalSum q a N w S - z) + z‖ := by rw [sub_add_cancel]
    _ ≤ ‖smoothReciprocalSum q a N w S - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ _ :=
      add_le_add (smoothReciprocalSum_sub_zero_norm_le q a hN w S hneg hS C hC hdecay) hz

/-- A fixed Schwartz profile has one constant for all moduli, scales,
signed phases and finite carriers. -/
theorem smoothReciprocalSum_uniform_norm_le (w : 𝓢(ℝ, ℂ))
    (hneg : ∀ x : ℝ, x < 0 → w x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (a : ℤ) (N : ℝ), 0 < N →
      ∀ S : Finset ℕ, (∀ n : ℕ, w ((n : ℝ) / N) ≠ 0 → n ∈ S) →
      ‖smoothReciprocalSum q a N w S‖ ≤ C *
        ((q.divisors.card : ℝ) ^ 2 * Real.sqrt q +
          (N / (q : ℝ)) * (q.gcd a.natAbs : ℝ)) := by
  obtain ⟨C, hC, hdecay⟩ := schwartz_norm_le_rapidDecay (𝓕 w) 2
  have hzero : ‖(𝓕 w) 0‖ ≤ 2 * C := by
    have h := hdecay 0
    norm_num at h
    linarith
  refine ⟨2 * C, by positivity, ?_⟩
  intro q _ a N hN S hS
  have ht : 0 ≤ N / (q : ℝ) := div_nonneg hN.le (Nat.cast_nonneg _)
  refine (smoothReciprocalSum_norm_le q a hN w S hneg hS C hC.le hdecay).trans ?_
  rw [mul_add, ← mul_assoc]
  apply add_le_add
  · exact le_of_eq (by ring)
  · rw [mul_comm (N / (q : ℝ)), mul_assoc]
    exact mul_le_mul_of_nonneg_right hzero (mul_nonneg ht (Nat.cast_nonneg _))

/-- Compact smooth profiles, including compact Gevrey profiles, are
Schwartz. A finite carrier for the dilated profile is supplied directly by
its support. The expression here is the literal inverse-phase sum. -/
theorem smoothCompactReciprocalSum_uniform_norm_le (w : ℝ → ℂ) {R : ℝ}
    (hw : ContDiff ℝ ∞ w) (hs : Function.support w ⊆ Set.Icc 0 R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (a : ℤ) (N : ℝ), 0 < N →
      ‖∑ n ∈ Icc 0 ⌈N * R⌉₊, if Nat.Coprime n q then
        w ((n : ℝ) / N) *
          fourier 1 (((a : ℝ) * (((n : ZMod q)⁻¹).val : ℝ) / (q : ℝ)) : UnitAddCircle)
      else 0‖ ≤ C * ((q.divisors.card : ℝ) ^ 2 * Real.sqrt q +
        (N / (q : ℝ)) * (q.gcd a.natAbs : ℝ)) := by
  have hcompact : HasCompactSupport w :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc)
  let v : 𝓢(ℝ, ℂ) := hcompact.toSchwartzMap hw
  have hneg (x : ℝ) (hx : x < 0) : v x = 0 := by
    by_contra h
    exact hx.not_ge (hs h).1
  obtain ⟨C, hC, hbound⟩ := smoothReciprocalSum_uniform_norm_le v hneg
  refine ⟨C, hC, ?_⟩
  intro q _ a N hN
  have hS (n : ℕ) (hn : v ((n : ℝ) / N) ≠ 0) : n ∈ Icc 0 ⌈N * R⌉₊ := by
    have hle := (div_le_iff₀ hN).mp (hs hn).2
    rw [mul_comm R N] at hle
    exact mem_Icc.mpr ⟨Nat.zero_le _, Nat.cast_le.mp (hle.trans (Nat.le_ceil _))⟩
  have hb := hbound q a N hN (Icc 0 ⌈N * R⌉₊) hS
  rw [smoothReciprocalSum_eq_signed_inverse] at hb
  exact hb

end

end ImbalancedChen.Part3
