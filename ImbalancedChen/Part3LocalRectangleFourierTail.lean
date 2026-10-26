import ImbalancedChen.Part3CuspHorizontalDerivativeParseval
import ImbalancedChen.Part3Gamma0CompactTensorPoincareC2Core
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.SpecificLimits.Basic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

A concrete local compactness prerequisite, stronger than convergence of
each individual Fourier series. The SAME finite Fourier window has squared
L2 error at most (4*pi^2*K^2)^(-1) times the actual derivative energy.
The derivative coefficient identity is proved by the existing actual FTC
and integration-by-parts supplier; it is not an assumption.

The estimate is integrated over the other coordinate of a real rectangle,
in either direction. A native positive-chart specialization retains the
hyperbolic y^(-2) density and derives horizontal boundary matching from a
genuine compact chart support. This is a quantitative high-frequency
primitive, NOT a claim that local Rellich or automorphic compactness has
already been proved. Two-direction finite-rank assembly and weak H1
completion/finite-cover transport remain separate obligations.
-/

namespace ImbalancedChen.Part3.LocalRectangleFourierTail20261026a

noncomputable section
open Set MeasureTheory Filter Topology
open scoped BigOperators UpperHalfPlane ENNReal
open P3CuspHorizontalDerivativeParsevalSourceOnly
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a

local instance unitPeriodPositive : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev CircleL2 := Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))

def frequencyWindow (K : ℕ) : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)

def frequencyProjection (K : ℕ) (u : CircleL2) : CircleL2 :=
  ∑ n ∈ frequencyWindow K,
    AddCircle.fourierCoeff u n • AddCircle.fourierBasis n

def highFrequencyMass (K : ℕ) (c : ℤ → ℂ) : ℝ :=
  ∑' n : ℤ, if n ∈ frequencyWindow K then 0 else ‖c n‖ ^ 2

def tailConstant (K : ℕ) : ℝ := (4 * Real.pi ^ 2 * (K : ℝ) ^ 2)⁻¹

theorem frequencyProjection_coefficient (K : ℕ) (u : CircleL2) (n : ℤ) :
    AddCircle.fourierCoeff (u - frequencyProjection K u) n =
      if n ∈ frequencyWindow K then 0 else AddCircle.fourierCoeff u n := by
  let b := AddCircle.fourierBasis (T := (1 : ℝ))
  have hrepr : b.repr (u - frequencyProjection K u) =
      b.repr u - ∑ m ∈ frequencyWindow K, b.repr u m • lp.single 2 m (1 : ℂ) := by
    simp only [frequencyProjection, map_sub, map_sum, map_smul,
      ← AddCircle.fourierBasis_repr, HilbertBasis.repr_self]
  rw [← AddCircle.fourierBasis_repr]
  change b.repr (u - frequencyProjection K u) n = _
  rw [hrepr]
  by_cases hn : n ∈ frequencyWindow K
  · simp [hn, ← AddCircle.fourierBasis_repr, b]
  · simp [hn, ← AddCircle.fourierBasis_repr, b]

theorem circle_norm_square_integral (u : CircleL2) :
    ‖u‖ ^ 2 = ∫ x : UnitAddCircle, ‖u x‖ ^ 2 ∂AddCircle.haarAddCircle := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner u u)]
  simp only [inner_self_eq_norm_sq_to_K, Complex.ofReal_re]

/-- Exact residual norm, including the constant mode in the finite part. -/
theorem frequencyProjection_error_square (K : ℕ) (u : CircleL2) :
    ‖u - frequencyProjection K u‖ ^ 2 =
      highFrequencyMass K (AddCircle.fourierCoeff u) := by
  rw [circle_norm_square_integral, ← AddCircle.tsum_sq_fourierCoeff]
  unfold highFrequencyMass
  apply tsum_congr
  intro n
  rw [frequencyProjection_coefficient]
  split_ifs <;> simp

def intervalMemLp (f : ℝ → ℂ) (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
    (hf.norm.pow 2).integrableOn_Ioc

def circleLiftMemLp (f : ℝ → ℂ) (hf : Continuous f) :
    MemLp (AddCircle.liftIoc (1 : ℝ) 0 f) 2 AddCircle.haarAddCircle := by
  simpa only [zero_add] using (intervalMemLp f hf).memLp_liftIoc.haarAddCircle

def intervalCircleL2 (f : ℝ → ℂ) (hf : Continuous f) : CircleL2 :=
  (circleLiftMemLp f hf).toLp (AddCircle.liftIoc (1 : ℝ) 0 f)

theorem intervalCircleL2_coefficient (f : ℝ → ℂ) (hf : Continuous f) (n : ℤ) :
    AddCircle.fourierCoeff (intervalCircleL2 f hf) n =
      AddCircle.fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n := by
  have hc := congrFun (AddCircle.fourierCoeff_congr_ae
    (circleLiftMemLp f hf).coeFn_toLp) n
  rw [hc]
  simpa only [zero_add] using
    (AddCircle.fourierCoeff_liftIoc_eq (T := (1 : ℝ)) (a := 0) f n)

private theorem frequency_norm_lower (K : ℕ) (n : ℤ)
    (hn : n ∉ frequencyWindow K) : (K : ℝ) ≤ ‖(n : ℂ)‖ := by
  rw [Complex.norm_intCast]
  by_contra h
  have habs : |(n : ℝ)| < (K : ℝ) := lt_of_not_ge h
  have hb := abs_le.mp habs.le
  apply hn
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast hb.1
  · exact_mod_cast hb.2

/-- Uniform high-frequency energy bound. Smoothness and equal endpoint
values are the only analytic inputs; no mean-zero condition is needed. -/
theorem smooth_highFrequency_mass_le (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hboundary : f 1 = f 0) (K : ℕ) (hK : 0 < K) :
    highFrequencyMass K (AddCircle.fourierCoeffOn
      (by norm_num : (0 : ℝ) < 1) f) ≤
        tailConstant K * (∫ x in (0 : ℝ)..1, ‖deriv f x‖ ^ 2) := by
  let c : ℤ → ℂ := AddCircle.fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f
  let C : ℝ := 4 * Real.pi ^ 2 * (K : ℝ) ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hd : Continuous (deriv f) := hf1.continuous_deriv_one
  have hF := AddCircle.hasSum_sq_fourierCoeffOn
    (by norm_num : (0 : ℝ) < 1) (intervalMemLp f hf.continuous)
  have hG := derivative_parseval f (deriv f)
    (fun x _ => (hf.differentiable (by norm_num) x).hasDerivAt) hboundary
    (hd.intervalIntegrable 0 1) (intervalMemLp (deriv f) hd)
  have htail : Summable (fun n : ℤ =>
      if n ∈ frequencyWindow K then 0 else ‖c n‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (fun n => by split_ifs <;> positivity) hF.summable
  have hpoint (n : ℤ) :
      C * (if n ∈ frequencyWindow K then 0 else ‖c n‖ ^ 2) ≤
        ‖(2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * c n‖ ^ 2 := by
    split_ifs with hn
    · simp only [mul_zero]
      positivity
    · have hnK := frequency_norm_lower K n hn
      have hfreq : ‖2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)‖ =
          (2 * Real.pi) * ‖(n : ℂ)‖ := by
        simp [norm_mul, Complex.norm_ofReal, abs_of_pos Real.pi_pos]
      have hscale : (2 * Real.pi) * (K : ℝ) ≤
          (2 * Real.pi) * ‖(n : ℂ)‖ :=
        mul_le_mul_of_nonneg_left hnK (by positivity)
      have hsq := pow_le_pow_left₀ (by positivity) hscale 2
      calc
        _ = ((2 * Real.pi) * (K : ℝ)) ^ 2 * ‖c n‖ ^ 2 := by dsimp [C]; ring
        _ ≤ ((2 * Real.pi) * ‖(n : ℂ)‖) ^ 2 * ‖c n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
        _ = _ := by rw [norm_mul, hfreq, mul_pow]
  have hle := (htail.mul_left C).tsum_le_tsum hpoint hG.summable
  rw [htail.tsum_mul_left, hG.tsum_eq] at hle
  have hquot : highFrequencyMass K c ≤
      (∫ x in (0 : ℝ)..1, ‖deriv f x‖ ^ 2) / C := by
    apply (le_div_iff₀ hC).mpr
    simpa only [highFrequencyMass, mul_comm] using hle
  simpa only [tailConstant, c, C, div_eq_mul_inv, mul_comm] using hquot

/-- A prescribed SAME finite window works for every smooth function
whose actual derivative energy obeys the same bound. -/
theorem smooth_projection_error_le (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hboundary : f 1 = f 0) (K : ℕ) (hK : 0 < K) :
    ‖intervalCircleL2 f hf.continuous -
      frequencyProjection K (intervalCircleL2 f hf.continuous)‖ ^ 2 ≤
        tailConstant K * (∫ x in (0 : ℝ)..1, ‖deriv f x‖ ^ 2) := by
  rw [frequencyProjection_error_square]
  simpa only [intervalCircleL2_coefficient] using
    smooth_highFrequency_mass_le f hf hboundary K hK

theorem tailConstant_tendsto_zero :
    Tendsto tailConstant atTop (𝓝 (0 : ℝ)) := by
  have hi : Tendsto (fun K : ℕ => (K : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun K : ℕ => (4 * Real.pi ^ 2)⁻¹ * ((K : ℝ)⁻¹)^2)
      atTop (𝓝 ((4 * Real.pi ^ 2)⁻¹ * (0 : ℝ)^2)) :=
    tendsto_const_nhds.mul (hi.pow 2)
  simpa only [tailConstant, mul_inv, inv_pow, mul_assoc, zero_pow (by decide : 2 ≠ 0),
    mul_zero] using ht

/-- A frequency window is selected BEFORE the function. This is uniform
over an actual derivative-energy ball, rather than individual convergence. -/
theorem exists_uniform_frequency_cutoff (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ K : ℕ, 0 < K ∧ ∀ (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f),
      f 1 = f 0 → (∫ x in (0 : ℝ)..1, ‖deriv f x‖ ^ 2) ≤ B →
      ‖intervalCircleL2 f hf.continuous -
        frequencyProjection K (intervalCircleL2 f hf.continuous)‖ ^ 2 < ε := by
  have ht : Tendsto (fun K => tailConstant K * B) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using tailConstant_tendsto_zero.mul_const B
  have he : ∀ᶠ K : ℕ in atTop, tailConstant K * B < ε := ht.eventually (gt_mem_nhds hε)
  obtain ⟨K, hK, hsmall⟩ := (eventually_gt_atTop 0 |>.and he).exists
  refine ⟨K, hK, ?_⟩
  intro f hf hb henergy
  apply lt_of_le_of_lt (smooth_projection_error_le f hf hb K hK)
  exact (mul_le_mul_of_nonneg_left henergy (by unfold tailConstant; positivity)).trans_lt hsmall

def sliceL2 (F : ℝ × ℝ → ℂ) (hF : ∀ y, ContDiff ℝ 2 (fun x => F (x,y)))
    (y : ℝ) : CircleL2 := intervalCircleL2 (fun x => F (x,y)) (hF y).continuous

def sliceErrorSquare (F : ℝ × ℝ → ℂ)
    (hF : ∀ y, ContDiff ℝ 2 (fun x => F (x,y))) (K : ℕ) (y : ℝ) : ℝ :=
  ‖sliceL2 F hF y - frequencyProjection K (sliceL2 F hF y)‖ ^ 2

def sliceDerivativeEnergy (F : ℝ × ℝ → ℂ) (y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, ‖deriv (fun t => F (t,y)) x‖ ^ 2

/-- Actual rectangular high-frequency estimate. The left side is a norm
of the actual Fourier projection residual, not an assumed coefficient tail.
No integrability assumption is required to state this nonnegative budget. -/
theorem rectangle_horizontal_tail (F : ℝ × ℝ → ℂ)
    (hF : ∀ y, ContDiff ℝ 2 (fun x => F (x,y)))
    (hboundary : ∀ y, F (1,y) = F (0,y)) (a b : ℝ) (K : ℕ) (hK : 0 < K) :
    (∫⁻ y in Icc a b, ENNReal.ofReal (sliceErrorSquare F hF K y)) ≤
      ENNReal.ofReal (tailConstant K) *
        ∫⁻ y in Icc a b, ENNReal.ofReal (sliceDerivativeEnergy F y) := by
  calc
    _ ≤ ∫⁻ y in Icc a b,
        ENNReal.ofReal (tailConstant K * sliceDerivativeEnergy F y) := by
      apply lintegral_mono
      intro y
      exact ENNReal.ofReal_le_ofReal
        (smooth_projection_error_le (fun x => F (x,y)) (hF y) (hboundary y) K hK)
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (show 0 ≤ tailConstant K by unfold tailConstant; positivity)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The same genuine estimate for vertical frequencies, obtained by
exchanging actual coordinates. It is not a compact embedding hypothesis. -/
theorem rectangle_vertical_tail (F : ℝ × ℝ → ℂ)
    (hF : ∀ x, ContDiff ℝ 2 (fun y => F (x,y)))
    (hboundary : ∀ x, F (x,1) = F (x,0)) (a b : ℝ) (K : ℕ) (hK : 0 < K) :
    (∫⁻ x in Icc a b, ENNReal.ofReal
      (sliceErrorSquare (fun p => F (p.2,p.1)) hF K x)) ≤
      ENNReal.ofReal (tailConstant K) *
        ∫⁻ x in Icc a b, ENNReal.ofReal
          (sliceDerivativeEnergy (fun p => F (p.2,p.1)) x) :=
  rectangle_horizontal_tail (fun p => F (p.2,p.1)) hF hboundary a b K hK

theorem native_horizontal_slice_C2 (f : UpperHalfPlane → ℂ)
    (hf : ContDiffOn ℝ 2 (extendUpper f) positiveChart) (y : ℝ) :
    ContDiff ℝ 2 (fun x => extendUpper f (x,y)) := by
  by_cases hy : 0 < y
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    have hopen : IsOpen positiveChart := isOpen_lt continuous_const continuous_snd
    exact ((hf (x,y) hy).contDiffAt (hopen.mem_nhds hy)).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
  · have heq : (fun x => extendUpper f (x,y)) = (fun _ => (0 : ℂ)) := by
      funext x
      simp [extendUpper, hy]
    rw [heq]
    exact contDiff_const

/-- Compact chart support produces the endpoint condition itself. No
periodicity or trace boundary condition is accepted as a conclusion premise. -/
theorem native_chart_endpoints_zero (f : UpperHalfPlane → ℂ)
    (hs : Function.support f ⊆ {z | z.re ∈ Ioo (0 : ℝ) 1}) (y : ℝ) :
    extendUpper f (1,y) = 0 ∧ extendUpper f (0,y) = 0 := by
  by_cases hy : 0 < y
  · have hz (x : ℝ) (hx : x ∉ Ioo (0 : ℝ) 1) : extendUpper f (x,y) = 0 := by
      rw [extendUpper, dif_pos hy]
      by_contra hn
      exact hx (hs hn)
    exact ⟨hz 1 (by simp), hz 0 (by simp)⟩
  · simp [extendUpper, hy]

/-- Local hyperbolic chart interface. The native x-coordinate cutoff
gives actual endpoint matching; the lower height a contributes exactly
a^(-2). The energy on the right is the Euclidean Dirichlet density in
the native chart, as required by hyperbolic dimension two. -/
theorem native_hyperbolic_rectangle_tail (f : UpperHalfPlane → ℂ)
    (hf : ContDiffOn ℝ 2 (extendUpper f) positiveChart)
    (hs : Function.support f ⊆ {z | z.re ∈ Ioo (0 : ℝ) 1})
    (a b : ℝ) (ha : 0 < a) (K : ℕ) (hK : 0 < K) :
    (∫⁻ y in Icc a b, ENNReal.ofReal ((y⁻¹) ^ 2) *
      ENNReal.ofReal (sliceErrorSquare (extendUpper f)
        (native_horizontal_slice_C2 f hf) K y)) ≤
      ENNReal.ofReal ((a⁻¹) ^ 2 * tailConstant K) *
        ∫⁻ y in Icc a b, ENNReal.ofReal (sliceDerivativeEnergy (extendUpper f) y) := by
  have hbound (y : ℝ) (hy : y ∈ Icc a b) :
      (y⁻¹) ^ 2 * sliceErrorSquare (extendUpper f)
        (native_horizontal_slice_C2 f hf) K y ≤
        ((a⁻¹) ^ 2 * tailConstant K) * sliceDerivativeEnergy (extendUpper f) y := by
    have hypos := lt_of_lt_of_le ha hy.1
    have hden : y⁻¹ ≤ a⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le ha hy.1
    have hden2 : (y⁻¹)^2 ≤ (a⁻¹)^2 := pow_le_pow_left₀ (by positivity) hden 2
    have hb := native_chart_endpoints_zero f hs y
    have he := smooth_projection_error_le (fun x => extendUpper f (x,y))
      (native_horizontal_slice_C2 f hf y) (hb.1.trans hb.2.symm) K hK
    have hn : 0 ≤ sliceErrorSquare (extendUpper f)
        (native_horizontal_slice_C2 f hf) K y := sq_nonneg _
    calc
      _ ≤ (a⁻¹)^2 * sliceErrorSquare (extendUpper f)
          (native_horizontal_slice_C2 f hf) K y := mul_le_mul_of_nonneg_right hden2 hn
      _ ≤ (a⁻¹)^2 * (tailConstant K * sliceDerivativeEnergy (extendUpper f) y) :=
        mul_le_mul_of_nonneg_left he (sq_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ ∫⁻ y in Icc a b, ENNReal.ofReal
        (((a⁻¹)^2 * tailConstant K) * sliceDerivativeEnergy (extendUpper f) y) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (hbound y hy)
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (show 0 ≤ (a⁻¹)^2 * tailConstant K by
        unfold tailConstant; positivity)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end
end ImbalancedChen.Part3.LocalRectangleFourierTail20261026a
