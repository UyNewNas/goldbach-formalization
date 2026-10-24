import ImbalancedChen.P2PositiveAffineSimplexLogJensen
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
SOURCE ONLY / NOT ELABORATED / no producer or numerical replay.
Prospective sibling import staging is required before a future authorized build.

Literal frozen moment-engine rule: top=max(vertex factor values),
Y=1-L/top, 0<=Y<=q<1, and
gap6=sum_{k=2}^6 (E_g[Y^k]-(E_g[Y])^k)/k.
The engine does not use a signed mean-centered variable.  Its top-scaled
deviation is nonnegative; using this same formula without its range guard
would not be justified by this module.

We retain the ENTIRE source remainder:
R6(y)=log(1-y)+sum_{k=1}^6 y^k/k, R6'(y)=-y^6/(1-y).
Its derivative is antitone on [0,q].  Thus R6 is concave there, and actual
integral Jensen proves E log L <= log(E L)-gap6.  No uncontrolled seventh
order term is dropped and no log-gap/integral lower bound is assumed.

The canonical-simplex mass and moments are deliberately separate inputs.
They must be proved for the true physical simplex measure/affine Jacobian;
this module does not infer them from the producer's stored rational rows.
-/

namespace ImbalancedChen.P2DegreeSixLogGapSoundnessSourceOnly

noncomputable section

open Set MeasureTheory
open P2PositiveAffineSimplexLogJensenSourceOnly

def partialSix (y : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 6, y ^ (i + 1) / ((i : ℝ) + 1)

def remainderSix (y : ℝ) : ℝ := Real.log (1 - y) + partialSix y

theorem partialSix_explicit (y : ℝ) :
    partialSix y = y + y ^ 2 / 2 + y ^ 3 / 3 + y ^ 4 / 4 + y ^ 5 / 5 + y ^ 6 / 6 := by
  norm_num [partialSix, Finset.sum_range_succ]
  <;> ring

theorem hasDerivAt_partialSix (y : ℝ) :
    HasDerivAt partialSix (1 + y + y ^ 2 + y ^ 3 + y ^ 4 + y ^ 5) y := by
  have h := (((((hasDerivAt_id y).add ((hasDerivAt_pow 2 y).div_const 2)).add
    ((hasDerivAt_pow 3 y).div_const 3)).add ((hasDerivAt_pow 4 y).div_const 4)).add
    ((hasDerivAt_pow 5 y).div_const 5)).add ((hasDerivAt_pow 6 y).div_const 6)
  have he : (fun x : ℝ => x + x ^ 2 / 2 + x ^ 3 / 3 + x ^ 4 / 4 + x ^ 5 / 5 + x ^ 6 / 6) =
      partialSix := funext (fun x => (partialSix_explicit x).symm)
  rw [he] at h
  convert h using 1 <;> norm_num <;> ring

theorem hasDerivAt_remainderSix {y : ℝ} (hy : y < 1) :
    HasDerivAt remainderSix (-y ^ 6 / (1 - y)) y := by
  have hn : 1 - y ≠ 0 := by linarith
  have h := (((hasDerivAt_id y).const_sub 1).log hn).add (hasDerivAt_partialSix y)
  convert h using 1 <;> dsimp [remainderSix]
  <;> field_simp [hn] <;> ring

theorem continuousOn_remainderSix {q : ℝ} (hq : q < 1) :
    ContinuousOn remainderSix (Icc (0 : ℝ) q) := by
  apply ((continuousOn_const.sub continuousOn_id).log ?_).add
    (fun y hy => (hasDerivAt_partialSix y).continuousAt.continuousWithinAt)
  intro y hy
  have h : 0 < 1 - y := by linarith [hy.2]
  exact h.ne'

/-- Exact remainder concavity supplies the sign of the omitted infinite tail. -/
theorem concaveOn_remainderSix {q : ℝ} (hq : q < 1) :
    ConcaveOn ℝ (Icc (0 : ℝ) q) remainderSix := by
  have hd : DifferentiableOn ℝ remainderSix (interior (Icc (0 : ℝ) q)) := by
    intro y hy
    have hy' : y ∈ Icc (0 : ℝ) q := interior_subset hy
    exact (hasDerivAt_remainderSix (by linarith [hy'.2])).differentiableAt.differentiableWithinAt
  have ha : AntitoneOn (deriv remainderSix) (interior (Icc (0 : ℝ) q)) := by
    intro x hx y hy hxy
    have hx' : x ∈ Icc (0 : ℝ) q := interior_subset hx
    have hy' : y ∈ Icc (0 : ℝ) q := interior_subset hy
    rw [(hasDerivAt_remainderSix (by linarith [hy'.2] : y < 1)).deriv,
      (hasDerivAt_remainderSix (by linarith [hx'.2] : x < 1)).deriv]
    have hp : x ^ 6 ≤ y ^ 6 := pow_le_pow_left₀ hx'.1 hxy _
    have hf : x ^ 6 / (1 - x) ≤ y ^ 6 / (1 - y) :=
      (div_le_div_of_nonneg_right hp (by linarith [hx'.2] : 0 ≤ 1 - x)).trans
        (div_le_div_of_nonneg_left (pow_nonneg hy'.1 _)
          (by linarith [hy'.2] : 0 < 1 - y) (by linarith))
    simpa only [neg_div] using neg_le_neg hf
  exact AntitoneOn.concaveOn_of_deriv (convex_Icc 0 q)
    (continuousOn_remainderSix hq) hd ha

variable {α : Type*} [MeasurableSpace α]

def gapSix (ν : Measure α) (Y : α → ℝ) : ℝ :=
  ∑ j ∈ Finset.range 5,
    ((∫ x, Y x ^ (j + 2) ∂ν) - (∫ x, Y x ∂ν) ^ (j + 2)) / ((j : ℝ) + 2)

theorem integrable_partialSix (ν : Measure α) (Y : α → ℝ)
    (hPow : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → Integrable (fun x => Y x ^ k) ν) :
    Integrable (fun x => partialSix (Y x)) ν := by
  apply integrable_finsetSum
  intro i hi
  exact (hPow (i + 1) (by omega) (by have h := Finset.mem_range.mp hi; omega)).div_const _

theorem integral_partialSix (ν : Measure α) (Y : α → ℝ)
    (hPow : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → Integrable (fun x => Y x ^ k) ν) :
    (∫ x, partialSix (Y x) ∂ν) =
      ∑ i ∈ Finset.range 6, (∫ x, Y x ^ (i + 1) ∂ν) / ((i : ℝ) + 1) := by
  unfold partialSix
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_div _ _
  · intro i hi
    exact (hPow (i + 1) (by omega) (by have h := Finset.mem_range.mp hi; omega)).div_const _

theorem partialSix_integral_difference (ν : Measure α) (Y : α → ℝ)
    (hPow : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → Integrable (fun x => Y x ^ k) ν) :
    (∫ x, partialSix (Y x) ∂ν) - partialSix (∫ x, Y x ∂ν) = gapSix ν Y := by
  rw [integral_partialSix ν Y hPow]
  norm_num [partialSix, gapSix, Finset.sum_range_succ]
  <;> ring

/-- Degree-six correction for the actual probability law.  All moments here
are real integrals for that law; no stored moment equality is presumed. -/
theorem probability_log_one_sub_bound
    (ν : Measure α) [IsProbabilityMeasure ν] (Y : α → ℝ) {q : ℝ} (hq : q < 1)
    (hRange : ∀ᵐ x ∂ν, Y x ∈ Icc (0 : ℝ) q)
    (hPow : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → Integrable (fun x => Y x ^ k) ν)
    (hLog : Integrable (fun x => Real.log (1 - Y x)) ν) :
    (∫ x, Real.log (1 - Y x) ∂ν) ≤
      Real.log (1 - ∫ x, Y x ∂ν) - gapSix ν Y := by
  have hY : Integrable Y ν := by simpa only [pow_one] using hPow 1 (by norm_num) (by norm_num)
  have hP := integrable_partialSix ν Y hPow
  have hR : Integrable (remainderSix ∘ Y) ν := hLog.add hP
  have hJ := (concaveOn_remainderSix hq).le_map_integral
    (continuousOn_remainderSix hq) isClosed_Icc hRange hY hR
  change (∫ x, Real.log (1 - Y x) + partialSix (Y x) ∂ν) ≤
    Real.log (1 - ∫ x, Y x ∂ν) + partialSix (∫ x, Y x ∂ν) at hJ
  rw [integral_add hLog hP] at hJ
  have hDiff := partialSix_integral_difference ν Y hPow
  linarith

def scaledDeviation (top : ℝ) (L : α → ℝ) (x : α) : ℝ := 1 - L x / top

/-- Vertex max/min guards in the actual engine give the required nonnegative
top-scaled variable.  This lemma does not apply to signed centered deviations. -/
theorem scaledDeviation_range {top lo v : ℝ}
    (hTop : 0 < top) (hLo : 0 < lo) (hV : lo ≤ v ∧ v ≤ top) :
    (1 - v / top) ∈ Icc (0 : ℝ) (1 - lo / top) ∧ 1 - lo / top < 1 := by
  constructor
  · constructor
    · have h := (div_le_one hTop).2 hV.2
      linarith
    · have h := (div_le_div_iff_of_pos_right hTop).2 hV.1
      linarith
  · have h := div_pos hLo hTop
    linarith

theorem scaledDeviation_mean (ν : Measure α) [IsProbabilityMeasure ν]
    (top : ℝ) (L : α → ℝ) (hL : Integrable L ν) :
    (∫ x, scaledDeviation top L x ∂ν) = 1 - (∫ x, L x ∂ν) / top := by
  simp only [scaledDeviation, integral_sub (integrable_const 1) (hL.div_const top),
    integral_const, probReal_univ, one_smul, integral_div]

/-- Real log-moment upper bound required by the physical weighted Jensen rule. -/
theorem probability_factor_log_bound
    (ν : Measure α) [IsProbabilityMeasure ν] (top : ℝ) (hTop : 0 < top) (L : α → ℝ)
    {q : ℝ} (hq : q < 1)
    (hRange : ∀ᵐ x ∂ν, scaledDeviation top L x ∈ Icc (0 : ℝ) q)
    (hL0 : ∀ᵐ x ∂ν, 0 < L x) (hL : Integrable L ν)
    (hLogL : Integrable (fun x => Real.log (L x)) ν)
    (hPow : ∀ k : ℕ, 1 ≤ k → k ≤ 6 →
      Integrable (fun x => scaledDeviation top L x ^ k) ν) :
    (∫ x, Real.log (L x) ∂ν) ≤
      Real.log (∫ x, L x ∂ν) - gapSix ν (scaledDeviation top L) := by
  let Y := scaledDeviation top L
  have hLogEq : (fun x => Real.log (1 - Y x)) =ᵐ[ν]
      (fun x => Real.log (L x) - Real.log top) := by
    filter_upwards [hL0] with x hx
    have he : 1 - Y x = L x / top := by dsimp [Y, scaledDeviation]; ring
    rw [he, Real.log_div hx.ne' hTop.ne']
  have hLogY : Integrable (fun x => Real.log (1 - Y x)) ν :=
    (hLogL.sub (integrable_const _)).congr hLogEq.symm
  have hY : Integrable Y ν := by simpa only [pow_one] using hPow 1 (by norm_num) (by norm_num)
  have hMean0 : 0 ≤ ∫ x, Y x ∂ν := integral_nonneg_of_ae (hRange.mono fun x hx => hx.1)
  have hMeanq : (∫ x, Y x ∂ν) ≤ q := by
    have h := integral_mono_ae hY (integrable_const q) (hRange.mono fun x hx => hx.2)
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hMeanPos : 0 < ∫ x, L x ∂ν := by
    have hMean := scaledDeviation_mean ν top L hL
    have hdiv : 0 < (∫ x, L x ∂ν) / top := by
      change (∫ x, Y x ∂ν) = _ at hMean
      linarith
    have h := (lt_div_iff₀ hTop).1 hdiv
    simpa only [zero_mul] using h
  have hLogMean : Real.log (1 - ∫ x, Y x ∂ν) =
      Real.log (∫ x, L x ∂ν) - Real.log top := by
    rw [show 1 - (∫ x, Y x ∂ν) = (∫ x, L x ∂ν) / top by
      have h := scaledDeviation_mean ν top L hL
      change (∫ x, Y x ∂ν) = _ at h
      linarith]
    exact Real.log_div hMeanPos.ne' hTop.ne'
  have hJ := probability_log_one_sub_bound ν Y hq hRange hPow hLogY
  rw [integral_congr_ae hLogEq, integral_sub hLogL (integrable_const _),
    integral_const, probReal_univ, one_smul, hLogMean] at hJ
  linarith

/-- Every moment excess asserted nonnegative by the frozen engine follows
from genuine power Jensen for its nonnegative top-scaled variable. -/
theorem probability_gapSix_nonneg
    (ν : Measure α) [IsProbabilityMeasure ν] (Y : α → ℝ)
    (hY0 : ∀ᵐ x ∂ν, 0 ≤ Y x)
    (hPow : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → Integrable (fun x => Y x ^ k) ν) :
    0 ≤ gapSix ν Y := by
  have hY : Integrable Y ν := by simpa only [pow_one] using hPow 1 (by norm_num) (by norm_num)
  unfold gapSix
  apply Finset.sum_nonneg
  intro j hj
  have hj6 : j + 2 ≤ 6 := by have h := Finset.mem_range.mp hj; omega
  have hJ := (convexOn_pow (𝕜 := ℝ) (j + 2)).map_integral_le
    (continuous_id.pow (j + 2)).continuousOn isClosed_Ici hY0 hY
    (hPow (j + 2) (by omega) hj6)
  exact div_nonneg (sub_nonneg.mpr hJ) (by positivity)

/-- Original physical weight, not an unrelated Dirichlet or abstract moment
law.  The probability is the exact g/m Radon-Nikodym normalization from the
weighted Jensen module.  Real moments up to degree6 remain explicit inputs. -/
theorem weighted_degreeSix_log_moment_bound
    (μ : Measure α) (g L : α → ℝ) (top : ℝ) (hTop : 0 < top)
    (hgMeas : Measurable g) (hgInt : Integrable g μ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hm : 0 < mass μ g)
    (hLInt : Integrable (fun x => g x * L x) μ)
    (hLogInt : Integrable (fun x => g x * Real.log (L x)) μ)
    (hL0 : ∀ᵐ x ∂μ, 0 < L x) {q : ℝ} (hq : q < 1)
    (hRange : ∀ᵐ x ∂μ, scaledDeviation top L x ∈ Icc (0 : ℝ) q)
    (hPow : ∀ k : ℕ, 1 ≤ k → k ≤ 6 →
      Integrable (fun x => scaledDeviation top L x ^ k) (weightedProbability μ g)) :
    (∫ x, g x * Real.log (L x) ∂μ) / mass μ g ≤
      Real.log ((∫ x, g x * L x ∂μ) / mass μ g) -
        gapSix (weightedProbability μ g) (scaledDeviation top L) := by
  let ν := weightedProbability μ g
  letI : IsProbabilityMeasure ν := weightedProbability_isProbability μ g hgInt hg0 hm
  have hLν : Integrable L ν := integrable_weightedProbability μ g hgMeas hg0 hm hLInt
  have hLogν : Integrable (fun x => Real.log (L x)) ν :=
    integrable_weightedProbability μ g hgMeas hg0 hm hLogInt
  have hL0ν : ∀ᵐ x ∂ν, 0 < L x := (withDensity_absolutelyContinuous _ _).ae_le hL0
  have hRangeν : ∀ᵐ x ∂ν, scaledDeviation top L x ∈ Icc (0 : ℝ) q :=
    (withDensity_absolutelyContinuous _ _).ae_le hRange
  have h := probability_factor_log_bound ν top hTop L hq hRangeν hL0ν hLν hLogν hPow
  simpa only [ν, integral_weightedProbability μ g hgMeas hg0 hm] using h

end

end ImbalancedChen.P2DegreeSixLogGapSoundnessSourceOnly
