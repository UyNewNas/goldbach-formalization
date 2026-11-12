import ImbalancedChen.Part3TorusSobolevContinuousRepresentative
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Literal classical Fourier-series calculus in TWO real coordinates. Each
complex character is genuinely Frechet differentiable. The derivative
series has a summable uniform OPERATOR-norm bound and is differentiated
by native hasFDerivAt_tsum. Its derivative is a fixed bounded-linear
combination of the two shifted coefficient series. Induction using the
native Frechet C^(n+1) criterion gives C^m, not merely separate partial
derivatives. The coefficient summability inputs are independently
provided by the preceding actual weak-Fourier Sobolev estimate.
-/
namespace ImbalancedChen.Part3.PlanarFourierSeriesClassicalCalculus20261026b
noncomputable section
open Set Filter
open scoped Topology BigOperators
open ProductCircleFiniteBoxRellich20261026a TorusWeakFourierSobolevEstimate20261026b
abbrev Plane := ℝ×ℝ

def firstLift : ℂ →L[ℝ] (Plane →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRightL ℝ Plane ℂ (ContinuousLinearMap.fst ℝ ℝ ℝ)

def secondLift : ℂ →L[ℝ] (Plane →L[ℝ] ℂ) :=
  ContinuousLinearMap.smulRightL ℝ Plane ℂ (ContinuousLinearMap.snd ℝ ℝ ℝ)

def coordinateLinear (a b : ℂ) : Plane →L[ℝ] ℂ := firstLift a + secondLift b

@[simp] theorem coordinateLinear_apply (a b : ℂ) (h : Plane) :
    coordinateLinear a b h = h.1 • a + h.2 • b := by simp [coordinateLinear,firstLift,secondLift]

theorem firstLift_norm_le (a : ℂ) : ‖firstLift a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro h
  have hx : ‖h.1‖ ≤ ‖h‖ := norm_fst_le h
  simpa only [firstLift,ContinuousLinearMap.smulRightL_apply_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.fst_apply,norm_smul,mul_comm] using mul_le_mul_of_nonneg_right hx (norm_nonneg a)

theorem secondLift_norm_le (a : ℂ) : ‖secondLift a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro h
  have hx : ‖h.2‖ ≤ ‖h‖ := norm_snd_le h
  simpa only [secondLift,ContinuousLinearMap.smulRightL_apply_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.snd_apply,norm_smul,mul_comm] using mul_le_mul_of_nonneg_right hx (norm_nonneg a)

theorem coordinateLinear_norm_le (a b : ℂ) : ‖coordinateLinear a b‖ ≤ ‖a‖+‖b‖ :=
  (norm_add_le _ _).trans (add_le_add (firstLift_norm_le a) (secondLift_norm_le b))

def frequencyLinear (k : Frequency) : Plane →L[ℝ] ℂ :=
  coordinateLinear (frequencyMultiplier 0 k) (frequencyMultiplier 1 k)

def planeCharacter (k : Frequency) (p : Plane) : ℂ := Complex.exp (frequencyLinear k p)

theorem frequencyLinear_re_zero (k : Frequency) (p : Plane) : (frequencyLinear k p).re = 0 := by
  simp [frequencyLinear,coordinateLinear_apply,frequencyMultiplier,Complex.mul_re,Complex.mul_im]

theorem planeCharacter_norm (k : Frequency) (p : Plane) : ‖planeCharacter k p‖ = 1 := by
  rw [planeCharacter,Complex.norm_exp,frequencyLinear_re_zero,Real.exp_zero]

def shiftX (α : ℕ×ℕ) : ℕ×ℕ := (α.1+1,α.2)
def shiftY (α : ℕ×ℕ) : ℕ×ℕ := (α.1,α.2+1)

def planeTerm (α : ℕ×ℕ) (c : Frequency → ℂ) (k : Frequency) (p : Plane) : ℂ :=
  derivativeCoefficient α c k * planeCharacter k p

def termGradient (α : ℕ×ℕ) (c : Frequency → ℂ) (k : Frequency) (p : Plane) : Plane →L[ℝ] ℂ :=
  coordinateLinear (planeTerm (shiftX α) c k p) (planeTerm (shiftY α) c k p)

/-- Direct Frechet differentiation of the actual two-variable character
precedes identification of its two coefficient shifts. -/
theorem planeTerm_hasFDerivAt (α : ℕ×ℕ) (c : Frequency → ℂ) (k : Frequency) (p : Plane) :
    HasFDerivAt (planeTerm α c k) (termGradient α c k p) p := by
  have h := ((frequencyLinear k).hasFDerivAt.cexp).const_mul (derivativeCoefficient α c k)
  apply h.congr_fderiv
  ext v
  simp [termGradient,planeTerm,planeCharacter,frequencyLinear,coordinateLinear_apply,
    derivativeCoefficient,shiftX,shiftY,pow_succ,smul_smul,smul_eq_mul]
  ring

theorem termGradient_norm_le (α : ℕ×ℕ) (c : Frequency → ℂ) (k : Frequency) (p : Plane) :
    ‖termGradient α c k p‖ ≤ ‖derivativeCoefficient (shiftX α) c k‖+‖derivativeCoefficient (shiftY α) c k‖ := by
  simpa only [planeTerm,norm_mul,planeCharacter_norm,mul_one] using
    coordinateLinear_norm_le (planeTerm (shiftX α) c k p) (planeTerm (shiftY α) c k p)

def planeSeries (α : ℕ×ℕ) (c : Frequency → ℂ) (p : Plane) : ℂ := ∑' k, planeTerm α c k p

def seriesGradient (α : ℕ×ℕ) (c : Frequency → ℂ) (p : Plane) : Plane →L[ℝ] ℂ :=
  coordinateLinear (planeSeries (shiftX α) c p) (planeSeries (shiftY α) c p)

theorem planeTerms_summable (α : ℕ×ℕ) (c : Frequency → ℂ)
    (hc : Summable (fun k => ‖derivativeCoefficient α c k‖)) (p : Plane) :
    Summable (fun k => planeTerm α c k p) := by
  apply Summable.of_norm
  simpa only [planeTerm,norm_mul,planeCharacter_norm,mul_one] using hc

theorem planeSeries_continuous (α : ℕ×ℕ) (c : Frequency → ℂ)
    (hc : Summable (fun k => ‖derivativeCoefficient α c k‖)) : Continuous (planeSeries α c) := by
  apply continuous_tsum (fun k => by unfold planeTerm planeCharacter; fun_prop) hc
  intro k p
  simp only [planeTerm,norm_mul,planeCharacter_norm,mul_one,le_refl]

theorem termGradient_tsum (α : ℕ×ℕ) (c : Frequency → ℂ)
    (hx : Summable (fun k => ‖derivativeCoefficient (shiftX α) c k‖))
    (hy : Summable (fun k => ‖derivativeCoefficient (shiftY α) c k‖)) (p : Plane) :
    (∑' k, termGradient α c k p) = seriesGradient α c p := by
  have hxs := planeTerms_summable (shiftX α) c hx p
  have hys := planeTerms_summable (shiftY α) c hy p
  unfold termGradient seriesGradient coordinateLinear planeSeries
  rw [(firstLift.summable hxs).tsum_add (secondLift.summable hys),
    ← firstLift.map_tsum hxs,← secondLift.map_tsum hys]

theorem planeSeries_hasFDerivAt (α : ℕ×ℕ) (c : Frequency → ℂ)
    (hc : Summable (fun k => ‖derivativeCoefficient α c k‖))
    (hx : Summable (fun k => ‖derivativeCoefficient (shiftX α) c k‖))
    (hy : Summable (fun k => ‖derivativeCoefficient (shiftY α) c k‖)) (p : Plane) :
    HasFDerivAt (planeSeries α c) (seriesGradient α c p) p := by
  have h := hasFDerivAt_tsum (hx.add hy) (planeTerm_hasFDerivAt α c)
    (termGradient_norm_le α c) (planeTerms_summable α c hc (0,0)) p
  exact h.congr_fderiv (termGradient_tsum α c hx hy p)

/-- Actual C^r for every shifted series permitted by the coefficient
budget. Native Frechet differentiation, not coordinatewise regularity,
is used at every induction step. -/
theorem planeSeries_contDiff (m : ℕ) (c : Frequency → ℂ)
    (hc : ∀ α : ℕ×ℕ, α.1+α.2 ≤ m → Summable (fun k => ‖derivativeCoefficient α c k‖)) :
    ∀ r : ℕ, ∀ α : ℕ×ℕ, α.1+α.2+r ≤ m → ContDiff ℝ r (planeSeries α c) := by
  intro r
  induction r with
  | zero =>
      intro α hα
      exact contDiff_zero.mpr (planeSeries_continuous α c (hc α (by omega)))
  | succ r ih =>
      intro α hα
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨seriesGradient α c,?_,?_⟩
      · exact (firstLift.contDiff.comp (ih (shiftX α) (by dsimp [shiftX]; omega))).add
          (secondLift.contDiff.comp (ih (shiftY α) (by dsimp [shiftY]; omega)))
      · intro p
        exact planeSeries_hasFDerivAt α c (hc α (by omega))
          (hc (shiftX α) (by dsimp [shiftX]; omega)) (hc (shiftY α) (by dsimp [shiftY]; omega)) p

end
end ImbalancedChen.Part3.PlanarFourierSeriesClassicalCalculus20261026b

