import ImbalancedChen.Part3RoughThinEulerFactors
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The finite Euler logarithm is an actual sum of principal logarithms of
positive-real factors; its exponential is the exact original correction.
Its derivative is proved, then integrated along the actual horizontal
segment. Both correction ratios are controlled by exp(width*prime mass),
not by an elementary log-squared estimate. No full-L or SW premise occurs.
-/

namespace ImbalancedChen.Part3.RoughThinEulerHorizontal20261026b
noncomputable section
open Classical Finset Complex Set
open scoped BigOperators
open RoughSlotCharacterLift20261026b RoughSlotDirichletSeries20261026b
open RoughFiniteEulerBounds20261026b RoughFiniteEulerLogDerivative20261026b
open RoughThinEulerFactors20261026b

def finiteEulerLog {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℝ) (s : ℂ) : ℂ :=
  ∑ p ∈ smallPrimes z, Complex.log (1-χ p*(p : ℂ)^(-s))

theorem finiteEulerLog_exp {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) {δ : ℝ} (hδ : δ≤1/4) {s : ℂ} (hs : 1-δ≤s.re) :
    Complex.exp (finiteEulerLog χ z s)=finiteCorrection χ z s := by
  rw [finiteEulerLog,Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro p hp
  exact Complex.exp_log (thin_prime_factor χ (smallPrimes_prime hp) hδ hs).2.1

theorem finiteEulerLog_hasDerivAt {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) {δ : ℝ} (hδ : δ≤1/4) {s : ℂ} (hs : 1-δ≤s.re) :
    HasDerivAt (finiteEulerLog χ z)
      (∑ p ∈ smallPrimes z,
        (χ p*(p : ℂ)^(-s)*Complex.log (p : ℂ))/(1-χ p*(p : ℂ)^(-s))) s := by
  apply HasDerivAt.fun_sum
  intro p hp
  have hprime := smallPrimes_prime hp
  have hslit : (1-χ p*(p : ℂ)^(-s))∈Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (thin_prime_factor χ hprime hδ hs).1)
  convert (Complex.hasDerivAt_log hslit).comp s (factor_hasDerivAt χ hprime s) using 1 <;> ring

theorem finiteEulerLog_deriv {q : ℕ} (χ : DirichletCharacter ℂ q)
    (z : ℝ) {δ : ℝ} (hδ : δ≤1/4) {s : ℂ} (hs : 1-δ≤s.re) :
    deriv (finiteEulerLog χ z) s=logDeriv (finiteCorrection χ z) s := by
  rw [finiteCorrection_logDeriv_thin χ z hδ hs]
  exact (finiteEulerLog_hasDerivAt χ z hδ hs).deriv

/-- The derivative estimate is integrated over the actual segment, so
the loss is proportional to its width 1-sigma. -/
theorem finiteEulerLog_horizontal {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z δ κ σ : ℝ} (hz : 0≤z) (hδ : 0≤δ) (hδ1 : δ≤1/4)
    (hκ : δ*Real.log (max 2 z)≤κ) (hσ : 1-δ≤σ) (hσ1 : σ≤1) (t : ℝ) :
    ‖finiteEulerLog χ z ((σ : ℂ)+I*t)-finiteEulerLog χ z ((1 : ℂ)+I*t)‖ ≤
      thinLogCost κ z*(1-σ) := by
  let a : ℂ := (1 : ℂ)+I*t
  let b : ℂ := (σ : ℂ)+I*t
  have hsegment : ∀ w∈segment ℝ a b,1-δ≤w.re := by
    intro w hw
    rw [segment_eq_image_lineMap] at hw
    obtain ⟨u,hu,rfl⟩ := hw
    have hre : (AffineMap.lineMap a b u).re=1+u*(σ-1) := by
      dsimp [a,b]
      simp [AffineMap.lineMap_apply] <;> ring
    rw [hre]
    nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hσ1)]
  have hmain : ‖finiteEulerLog χ z b-finiteEulerLog χ z a‖ ≤
      thinLogCost κ z*‖b-a‖ :=
    (convex_segment (𝕜:=ℝ) a b).norm_image_sub_le_of_norm_fderiv_le
      (𝕜:=ℂ) (f:=finiteEulerLog χ z) (C:=thinLogCost κ z)
      (fun w hw => (finiteEulerLog_hasDerivAt χ z hδ1 (hsegment w hw)).differentiableAt)
      (fun w hw => by
        rw [← norm_deriv_eq_norm_fderiv,finiteEulerLog_deriv χ z hδ1 (hsegment w hw)]
        exact finiteCorrection_logDeriv_norm_thin χ hz hδ hδ1 hκ (hsegment w hw))
      (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  have hdist : ‖b-a‖=1-σ := by
    have heq : b-a=((σ-1 : ℝ) : ℂ) := by dsimp [a,b]; push_cast; ring
    rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
    ring
  simpa only [a,b,hdist] using hmain

/-- Both relative Euler corrections are bounded, including original
principal characters and factors at primes dividing the level. -/
theorem finiteCorrection_horizontal_ratios {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z δ κ σ : ℝ} (hz : 0≤z) (hδ : 0≤δ) (hδ1 : δ≤1/4)
    (hκ : δ*Real.log (max 2 z)≤κ) (hσ : 1-δ≤σ) (hσ1 : σ≤1) (t : ℝ) :
    ‖finiteCorrection χ z ((σ : ℂ)+I*t)/finiteCorrection χ z ((1 : ℂ)+I*t)‖ ≤
        Real.exp (thinLogCost κ z*(1-σ)) ∧
      ‖finiteCorrection χ z ((1 : ℂ)+I*t)/finiteCorrection χ z ((σ : ℂ)+I*t)‖ ≤
        Real.exp (thinLogCost κ z*(1-σ)) := by
  have hs : 1-δ≤((σ : ℂ)+I*t).re := by simpa using hσ
  have h1 : 1-δ≤((1 : ℂ)+I*t).re := by simp; linarith
  have hdiff := finiteEulerLog_horizontal χ hz hδ hδ1 hκ hσ hσ1 t
  have hratio : finiteCorrection χ z ((σ : ℂ)+I*t)/finiteCorrection χ z ((1 : ℂ)+I*t)=
      Complex.exp (finiteEulerLog χ z ((σ : ℂ)+I*t)-finiteEulerLog χ z ((1 : ℂ)+I*t)) := by
    rw [Complex.exp_sub,finiteEulerLog_exp χ z hδ1 hs,finiteEulerLog_exp χ z hδ1 h1]
  have hratio' : finiteCorrection χ z ((1 : ℂ)+I*t)/finiteCorrection χ z ((σ : ℂ)+I*t)=
      Complex.exp (finiteEulerLog χ z ((1 : ℂ)+I*t)-finiteEulerLog χ z ((σ : ℂ)+I*t)) := by
    rw [Complex.exp_sub,finiteEulerLog_exp χ z hδ1 hs,finiteEulerLog_exp χ z hδ1 h1]
  constructor
  · rw [hratio,Complex.norm_exp]
    exact Real.exp_le_exp.mpr
      (((abs_le.mp (Complex.abs_re_le_norm _)).2).trans hdiff)
  · rw [hratio',Complex.norm_exp]
    exact Real.exp_le_exp.mpr
      (((abs_le.mp (Complex.abs_re_le_norm _)).2).trans ((norm_sub_rev _ _).le.trans hdiff))

/-- Magnitude and reciprocal in the thin strip compared with the already
proved actual boundary envelopes. -/
theorem finiteCorrection_horizontal_envelopes {q : ℕ} (χ : DirichletCharacter ℂ q)
    {z δ κ σ : ℝ} (hz : 0≤z) (hδ : 0≤δ) (hδ1 : δ≤1/4)
    (hκ : δ*Real.log (max 2 z)≤κ) (hσ : 1-δ≤σ) (hσ1 : σ≤1) (t : ℝ) :
    ‖finiteCorrection χ z ((σ : ℂ)+I*t)‖ ≤
        Real.exp (thinLogCost κ z*(1-σ))*plusEnvelope z ∧
      ‖(finiteCorrection χ z ((σ : ℂ)+I*t))⁻¹‖ ≤
        Real.exp (thinLogCost κ z*(1-σ))*inverseEnvelope z := by
  have hr := finiteCorrection_horizontal_ratios χ hz hδ hδ1 hκ hσ hσ1 t
  have hboundary := finiteCorrection_bounds χ z (by simp : 1≤((1 : ℂ)+I*t).re)
  have hleft := finiteCorrection_ne_zero_thin χ z hδ1 (by simpa using hσ)
  constructor
  · have heq : finiteCorrection χ z ((σ : ℂ)+I*t)=
        (finiteCorrection χ z ((σ : ℂ)+I*t)/finiteCorrection χ z ((1 : ℂ)+I*t))*
          finiteCorrection χ z ((1 : ℂ)+I*t) := by
      rw [div_mul_cancel₀ _ hboundary.1]
    rw [heq,norm_mul]
    exact mul_le_mul hr.1 hboundary.2.1 (norm_nonneg _) (Real.exp_pos _).le
  · have heq : (finiteCorrection χ z ((σ : ℂ)+I*t))⁻¹=
        (finiteCorrection χ z ((1 : ℂ)+I*t)/finiteCorrection χ z ((σ : ℂ)+I*t))*
          (finiteCorrection χ z ((1 : ℂ)+I*t))⁻¹ := by
      field_simp [hleft,hboundary.1]
    rw [heq,norm_mul]
    exact mul_le_mul hr.2 hboundary.2.2 (norm_nonneg _) (Real.exp_pos _).le

end
end ImbalancedChen.Part3.RoughThinEulerHorizontal20261026b
