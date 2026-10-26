import ImbalancedChen.Part3NestedRectangleRealCutoff
import ImbalancedChen.Part3Gamma0SmoothedPotentialL2Budget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Complex nonperiodic interior Caccioppoli for the actual defect
mollifications. Native planar Green supplies integration by parts and
real squares supply absorption. The actual theorem obtains its equation
from minimalShiftDefect; neither H1, a smoothed equation, nor a gradient
estimate is an input. The cutoff and lower-height margin precede n.
-/

namespace ImbalancedChen.Part3.Gamma0InteriorSmoothedCaccioppoli20261026b
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology ContDiff UpperHalfPlane
open ProductConvolutionSecondDerivatives20261026a
open PlanarFrechetCompactGreen20261026b NestedRectangleRealCutoff20261026b
open Gamma0SmoothedCoordinateWeakPDE20261026a Gamma0SmoothedPotentialL2Budget20261026a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMinimalShiftRange20261025a
open Gamma0CompactDefectMollifier20261026a Gamma0TranslatedProductWeakPDE20261026a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a

def weightedTest (θ : Plane → ℝ) (U : Plane → ℂ) (p : Plane) : ℂ :=
  ((θ p)^2 : ℂ) * U p

def weightedEnergy (θ : Plane → ℝ) (U : Plane → ℂ) (p : Plane) : ℝ :=
  θ p ^ 2 * (Complex.normSq (directional xDirection U p) +
    Complex.normSq (directional yDirection U p))

def cutoffError (θ : Plane → ℝ) (U : Plane → ℂ) (p : Plane) : ℝ :=
  cutoffGradientSq θ p * Complex.normSq (U p)

def weightedMass (θ : Plane → ℝ) (U : Plane → ℂ) (p : Plane) : ℝ :=
  θ p ^ 2 * Complex.normSq (U p)

theorem weightedTest_smooth {θ : Plane → ℝ} {U : Plane → ℂ}
    (hθ : ContDiff ℝ ∞ θ) (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (weightedTest θ U) :=
  (Complex.ofRealCLM.contDiff.comp (hθ.pow 2)).mul hU

theorem weightedTest_compact {θ : Plane → ℝ} (hc : HasCompactSupport θ)
    (U : Plane → ℂ) : HasCompactSupport (weightedTest θ U) :=
  (hc.comp_left (g := fun t : ℝ => ((t^2 : ℝ) : ℂ)) (by simp)).mul_right

theorem weightedTest_directional {θ : Plane → ℝ} {U : Plane → ℂ}
    (hθ : ContDiff ℝ ∞ θ) (hU : ContDiff ℝ ∞ U) (v p : Plane) :
    directional v (weightedTest θ U) p =
      ((2 * θ p * directional v θ p : ℝ) : ℂ) * U p +
        ((θ p)^2 : ℂ) * directional v U p := by
  have hdθ := ((hθ.differentiable (by simp)) p).hasFDerivAt
  have hdU := ((hU.differentiable (by simp)) p).hasFDerivAt
  have hc := Complex.ofRealCLM.hasFDerivAt.comp p hdθ
  have h := congrArg (fun A : Plane →L[ℝ] ℂ => A v) ((hc.mul hc).mul hdU).fderiv
  simp only [Pi.mul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul] at h
  convert h using 1 <;>
    simp only [weightedTest, directional, pow_two, Complex.ofReal_mul] <;> ring

private theorem real_square_absorption (t dt : ℝ) (u du : ℂ) :
    t^2 * Complex.normSq du ≤
      2 * (star (((2*t*dt : ℝ) : ℂ)*u + ((t^2 : ℝ) : ℂ)*du) * du).re +
        4 * dt^2 * Complex.normSq u := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (t*du.re + 2*dt*u.re), sq_nonneg (t*du.im + 2*dt*u.im)]

theorem weightedEnergy_absorption {θ : Plane → ℝ} {U : Plane → ℂ}
    (hθ : ContDiff ℝ ∞ θ) (hU : ContDiff ℝ ∞ U) (p : Plane) :
    weightedEnergy θ U p ≤
      2 * (gradientPair (weightedTest θ U) U p).re + 4 * cutoffError θ U p := by
  have hx := real_square_absorption (θ p) (directional xDirection θ p)
    (U p) (directional xDirection U p)
  have hy := real_square_absorption (θ p) (directional yDirection θ p)
    (U p) (directional yDirection U p)
  unfold gradientPair
  rw [weightedTest_directional hθ hU xDirection p,
    weightedTest_directional hθ hU yDirection p, Complex.add_re]
  dsimp [weightedEnergy, cutoffError, cutoffGradientSq]
  linarith

private theorem forcing_absorption (t : ℝ) (u v : ℂ) :
    -2 * t^2 * (star u * v).re ≤ t^2 * (Complex.normSq u + Complex.normSq v) := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (t*(u.re+v.re)), sq_nonneg (t*(u.im+v.im))]

private theorem compact_real_weight_integrable {w g : Plane → ℝ}
    (hw : HasCompactSupport w) (hwc : Continuous w) (hgc : Continuous g) :
    Integrable (fun p => w p * g p) :=
  (hwc.mul hgc).integrable_of_hasCompactSupport hw.mul_right

theorem weightedEnergy_integrable {θ : Plane → ℝ} {U : Plane → ℂ}
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) (hU : ContDiff ℝ ∞ U) :
    Integrable (weightedEnergy θ U) :=
  compact_real_weight_integrable (hc.comp_left (g := fun t : ℝ => t^2) (by simp))
    (hθ.continuous.pow 2)
    ((Complex.continuous_normSq.comp (directional_cinfty hU xDirection).continuous).add
      (Complex.continuous_normSq.comp (directional_cinfty hU yDirection).continuous))

theorem weightedMass_integrable {θ : Plane → ℝ} {U : Plane → ℂ}
    (hθ : Continuous θ) (hc : HasCompactSupport θ) (hU : Continuous U) :
    Integrable (weightedMass θ U) :=
  compact_real_weight_integrable (hc.comp_left (g := fun t : ℝ => t^2) (by simp))
    (hθ.pow 2) (Complex.continuous_normSq.comp hU)

theorem cutoffError_integrable {θ : Plane → ℝ} {U : Plane → ℂ}
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) (hU : Continuous U) :
    Integrable (cutoffError θ U) :=
  compact_real_weight_integrable (cutoffGradientSq_compact hc)
    (cutoffGradientSq_continuous hθ) (Complex.continuous_normSq.comp hU)

/-- Analytic local lemma. Its genuine smooth PDE hypothesis is eliminated
by the actual-defect theorem below, using the supplied kernel equation. -/
theorem smooth_interior_Caccioppoli {θ : Plane → ℝ} {U V : Plane → ℂ}
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hU : ContDiff ℝ ∞ U) (hV : Continuous V)
    (hPDE : ∀ p ∈ tsupport θ, euclideanLaplacian U p = V p) :
    (∫ p : Plane, weightedEnergy θ U p) ≤
      4 * (∫ p : Plane, cutoffError θ U p) +
        (∫ p : Plane, weightedMass θ U p) + (∫ p : Plane, weightedMass θ V p) := by
  have hP := weightedTest_smooth hθ hU
  have hPc := weightedTest_compact hc U
  have hx := compact_star_pair_integrable (directional_hasCompactSupport hPc xDirection)
    (directional_cinfty hP xDirection).continuous (directional_cinfty hU xDirection).continuous
  have hy := compact_star_pair_integrable (directional_hasCompactSupport hPc yDirection)
    (directional_cinfty hP yDirection).continuous (directional_cinfty hU yDirection).continuous
  have hG : Integrable (gradientPair (weightedTest θ U) U) := hx.add hy
  have hL := (compact_star_pair_integrable hPc hP.continuous
    ((directional_cinfty (directional_cinfty hU xDirection) xDirection).continuous.add
      (directional_cinfty (directional_cinfty hU yDirection) yDirection).continuous)).neg
  have hgreen := congrArg Complex.re (compact_planar_green hPc hP hU)
  rw [← integral_re hL, ← integral_re hG] at hgreen
  have hforce (p : Plane) :
      (-(star (weightedTest θ U p) * euclideanLaplacian U p)).re =
        -(θ p)^2 * (star (U p) * V p).re := by
    by_cases hp : p ∈ tsupport θ
    · rw [hPDE p hp]
      simp [weightedTest, Complex.mul_re, Complex.mul_im, Complex.star_def]
      <;> ring
    · simp [weightedTest, image_eq_zero_of_notMem_tsupport hp]
  have hE := weightedEnergy_integrable hθ hc hU
  have hErr := cutoffError_integrable hθ hc hU.continuous
  have hMU := weightedMass_integrable hθ.continuous hc hU.continuous
  have hMV := weightedMass_integrable hθ.continuous hc hV
  have hA := integral_mono hE ((hG.re.const_mul 2).add (hErr.const_mul 4))
    (weightedEnergy_absorption hθ hU)
  rw [integral_add (hG.re.const_mul 2) (hErr.const_mul 4),
    integral_const_mul, integral_const_mul] at hA
  have hB : 2 * (∫ p : Plane, (gradientPair (weightedTest θ U) U p).re) ≤
      (∫ p : Plane, weightedMass θ U p) + (∫ p : Plane, weightedMass θ V p) := by
    rw [← hgreen, ← integral_const_mul, ← integral_add hMU hMV]
    apply integral_mono (hL.re.const_mul 2) (hMU.add hMV)
    intro p
    rw [hforce p]
    convert forcing_absorption (θ p) (U p) (V p) using 1 <;>
      dsimp [weightedMass] <;> ring
  linarith

theorem integral_normSq_toLp {g : Plane → ℂ} (hg : MemLp g 2 volume) :
    (∫ p : Plane, Complex.normSq (g p)) = ‖hg.toLp g‖^2 := by
  have hLp (f : Lp (α := Plane) ℂ 2 volume) : (∫ p : Plane, ‖f p‖^2) = ‖f‖^2 := by
    apply Complex.ofRealLI.injective
    simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
      (L2.inner_def (𝕜 := ℂ) f f).symm
  rw [← hLp (hg.toLp g)]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with p hp
  rw [hp, Complex.sq_norm]

theorem normSq_integrable {g : Plane → ℂ} (hg : MemLp g 2 volume) :
    Integrable (fun p => Complex.normSq (g p)) := by
  simpa only [Complex.normSq_eq_norm_sq] using hg.integrable_norm_pow (by decide : 2 ≠ 0)

/-- The controlled energy is literally the sum of squared norms of two
global ordinary L2 vectors, suitable for native Hilbert weak extraction. -/
theorem weightedEnergy_eq_L2 {θ : Plane → ℝ} {U : Plane → ℂ}
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) (hU : ContDiff ℝ ∞ U) :
    (∫ p : Plane, weightedEnergy θ U p) =
      ‖(weightedDerivative_memLp hθ hc hU xDirection).toLp
        (fun p => (θ p : ℂ) * directional xDirection U p)‖^2 +
      ‖(weightedDerivative_memLp hθ hc hU yDirection).toLp
        (fun p => (θ p : ℂ) * directional yDirection U p)‖^2 := by
  have hx := weightedDerivative_memLp hθ hc hU xDirection
  have hy := weightedDerivative_memLp hθ hc hU yDirection
  rw [← integral_normSq_toLp hx, ← integral_normSq_toLp hy,
    ← integral_add (normSq_integrable hx) (normSq_integrable hy)]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => by
    simp only [weightedEnergy, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring

theorem smooth_interior_L2_budget {θ : Plane → ℝ} {U V : Plane → ℂ} {D : ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hrange : ∀ p, 0 ≤ θ p ∧ θ p ≤ 1)
    (hD : ∀ p, cutoffGradientSq θ p ≤ D)
    (hU : ContDiff ℝ ∞ U) (hV : Continuous V)
    (hU2 : MemLp U 2 volume) (hV2 : MemLp V 2 volume)
    (hPDE : ∀ p ∈ tsupport θ, euclideanLaplacian U p = V p) :
    (∫ p : Plane, weightedEnergy θ U p) ≤
      (4*D+1) * ‖hU2.toLp U‖^2 + ‖hV2.toLp V‖^2 := by
  have h := smooth_interior_Caccioppoli hθ hc hU hV hPDE
  have hMU : (∫ p : Plane, weightedMass θ U p) ≤ ∫ p : Plane, Complex.normSq (U p) := by
    apply integral_mono (weightedMass_integrable hθ.continuous hc hU.continuous)
      (normSq_integrable hU2)
    intro p
    have ht : θ p ^ 2 ≤ 1 := by nlinarith [(hrange p).1, (hrange p).2]
    exact mul_le_of_le_one_left (Complex.normSq_nonneg _) ht
  have hMV : (∫ p : Plane, weightedMass θ V p) ≤ ∫ p : Plane, Complex.normSq (V p) := by
    apply integral_mono (weightedMass_integrable hθ.continuous hc hV) (normSq_integrable hV2)
    intro p
    have ht : θ p ^ 2 ≤ 1 := by nlinarith [(hrange p).1, (hrange p).2]
    exact mul_le_of_le_one_left (Complex.normSq_nonneg _) ht
  have hErr : (∫ p : Plane, cutoffError θ U p) ≤
      D * (∫ p : Plane, Complex.normSq (U p)) := by
    rw [← integral_const_mul]
    apply integral_mono (cutoffError_integrable hθ hc hU.continuous)
      ((normSq_integrable hU2).const_mul D)
    intro p
    exact mul_le_mul_of_nonneg_right (hD p) (Complex.normSq_nonneg _)
  rw [integral_normSq_toLp hU2] at hMU hErr
  rw [integral_normSq_toLp hV2] at hMV
  nlinarith

/-- Genuine scale-uniform bound. The local equation is supplied by the
actual adjoint defect and legal kernel geometry, with no equation premise.
The compact margin a, cutoff θ and its proved D are fixed before n. -/
theorem actual_defect_uniform_interior_energy (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B a : ℝ}
    (hB : 0 ≤ B) (ha : 0 < a) (hbound : ∀ z ∈ K, z.im ≤ B)
    (hlower : ∀ z ∈ K, a ≤ z.im) (f : QuotientL2 N)
    (hf : f ∈ minimalShiftDefect N)
    {θ : Plane → ℝ} (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hrange : ∀ p, 0 ≤ θ p ∧ θ p ≤ 1) {D : ℝ}
    (hD0 : 0 ≤ D) (hD : ∀ p, cutoffGradientSq θ p ≤ D)
    (n : ℕ)
    (hheight : ∀ p ∈ tsupport θ, mollifierRadius n < p.2)
    (hlocal : ∀ p ∈ tsupport θ, productRectangle n p.1 p.2 ⊆ K)
    (hcarrier : ∀ p ∈ tsupport θ, productRectangle n p.1 p.2 ⊆ reducedCarrier N) :
    (∫ p : Plane, weightedEnergy θ (actualProductSmooth N K B f n) p) ≤
      ((4*D+1) + ((a⁻¹)^2)^2) *
        ‖(localizedPlane_memLp N hK hB f).toLp (localizedPlane N K B f)‖^2 := by
  have hU := actualProductSmooth_cinfty N hK hB f n
  have hV : ContDiff ℝ ∞ (potentialSmooth N K B a f n) :=
    productSmooth_cinfty ((localizedPotential_memLp N hK hB ha f).locallyIntegrable
      (by norm_num)) n
  have hU2 := actualProductSmooth_memLp N hK hB hbound f n
  have hV2 := potentialSmooth_memLp N hK hB ha hbound f n
  have hPDE : ∀ p ∈ tsupport θ,
      euclideanLaplacian (actualProductSmooth N K B f n) p =
        potentialSmooth N K B a f n p := by
    intro p hp
    exact actual_smoothed_equation_with_L2_forcing N hK hB ha hbound hlower f hf
      n p.1 p.2 (hheight p hp) (hlocal p hp) (hcarrier p hp)
  have h := smooth_interior_L2_budget hθ hc hrange hD hU hV.continuous hU2 hV2 hPDE
  have hUb := actualProductSmooth_uniform_L2_bound N hK hB hbound f n
  have hVb := potentialSmooth_uniform_L2_bound N hK hB ha hbound f n
  have hUsq := mul_self_le_mul_self (norm_nonneg _) hUb
  have hVsq := mul_self_le_mul_self (norm_nonneg _) hVb
  simp only [← pow_two] at hUsq hVsq
  have hcoef : 0 ≤ 4*D+1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hUsq hcoef
  calc
    _ ≤ (4*D+1) * ‖hU2.toLp (actualProductSmooth N K B f n)‖^2 +
        ‖hV2.toLp (potentialSmooth N K B a f n)‖^2 := h
    _ ≤ (4*D+1) * ‖(localizedPlane_memLp N hK hB f).toLp
        (localizedPlane N K B f)‖^2 +
        (((a⁻¹)^2) * ‖(localizedPlane_memLp N hK hB f).toLp
          (localizedPlane N K B f)‖)^2 := add_le_add hmul hVsq
    _ = _ := by ring

/-- Explicit nested-rectangle instance. D is proved to exist and is
chosen outside the universal quantifier over smoothing scales. The only
n-dependent premises are kernel support/height geometry. -/
theorem actual_rectangle_uniform_gradient_budget (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B a : ℝ}
    (hB : 0 ≤ B) (ha : 0 < a) (hbound : ∀ z ∈ K, z.im ≤ B)
    (hlower : ∀ z ∈ K, a ≤ z.im) (f : QuotientL2 N)
    (hf : f ∈ minimalShiftDefect N)
    (L R c d δ : ℝ) (hLR : L ≤ R) (hcd : c ≤ d) (hδ : 0 < δ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ,
      (∀ p ∈ tsupport (rectangleCutoff L R c d δ hLR hcd hδ),
        mollifierRadius n < p.2) →
      (∀ p ∈ tsupport (rectangleCutoff L R c d δ hLR hcd hδ),
        productRectangle n p.1 p.2 ⊆ K) →
      (∀ p ∈ tsupport (rectangleCutoff L R c d δ hLR hcd hδ),
        productRectangle n p.1 p.2 ⊆ reducedCarrier N) →
      (∫ p : Plane, weightedEnergy (rectangleCutoff L R c d δ hLR hcd hδ)
        (actualProductSmooth N K B f n) p) ≤
        ((4*D+1) + ((a⁻¹)^2)^2) *
          ‖(localizedPlane_memLp N hK hB f).toLp (localizedPlane N K B f)‖^2 := by
  have hθ := rectangleCutoff_smooth L R c d δ hLR hcd hδ
  have hc := rectangleCutoff_compact L R c d δ hLR hcd hδ
  obtain ⟨D, hD0, hD⟩ := exists_cutoff_gradient_budget hθ hc
  refine ⟨D, hD0, fun n hh hloc hcar => ?_⟩
  exact actual_defect_uniform_interior_energy N hK hB ha hbound hlower f hf
    hθ hc (rectangleCutoff_range L R c d δ hLR hcd hδ) hD0 hD n hh hloc hcar

end
end ImbalancedChen.Part3.Gamma0InteriorSmoothedCaccioppoli20261026b
