import ImbalancedChen.Part3GammaActualAdjointLocalizedH1
import ImbalancedChen.Part3Gamma0CompactQuotientLocalLp

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Quantitative ordinary-coordinate local L2 and smoothed-gradient budgets
from the original quotient norm. The geometric constant contains the
actual finite proper-action overlap count, upper/lower heights, and the
supremum of the explicitly fixed cutoff's squared derivative. Every cap
is proved finite and bounds the actual derivative; no budget is assumed.
-/

namespace ImbalancedChen.Part3.GammaActualInteriorSmoothGraphBudget20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open ProductConvolutionSecondDerivatives20261026a
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualMaassClosedOperator20261025a
open GammaActualAdjointLocalizedH120261026b Gamma0CompactDefectMollifier20261026a
open Gamma0CompactGlobalOverlap20261025a Gamma0CompactQuotientLocalLp20261025a
open Gamma0QuotientCellPushforward20261025a CanonicalPlanarL2UnitarySourceOnly
open MaassWeightedCoordinateL220261024zz
open Gamma0SmoothedCoordinateWeakPDE20261026a Gamma0SmoothedPotentialL2Budget20261026a
open NestedRectangleRealCutoff20261026b Gamma0InteriorSmoothedCaccioppoli20261026b
open GammaCompactSeedH1EnergyTransfer20261026b

def localizationSquaredConstant (N : ℕ) (K : Set UpperHalfPlane) (B : ℝ) : ℝ :=
  B^2*(compactOverlapBound N K : ℝ)

/-- The true compact-overlap quotient L2 comparison survives the exact
canonical y^-1 unitary and the bounded height multiplier. -/
theorem localizedPlane_norm_sq_le (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B : ℝ} (hB : 0 ≤ B)
    (f : QuotientL2 N) :
    ‖(localizedPlane_memLp N hK hB f).toLp (localizedPlane N K B f)‖^2 ≤
      localizationSquaredConstant N K B * ‖f‖^2 := by
  let H := compactPullback N K f
  have hH : MemLp H 2 (volume : Measure UpperHalfPlane) := compactPullback_memLp N hK f
  have hforward := forwardFunction_memLp hH
  have hlocal := localizedPlane_memLp N hK hB f
  have hnorm : (∫ p : Plane, ‖localizedPlane N K B f p‖^2) =
      ‖hlocal.toLp (localizedPlane N K B f)‖^2 := by
    simpa only [Complex.normSq_eq_norm_sq] using integral_normSq_toLp hlocal
  have hi : (∫ p : Plane, ‖localizedPlane N K B f p‖^2) ≤
      B^2 * (∫ p : Plane, ‖forwardFunction H p‖^2) := by
    rw [← integral_const_mul]
    apply integral_mono (hlocal.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
      ((hforward.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).const_mul (B^2))
    intro p
    have ht := mul_self_le_mul_self (cappedHeight_nonneg hB p) (cappedHeight_le B p)
    simp only [← pow_two] at ht
    have hm := mul_le_mul_of_nonneg_right ht (sq_nonneg ‖forwardFunction H p‖)
    simpa only [localizedPlane,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (cappedHeight_nonneg hB p),mul_pow] using hm
  have hcanon : (∫ p : Plane, ‖forwardFunction H p‖^2) = ∫ z : UpperHalfPlane, ‖H z‖^2 := by
    simpa only [forwardFunction] using (canonicalL2_square_eq_unweight H).symm
  have hind : (∫ z : UpperHalfPlane, ‖H z‖^2) = ∫ z in K, ‖f (orbitProjection N z)‖^2 := by
    calc
      _ = ∫ z : UpperHalfPlane, K.indicator (fun z => ‖f (orbitProjection N z)‖^2) z := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          by_cases hz : z ∈ K <;> simp [H,compactPullback,hz]
      _ = _ := integral_indicator hK.measurableSet
  have hq := quotientL2_compact_integral_sq_le N hK f
  rw [scalar_L2_integral_sq (carrierPushforward N) f] at hq
  rw [← hnorm]
  calc
    _ ≤ B^2 * (∫ p : Plane, ‖forwardFunction H p‖^2) := hi
    _ = B^2 * (∫ z in K, ‖f (orbitProjection N z)‖^2) := by rw [hcanon,hind]
    _ ≤ B^2 * ((compactOverlapBound N K : ℝ)*‖f‖^2) :=
      mul_le_mul_of_nonneg_left hq (sq_nonneg B)
    _ = _ := by dsimp [localizationSquaredConstant]; ring

def cutoffDerivativeCap (θ : Plane → ℝ) : ℝ := max 0 (sSup (range (cutoffGradientSq θ)))

theorem cutoffDerivativeCap_nonneg (θ : Plane → ℝ) : 0 ≤ cutoffDerivativeCap θ := le_max_left _ _

theorem cutoffGradientSq_le_cap {θ : Plane → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) (p : Plane) :
    cutoffGradientSq θ p ≤ cutoffDerivativeCap θ := by
  obtain ⟨D,_,hD⟩ := exists_cutoff_gradient_budget hθ hc
  have hb : BddAbove (range (cutoffGradientSq θ)) := by
    refine ⟨D,?_⟩
    rintro _ ⟨q,rfl⟩
    exact hD q
  exact (le_csSup hb (mem_range_self p)).trans (le_max_right _ _)

def localSmoothGradientConstant (N : ℕ) (K : Set UpperHalfPlane) (B a : ℝ)
    (θ : Plane → ℝ) : ℝ :=
  ((4*cutoffDerivativeCap θ+1)+((a⁻¹)^2)^2)*localizationSquaredConstant N K B

/-- A genuine explicit quotient graph-norm bound BEFORE weak extraction.
Its only scale-dependent inputs are literal kernel height/support geometry. -/
theorem actual_adjoint_smooth_gradient_budget (N : ℕ) [NeZero N]
    {f w : QuotientL2 N} (hfw : (f,w) ∈ (actualClosedGammaMaass N).adjoint.graph)
    {K : Set UpperHalfPlane} (hK : IsCompact K) {B a : ℝ}
    (hB : 0 ≤ B) (ha : 0 < a) (hbound : ∀ z ∈ K, z.im ≤ B)
    (hlower : ∀ z ∈ K, a ≤ z.im)
    {θ : Plane → ℝ} (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hrange : ∀ p, 0 ≤ θ p ∧ θ p ≤ 1) (n : ℕ)
    (hheight : ∀ p ∈ tsupport θ, mollifierRadius n < p.2)
    (hlocal : ∀ p ∈ tsupport θ, Gamma0TranslatedProductWeakPDE20261026a.productRectangle n p.1 p.2 ⊆ K) :
    (∫ p : Plane, weightedEnergy θ (actualProductSmooth N K B f n) p) ≤
      localSmoothGradientConstant N K B a θ * (‖f‖^2+‖w‖^2) := by
  let U := actualProductSmooth N K B f n
  let V : Plane → ℂ := -potentialSmooth N K B a w n
  have hU := actualProductSmooth_cinfty N hK hB f n
  have hU2 := actualProductSmooth_memLp N hK hB hbound f n
  have hV : ContDiff ℝ ∞ V := (productSmooth_cinfty
    ((localizedPotential_memLp N hK hB ha w).locallyIntegrable (by norm_num)) n).neg
  have hV2 : MemLp V 2 volume := (potentialSmooth_memLp N hK hB ha hbound w n).neg
  have hPDE : ∀ p ∈ tsupport θ, euclideanLaplacian U p = V p := fun p hp =>
    actual_adjoint_smoothed_equation N hfw hK hB ha hbound hlower n p.1 p.2
      (hheight p hp) (hlocal p hp)
  have he := smooth_interior_L2_budget hθ hc hrange (cutoffGradientSq_le_cap hθ hc)
    hU hV.continuous hU2 hV2 hPDE
  have hu := mul_self_le_mul_self (norm_nonneg _)
    (actualProductSmooth_uniform_L2_bound N hK hB hbound f n)
  have hvb : ‖hV2.toLp V‖ ≤ (a⁻¹)^2*
      ‖(localizedPlane_memLp N hK hB w).toLp (localizedPlane N K B w)‖ := by
    simpa only [V,MemLp.toLp_neg,norm_neg] using
      potentialSmooth_uniform_L2_bound N hK hB ha hbound w n
  have hv := mul_self_le_mul_self (norm_nonneg _) hvb
  simp only [← pow_two] at hu hv
  have hF := localizedPlane_norm_sq_le N hK hB f
  have hW := localizedPlane_norm_sq_le N hK hB w
  have hcoef : 0 ≤ 4*cutoffDerivativeCap θ+1 := by
    have hd := cutoffDerivativeCap_nonneg θ
    linarith
  have hloc : 0 ≤ localizationSquaredConstant N K B := by
    dsimp [localizationSquaredConstant]; positivity
  have hu' := hu.trans hF
  have hv' : ‖hV2.toLp V‖^2 ≤ ((a⁻¹)^2)^2*localizationSquaredConstant N K B*‖w‖^2 := by
    calc
      _ ≤ ((a⁻¹)^2 * ‖(localizedPlane_memLp N hK hB w).toLp (localizedPlane N K B w)‖)^2 := hv
      _ = ((a⁻¹)^2)^2*‖(localizedPlane_memLp N hK hB w).toLp (localizedPlane N K B w)‖^2 := by ring
      _ ≤ ((a⁻¹)^2)^2*(localizationSquaredConstant N K B*‖w‖^2) :=
        mul_le_mul_of_nonneg_left hW (sq_nonneg _)
      _ = _ := by ring
  have hb := he.trans (add_le_add (mul_le_mul_of_nonneg_left hu' hcoef) hv')
  calc
    _ ≤ (4*cutoffDerivativeCap θ+1)*(localizationSquaredConstant N K B*‖f‖^2)+
        ((a⁻¹)^2)^2*localizationSquaredConstant N K B*‖w‖^2 := hb
    _ ≤ (4*cutoffDerivativeCap θ+1)*(localizationSquaredConstant N K B*‖f‖^2)+
        ((a⁻¹)^2)^2*localizationSquaredConstant N K B*‖w‖^2+
        ((4*cutoffDerivativeCap θ+1)*localizationSquaredConstant N K B*‖w‖^2+
          ((a⁻¹)^2)^2*localizationSquaredConstant N K B*‖f‖^2) := by
      apply le_add_of_nonneg_right
      exact add_nonneg (mul_nonneg (mul_nonneg hcoef hloc) (sq_nonneg _))
        (mul_nonneg (mul_nonneg (sq_nonneg _) hloc) (sq_nonneg _))
    _ = _ := by dsimp [localSmoothGradientConstant]; ring

end
end ImbalancedChen.Part3.GammaActualInteriorSmoothGraphBudget20261026b
