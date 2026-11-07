import ImbalancedChen.Part3CompactGradientOrdinaryCoordinateCLM

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The ORIGINAL energy completion has a bounded COMPLEX LINEAR ordinary local
H1 jet on each positive open rectangle: local value, dx and dy in native
coordinate-volume L2. The explicit norm constant is
max(sqrt(B^2*M_K),sqrt(M_K)); actual finite quotient overlap pays M_K.
All compact smooth weak identities and original-value representatives
are proved. No operator output, PDE or H1 premise is supplied. -/

namespace ImbalancedChen.Part3.GammaEnergyOrdinaryLocalH1Jet20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0CompactGlobalOverlap20261025a Gamma0EnergyCompactGradientExtension20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CompactCoreGradient20261025a
open Gamma0EnergyGeometricWeakGradient20261025a Gamma0CompactQuotientPullbackLinear20261025a
open ProductConvolutionSecondDerivatives20261026a RestrictedL2WeakDerivative20261026b
open GammaGraphLocalGradientLinear20261026b CompactGradientOrdinaryCoordinateCLM20261026b
open GammaActualInteriorSmoothGraphBudget20261026b ActualPullbackLocalH1Transfer20261026b
open GammaCompletedGradientClassicalRepresentative20261026b ArbitraryCompactFirstGradientIBP20261026b
open CanonicalPlanarL2UnitarySourceOnly MaassWeakOperatorCore20261024zz

def energyLocalValue (N : ℕ) [NeZero N] (r : PositiveRectangle) :
    EnergyCompletion N →L[ℂ] LocalL2 r.region :=
  (localValueCLM N r).comp (physicalProjection N)

def energyPlanarPartial (N : ℕ) [NeZero N] (r : PositiveRectangle) (vertical : Bool) :
    EnergyCompletion N →L[ℂ] PlanarLocalWeakGradientExtraction20261026b.PlaneL2 :=
  (compactGradientToPlane r.outer r.outer_compact.measurableSet vertical).comp
    (completedCompactGradient N r.outer_compact)

def energyLocalPartial (N : ℕ) [NeZero N] (r : PositiveRectangle) (vertical : Bool) :
    EnergyCompletion N →L[ℂ] LocalL2 r.region :=
  (restrictionCLM r.region).comp (energyPlanarPartial N r vertical)

def energyLocalGradient (N : ℕ) [NeZero N] (r : PositiveRectangle) :
    EnergyCompletion N →L[ℂ] LocalGradientPair r :=
  (energyLocalPartial N r false).prod (energyLocalPartial N r true)

def energyLocalH1Jet (N : ℕ) [NeZero N] (r : PositiveRectangle) :
    EnergyCompletion N →L[ℂ] (LocalL2 r.region × LocalGradientPair r) :=
  (energyLocalValue N r).prod (energyLocalGradient N r)

theorem energyLocalValue_coe_ae (N : ℕ) [NeZero N] (r : PositiveRectangle) (e : EnergyCompletion N) :
    (energyLocalValue N r e : Plane → ℂ)=ᵐ[(volume : Measure Plane).restrict r.region]
      actualPlanePullback N (physicalProjection N e) :=
  localValue_coe_ae N r (physicalProjection N e)

theorem energyPlanarPartial_coe_ae (N : ℕ) [NeZero N] (r : PositiveRectangle)
    (vertical : Bool) (e : EnergyCompletion N) :
    (energyPlanarPartial N r vertical e : Plane → ℂ)=ᵐ[volume]
      planarCompletedPartial N r.outer_compact vertical e :=
  compactGradientToPlane_coe_ae r.outer r.outer_compact.measurableSet vertical
    (completedCompactGradient N r.outer_compact e)

theorem energyLocalPartial_coe_ae (N : ℕ) [NeZero N] (r : PositiveRectangle)
    (vertical : Bool) (e : EnergyCompletion N) :
    (energyLocalPartial N r vertical e : Plane → ℂ)=ᵐ[(volume : Measure Plane).restrict r.region]
      planarCompletedPartial N r.outer_compact vertical e :=
  (restriction_coe_ae r.region (energyPlanarPartial N r vertical e)).trans
    (ae_restrict_of_ae (energyPlanarPartial_coe_ae N r vertical e))

theorem energyLocalPartial_weak (N : ℕ) [NeZero N] (r : PositiveRectangle)
    (vertical : Bool) (e : EnergyCompletion N) :
    HasRestrictedDerivative r.region (energyLocalValue N r e) (energyLocalPartial N r vertical e)
      (coordinateDirection vertical) := by
  let F := actualPlanePullback N (physicalProjection N e)
  have hpos : r.region⊆positiveChart := fun p hp => r.hc.trans hp.2.1
  have hUK : ∀ z : UpperHalfPlane,(z.re,z.im)∈r.region → z∈r.outer :=
    fun z hz => r.inner_subset (r.region_subset hz)
  have hrep : ∀ᵐ z ∂((volume : Measure UpperHalfPlane).restrict r.outer),
      (physicalProjection N e) (orbitProjection N z)=F (z.re,z.im) :=
    Eventually.of_forall fun z => (actualPlanePullback_at_upper N (physicalProjection N e) z).symm
  apply restricted_derivative_of_global_tests r.region_open.measurableSet F
    (energyLocalValue N r e) (energyLocalValue_coe_ae N r e)
    (energyPlanarPartial N r vertical e) (coordinateDirection vertical)
  intro ψ hψ hc hs
  have hw := planarCompletedPartial_weak_for_representative N r.outer_compact vertical e
    hpos hUK F hrep hψ hc hs
  calc
    _ = ∫ p,star (ψ p)*planarCompletedPartial N r.outer_compact vertical e p := by
      apply integral_congr_ae
      filter_upwards [energyPlanarPartial_coe_ae N r vertical e] with p hp
      rw [hp]
    _ = _ := hw

theorem energyLocalGradient_weak (N : ℕ) [NeZero N] (r : PositiveRectangle) (e : EnergyCompletion N) :
    HasRestrictedDerivative r.region (energyLocalValue N r e) (energyLocalGradient N r e).1 xDirection ∧
      HasRestrictedDerivative r.region (energyLocalValue N r e) (energyLocalGradient N r e).2 yDirection := by
  constructor
  · simpa [coordinateDirection,CompactC2ProductMollifier20261026a.ex,xDirection] using
      energyLocalPartial_weak N r false e
  · simpa [coordinateDirection,CompactC2ProductMollifier20261026a.ey,yDirection] using
      energyLocalPartial_weak N r true e

def localEnergyJetConstant (N : ℕ) (r : PositiveRectangle) : ℝ :=
  max (Real.sqrt (localizationSquaredConstant N r.outer r.height))
    (Real.sqrt (compactOverlapBound N r.outer : ℝ))

theorem energyLocalValue_norm_le (N : ℕ) [NeZero N] (r : PositiveRectangle) (e : EnergyCompletion N) :
    ‖energyLocalValue N r e‖≤Real.sqrt (localizationSquaredConstant N r.outer r.height)*‖e‖ := by
  calc
    _ ≤ ‖localizationCLM N r.outer_compact r.height_nonneg (physicalProjection N e)‖ :=
      restriction_norm_le r.region _
    _ ≤ Real.sqrt (localizationSquaredConstant N r.outer r.height)*‖physicalProjection N e‖ :=
      localizationLinear_bound N r.outer_compact r.height_nonneg (physicalProjection N e)
    _ ≤ Real.sqrt (localizationSquaredConstant N r.outer r.height)*‖e‖ :=
      mul_le_mul_of_nonneg_left (physicalProjection_norm_le N e) (Real.sqrt_nonneg _)

theorem energyLocalPartial_norm_le (N : ℕ) [NeZero N] (r : PositiveRectangle)
    (vertical : Bool) (e : EnergyCompletion N) :
    ‖energyLocalPartial N r vertical e‖≤Real.sqrt (compactOverlapBound N r.outer : ℝ)*‖e‖ := by
  calc
    _ ≤ ‖energyPlanarPartial N r vertical e‖ := restriction_norm_le r.region _
    _ ≤ ‖completedCompactGradient N r.outer_compact e‖ :=
      compactGradientToPlane_norm_le r.outer r.outer_compact.measurableSet vertical _
    _ ≤ Real.sqrt (compactOverlapBound N r.outer : ℝ)*‖e‖ :=
      completedCompactGradient_norm_le N r.outer_compact e

theorem energyLocalH1Jet_norm_le (N : ℕ) [NeZero N] (r : PositiveRectangle) (e : EnergyCompletion N) :
    ‖energyLocalH1Jet N r e‖≤localEnergyJetConstant N r*‖e‖ := by
  have hV : ‖energyLocalValue N r e‖≤localEnergyJetConstant N r*‖e‖ := (energyLocalValue_norm_le N r e).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg e))
  have hX : ‖energyLocalPartial N r false e‖≤localEnergyJetConstant N r*‖e‖ := (energyLocalPartial_norm_le N r false e).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg e))
  have hY : ‖energyLocalPartial N r true e‖≤localEnergyJetConstant N r*‖e‖ := (energyLocalPartial_norm_le N r true e).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg e))
  change max ‖energyLocalValue N r e‖
    (max ‖energyLocalPartial N r false e‖ ‖energyLocalPartial N r true e‖)≤_
  exact max_le hV (max_le hX hY)

theorem energyLocalH1Jet_opNorm_le (N : ℕ) [NeZero N] (r : PositiveRectangle) :
    ‖energyLocalH1Jet N r‖≤localEnergyJetConstant N r :=
  (energyLocalH1Jet N r).opNorm_le_bound
    ((Real.sqrt_nonneg _).trans (le_max_left _ _)) (energyLocalH1Jet_norm_le N r)

end
end ImbalancedChen.Part3.GammaEnergyOrdinaryLocalH1Jet20261026b
