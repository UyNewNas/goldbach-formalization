import ImbalancedChen.Part3Gamma0LocalizedChartIntegralBudget
import ImbalancedChen.Part3Gamma0CompactQuotientPullbackLinear
import ImbalancedChen.Part3Gamma0PhysicalClosedDirichletForm

/-! SOURCE_ONLY / UNCOMPILED / zero formal credit.
Actual inverse-class Mobius pullback followed by bounded local cutoff
is a concrete continuous linear map on the ORIGINAL quotient L2 space
and on the ORIGINAL completed Gamma0 form. Its actual representative and
norm constant are proved, including agreement with genuine smooth-core
localized functions. No completed local-value or chart budget is assumed. -/

namespace ImbalancedChen.Part3.Gamma0CompletedLocalizedChartValue20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped UpperHalfPlane
open Gamma0LocalizedChartIntegralBudget20261026b
open Gamma0LocalizedChartPointwiseEnergy20261026b
open Gamma0FiniteMeasureCarrier20261024z
open Gamma0QuotientCellPushforward20261025a
open Gamma0CompactGlobalOverlap20261025a
open Gamma0CompactQuotientLocalLp20261025a
open Gamma0CompactQuotientPullbackLinear20261025a
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open Gamma0PhysicalClosedDirichletForm20261025a
open Gamma0LocalFourierTailCharts20261026a

theorem classAction_injective (N : ℕ) [NeZero N] (q : gamma0Classes N) :
    Function.Injective (classAction N q) := by
  intro z w h
  have hi := congrArg (fun t : UpperHalfPlane => (inverseClassRep N q)⁻¹ • t) h
  simpa only [classAction, inv_smul_smul] using hi

theorem classAction_image_preimage (N : ℕ) [NeZero N] (q : gamma0Classes N)
    (K : Set UpperHalfPlane) : classAction N q ⁻¹' (classAction N q '' K) = K := by
  ext z
  constructor
  · rintro ⟨w, hw, heq⟩
    exact (classAction_injective N q heq) ▸ hw
  · intro hz
    exact ⟨z,hz,rfl⟩

theorem classAction_restricted_measurePreserving (N : ℕ) [NeZero N]
    (q : gamma0Classes N) (K : Set UpperHalfPlane) :
    MeasurePreserving (classAction N q) ((volume : Measure UpperHalfPlane).restrict K)
      ((volume : Measure UpperHalfPlane).restrict (classAction N q '' K)) := by
  simpa only [classAction_image_preimage] using
    (classAction_measurePreserving N q).restrict_preimage_emb
      (classAction_measurableEmbedding N q) (classAction N q '' K)

/-- The exact compact-action pullback, without introducing a new measure
or a whole-upper-half-plane L2 hypothesis. -/
def chartPullbackCLM (N : ℕ) [NeZero N] {K : Set UpperHalfPlane} (hK : IsCompact K)
    (q : gamma0Classes N) : QuotientL2 N →L[ℂ] LocalScalarL2 K :=
  (Lp.compMeasurePreservingₗᵢ ℂ (classAction N q)
    (classAction_restricted_measurePreserving N q K)).toContinuousLinearMap.comp
      (compactPullbackCLM N (hK.image (classAction_continuous N q)))

theorem chartPullbackCLM_coe_ae (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (q : gamma0Classes N) (u : QuotientL2 N) :
    chartPullbackCLM N hK q u =ᵐ[(volume : Measure UpperHalfPlane).restrict K]
      (fun z => u (orbitProjection N (inverseClassRep N q • z))) := by
  have hc := Lp.coeFn_compMeasurePreserving
    (compactPullbackCLM N (hK.image (classAction_continuous N q)) u)
    (classAction_restricted_measurePreserving N q K)
  have hr := (classAction_restricted_measurePreserving N q K).quasiMeasurePreserving.ae
    (compactPullbackL2_coe_ae N (hK.image (classAction_continuous N q)) u)
  filter_upwards [hc,hr] with z hcomp hraw
  exact hcomp.trans hraw

theorem chartPullbackCLM_norm_le (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (q : gamma0Classes N) (u : QuotientL2 N) :
    ‖chartPullbackCLM N hK q u‖ ≤ Real.sqrt (chartOverlap N K q : ℝ) * ‖u‖ := by
  change ‖(Lp.compMeasurePreservingₗᵢ ℂ (classAction N q)
    (classAction_restricted_measurePreserving N q K))
      (compactPullbackCLM N (hK.image (classAction_continuous N q)) u)‖ ≤ _
  rw [(Lp.compMeasurePreservingₗᵢ ℂ (classAction N q)
    (classAction_restricted_measurePreserving N q K)).norm_map]
  exact compactPullbackLinear_bound N (hK.image (classAction_continuous N q)) u

theorem cutoffMultiply_memLp {K : Set UpperHalfPlane} (ρ : UpperHalfPlane → ℂ)
    (hc : Continuous ρ) (B : ℝ) (hB : ∀ z, ‖ρ z‖ ≤ B) (u : LocalScalarL2 K) :
    MemLp (fun z => ρ z * u z) 2 ((volume : Measure UpperHalfPlane).restrict K) := by
  apply u.memLp.of_le_mul (hc.aestronglyMeasurable.mul u.aestronglyMeasurable)
  apply Eventually.of_forall
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hB z) (norm_nonneg _)

def cutoffMultiply {K : Set UpperHalfPlane} (ρ : UpperHalfPlane → ℂ)
    (hc : Continuous ρ) (B : ℝ) (hB : ∀ z, ‖ρ z‖ ≤ B)
    (u : LocalScalarL2 K) : LocalScalarL2 K :=
  (cutoffMultiply_memLp ρ hc B hB u).toLp (fun z => ρ z * u z)

theorem cutoffMultiply_coe_ae {K : Set UpperHalfPlane} (ρ : UpperHalfPlane → ℂ)
    (hc : Continuous ρ) (B : ℝ) (hB : ∀ z, ‖ρ z‖ ≤ B) (u : LocalScalarL2 K) :
    cutoffMultiply ρ hc B hB u =ᵐ[(volume : Measure UpperHalfPlane).restrict K]
      (fun z => ρ z * u z) := (cutoffMultiply_memLp ρ hc B hB u).coeFn_toLp

def cutoffMultiplyLinear {K : Set UpperHalfPlane} (ρ : UpperHalfPlane → ℂ)
    (hc : Continuous ρ) (B : ℝ) (hB : ∀ z, ‖ρ z‖ ≤ B) :
    LocalScalarL2 K →ₗ[ℂ] LocalScalarL2 K where
  toFun := cutoffMultiply ρ hc B hB
  map_add' u v := by
    apply Lp.ext
    filter_upwards [cutoffMultiply_coe_ae ρ hc B hB (u+v),
      cutoffMultiply_coe_ae ρ hc B hB u, cutoffMultiply_coe_ae ρ hc B hB v,
      Lp.coeFn_add u v, Lp.coeFn_add (cutoffMultiply ρ hc B hB u)
        (cutoffMultiply ρ hc B hB v)] with z hsum hu hv hin hout
    rw [hsum,hout,hu,hv,hin]
    ring
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [cutoffMultiply_coe_ae ρ hc B hB (c • u),
      cutoffMultiply_coe_ae ρ hc B hB u, Lp.coeFn_smul c u,
      Lp.coeFn_smul c (cutoffMultiply ρ hc B hB u)] with z hmul hu hin hout
    rw [hmul,hout,hu,hin]
    simp only [smul_eq_mul]
    ring

theorem cutoffMultiply_norm_le {K : Set UpperHalfPlane} (ρ : UpperHalfPlane → ℂ)
    (hc : Continuous ρ) (B : ℝ) (hB : ∀ z, ‖ρ z‖ ≤ B) (u : LocalScalarL2 K) :
    ‖cutoffMultiply ρ hc B hB u‖ ≤ B * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [cutoffMultiply_coe_ae ρ hc B hB u] with z hz
  rw [hz,norm_mul]
  exact mul_le_mul_of_nonneg_right (hB z) (norm_nonneg _)

def cutoffMultiplyCLM {K : Set UpperHalfPlane} (ρ : UpperHalfPlane → ℂ)
    (hc : Continuous ρ) (B : ℝ) (hB : ∀ z, ‖ρ z‖ ≤ B) :
    LocalScalarL2 K →L[ℂ] LocalScalarL2 K :=
  (cutoffMultiplyLinear ρ hc B hB).mkContinuous B (cutoffMultiply_norm_le ρ hc B hB)

/-- A concrete value map on the ACTUAL completed quotient form. -/
def localizedCompletedValue (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (q : gamma0Classes N) (ρ : UpperHalfPlane → ℂ)
    (hc : Continuous ρ) (B : ℝ) (hB : ∀ z, ‖ρ z‖ ≤ B) :
    EnergyCompletion N →L[ℂ] LocalScalarL2 K :=
  (cutoffMultiplyCLM ρ hc B hB).comp
    ((chartPullbackCLM N hK q).comp (physicalProjection N))

theorem localizedCompletedValue_coe_ae (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (q : gamma0Classes N) (ρ : UpperHalfPlane → ℂ)
    (hc : Continuous ρ) (B : ℝ) (hB : ∀ z, ‖ρ z‖ ≤ B) (e : EnergyCompletion N) :
    localizedCompletedValue N hK q ρ hc B hB e =ᵐ[(volume : Measure UpperHalfPlane).restrict K]
      (fun z => ρ z * (physicalProjection N e) (orbitProjection N (inverseClassRep N q • z))) := by
  filter_upwards [cutoffMultiply_coe_ae ρ hc B hB
    (chartPullbackCLM N hK q (physicalProjection N e)),
    chartPullbackCLM_coe_ae N hK q (physicalProjection N e)] with z hz hp
  rw [hz,hp]

theorem localizedCompletedValue_norm_le (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (q : gamma0Classes N) (ρ : UpperHalfPlane → ℂ)
    (hc : Continuous ρ) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ z, ‖ρ z‖ ≤ B)
    (e : EnergyCompletion N) :
    ‖localizedCompletedValue N hK q ρ hc B hB e‖ ≤
      B * Real.sqrt (chartOverlap N K q : ℝ) * ‖e‖ := by
  apply (cutoffMultiply_norm_le ρ hc B hB _).trans
  have hp := (chartPullbackCLM_norm_le N hK q (physicalProjection N e)).trans
    (mul_le_mul_of_nonneg_left (physicalProjection_norm_le N e) (Real.sqrt_nonneg _))
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hB0

/-- Canonical smooth core representatives agree with the completed value
map after the actual quotient AE representative is transported through
the true compact image and actual measure-preserving matrix action. -/
theorem localizedCompletedValue_core_ae (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (q : gamma0Classes N) (ρ : UpperHalfPlane → ℂ)
    (hc : Continuous ρ) (B : ℝ) (hB : ∀ z, ‖ρ z‖ ≤ B) (u : EnergyCore N) :
    localizedCompletedValue N hK q ρ hc B hB (coreEmbedding N u)
      =ᵐ[(volume : Measure UpperHalfPlane).restrict K]
        localizedClassChart N (coreRepresentative N u) ρ q := by
  have hraw := (classAction_restricted_measurePreserving N q K).quasiMeasurePreserving.ae
    (quotient_ae_eq_pullback_compact N (hK.image (classAction_continuous N q))
      (chosenRepresentative_spec N u).1)
  filter_upwards [localizedCompletedValue_coe_ae N hK q ρ hc B hB (coreEmbedding N u),
    hraw] with z hz hu
  rw [hz,physicalProjection_core]
  change ρ z * (u : QuotientL2 N) (orbitProjection N (classAction N q z)) = _
  rw [hu]
  rfl

theorem localizedCompletedValue_norm_sq (N : ℕ) [NeZero N] {K : Set UpperHalfPlane}
    (hK : IsCompact K) (q : gamma0Classes N) (ρ : UpperHalfPlane → ℂ)
    (hc : Continuous ρ) (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ z, ‖ρ z‖ ≤ B)
    (e : EnergyCompletion N) :
    ‖localizedCompletedValue N hK q ρ hc B hB e‖^2 ≤
      B^2 * (chartOverlap N K q : ℝ) * ‖e‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (localizedCompletedValue_norm_le N hK q ρ hc B hB0 hB e) 2
  simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] using h

/-- Same explicit scalar mass bound on the actual physical form domain,
with its ORIGINAL quotient norm and its actual Dirichlet pairing. -/
theorem actualForm_localized_value_mass_bound (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) (q : gamma0Classes N)
    (ρ : UpperHalfPlane → ℂ) (hc : Continuous ρ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ z, ‖ρ z‖ ≤ B) (u : actualEnergyFormDomain N) :
    ‖localizedCompletedValue N hK q ρ hc B hB (actualEnergyLift N u)‖^2 ≤
      B^2 * (chartOverlap N K q : ℝ) * (‖(u : QuotientL2 N)‖^2 +
        (actualDirichletPair N (actualEnergyLift N u) (actualEnergyLift N u)).re) := by
  rw [actualEnergyLift_shifted_norm]
  exact localizedCompletedValue_norm_sq N hK q ρ hc B hB0 hB _

end
end ImbalancedChen.Part3.Gamma0CompletedLocalizedChartValue20261026b
