import ImbalancedChen.Part3Gamma0ActualDefectLocalH1
import ImbalancedChen.Part3UpperRectangleMollifierGeometry

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Local H1 for the literal orbit pullback, rather than only its compact
localization. Global ordinary L2 of the automorphic pullback is neither
assumed nor asserted. L2 membership is on the actual local rectangle;
the weak identities are literal integrals with that original pullback. -/

namespace ImbalancedChen.Part3.ActualPullbackLocalH1Transfer20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open ProductConvolutionSecondDerivatives20261026a
open PlanarLocalWeakGradientExtraction20261026b
open Gamma0ActualSmoothQuotientCore20261025a Gamma0QuotientCellPushforward20261025a
open Gamma0CompactDefectMollifier20261026a
open CanonicalPlanarL2UnitarySourceOnly UpperRectangleMollifierGeometry20261026b

def actualPlanePullback (N : ℕ) (f : QuotientL2 N) (p : Plane) : ℂ :=
  if hp : 0 < p.2 then f (orbitProjection N (⟨⟨p.1, p.2⟩, hp⟩ : UpperHalfPlane)) else 0

theorem actualPlanePullback_at_upper (N : ℕ) (f : QuotientL2 N) (z : UpperHalfPlane) :
    actualPlanePullback N f (chartMap z) = f (orbitProjection N z) := by
  have hp : 0 < (chartMap z).2 := z.im_pos
  have hz : (⟨⟨(chartMap z).1, (chartMap z).2⟩, hp⟩ : UpperHalfPlane) = z := by
    apply UpperHalfPlane.coe_injective
    apply Complex.ext <;> rfl
  rw [actualPlanePullback, dif_pos hp, hz]

/-- The local definition includes actual local L2 membership and both
literal weak derivative identities for every compact smooth test. -/
def HasCoordinateLocalH1On (Ω : Set Plane) (F : Plane → ℂ) : Prop :=
  MemLp F 2 ((volume : Measure Plane).restrict Ω) ∧
    ∃ gx gy : PlaneL2, ∀ ψ : Plane → ℂ,
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
        ((∫ p : Plane, star (ψ p) * gx p) =
          -(∫ p : Plane, star (directional xDirection ψ p) * F p)) ∧
        ((∫ p : Plane, star (ψ p) * gy p) =
          -(∫ p : Plane, star (directional yDirection ψ p) * F p))

/-- Replacing a localized representative by its original values on Ω
preserves all compact tests; outside Ω each test derivative is zero. -/
theorem localH1_of_local_extension {Ω : Set Plane} (hΩ : MeasurableSet Ω)
    {F G : Plane → ℂ} (hF : HasLocalL2GradientOn Ω F)
    (heq : ∀ p ∈ Ω, F p = G p) : HasCoordinateLocalH1On Ω G := by
  obtain ⟨hF2, gx, gy, hweak⟩ := hF
  have hae : F =ᵐ[(volume : Measure Plane).restrict Ω] G :=
    (ae_restrict_iff' hΩ).2 (Eventually.of_forall heq)
  refine ⟨(memLp_congr_ae hae).1 (hF2.restrict Ω), gx, gy, fun ψ hψ hc hs => ?_⟩
  have hpair (v : Plane) :
      (∫ p : Plane, star (directional v ψ p) * F p) =
        ∫ p : Plane, star (directional v ψ p) * G p := by
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by
      by_cases hp : p ∈ tsupport ψ
      · rw [heq p (hs hp)]
      · unfold directional
        rw [fderiv_of_notMem_tsupport hp]
        simp
  obtain ⟨hx, hy⟩ := hweak ψ hψ hc hs
  exact ⟨(hpair xDirection) ▸ hx, (hpair yDirection) ▸ hy⟩

theorem localizedPlane_eq_actual_on_rectangle (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} {B L R c d : ℝ} (hc : 0 < c)
    (hbound : ∀ z ∈ K, z.im ≤ B) (f : QuotientL2 N)
    (hK : upperRectangle L R c d ⊆ K) :
    ∀ p ∈ Icc L R ×ˢ Icc c d,
      localizedPlane N K B f p = actualPlanePullback N f p := by
  intro p hp
  have hpos : 0 < p.2 := hc.trans_le hp.2.1
  let z : UpperHalfPlane := ⟨⟨p.1, p.2⟩, hpos⟩
  have hzp : chartMap z = p := by apply Prod.ext <;> rfl
  have hz : z ∈ K := hK hp
  rw [← hzp, localizedPlane_at_upper N hbound f z,
    actualPlanePullback_at_upper N f z]
  simp only [compactPullback, indicator_of_mem hz]

end
end ImbalancedChen.Part3.ActualPullbackLocalH1Transfer20261026b
