import ImbalancedChen.Part3GammaCompletedGradientClassicalRepresentative
import ImbalancedChen.Part3GammaQuotientPlanarLocalL2
import ImbalancedChen.Part3CoordinateLocalH1CompactProducts

/-! SOURCE_ONLY / UNCOMPILED / zero formal credit.
Every ACTUAL completed Gamma0 form vector has weak coordinate H1 on
every compact positive rectangle. Its VALUE is the original physical
J-image orbit pullback, not a supplied smooth representative. The only
part of the classical-representative source used is its arbitrary weak
test identity, which has NO smoothness hypothesis on the value.
Compact cutoff products therefore give genuine compact H1 jets for the
subsequent rational-cusp transport; no local-H1 supplier is assumed. -/

namespace ImbalancedChen.Part3.GammaCompletedPhysicalLocalH120261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology UpperHalfPlane
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualEnergyCompletion20261025a
open GammaCompletedGradientClassicalRepresentative20261026b
open GammaQuotientPlanarLocalL220261026a
open ActualPullbackLocalH1Transfer20261026b
open CoordinateLocalH1CompactProducts20261026b
open CompactC2ProductMollifier20261026a
open PlanarLocalWeakGradientExtraction20261026b
open WeakH1ProductMollifierDerivative20261026a
open WeakGradientRectangleTensorPairing20261026a
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactGreenProductL120261025a
open ArbitraryCompactFirstGradientIBP20261026b
open OneCompactFirstGradientIBP20261025a
open LocalWeakH1CutoffProduct20261026b

def completedPlanePartial (N : ℕ) [NeZero N] (L R c d : ℝ) (hc : 0 < c)
    (vertical : Bool) (e : EnergyCompletion N) : PlaneL2 :=
  (planarCompletedPartial_memLp N (compactUpperBox_isCompact L R c d hc) vertical e).toLp
    (planarCompletedPartial N (compactUpperBox_isCompact L R c d hc) vertical e)

theorem actual_completed_pullback_memLp_closed_rectangle (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) (L R c d : ℝ) (hc : 0 < c) :
    MemLp (actualPlanePullback N (physicalProjection N e)) 2
      ((volume : Measure Plane).restrict (Icc L R ×ˢ Icc c d)) := by
  have hlarge := quotientPlanarRepresentative_memLp_rectangle N (physicalProjection N e)
    (L-1) (R+1) (c/2) (d+1) (by linarith)
  have hsub : Icc L R ×ˢ Icc c d ⊆ openRectangle (L-1) (R+1) (c/2) (d+1) := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩,
      ⟨by linarith [hp.2.1],by linarith [hp.2.2]⟩⟩
  exact hlarge.mono_measure (Measure.restrict_mono hsub le_rfl)

/-- All-smooth compact testing for the original nonsmooth physical
representative. There is no classical derivative identification premise. -/
theorem actual_completed_pullback_coordinate_local_H1 (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) (L R c d : ℝ) (hc : 0 < c) :
    HasCoordinateLocalH1On (Icc L R ×ˢ Icc c d)
      (actualPlanePullback N (physicalProjection N e)) := by
  let K := compactUpperBox L R c d
  have hK : IsCompact K := compactUpperBox_isCompact L R c d hc
  have hpos : Icc L R ×ˢ Icc c d ⊆ positiveChart :=
    fun p hp => hc.trans_le hp.2.1
  have hUK : ∀ z : UpperHalfPlane, (z.re,z.im) ∈ Icc L R ×ˢ Icc c d → z ∈ K :=
    fun z hz => hz
  have hrep : ∀ᵐ z ∂((volume : Measure UpperHalfPlane).restrict K),
      (physicalProjection N e) (Gamma0QuotientCellPushforward20261025a.orbitProjection N z) =
        actualPlanePullback N (physicalProjection N e) (z.re,z.im) :=
    Eventually.of_forall (fun z => (actualPlanePullback_at_upper N (physicalProjection N e) z).symm)
  refine ⟨actual_completed_pullback_memLp_closed_rectangle N e L R c d hc,
    completedPlanePartial N L R c d hc false e,completedPlanePartial N L R c d hc true e,?_⟩
  intro ψ hψ hψc hs
  have hx := planarCompletedPartial_weak_for_representative N hK false e hpos hUK
    (actualPlanePullback N (physicalProjection N e)) hrep hψ hψc hs
  have hy := planarCompletedPartial_weak_for_representative N hK true e hpos hUK
    (actualPlanePullback N (physicalProjection N e)) hrep hψ hψc hs
  have hp (vertical : Bool) :
      (∫ p : Plane, star (ψ p)*completedPlanePartial N L R c d hc vertical e p) =
        ∫ p : Plane, star (ψ p)*planarCompletedPartial N hK vertical e p := by
    apply integral_congr_ae
    filter_upwards [(planarCompletedPartial_memLp N hK vertical e).coeFn_toLp] with p hpartial
    rw [hpartial]
  constructor
  · rw [hp false]
    exact hx
  · rw [hp true]
    exact hy

/-- A legal compact smooth cutoff PRODUCES a genuine compact H1 jet of
the actual completed form's raw physical pullback. Both product derivatives
and all three support inclusions are retained for weak Mobius transport. -/
theorem actual_completed_compact_cutoff_H1_jet (N : ℕ) [NeZero N]
    (e : EnergyCompletion N) (L R c d : ℝ) (hc : 0 < c)
    {χ : Plane → ℂ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Icc L R ×ˢ Icc c d) :
    ∃ (gx gy : PlaneL2) (J : CompactH1Jet),
      J.value = (fun p => χ p*actualPlanePullback N (physicalProjection N e) p) ∧
      J.dx = productDerivative χ (actualPlanePullback N (physicalProjection N e)) gx ex ∧
      J.dy = productDerivative χ (actualPlanePullback N (physicalProjection N e)) gy ey ∧
      HasCompactSupport J.dx ∧ HasCompactSupport J.dy ∧
      tsupport J.value ⊆ tsupport χ ∧ tsupport J.dx ⊆ tsupport χ ∧ tsupport J.dy ⊆ tsupport χ := by
  obtain ⟨gx,gy,J,hv,hx,hy,hsv,hsx,hsy⟩ := coordinate_local_compact_product
    (measurableSet_Icc.prod measurableSet_Icc)
    (actual_completed_pullback_coordinate_local_H1 N e L R c d hc) hχ hχc hs
  exact ⟨gx,gy,J,hv,hx,hy,hχc.of_isClosed_subset isClosed_tsupport hsx,
    hχc.of_isClosed_subset isClosed_tsupport hsy,hsv,hsx,hsy⟩

end
end ImbalancedChen.Part3.GammaCompletedPhysicalLocalH120261026b
