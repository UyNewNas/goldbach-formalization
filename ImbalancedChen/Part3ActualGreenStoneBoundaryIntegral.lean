import ImbalancedChen.Part3ActualGreenBoundaryDiagonal
import ImbalancedChen.Part3CompactRectangleBoundaryIntegral
import ImbalancedChen.Part3ActualStoneSqrtPathUniform
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Actual compact-test Stone boundary integral along vertical spectral paths

nuPlus is the positive-real square root of -(x+i*epsilon), so its order
boundary is -i*sqrt(x). nuMinus corresponds to x-i*epsilon and has boundary
+i*sqrt(x). The normalized difference has density
sinh(pi*sqrt(x))/pi^2 * |actualKtransform f (sqrt(x))|^2 with respect to dx.

The common bound is proved from continuity on a genuine compact rectangle:
actual closed-slab Green pairing continuity is composed with the actual
square-root paths. Thus the spectral-interval limit exchange has no hBound,
hLimit, hConnection, spectral measure, or Stone formula premise.

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualGreenStoneBoundaryIntegral20261025a

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open ActualGreenPairingHolomorphy20261025a ActualGreenBoundaryMajorant20261025a
open ActualGreenBoundaryDiagonal20261025a ActualStoneSqrtPath20261025a
open CompactRectangleBoundaryIntegral20261025a ActualKLCompactTestIntegrationByParts20261025a

def normalizedStonePairJump (f : ℝ → ℂ) (x eps : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
    (actualGreenPairing f (fun r => star (f r)) (nuPlus x eps) -
      actualGreenPairing f (fun r => star (f r)) (nuMinus x eps))

def actualCompactLambdaDensity (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  Real.sinh (Real.pi * Real.sqrt x) / Real.pi ^ 2 *
    ‖actualKtransform f (Real.sqrt x)‖ ^ 2

private theorem orderRectangle_subset_boundarySlab (B : ℝ) :
    orderRectangle B ⊆ boundaryOrderSlab := by
  intro nu hnu
  have h := orderRectangle_coordinates hnu
  exact ⟨h.1, h.2.1.trans (by norm_num)⟩

/-- Both actual spectral paths stay in the domain of the proved boundary
continuity, including epsilon=0. This supplies the compact bound used below. -/
theorem normalizedStonePairJump_continuousOn_rectangle {A B : ℝ}
    (hA : 0 < A) {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ContinuousOn (fun p : ℝ × ℝ => normalizedStonePairJump f p.1 p.2)
      (Icc A B ×ˢ Icc 0 (pathRadius A)) := by
  have hpair := continuousOn_actualGreenPairing_boundary
    hf hf.star hfc (hasCompactSupport_star hfc)
  have hplus : MapsTo (fun p : ℝ × ℝ => nuPlus p.1 p.2)
      (Icc A B ×ˢ Icc 0 (pathRadius A)) boundaryOrderSlab := by
    intro p hp
    exact orderRectangle_subset_boundarySlab B
      (nuPlus_mem_orderRectangle hA hp.1.1 hp.1.2 hp.2.1 hp.2.2)
  have hminus : MapsTo (fun p : ℝ × ℝ => nuMinus p.1 p.2)
      (Icc A B ×ˢ Icc 0 (pathRadius A)) boundaryOrderSlab := by
    intro p hp
    exact orderRectangle_subset_boundarySlab B
      (nuMinus_mem_orderRectangle hA hp.1.1 hp.1.2 hp.2.1 hp.2.2)
  exact continuousOn_const.mul
    ((hpair.comp (continuousOn_nuPlus_rectangle hA) hplus).sub
      (hpair.comp (continuousOn_nuMinus_rectangle hA) hminus))

/-- The actual spectral density at the zero-epsilon edge of the rectangle. -/
theorem normalizedStonePairJump_zero {x : ℝ} (hx : 0 < x)
    {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    normalizedStonePairJump f x 0 = (actualCompactLambdaDensity f x : ℂ) := by
  unfold normalizedStonePairJump actualCompactLambdaDensity
  rw [nuPlus_zero hx, nuMinus_zero hx]
  simpa only [boundaryPlus, boundaryMinus, neg_mul] using
    actualGreenPairing_normalized_diagonal_jump hf hfc (Real.sqrt x)

/-- Explicit existence of one finite bound for all x and epsilon in the
actual Stone rectangle. This is a conclusion, not a supplier hypothesis. -/
theorem exists_normalizedStonePairJump_bound {A B : ℝ}
    (hA : 0 < A) {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ x ∈ Icc A B, ∀ eps ∈ Icc 0 (pathRadius A),
      ‖normalizedStonePairJump f x eps‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (normalizedStonePairJump_continuousOn_rectangle (B := B) hA hf hfc)
  exact ⟨C, fun x hx eps heps => hC (x, eps) ⟨hx, heps⟩⟩

/-- Actual compact-test boundary exchange over a closed spectral interval.
The majorant is produced by the compact rectangle, and the pointwise limit
is the actual K-transform square from the true K/I connection. -/
theorem actualGreenPairing_Stone_Icc_tendsto {A B : ℝ}
    (hA : 0 < A) {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun eps : ℝ => (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      ∫ x in Icc A B,
        (actualGreenPairing f (fun r => star (f r)) (nuPlus x eps) -
          actualGreenPairing f (fun r => star (f r)) (nuMinus x eps)))
      (𝓝[>] 0) (𝓝 ((∫ x in Icc A B, actualCompactLambdaDensity f x : ℝ) : ℂ)) := by
  have h := integral_tendsto_of_continuousOn_rectangle
    (fun p : ℝ × ℝ => normalizedStonePairJump f p.1 p.2)
    A B (pathRadius A) (pathRadius_pos hA)
    (normalizedStonePairJump_continuousOn_rectangle hA hf hfc)
  have hzero : (∫ x in Icc A B, normalizedStonePairJump f x 0) =
      ((∫ x in Icc A B, actualCompactLambdaDensity f x : ℝ) : ℂ) := by
    calc
      _ = ∫ x in Icc A B, (actualCompactLambdaDensity f x : ℂ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        exact normalizedStonePairJump_zero (hA.trans_le hx.1) hf hfc
      _ = _ := integral_ofReal
  rw [hzero] at h
  simpa only [normalizedStonePairJump, integral_const_mul] using h

/-- Oriented-interval form for direct use with the actual scalar Stone caller.
The density is with respect to lambda=x, before any tau=sqrt(x) Jacobian. -/
theorem actualGreenPairing_Stone_interval_tendsto {A B : ℝ}
    (hA : 0 < A) (hAB : A ≤ B)
    {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun eps : ℝ => (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      ∫ x in A..B,
        (actualGreenPairing f (fun r => star (f r)) (nuPlus x eps) -
          actualGreenPairing f (fun r => star (f r)) (nuMinus x eps)))
      (𝓝[>] 0) (𝓝 ((∫ x in A..B, actualCompactLambdaDensity f x : ℝ) : ℂ)) := by
  simpa only [intervalIntegral.integral_of_le hAB, ← integral_Icc_eq_integral_Ioc] using
    actualGreenPairing_Stone_Icc_tendsto (B := B) hA hf hfc

end
end ImbalancedChen.Part3.ActualGreenStoneBoundaryIntegral20261025a
