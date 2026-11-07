import ImbalancedChen.P2FullMaskActualNativeGain

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The first additional Delta/8 allowance now pays two proved errors of
one actual source: a positive inward collar (at most half the allowance)
and the subsequent native four-prime harmonic approximation (strictly
less than half). Delta is fixed before one uniform target threshold.

The SECOND Delta/8 is still explicitly booked for compilation. No
arithmetic compiler, AP discrepancy, baseline mean, parent majorant
licence or Chen counting conclusion is manufactured by this file.
-/

namespace ImbalancedChen.P2FullMaskNativeApproximationReserve

noncomputable section

open Set MeasureTheory Filter Topology
open scoped BigOperators
open P2FullMaskActualNativeGain
open P2ActualSameMaskFloorFibreAccounting P2ActualSameMaskDelta8Endpoint
open Certificates.PairedV2.FullMask.P2SemanticGainSetIntegral
open Certificates.PairedV2.FullMask.P2PairedSemanticRestrictionError
open Certificates.PairedV2.FullMask.P2PairedBoundaryCollarReserve
open P5OriginalCoefficientArithmetic

/-- The same real delta works for the geometric gain and every later
native prime target. No asymptotic rate or finite mean is an assumption. -/
theorem exists_native_gain_approximation {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      lostGain (shrunkRegion δ) ≤ ε / 2 ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
        |nativeGain δ N - retainedGain (shrunkRegion δ)| < ε / 2 ∧
          actualExtraFibreGain - ε < nativeGain δ N := by
  obtain ⟨δ, hδ, hloss⟩ := exists_positive_buffer_loss_le (half_pos hε)
  have ht := tendsto_nativeGain hδ.le
  have happ : ∀ᶠ N : ℕ in atTop,
      |nativeGain δ N - retainedGain (shrunkRegion δ)| < ε / 2 := by
    simpa only [Real.dist_eq] using
      Metric.tendsto_nhds.mp ht (ε / 2) (half_pos hε)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp happ
  refine ⟨δ, hδ, hloss, max 2 N₁, le_max_left _ _, ?_⟩
  intro N hN
  have hclose := hN₁ N ((le_max_right _ _).trans hN)
  have hlower := (abs_lt.mp hclose).1
  have hexact := full_sub_retained_eq_lost (shrunkRegion_measurable δ)
    (shrunkRegion_subset_region hδ.le)
  change actualExtraFibreGain - retainedGain (shrunkRegion δ) =
    lostGain (shrunkRegion δ) at hexact
  exact ⟨hclose, by linarith⟩

/-- The saved loss remains the actual historical saved ordinary-plus-
defect quantity. Only the EXTRA positive contribution is now evaluated
on the genuine original prime source. -/
def nativeIncrement (δ : ℝ) (N : ℕ) : ℝ :=
  nativeGain δ N + (oldSavedFloorPayment - actualStoredLoss)

def nativeSourceEndpoint (δ : ℝ) (N : ℕ) : ℝ :=
  adoptedAtK0 + baselineContinuation + nativeIncrement δ N

/-- Delta/8 finite density approximation, with its exact native source,
is discharged. The second allowance is NOT claimed to have been paid. -/
theorem exists_native_increment_after_density_reserve :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      actualSameMaskIncrement - extraReserve < nativeIncrement δ N := by
  obtain ⟨δ, hδ, _hloss, N₀, hN₀, hN⟩ :=
    exists_native_gain_approximation extraReserve_pos
  refine ⟨δ, hδ, N₀, hN₀, ?_⟩
  intro N hNN
  have h := (hN N hNN).2
  dsimp only [nativeIncrement, actualSameMaskIncrement]
  linarith

/-- A fixed positive collar and one common N threshold preserve the
original source-endpoint room after the FIRST extra allowance is spent.
The second extra allowance and BOTH baseline reserves stay explicit.
The baseline summands remain a ledger, so this is not a Chen mean. -/
theorem exists_native_currentC_source_room :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      currentC + originalEndpointSlack <
        nativeSourceEndpoint δ N - 2 * baselineReserve - extraReserve := by
  obtain ⟨δ, hδ, N₀, hN₀, hN⟩ := exists_native_increment_after_density_reserve
  refine ⟨δ, hδ, N₀, hN₀, ?_⟩
  intro N hNN
  have hinc := hN N hNN
  have hraw := actual_increment_gt_original_delta
  unfold nativeSourceEndpoint originalEndpointSlack adoptedReconstruction
  rw [original_eachReserve_eq]
  linarith

/-- The rational source endpoint is retained strictly, without erasing
the positive original slack or changing the current constant. -/
theorem exists_native_currentC_source_room_literal :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (49044063 / 25000000 : ℝ) <
        nativeSourceEndpoint δ N - 2 * baselineReserve - extraReserve := by
  obtain ⟨δ, hδ, N₀, hN₀, hN⟩ := exists_native_currentC_source_room
  refine ⟨δ, hδ, N₀, hN₀, ?_⟩
  intro N hNN
  have h := hN N hNN
  have hs := originalEndpointSlack_pos
  change currentC < _
  linarith

/-- The true saved ordinary comparison retains its direction alongside
the new native limit. No inequality for the true removed Y6 count is
obtained by reversing the proxy inequality. -/
theorem native_gain_with_original_saved_direction :
    Tendsto (nativeGain 0) atTop (𝓝 actualExtraFibreGain) ∧
      actualStoredLoss - actualDefectStoredLoss ≤
        P2HistoricalOrdinaryProxyIntegral.selectedOrdinaryProxy ∧
      P2HistoricalOrdinaryProxyIntegral.selectedOrdinaryProxy ≤
        P2HistoricalOrdinaryProxyIntegral.selectedOrdinaryIntegral / 4 :=
  ⟨tendsto_nativeGain_full, actual_ordinary_proxy_chain⟩

end

end ImbalancedChen.P2FullMaskNativeApproximationReserve
