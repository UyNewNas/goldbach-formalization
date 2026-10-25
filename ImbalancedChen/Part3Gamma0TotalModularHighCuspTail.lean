import ImbalancedChen.Part3Gamma0ModularFiniteCoverMeasure
import ImbalancedChen.Part3Gamma0ActualHighCuspTail

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The TOTAL pullback of the full-modular high-cusp tail to Gamma0(N).
Its actual carrier measure is index(Gamma0(N))/Y, obtained from the
proved finite-cover pushforward and the actual level-one cusp theorem.
This differs from the single width-one infinity cusp of Gamma0(N),
whose mass is 1/Y. No decomposition into separately indexed Gamma0
cusps, smooth cutoff, form-core membership, or spectral assertion is
made. The full-modular observable is actually SL(2,Z)-invariant.
-/

namespace ImbalancedChen.Part3.Gamma0TotalModularHighCuspTail20261025a

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane ENNReal
open Gamma0QuotientCellPushforward20261025a
open Gamma0ModularFiniteCoverMeasure20261025a
open Gamma0ActualHighCuspTail20261025a

/-- The actual total lifted modular high-cusp set in the Gamma0 quotient.
It uses the original canonical quotient measures on both levels. -/
def totalModularHighTail (N : ℕ) (Y : ℝ) : Set (Gamma0OrbitSpace N) :=
  forgetLevel N ⁻¹' quotientHighTail 1 Y

theorem totalModularHighTail_measurable (N : ℕ) (Y : ℝ) :
    MeasurableSet (totalModularHighTail N Y) :=
  (forgetLevel_measurable N) (quotientHighTail_measurable 1 Y)

def totalModularHighIndicator (N : ℕ) (Y : ℝ) : Gamma0OrbitSpace N → ℝ≥0∞ :=
  quotientHighIndicator 1 Y ∘ forgetLevel N

theorem totalModularHighIndicator_measurable (N : ℕ) (Y : ℝ) :
    Measurable (totalModularHighIndicator N Y) :=
  (quotientHighIndicator_measurable 1 Y).comp (forgetLevel_measurable N)

theorem totalModularHighIndicator_zero_or_one (N : ℕ) (Y : ℝ) (hY : 1 < Y)
    (q : Gamma0OrbitSpace N) :
    totalModularHighIndicator N Y q = 0 ∨ totalModularHighIndicator N Y q = 1 :=
  quotientHighIndicator_zero_or_one 1 Y hY (forgetLevel N q)

theorem totalModularHighIndicator_eq_indicator (N : ℕ) (Y : ℝ) (hY : 1 < Y) :
    totalModularHighIndicator N Y = (totalModularHighTail N Y).indicator (fun _ => 1) := by
  funext q
  change quotientHighIndicator 1 Y (forgetLevel N q) = _
  rw [quotientHighIndicator_eq_indicator 1 Y hY]
  rfl

/-- Exact TOTAL mass, from a genuine finite-cover measure theorem.
There is no hCovolume, hCoverMeasure, or hTailMass argument. -/
theorem totalModularHighTail_volume (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 < Y) :
    carrierPushforward N (totalModularHighTail N Y) =
      ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) * ENNReal.ofReal (1 / Y) := by
  rw [totalModularHighTail,
    carrier_preimage_modular_set N (quotientHighTail_measurable 1 Y),
    quotientHighTail_volume 1 Y hY]

theorem lintegral_totalModularHighIndicator (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 < Y) :
    (∫⁻ q, totalModularHighIndicator N Y q ∂carrierPushforward N) =
      ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) * ENNReal.ofReal (1 / Y) := by
  rw [totalModularHighIndicator_eq_indicator N Y hY,
    lintegral_indicator (totalModularHighTail_measurable N Y)]
  simp only [lintegral_const, Measure.restrict_apply_univ, one_mul]
  exact totalModularHighTail_volume N Y hY

/-- This TOTAL observable retains full modular invariance on the actual
upper half-plane, whereas a single Gamma0 infinity cusp need not. -/
theorem totalModularHighIndicator_smul (N : ℕ) (Y : ℝ)
    (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    totalModularHighIndicator N Y (orbitProjection N (g • z)) =
      totalModularHighIndicator N Y (orbitProjection N z) :=
  modular_observable_lift_invariant N (quotientHighIndicator 1 Y) g z

theorem totalModularHighTail_smul_iff (N : ℕ) (Y : ℝ)
    (g : SL(2, ℤ)) (z : UpperHalfPlane) :
    orbitProjection N (g • z) ∈ totalModularHighTail N Y ↔
      orbitProjection N z ∈ totalModularHighTail N Y := by
  change quotientHighIndicator 1 Y (forgetLevel N (orbitProjection N (g • z))) = 1 ↔
    quotientHighIndicator 1 Y (forgetLevel N (orbitProjection N z)) = 1
  rw [modular_observable_lift_invariant N (quotientHighIndicator 1 Y) g z]

end
end ImbalancedChen.Part3.Gamma0TotalModularHighCuspTail20261025a
