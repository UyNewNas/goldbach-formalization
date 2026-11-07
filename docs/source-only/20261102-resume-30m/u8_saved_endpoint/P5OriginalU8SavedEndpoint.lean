import ImbalancedChen.P5OriginalU8MidpointEndpointPort
import ImbalancedChen.P2DirectedLogRounding

/-!
SOURCE ONLY / UNCOMPILED / UNEVALUATED FINITE COMPARISON / ZERO CREDIT.

The parameters below are fixed in source, without executing a parameter
search or any arithmetic checker. The only decisive finite proof body is
`of_decide_eq_true rfl`. Its reduction is deliberately left to a later
user-owned compilation. Neither its reduction result nor its resource
requirements have been checked in this session.

Each exact K midpoint panel is rounded UP once, after its analytic
enclosure has been computed. This controls denominators in the final sum.
It does not reproduce or authenticate the archived Q80 producer. The
unchanged exact K rationalUpper is bounded by this dyadic aggregate.
The endpoint remains exactly the original savedU8 / K0.
-/

namespace ImbalancedChen.P5OriginalU8SavedEndpoint

noncomputable section

open scoped BigOperators
open P5OriginalU8ScalarProducer P5OriginalU8MidpointEnclosure
open P5OriginalU8MidpointEndpointPort P5OriginalCoefficientArithmetic
open Certificates.P2DirectedLogRounding

/-- Fixed analytic log order, not selected by an executed search. -/
def logOrder : ℕ := 32

/-- Fourfold refinement of the archived 1024-panel partition. -/
def panelCount : ℕ := 4096

/-- A single upward Q80 rounding of each completed exact panel. -/
def roundingBits : ℕ := 80

theorem panelCount_pos : 0 < panelCount := of_decide_eq_true rfl

def dyadicUpper (n m bits : ℕ) : ℚ :=
  ∑ k ∈ Finset.range m,
    roundUp bits (panelUpper n (mesh m k) (mesh m (k + 1)))

/-- This majorizes the actual K rationalUpper, including signed curvature.
No positivity assertion about a panel or its curvature is needed. -/
theorem rationalUpper_le_dyadicUpper (n m bits : ℕ) :
    rationalUpper n m ≤ dyadicUpper n m bits := by
  unfold rationalUpper dyadicUpper
  exact Finset.sum_le_sum (fun k _ =>
    le_roundUp bits (panelUpper n (mesh m k) (mesh m (k + 1))))

/-- Closed exact rational comparison; UNEVALUATED. There is no Boolean
truth hypothesis, saved execution equality, or imported endpoint estimate.
This is a candidate pure kernel reduction, not a report that it ran.
The large local recursion setting grants no correctness assumption. -/
set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem closed_dyadicUpper_le_storedIntegralUpper :
    dyadicUpper logOrder panelCount roundingBits ≤ storedIntegralUpper :=
  of_decide_eq_true rfl

/-- The exact original comparison requested by the K endpoint port.
No weakened endpoint or replacement integral is introduced. -/
theorem rationalUpper_le_original_storedIntegralUpper :
    rationalUpper logOrder panelCount ≤ storedIntegralUpper :=
  (rationalUpper_le_dyadicUpper logOrder panelCount roundingBits).trans
    closed_dyadicUpper_le_storedIntegralUpper

/-- Existing K Boolean port discharged by the preceding closed proof
candidate, rather than supplied as an argument. -/
theorem original_upperEndpointCheck :
    upperEndpointCheck logOrder panelCount = true := by
  unfold upperEndpointCheck
  exact decide_eq_true_iff.mpr rationalUpper_le_original_storedIntegralUpper

/-- Consume the K full-domain analytic enclosure at the fixed parameters. -/
theorem original_integral_le_saved_endpoint :
    currentChenUpsilon8HarmonicIntegral ≤ p5z_originalU8UpperIntegralEndpoint :=
  original_upper_endpoint_of_check logOrder panelCount panelCount_pos
    original_upperEndpointCheck

/-- Exact unchanged upper-only coefficient envelope. The common density,
same-rho strict-source PP and full original h8 remain separate obligations. -/
theorem unchanged_original_upper_envelope :
    fixedProductDensityCoefficient * currentChenUpsilon8HarmonicIntegral ≤
      U8Envelope fixedProductDensityCoefficient :=
  originalU8_envelope_of_upper_only original_integral_le_saved_endpoint

end

end ImbalancedChen.P5OriginalU8SavedEndpoint
