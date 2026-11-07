import ImbalancedChen.P5OriginalU8MidpointEnclosure
import ImbalancedChen.P5OriginalU8UpperOnlyStrictSourceSlot

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The finite endpoint comparison is explicitly still a port. The analytic
midpoint enclosure feeding it is proved without that port in the imported
file. No check is executed or asserted true here. The exact stored endpoint,
original K0, fixed positive density coefficient, and U8Envelope are retained.
Common full-policy density and strict-source PP debts remain in the J slot.
-/

namespace ImbalancedChen.P5OriginalU8MidpointEndpointPort

noncomputable section

open P5OriginalCoefficientArithmetic P5OriginalU8MidpointEnclosure

def storedIntegralUpper : ℚ :=
  (4904703865205402441361491 / 1208925819614629174706176) / (67619 / 10000)

theorem storedIntegralUpper_cast :
    (storedIntegralUpper : ℝ) = p5z_originalU8UpperIntegralEndpoint := by
  simp only [storedIntegralUpper, p5z_originalU8UpperIntegralEndpoint, savedU8,
    K0, Rat.cast_div, Rat.cast_ofNat]

def upperEndpointCheck (n m : ℕ) : Bool := decide (rationalUpper n m ≤ storedIntegralUpper)

/-- Conditional finite-check consumer, not a proof that the check passes.
All analytic enclosure and full-domain integration work is upstream. -/
theorem original_upper_endpoint_of_check (n m : ℕ) (hm : 0 < m)
    (hcheck : upperEndpointCheck n m = true) :
    currentChenUpsilon8HarmonicIntegral ≤ p5z_originalU8UpperIntegralEndpoint := by
  have hQ : rationalUpper n m ≤ storedIntegralUpper := of_decide_eq_true hcheck
  have hR : (rationalUpper n m : ℝ) ≤ (storedIntegralUpper : ℝ) := by exact_mod_cast hQ
  rw [← storedIntegralUpper_cast]
  exact (original_integral_midpoint_enclosure n m hm).2.trans hR

/-- The exact unchanged upper-only J envelope consumes the finite port.
No density, strict-PP, or original h8 assertion is inferred from it alone. -/
theorem unchanged_original_envelope_of_check (n m : ℕ) (hm : 0 < m)
    (hcheck : upperEndpointCheck n m = true) :
    fixedProductDensityCoefficient * currentChenUpsilon8HarmonicIntegral ≤
      U8Envelope fixedProductDensityCoefficient :=
  originalU8_envelope_of_upper_only (original_upper_endpoint_of_check n m hm hcheck)

end

end ImbalancedChen.P5OriginalU8MidpointEndpointPort
