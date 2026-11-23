import ImbalancedChen.P5OriginalFixedDensitySupplierAssembly
import ImbalancedChen.P5U7OriginalRationalCoverCertificate
import ImbalancedChen.P2U8UniformRationalCover
import ImbalancedChen.P2U9DirectedRationalCover

/-! Only upper rational covers are needed at the realized Fine density currentK.
The affine envelopes retain their original independent slope and k = currentK + 1e-8. -/
namespace ImbalancedChen.P6OriginalMarkedIntegralPrices

noncomputable section
open P5OriginalCoefficientArithmetic

/-- All three covers have a positive subdivision count. The two Taylor orders
and three subdivision counts can be chosen independently. -/
structure Mesh where
  order7 : ℕ
  subdivisions7Pred : ℕ
  subdivisions8Pred : ℕ
  order9 : ℕ
  subdivisions9Pred : ℕ

def Mesh.upper7 (g : Mesh) := P5U7OriginalRationalCoverCertificate.rationalUpper
  g.order7 (g.subdivisions7Pred+1)
def Mesh.upper8 (g : Mesh) := P2U8UniformRationalCover.uniformUpper (g.subdivisions8Pred+1)
def Mesh.upper9 (g : Mesh) := P2U9DirectedRationalCover.rationalUpper
  g.order9 (g.subdivisions9Pred+1)

def Mesh.rate (g : Mesh) : ℝ :=
  let k := fixedProductDensityCoefficient
  2*max (currentK*(g.upper7 : ℝ) - U7Envelope k) 0 +
    max (currentK*(g.upper8 : ℝ) - U8Envelope k) 0 +
    max (currentK*(g.upper9 : ℝ) - U9Envelope k) 0

theorem original_upper_price_gaps :
    currentK*(savedU7/K0) < U7Envelope fixedProductDensityCoefficient ∧
    currentK*(savedU8/K0) < U8Envelope fixedProductDensityCoefficient ∧
    currentK*(savedU9/K0) < U9Envelope fixedProductDensityCoefficient := by
  norm_num [currentK, K0, savedU7, savedU8, savedU9, U7Envelope, U8Envelope, U9Envelope,
    fixedProductDensityCoefficient, allowedDensityDelta, lowerU7AtK0, lowerU8AtK0, lowerU9AtK0]

/-- Three upper-only rational comparisons pay this part of the final ledger. -/
theorem Mesh.rate_eq_zero (g : Mesh) (h7 : (g.upper7 : ℝ) ≤ savedU7/K0)
    (h8 : (g.upper8 : ℝ) ≤ savedU8/K0) (h9 : (g.upper9 : ℝ) ≤ savedU9/K0) : g.rate = 0 := by
  have hk : 0 ≤ currentK := by norm_num [currentK]
  obtain ⟨hp7,hp8,hp9⟩ := original_upper_price_gaps
  have he7 := sub_nonpos.mpr ((mul_le_mul_of_nonneg_left h7 hk).trans hp7.le)
  have he8 := sub_nonpos.mpr ((mul_le_mul_of_nonneg_left h8 hk).trans hp8.le)
  have he9 := sub_nonpos.mpr ((mul_le_mul_of_nonneg_left h9 hk).trans hp9.le)
  simp only [Mesh.rate, max_eq_right he7, max_eq_right he8, max_eq_right he9, mul_zero, add_zero]

private theorem charge {J u H : ℝ} (h : J ≤ u) (hH : 0 ≤ H) (price : ℝ) :
    (currentK*J - price)*H ≤ max (currentK*u - price) 0*H :=
  mul_le_mul_of_nonneg_right ((sub_le_sub_right
    (mul_le_mul_of_nonneg_left h (by norm_num [currentK] : 0 ≤ currentK)) price).trans
      (le_max_left _ _)) hH

/-- The original analytic integrals have already been replaced here by
finite rational costs. No successful mesh comparison is assumed. -/
theorem Mesh.integral_prices (g : Mesh) {H : ℝ} (hH : 0 ≤ H) :
    ((2*(currentK*p5U7OriginalOmegaIntegral 1 - U7Envelope fixedProductDensityCoefficient) +
        (currentK*currentChenUpsilon8HarmonicIntegral - U8Envelope fixedProductDensityCoefficient) +
        (currentK*currentChenUpsilon9HarmonicIntegral - U9Envelope fixedProductDensityCoefficient))*H)
      ≤ g.rate*H := by
  have h7 := charge (P5U7OriginalRationalCoverCertificate.actual_integral_le_rationalUpper
    g.order7 (g.subdivisions7Pred+1) (Nat.succ_pos _)) hH (U7Envelope fixedProductDensityCoefficient)
  have h8 := charge (P2U8UniformRationalCover.eighthIntegral_le_uniformUpper
    (g.subdivisions8Pred+1) (Nat.succ_pos _)) hH (U8Envelope fixedProductDensityCoefficient)
  have h9 := charge (P2U9DirectedRationalCover.actual_integral_le_rationalUpper
    g.order9 (g.subdivisions9Pred+1) (Nat.succ_pos _)) hH (U9Envelope fixedProductDensityCoefficient)
  dsimp only [Mesh.rate, Mesh.upper7, Mesh.upper8, Mesh.upper9]
  linarith only [h7,h8,h9]

end
end ImbalancedChen.P6OriginalMarkedIntegralPrices
