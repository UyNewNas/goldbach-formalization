import ImbalancedChen.P6OriginalMarkedIntegralPrices
import ImbalancedChen.P6OriginalSeventhMeshPrice
import ImbalancedChen.P6OriginalEighthMeshPrice
import ImbalancedChen.P6OriginalNinthMeshPrice

namespace ImbalancedChen.P6OriginalZeroMarkedIntegralCost

noncomputable section
open P6OriginalMarkedIntegralPrices P5OriginalCoefficientArithmetic

def originalMesh : Mesh :=
  ⟨32,999999999999999999,999999999999999999,32,999999999999999999⟩

theorem literal_prices_eq_original :
    (P6OriginalLiteralMeshPrices.price7:ℝ)=savedU7/K0 ∧
    (P6OriginalLiteralMeshPrices.price8:ℝ)=savedU8/K0 ∧
    (P6OriginalLiteralMeshPrices.price9:ℝ)=savedU9/K0 := by
  norm_num [P6OriginalLiteralMeshPrices.price7, P6OriginalLiteralMeshPrices.price8,
    P6OriginalLiteralMeshPrices.price9, savedU7, savedU8, savedU9, K0]

theorem original_mesh_upper_prices :
    (originalMesh.upper7 : ℝ) ≤ savedU7/K0 ∧ (originalMesh.upper8 : ℝ) ≤ savedU8/K0 ∧
      (originalMesh.upper9 : ℝ) ≤ savedU9/K0 := by
  constructor
  · change (P5U7OriginalRationalCoverCertificate.rationalUpper 32 1000000000000000000 : ℝ) ≤
      (1672464594622060236183097/1208925819614629174706176:ℝ)/(67619/10000)
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_le (K:=ℝ)).mpr P6OriginalSeventhMeshPrice.seventh_mesh_passes
  constructor
  · change (P2U8UniformRationalCover.uniformUpper 1000000000000000000 : ℝ) ≤
      (4904703865205402441361491/1208925819614629174706176:ℝ)/(67619/10000)
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_le (K:=ℝ)).mpr P6OriginalEighthMeshPrice.eighth_mesh_passes
  · change (P2U9DirectedRationalCover.rationalUpper 32 1000000000000000000 : ℝ) ≤
      (3937512077512215599969887/1208925819614629174706176:ℝ)/(67619/10000)
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_le (K:=ℝ)).mpr P6OriginalNinthMeshPrice.ninth_mesh_passes

@[simp] theorem original_mesh_rate_zero : originalMesh.rate = 0 :=
  originalMesh.rate_eq_zero original_mesh_upper_prices.1 original_mesh_upper_prices.2.1
    original_mesh_upper_prices.2.2

theorem three_actual_integral_cost_nonpos (H : ℝ) (hH : 0≤H) :
    ((2*(currentK*p5U7OriginalOmegaIntegral 1-U7Envelope fixedProductDensityCoefficient)+
      (currentK*currentChenUpsilon8HarmonicIntegral-U8Envelope fixedProductDensityCoefficient)+
      (currentK*currentChenUpsilon9HarmonicIntegral-U9Envelope fixedProductDensityCoefficient))*H) ≤ 0 := by
  simpa only [original_mesh_rate_zero,zero_mul] using originalMesh.integral_prices hH

end
end ImbalancedChen.P6OriginalZeroMarkedIntegralCost
