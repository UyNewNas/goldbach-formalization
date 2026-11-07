import ImbalancedChen.Part3ActualKRadialEnergyIdentity
import ImbalancedChen.Part3ImaginaryOrderKExplicitMajorant
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED, 2026-10-24. No acceptance credit.

The sibling finite-interval radial energy identity is consumed verbatim.
Only its actual infinity endpoint is added here. The bound uses the existing
raw-K estimate |K_(2it)(q)| <= 2/q and the existing q-derivative estimate
|K'_(2it)(q)| <= 8/q^2. Thus q*K*K' tends to zero at infinity without a
spectral assumption or a second derivation of the q-calculus chain.

The final theorem is the half-infinite Green identity in its improper-limit
form. The two finite integrals are kept together as one convergent signed
expression; no separate spectral L2 or Kuznetsov assertion is implied.
-/

namespace ImbalancedChen.Part3.ActualKFluxInfinitySourceOnly

noncomputable section

open Set Filter MeasureTheory
open scoped Topology
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKQDerivativeSourceOnly
open ImaginaryOrderKExplicitMajorantSourceOnly
open ImbalancedChen.Part3.ActualKRadialEnergyIdentity20261024zz

/-- The actual ODE boundary flux is O(q^-2), uniformly in real t. -/
theorem actual_K_flux_abs_le (t : ℝ) {q : ℝ} (hq : 0 < q) :
    |kFlux t q| ≤ 16 / q ^ 2 := by
  have hK := imaginaryOrderK_abs_le t hq
  have hD := qDerivative_abs_le t hq
  calc
    |kFlux t q| = q * |imaginaryOrderK t q| * |qDerivative t q| := by
      simp only [kFlux, abs_mul, abs_of_pos hq]
    _ ≤ q * (2 / q) * |qDerivative t q| :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hK hq.le) (abs_nonneg _)
    _ ≤ q * (2 / q) * (8 / q ^ 2) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    _ = 16 / q ^ 2 := by
      field_simp [hq.ne']
      ring

/-- The q*K*K' boundary term vanishes at the infinite cusp endpoint. -/
theorem actual_K_flux_tendsto_zero (t : ℝ) :
    Tendsto (kFlux t) atTop (𝓝 0) := by
  have hupper : Tendsto (fun q : ℝ => 16 / q ^ 2) atTop (𝓝 0) := by
    exact ((tendsto_pow_atTop (α := ℝ) (n := 2) (by norm_num)).const_div_atTop 16)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using hupper.neg) hupper ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with q hq
    exact neg_le_of_abs_le (actual_K_flux_abs_le t hq)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with q hq
    exact le_of_abs_le (actual_K_flux_abs_le t hq)

/-- The finite Green identity has a genuine half-infinite limit. The
negative imaginary-order term retains the factor 4*t^2 and the dq/q weight.
This is an endpoint statement for the actual K integral, not a spectral
Plancherel identity. -/
theorem actual_K_halfLine_Green_limit (t : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun b : ℝ =>
        (∫ q in a..b,
          q * (qDerivative t q) ^ 2 +
            q * (imaginaryOrderK t q) ^ 2) -
          4 * t ^ 2 *
            (∫ q in a..b, (imaginaryOrderK t q) ^ 2 / q))
      atTop (𝓝 (-kFlux t a)) := by
  have hflux := (actual_K_flux_tendsto_zero t).sub
    tendsto_const_nhds
  have hlim : Tendsto (fun b : ℝ => kFlux t b - kFlux t a)
      atTop (𝓝 (-kFlux t a)) := by
    simpa only [zero_sub] using hflux
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop a] with b hab
  have hfinite := k_energy_finite t ha hab
  dsimp
  linarith

end

end ImbalancedChen.Part3.ActualKFluxInfinitySourceOnly
