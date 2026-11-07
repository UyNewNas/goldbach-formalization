import ImbalancedChen.Part3ActualHeckeForgetCoverMeasure
import Mathlib.MeasureTheory.Function.L2Space

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
Actual native L2 pullback along the true relative cover, with squared norm
multiplier p+1 and canonical normalized complex-linear isometric embedding.
Well-definedness uses proved quasi-measure-preservation; the norm uses the
proved actual canonical pushforward, not a supplied cover/norm hypothesis.
-/

namespace ImbalancedChen.Part3.ActualHeckeForgetL220261026b
noncomputable section
open Set MeasureTheory
open ActualHeckeForgetCoverMeasure20261026b Gamma0QuotientCellPushforward20261025a

variable (N p : ℕ) [NeZero N] [NeZero (N*p)] (hp : p.Prime) (hpN : ¬ p ∣ N)

theorem forgetPrimeLevel_measurePreserving :
    MeasurePreserving (forgetPrimeLevel N p) (carrierPushforward (N*p))
      ((p+1 : ℝ≥0∞) • carrierPushforward N) :=
  ⟨forgetPrimeLevel_measurable N p, forgetPrimeLevel_map_measure N p hp hpN⟩

theorem forgetPrimeLevel_quasiMeasurePreserving :
    QuasiMeasurePreserving (forgetPrimeLevel N p) (carrierPushforward (N*p)) (carrierPushforward N) := by
  refine ⟨forgetPrimeLevel_measurable N p, ?_⟩
  rw [forgetPrimeLevel_map_measure N p hp hpN]
  exact Measure.smul_absolutelyContinuous

theorem forgetPrimeLevel_memLp {U : Gamma0OrbitSpace N → ℂ}
    (hU : MemLp U 2 (carrierPushforward N)) :
    MemLp (U ∘ forgetPrimeLevel N p) 2 (carrierPushforward (N*p)) :=
  (hU.smul_measure (by simp : (p+1 : ℝ≥0∞) ≠ ∞)).comp_measurePreserving
    (forgetPrimeLevel_measurePreserving N p hp hpN)

def rawPullback (F : Lp ℂ 2 (carrierPushforward N)) : Lp ℂ 2 (carrierPushforward (N*p)) :=
  (forgetPrimeLevel_memLp N p hp hpN (Lp.memLp F)).toLp (F ∘ forgetPrimeLevel N p)

theorem rawPullback_coe (F : Lp ℂ 2 (carrierPushforward N)) :
    (rawPullback N p hp hpN F : Gamma0OrbitSpace (N*p) → ℂ) =ᵐ[carrierPushforward (N*p)]
      F ∘ forgetPrimeLevel N p :=
  (forgetPrimeLevel_memLp N p hp hpN (Lp.memLp F)).coeFn_toLp

private theorem l2_integral_norm_square {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : Lp ℂ 2 μ) : (∫ x, ‖F x‖^2 ∂μ) = ‖F‖^2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    (L2.inner_def (𝕜 := ℂ) F F).symm

theorem rawPullback_norm_sq (F : Lp ℂ 2 (carrierPushforward N)) :
    ‖rawPullback N p hp hpN F‖^2 = (p+1 : ℝ)*‖F‖^2 := by
  have hsq : Integrable (fun q => ‖F q‖^2) ((p+1 : ℝ≥0∞) • carrierPushforward N) :=
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp F).aestronglyMeasurable).mp (Lp.memLp F)).smul_measure (by simp)
  have hm : AEStronglyMeasurable (fun q => ‖F q‖^2)
      ((carrierPushforward (N*p)).map (forgetPrimeLevel N p)) := by
    rw [forgetPrimeLevel_map_measure N p hp hpN]
    exact hsq.aestronglyMeasurable
  calc
    _ = ∫ q, ‖rawPullback N p hp hpN F q‖^2 ∂carrierPushforward (N*p) :=
      (l2_integral_norm_square _ _).symm
    _ = ∫ q, ‖F (forgetPrimeLevel N p q)‖^2 ∂carrierPushforward (N*p) := by
      apply integral_congr_ae
      filter_upwards [rawPullback_coe N p hp hpN F] with q hq
      rw [hq]
    _ = ∫ q, ‖F q‖^2 ∂(carrierPushforward (N*p)).map (forgetPrimeLevel N p) :=
      (integral_map (forgetPrimeLevel_measurable N p).aemeasurable hm).symm
    _ = _ := by
      rw [forgetPrimeLevel_map_measure N p hp hpN, integral_smul_measure,
        l2_integral_norm_square]
      simp

theorem rawPullback_norm (F : Lp ℂ 2 (carrierPushforward N)) :
    ‖rawPullback N p hp hpN F‖ = Real.sqrt (p+1 : ℝ)*‖F‖ := by
  have hs := rawPullback_norm_sq N p hp hpN F
  have hroot := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ p+1)
  have hnon : 0 ≤ Real.sqrt (p+1 : ℝ)*‖F‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  apply (sq_eq_sq₀ (norm_nonneg _) hnon).mp
  rw [mul_pow, hroot]
  exact hs

def rawPullbackLinear : Lp ℂ 2 (carrierPushforward N) →ₗ[ℂ] Lp ℂ 2 (carrierPushforward (N*p)) where
  toFun := rawPullback N p hp hpN
  map_add' F G := by
    apply Lp.ext
    have hcomp := (forgetPrimeLevel_quasiMeasurePreserving N p hp hpN).ae_eq_comp (Lp.coeFn_add F G)
    filter_upwards [rawPullback_coe N p hp hpN (F+G), rawPullback_coe N p hp hpN F,
      rawPullback_coe N p hp hpN G, hcomp,
      Lp.coeFn_add (rawPullback N p hp hpN F) (rawPullback N p hp hpN G)] with q hsum hF hG hcomp hout
    simpa only [Function.comp_apply, Pi.add_apply] using hsum.trans (hcomp.trans (by rw [hout,hF,hG]))
  map_smul' c F := by
    apply Lp.ext
    have hcomp := (forgetPrimeLevel_quasiMeasurePreserving N p hp hpN).ae_eq_comp (Lp.coeFn_smul c F)
    filter_upwards [rawPullback_coe N p hp hpN (c • F), rawPullback_coe N p hp hpN F,
      hcomp, Lp.coeFn_smul c (rawPullback N p hp hpN F)] with q hin hF hcomp hout
    simpa only [Function.comp_apply, Pi.smul_apply] using hin.trans (hcomp.trans (by rw [hout,hF]))

/-- Canonical native L2 isometric pullback, normalized by exactly
1/sqrt(p+1); no automorphic spectral measure is involved. -/
def normalizedPullback : Lp ℂ 2 (carrierPushforward N) →ₗᵢ[ℂ] Lp ℂ 2 (carrierPushforward (N*p)) where
  toLinearMap := (Real.sqrt (p+1 : ℝ) : ℂ)⁻¹ • rawPullbackLinear N p hp hpN
  norm_map' F := by
    change ‖(Real.sqrt (p+1 : ℝ) : ℂ)⁻¹ • rawPullback N p hp hpN F‖ = ‖F‖
    have hs : 0 < Real.sqrt (p+1 : ℝ) := Real.sqrt_pos.mpr (by positivity)
    rw [norm_smul, rawPullback_norm N p hp hpN, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs]
    field_simp [hs.ne'] <;> ring

end
end ImbalancedChen.Part3.ActualHeckeForgetL220261026b
