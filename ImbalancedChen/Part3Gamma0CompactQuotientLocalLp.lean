import ImbalancedChen.Part3Gamma0CompactQuotientMeasureDomination
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

Every actual quotient Lp function pulls back to Lp on each compact subset
of the upper half-plane. The measure comparison comes from the original
effective Gamma0 compact-hit bound and conull unfolding, not an assumed
local integrability condition. In particular the actual quotient L2
representative has a compact square-integral budget with the true overlap
constant. Equality of quotient representatives is preserved locally AE.
There is no assertion of global upper-half-plane L2 integrability.
-/

namespace ImbalancedChen.Part3.Gamma0CompactQuotientLocalLp20261025a

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane ENNReal
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CompactGlobalOverlap20261025a
open ImbalancedChen.Part3.Gamma0CompactQuotientMeasureDomination20261025a

/-- Actual compact pushforward Lp control, with no regularity of a
chosen quotient representative beyond its original MemLp condition. -/
theorem quotient_memLp_compact_pushforward (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    {p : ℝ≥0∞} {F : Gamma0OrbitSpace N → ℂ}
    (hF : MemLp F p (carrierPushforward N)) :
    MemLp F p (compactQuotientPushforward N K) :=
  hF.of_measure_le_smul (by simp) (compactQuotientPushforward_le N hK)

theorem quotient_memLp_pullback_compact (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    {p : ℝ≥0∞} {F : Gamma0OrbitSpace N → ℂ}
    (hF : MemLp F p (carrierPushforward N)) :
    MemLp (fun z => F (orbitProjection N z)) p
      ((volume : Measure UpperHalfPlane).restrict K) := by
  have hpush := quotient_memLp_compact_pushforward N hK hF
  exact hpush.comp_of_map (orbitProjection_measurable N).aemeasurable

theorem quotient_ae_eq_pullback_compact (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    {F G : Gamma0OrbitSpace N → ℂ}
    (hFG : F =ᵐ[carrierPushforward N] G) :
    (fun z => F (orbitProjection N z)) =ᵐ[(volume : Measure UpperHalfPlane).restrict K]
      (fun z => G (orbitProjection N z)) :=
  (orbitProjection_compact_quasiMeasurePreserving N hK).ae_eq hFG

theorem quotientLp_pullback_memLp (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {p : ℝ≥0∞}
    (f : Lp ℂ p (carrierPushforward N)) :
    MemLp (fun z => f (orbitProjection N z)) p
      ((volume : Measure UpperHalfPlane).restrict K) :=
  quotient_memLp_pullback_compact N hK f.memLp

theorem quotientLp_pullback_aestronglyMeasurable (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {p : ℝ≥0∞}
    (f : Lp ℂ p (carrierPushforward N)) :
    AEStronglyMeasurable (fun z => f (orbitProjection N z))
      ((volume : Measure UpperHalfPlane).restrict K) :=
  (quotientLp_pullback_memLp N hK f).aestronglyMeasurable

/-- Square-integral comparison for arbitrary MemLp representatives. The
AE version of the map formula avoids imposing pointwise measurability
on the canonical Lp representative. -/
theorem quotient_memLp_two_compact_lintegral_sq_le (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    {F : Gamma0OrbitSpace N → ℂ} (hF : MemLp F 2 (carrierPushforward N)) :
    (∫⁻ z in K, ENNReal.ofReal (‖F (orbitProjection N z)‖ ^ 2)) ≤
      (compactOverlapBound N K : ℝ≥0∞) *
        ∫⁻ q, ENNReal.ofReal (‖F q‖ ^ 2) ∂carrierPushforward N := by
  have hpush := quotient_memLp_compact_pushforward N hK hF
  have hsq : AEMeasurable (fun q => ENNReal.ofReal (‖F q‖ ^ 2))
      (compactQuotientPushforward N K) :=
    (hpush.aestronglyMeasurable.aemeasurable.norm.pow_const 2).ennreal_ofReal
  calc
    _ = ∫⁻ q, ENNReal.ofReal (‖F q‖ ^ 2) ∂compactQuotientPushforward N K :=
      (lintegral_map' hsq (orbitProjection_measurable N).aemeasurable).symm
    _ ≤ ∫⁻ q, ENNReal.ofReal (‖F q‖ ^ 2)
        ∂((compactOverlapBound N K : ℝ≥0∞) • carrierPushforward N) :=
      lintegral_mono_measure (compactQuotientPushforward_le N hK)
    _ = _ := by rw [lintegral_smul_measure]; rfl

theorem quotient_memLp_two_compact_integrable_sq (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    {F : Gamma0OrbitSpace N → ℂ} (hF : MemLp F 2 (carrierPushforward N)) :
    Integrable (fun z => ‖F (orbitProjection N z)‖ ^ 2)
      ((volume : Measure UpperHalfPlane).restrict K) :=
  (quotient_memLp_pullback_compact N hK hF).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)

theorem quotient_memLp_two_compact_integral_sq_le (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    {F : Gamma0OrbitSpace N → ℂ} (hF : MemLp F 2 (carrierPushforward N)) :
    (∫ z in K, ‖F (orbitProjection N z)‖ ^ 2) ≤
      (compactOverlapBound N K : ℝ) * ∫ q, ‖F q‖ ^ 2 ∂carrierPushforward N := by
  have hlocal := quotient_memLp_two_compact_integrable_sq N hK hF
  have hglobal : Integrable (fun q => ‖F q‖ ^ 2) (carrierPushforward N) :=
    hF.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hlocal_nonneg : 0 ≤ᵐ[(volume : Measure UpperHalfPlane).restrict K]
      (fun z => ‖F (orbitProjection N z)‖ ^ 2) :=
    Filter.Eventually.of_forall (fun _ => sq_nonneg _)
  have hglobal_nonneg : 0 ≤ᵐ[carrierPushforward N] (fun q => ‖F q‖ ^ 2) :=
    Filter.Eventually.of_forall (fun _ => sq_nonneg _)
  have hbound := quotient_memLp_two_compact_lintegral_sq_le N hK hF
  rw [← ofReal_integral_eq_lintegral_ofReal hlocal hlocal_nonneg,
    ← ofReal_integral_eq_lintegral_ofReal hglobal hglobal_nonneg] at hbound
  have hreal := ENNReal.toReal_mono (by simp) hbound
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hlocal_nonneg),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hglobal_nonneg)] using hreal

theorem quotientL2_compact_integral_sq_le (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (f : Lp ℂ 2 (carrierPushforward N)) :
    (∫ z in K, ‖f (orbitProjection N z)‖ ^ 2) ≤
      (compactOverlapBound N K : ℝ) * ∫ q, ‖f q‖ ^ 2 ∂carrierPushforward N :=
  quotient_memLp_two_compact_integral_sq_le N hK f.memLp

end
end ImbalancedChen.Part3.Gamma0CompactQuotientLocalLp20261025a
