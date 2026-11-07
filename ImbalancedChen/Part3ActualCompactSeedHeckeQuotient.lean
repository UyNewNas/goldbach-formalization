import ImbalancedChen.Part3ActualBoundedPhysicalHecke
import ImbalancedChen.Part3ActualCompactSeedHeckeReindex
import ImbalancedChen.Part3GlobalFrickeHilbertInvolution

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The actual bounded physical Hecke operator acts on the ORIGINAL quotient
compact-seed Poincare vector as the Poincare vector of the genuine dual
seed. Section-defined quotient series are joined to their already-proved
full invariant trace quotient. Measurable Hecke AE congruence is derived
from the actual squared-mass estimate at original AE-zero differences;
it is not a branchwise null-set preservation assumption. The original
compact locally-finite right reindex supplies the pointwise trace identity.
No Poincare-Hecke equality or native-domain conclusion is assumed.
-/

namespace ImbalancedChen.Part3.ActualCompactSeedHeckeQuotient20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane BigOperators
open ActualBoundedPhysicalHecke20261026b ActualPhysicalHeckeL220261026b
open ActualPrimeHeckeQuotientDescent20261026b ActualCompactSeedHeckeReindex20261026b
open Gamma0QuotientCellPushforward20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open Gamma0CompactSeedQuotientL2Budget20261025a GlobalFrickeHilbertInvolution20261026b
open ActualPoincareSpectralCoefficient20261026a

variable (N p : ℕ) [NeZero N] [NeZero (N*p)]
  (hN : 0 < N) (hp : p.Prime) (hpN : ¬ p ∣ N)

theorem quotientHecke_sub (U V : Gamma0OrbitSpace N → ℂ) :
    quotientHecke N p hp hpN (U-V) = quotientHecke N p hp hpN U - quotientHecke N p hp hpN V := by
  funext q
  refine Quotient.inductionOn q (fun z => ?_)
  letI : NeZero p := ⟨hp.ne_zero⟩
  change nativeHecke p hp.pos (testLift N (U-V)) z =
    nativeHecke p hp.pos (testLift N U) z-nativeHecke p hp.pos (testLift N V) z
  simp [nativeHecke,testLift,Finset.sum_sub_distrib,mul_sub]

/-- Actual AE well-definedness for the physical descended finite trace,
derived from its proved canonical mass estimate, without any branch AE map. -/
theorem quotientHecke_congr_ae (U V : Gamma0OrbitSpace N → ℂ)
    (hU : Measurable U) (hV : Measurable V) (heq : U =ᵐ[carrierPushforward N] V) :
    quotientHecke N p hp hpN U =ᵐ[carrierPushforward N] quotientHecke N p hp hpN V := by
  have hmass : (∫⁻ q, ENNReal.ofReal (‖(U-V) q‖^2) ∂carrierPushforward N)=0 := by
    calc
      _ = ∫⁻ q, (0 : ℝ≥0∞) ∂carrierPushforward N := by
        apply lintegral_congr_ae
        filter_upwards [heq] with q hq
        simp [hq]
      _ = 0 := by simp
  have hbound := quotientHecke_sq_mass_le N p hN hp hpN (U-V) (hU.sub hV)
  have hTmass : (∫⁻ q, ENNReal.ofReal (‖quotientHecke N p hp hpN (U-V) q‖^2)
      ∂carrierPushforward N)=0 := by
    apply le_antisymm
    · simpa only [hmass,mul_zero] using hbound
    · exact bot_le
  have hTm := quotientHecke_measurable N p hp hpN (U-V) (hU.sub hV)
  have hzero := (lintegral_eq_zero_iff (hTm.norm.pow_const 2).ennreal_ofReal).mp hTmass
  filter_upwards [hzero] with q hq
  have hsq : ‖quotientHecke N p hp hpN (U-V) q‖^2 ≤ 0 := ENNReal.ofReal_eq_zero.mp hq
  have hn : ‖quotientHecke N p hp hpN (U-V) q‖=0 := by
    nlinarith [norm_nonneg (quotientHecke N p hp hpN (U-V) q)]
  have hz := norm_eq_zero.mp hn
  rw [quotientHecke_sub N p hp hpN] at hz
  exact sub_eq_zero.mp hz

/-- Correct pointwise quotient identity through the full invariant trace,
with original compact support paying the genuine right-index reindex. -/
theorem quotientHecke_originalTrace (f : ℍ → ℂ) {K : Set ℍ} (hK : IsCompact K)
    (hs : Function.support f ⊆ K) :
    quotientHecke N p hp hpN (originalTraceQuotient N f) =
      originalTraceQuotient N (dualHeckeSeed p hp f) := by
  funext q
  refine Quotient.inductionOn q (fun z => ?_)
  change nativeHecke p hp.pos (complexSeedTrace N f) z =
    complexSeedTrace N (dualHeckeSeed p hp f) z
  exact compact_seed_trace_Hecke N p hp hpN f hK hs z

/-- The actual bounded original physical Hecke acts on the ORIGINAL
compact-seed Poincare L2 vector with the actual transformed seed.
The only AE representative premise names the original INPUT vector. -/
theorem physicalHecke_original_compact_seed (f : ℍ → ℂ) (hf : Continuous f)
    {K : Set ℍ} (hK : IsCompact K) (hs : Function.support f ⊆ K)
    (F : Lp ℂ 2 (carrierPushforward N))
    (hF : (F : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N] complexPoincare N f) :
    (physicalHeckeOperator N p hN hp hpN F : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N (dualHeckeSeed p hp f) := by
  have hfull := hF.trans (complexPoincare_ae_originalTraceQuotient N f)
  have hmeas : Measurable (originalTraceQuotient N f) :=
    measurable_from_quotient.mpr (compactSeedTrace_continuous N f hf hK hs).measurable
  have hcongr := quotientHecke_congr_ae N p hN hp hpN F (originalTraceQuotient N f)
    F.stronglyMeasurable.measurable hmeas hfull
  have htrace := (physicalHeckeOperator_coe N p hN hp hpN F).trans hcongr
  rw [quotientHecke_originalTrace N p hp hpN f hK hs] at htrace
  exact htrace.trans (complexPoincare_ae_originalTraceQuotient N (dualHeckeSeed p hp f)).symm

end
end ImbalancedChen.Part3.ActualCompactSeedHeckeQuotient20261026b
