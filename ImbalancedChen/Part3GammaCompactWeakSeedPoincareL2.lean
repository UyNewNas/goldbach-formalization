import ImbalancedChen.Part3GammaCompactSeedH1EnergyTransfer

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual Poincare periodization of compact L2 seeds with genuine AE
representatives, including nonsmooth H1 seeds. Countable measure-preserving
translates supply AE Tonelli unfolding directly; no everywhere-measurable
representative, continuity, or pointwise supremum premise is needed.
-/

namespace ImbalancedChen.Part3.GammaCompactWeakSeedPoincareL220261026b
noncomputable section
open Set Function Filter MeasureTheory
open scoped UpperHalfPlane ENNReal
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0NonnegativePoincareUnfolding20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open Gamma0CompactGlobalOverlap20261025a Gamma0CompactSeedSharpL2Budget20261025a
open Gamma0ActualSmoothQuotientCore20261025a GammaCompactSeedH1EnergyTransfer20261026b

theorem lintegral_fullSeedTrace_ae (N : ℕ) [NeZero N]
    (g : UpperHalfPlane → ℝ≥0∞) (hg : AEMeasurable g (volume : Measure UpperHalfPlane)) :
    (∫⁻ z, g z) = ∫⁻ z in reducedCarrier N, fullSeedTrace N g z := by
  have hterm (q : effectiveGamma0 N) :
      AEMeasurable (fun z => g (effectiveMatrixAction N q z))
        ((volume : Measure UpperHalfPlane).restrict (reducedCarrier N)) :=
    (hg.comp_measurePreserving (effectiveMatrixAction_measurePreserving N q)).restrict
  have hdisj : Pairwise (Disjoint on effectiveCell N) := fun q r hqr => effectiveCell_disjoint N hqr
  calc
    _ = ∫⁻ z in allEffectiveCells N, g z := by
      rw [Measure.restrict_eq_self_of_ae_mem (allEffectiveCells_ae N)]
    _ = ∑' q : effectiveGamma0 N, ∫⁻ z in effectiveCell N q, g z :=
      lintegral_iUnion (effectiveCell_measurable N) hdisj g
    _ = ∑' q : effectiveGamma0 N, ∫⁻ z in reducedCarrier N,
        g (effectiveMatrixAction N q z) := by
      apply tsum_congr
      intro q
      exact lintegral_effectiveCell N q g
    _ = _ := (lintegral_tsum hterm).symm

theorem compact_seed_integrable_of_memLp (a : UpperHalfPlane → ℂ)
    (ha : MemLp a 2 volume) {K : Set UpperHalfPlane} (hK : IsCompact K)
    (hs : Function.support a ⊆ K) : Integrable a := by
  letI : IsFiniteMeasure ((volume : Measure UpperHalfPlane).restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top⟩
  have hi : IntegrableOn a K := (ha.restrict K).integrable (by norm_num)
  exact (integrableOn_iff_integrable_of_support_subset hs).mp hi

/-- Same sharp effective-overlap bound for true L2 representatives. -/
theorem compact_weak_seed_squareMass_budget (N : ℕ) [NeZero N]
    (a : UpperHalfPlane → ℂ) (ha : MemLp a 2 volume)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hs : Function.support a ⊆ K) :
    (∫⁻ q, ENNReal.ofReal (‖complexPoincare N a q‖^2) ∂carrierPushforward N) ≤
      ENNReal.ofReal (compactOverlapBound N K : ℝ) *
        ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (‖a z‖^2) := by
  have hm : AEMeasurable (seedSquareMass a) volume :=
    (ha.aestronglyMeasurable.aemeasurable.norm.pow_const 2).ennreal_ofReal
  have hterm (q : effectiveGamma0 N) :
      AEMeasurable (fun z => seedSquareMass a (effectiveMatrixAction N q z))
        ((volume : Measure UpperHalfPlane).restrict (reducedCarrier N)) :=
    (hm.comp_measurePreserving (effectiveMatrixAction_measurePreserving N q)).restrict
  rw [quotient_squareMass_eq_carrier]
  calc
    _ ≤ ∫⁻ z in reducedCarrier N, ENNReal.ofReal (compactOverlapBound N K : ℝ) *
        fullSeedTrace N (seedSquareMass a) z :=
      lintegral_mono (compactSeed_pointwise_squareMass_majorant N a hK hs)
    _ = ENNReal.ofReal (compactOverlapBound N K : ℝ) *
        ∫⁻ z in reducedCarrier N, fullSeedTrace N (seedSquareMass a) z :=
      lintegral_const_mul'' _ (AEMeasurable.tsum hterm)
    _ = _ := by rw [← lintegral_fullSeedTrace_ae N _ hm]; rfl

/-- The output L2 conclusion is derived from seed L2 and compact support,
not supplied as a norm or regularity premise. -/
theorem compact_weak_seed_Poincare_memLp (N : ℕ) [NeZero N]
    (a : UpperHalfPlane → ℂ) (ha : MemLp a 2 volume)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hs : Function.support a ⊆ K) :
    MemLp (complexPoincare N a) 2 (carrierPushforward N) := by
  have hi := compact_seed_integrable_of_memLp a ha hK hs
  have hmeas := (complexPoincare_integrable N a hi).aestronglyMeasurable
  have hseed := ha.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hnn : ∀ᵐ z ∂(volume : Measure UpperHalfPlane), 0 ≤ ‖a z‖^2 :=
    Eventually.of_forall fun _ => sq_nonneg _
  have hseedfin : (∫⁻ z : UpperHalfPlane, ENNReal.ofReal (‖a z‖^2)) < ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hseed hnn]
    exact ENNReal.ofReal_lt_top
  have hfin := (compact_weak_seed_squareMass_budget N a ha hK hs).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hseedfin)
  apply (memLp_two_iff_integrable_sq_norm hmeas).mpr
  refine ⟨hmeas.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] using hfin

def weakSeedL2 (N : ℕ) [NeZero N] (a : UpperHalfPlane → ℂ) (ha : MemLp a 2 volume)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hs : Function.support a ⊆ K) : QuotientL2 N :=
  (compact_weak_seed_Poincare_memLp N a ha hK hs).toLp (complexPoincare N a)

theorem weakSeedL2_ae (N : ℕ) [NeZero N] (a : UpperHalfPlane → ℂ) (ha : MemLp a 2 volume)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hs : Function.support a ⊆ K) :
    (weakSeedL2 N a ha K hK hs : Gamma0OrbitSpace N → ℂ) =ᵐ[carrierPushforward N]
      complexPoincare N a := (compact_weak_seed_Poincare_memLp N a ha hK hs).coeFn_toLp

theorem weakSeedL2_norm_sq_le (N : ℕ) [NeZero N]
    (a : UpperHalfPlane → ℂ) (ha : MemLp a 2 volume)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hs : Function.support a ⊆ K) :
    ‖weakSeedL2 N a ha K hK hs‖^2 ≤ (compactOverlapBound N K : ℝ) * ‖ha.toLp a‖^2 := by
  have hq := compact_weak_seed_Poincare_memLp N a ha hK hs
  have hi := ha.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hqi := hq.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hnn : ∀ᵐ z ∂(volume : Measure UpperHalfPlane), 0 ≤ ‖a z‖^2 :=
    Eventually.of_forall fun _ => sq_nonneg _
  have hqnn : ∀ᵐ q ∂carrierPushforward N, 0 ≤ ‖complexPoincare N a q‖^2 :=
    Eventually.of_forall fun _ => sq_nonneg _
  have hb := compact_weak_seed_squareMass_budget N a ha hK hs
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn,
    ← ofReal_integral_eq_lintegral_ofReal hqi hqnn] at hb
  have hr := ENNReal.toReal_mono (by simp) hb
  have hseed : (∫ z : UpperHalfPlane, ‖a z‖^2) = ‖ha.toLp a‖^2 := by
    rw [← scalar_L2_integral_sq volume (ha.toLp a)]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp] with z hz
    rw [hz]
  have hquot : (∫ q, ‖complexPoincare N a q‖^2 ∂carrierPushforward N) =
      ‖weakSeedL2 N a ha K hK hs‖^2 := by
    rw [← scalar_L2_integral_sq (carrierPushforward N) (weakSeedL2 N a ha K hK hs)]
    apply integral_congr_ae
    filter_upwards [weakSeedL2_ae N a ha K hK hs] with q hq
    rw [hq]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Nat.cast_nonneg _),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnn),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hqnn), hseed, hquot] using hr

end
end ImbalancedChen.Part3.GammaCompactWeakSeedPoincareL220261026b
