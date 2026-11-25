import ImbalancedChen.ActualExtendedThirdKernelL1Convergence

/-!
# The real functional of the actual finite robust policy

The same physical and ideal kernels are integrable on the entire original
closed ordered domain. The proof pays the small-z tail before bounding the
compact remainder; integrability is not an input to the limit theorem.

The whole-domain absolute L1 estimate then gives convergence of the actual
finite-policy real integral to the literal unbuffered manuscript functional.
The original old-cube face is handled by its proved pointwise zero value.
This is an analytic policy limit, not an arithmetic counting asymptotic or
the final hUpper estimate.
-/

namespace ImbalancedChen

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

/-- Both actual kernels have a genuine integrable full-domain extension. -/
theorem integrableOn_actualExtendedThirdWallKernel_full (physical : Bool)
    {e : ℝ} (he0 : 0 ≤ e) (he : e ≤ 1 / 384) (m : ℕ) :
    IntegrableOn (actualExtendedThirdWallKernel physical e m)
      (actualExtendedThirdClosedOrderRegion thirdPrefixRho) := by
  obtain ⟨h, hh, _hs, hb⟩ :=
    actualExtendedThirdWallClosedTailMass_uniform_small (by norm_num : (0 : ℝ) < 1)
  have htail : IntegrableOn (actualExtendedThirdWallKernel physical e m)
      (actualExtendedThirdClosedOrderRegion h) := by
    refine ⟨(measurable_actualExtendedThirdWallKernel physical e m).aestronglyMeasurable.restrict,
      (hasFiniteIntegral_iff_norm _).mpr ?_⟩
    simpa only [actualExtendedThirdWallClosedTailMass, Real.norm_eq_abs] using
      lt_of_le_of_lt (hb e he0 he m physical) ENNReal.ofReal_lt_top
  have hcompact : IntegrableOn (actualExtendedThirdWallKernel physical e m)
      (actualExtendedThirdCompactOrder h) := by
    apply Measure.integrableOn_of_bounded
      (ne_of_lt ((actualExtendedThirdCompactOrder_volume_le hh).trans_lt ENNReal.ofReal_lt_top))
      (measurable_actualExtendedThirdWallKernel physical e m).aestronglyMeasurable
    filter_upwards [ae_restrict_mem (isClosed_actualExtendedThirdCompactOrder h).measurableSet]
      with t ht
    simpa only [Real.norm_eq_abs] using actualExtendedThirdWallKernel_abs_le physical hh ht
  apply (htail.union hcompact).mono_set
  intro t ht
  by_cases hz : t 2 ≤ h
  · exact Or.inl ⟨ht.1, hz, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩
  · exact Or.inr ⟨(lt_of_not_ge hz).le, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2⟩

theorem integrableOn_actualExtendedThirdFiniteKernel_full {e : ℝ}
    (he0 : 0 ≤ e) (he : e ≤ 1 / 384) (m : ℕ) :
    IntegrableOn (actualExtendedThirdFiniteKernel e m)
      (actualExtendedThirdClosedOrderRegion thirdPrefixRho) :=
  integrableOn_actualExtendedThirdWallKernel_full true he0 he m

theorem integrableOn_actualExtendedThirdGatedKernel_full {e : ℝ}
    (he0 : 0 ≤ e) (he : e ≤ 1 / 384) :
    IntegrableOn (fun t : Fin 3 → ℝ => actualExtendedThirdGatedKernel e (t 0) (t 1) (t 2))
      (actualExtendedThirdClosedOrderRegion thirdPrefixRho) :=
  integrableOn_actualExtendedThirdWallKernel_full false he0 he 0

def actualExtendedThirdFiniteFunctional (e : ℝ) (m : ℕ) : ℝ :=
  ∫ t in actualExtendedThirdClosedOrderRegion thirdPrefixRho,
    actualExtendedThirdFiniteKernel e m t

/-- The original closed-order, closed-old-cube manuscript functional. -/
def actualExtendedThirdIdealFunctional : ℝ :=
  ∫ t in actualExtendedThirdManuscriptTailRegion 0 thirdPrefixRho,
    actualExtendedThirdOrderedKernel 0 (t 0) (t 1) (t 2)

theorem actualExtendedThirdIdealFunctional_eq_gated :
    actualExtendedThirdIdealFunctional =
      ∫ t in actualExtendedThirdClosedOrderRegion thirdPrefixRho,
        actualExtendedThirdGatedKernel 0 (t 0) (t 1) (t 2) := by
  unfold actualExtendedThirdIdealFunctional
  rw [← integral_indicator (measurableSet_actualExtendedThirdManuscriptTailRegion 0 thirdPrefixRho),
    ← integral_indicator (measurableSet_actualExtendedThirdClosedOrderRegion thirdPrefixRho)]
  exact integral_congr_ae
    (Filter.Eventually.of_forall (actualExtendedThirdManuscript_indicator 0 thirdPrefixRho))

/-- The real functional error is paid by the same absolute L1 mass. -/
theorem actualExtendedThirdFiniteFunctional_abs_sub_le {e : ℝ}
    (he0 : 0 ≤ e) (he : e ≤ 1 / 384) (m : ℕ) :
    |actualExtendedThirdFiniteFunctional e m - actualExtendedThirdIdealFunctional| ≤
      (actualExtendedThirdKernelDifferenceMassOn e m
        (actualExtendedThirdClosedOrderRegion thirdPrefixRho)).toReal := by
  rw [actualExtendedThirdIdealFunctional_eq_gated]
  unfold actualExtendedThirdFiniteFunctional
  rw [← integral_sub (integrableOn_actualExtendedThirdFiniteKernel_full he0 he m)
    (integrableOn_actualExtendedThirdGatedKernel_full (by norm_num) (by norm_num))]
  simpa only [actualExtendedThirdKernelDifferenceMassOn, Real.norm_eq_abs] using
    norm_integral_le_lintegral_norm
      (μ := volume.restrict (actualExtendedThirdClosedOrderRegion thirdPrefixRho))
      (fun t : Fin 3 → ℝ => actualExtendedThirdFiniteKernel e m t -
        actualExtendedThirdGatedKernel 0 (t 0) (t 1) (t 2))

/-- One buffer threshold and mesh threshold work for every subsequent policy.
No integrability or selector-limit premise is supplied by the caller. -/
theorem actualExtendedThirdFiniteFunctional_uniform_approx {ε : ℝ} (hε : 0 < ε) :
    ∃ e₀ : ℝ, 0 < e₀ ∧ e₀ ≤ 1 / 384 ∧ ∃ m₀ : ℕ,
      ∀ e : ℝ, 0 ≤ e → e ≤ e₀ → ∀ m : ℕ, m₀ ≤ m →
        |actualExtendedThirdFiniteFunctional e m - actualExtendedThirdIdealFunctional| ≤ ε := by
  obtain ⟨_h, _hh, _hs, e₀, he₀, he₀cap, m₀, hb⟩ :=
    actualExtendedThirdKernelDifferenceMass_uniform_small hε
  refine ⟨e₀, he₀, he₀cap, m₀, ?_⟩
  intro e he0 he m hm
  apply (actualExtendedThirdFiniteFunctional_abs_sub_le he0 (he.trans he₀cap) m).trans
  calc
    _ ≤ (ENNReal.ofReal ε).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hb e he0 he m hm)
    _ = ε := ENNReal.toReal_ofReal hε.le

end

end ImbalancedChen
