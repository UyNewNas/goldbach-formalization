import ImbalancedChen.Part3ActualKLInversionBounds
import ImbalancedChen.Part3ComplexOrderKHolomorphic

/-!
Absolute convergence and continuity of the literal normalized KL inversion
integral for actual compact smooth radial tests. The majorant is built from
the actual third Hamiltonian transfer and actual contour bound. Its spatial
dependence is locally uniform. No Plancherel, almost-everywhere inversion,
pointwise inversion, or continuity hypothesis is supplied by the caller.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualKLInversionContinuity20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open RadialSchrodingerL2Form20261025a ComplexOrderKBridgeSourceOnly
open ComplexOrderKRadialRegularitySourceOnly ComplexOrderKHolomorphicSourceOnly
open ActualKLCompactTestIntegrationByParts20261025a ActualKLCompactTestWeightedL220261025a
open ActualKLInversionBounds20261025a

def inversionMajorant (T : RadialTest) (a tau : ℝ) : ℝ :=
  if tau ≤ 1 then
    normalization * Real.exp Real.pi * contourBudget T a * physicalKernelBudget a
  else
    (normalization * contourBudget (hamiltonianIterate 2 (hamiltonianTest T)) a *
      physicalKernelBudget a) * (tau ^ 3)⁻¹

private theorem inverse_third_integrable :
    IntegrableOn (fun tau : ℝ => (tau ^ 3)⁻¹) (Ioi (1 : ℝ)) := by
  have h := integrableOn_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num)
    (by norm_num : (0 : ℝ) < 1)
  simpa only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast] using h

theorem inversionMajorant_integrable (T : RadialTest) (a : ℝ) :
    IntegrableOn (inversionMajorant T a) (Ioi (0 : ℝ)) := by
  have hl : IntegrableOn (inversionMajorant T a) (Ioc (0 : ℝ) 1) := by
    have hc : IntegrableOn (fun _ : ℝ =>
        normalization * Real.exp Real.pi * contourBudget T a * physicalKernelBudget a)
        (Ioc (0 : ℝ) 1) :=
      continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    apply hc.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with tau htau
    simp only [inversionMajorant, if_pos htau.2]
  have hh : IntegrableOn (inversionMajorant T a) (Ioi (1 : ℝ)) := by
    have hc := inverse_third_integrable.const_mul
      (normalization * contourBudget (hamiltonianIterate 2 (hamiltonianTest T)) a *
        physicalKernelBudget a)
    apply hc.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with tau htau
    simp only [inversionMajorant, if_neg (not_le.mpr htau)]
  have hset : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi (0 : ℝ) := by
    ext tau
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      rcases le_or_gt tau 1 with ht | ht
      · exact Or.inl ⟨h, ht⟩
      · exact Or.inr ht
  simpa only [hset] using hl.union hh

theorem actualKLInversionIntegrand_norm_le_majorant (T : RadialTest) {a : ℝ}
    (ha : 0 < a) (hsupport : ∀ r ∈ tsupport T.function, a ≤ Real.exp r)
    {r tau : ℝ} (hr : a ≤ Real.exp r) (htau : 0 < tau) :
    ‖actualKLInversionIntegrand T r tau‖ ≤ inversionMajorant T a tau := by
  by_cases ht : tau ≤ 1
  · rw [inversionMajorant, if_pos ht]
    exact actualKLInversionIntegrand_low_bound T ha hsupport hr htau.le ht
  · rw [inversionMajorant, if_neg ht]
    exact actualKLInversionIntegrand_high_bound T ha hsupport hr (le_of_not_ge ht)

theorem actualKLInversionIntegrand_stronglyMeasurable (T : RadialTest) (r : ℝ) :
    StronglyMeasurable (actualKLInversionIntegrand T r) := by
  have hw : Continuous (fun tau : ℝ => (actualKLWeight tau : ℂ)) := by
    unfold actualKLWeight normalization
    fun_prop
  have hk : Continuous (fun tau : ℝ => radialK ((tau : ℂ) * Complex.I) r) := by
    apply continuous_iff_continuousAt.mpr
    intro tau
    have h := complexOrderK_hasDerivAt ((tau : ℂ) * Complex.I) (Real.exp r)
      (Real.exp_pos r) (by simp; norm_num)
    exact h.continuousAt.comp (by fun_prop)
  exact (hw.stronglyMeasurable.mul (actualKtransform_stronglyMeasurable T)).mul
    hk.stronglyMeasurable

/-- Absolute convergence of the actual normalized inversion integral at
every radial point. Only the compact smooth test is an input. -/
theorem actualKLInversionIntegrand_integrable (T : RadialTest) (r : ℝ) :
    IntegrableOn (actualKLInversionIntegrand T r) (Ioi (0 : ℝ)) := by
  obtain ⟨a0, ha0, hs0⟩ := exists_positive_physical_lower T
  let a : ℝ := min a0 (Real.exp r)
  have ha : 0 < a := lt_min ha0 (Real.exp_pos r)
  have hs : ∀ t ∈ tsupport T.function, a ≤ Real.exp t :=
    fun t ht => (min_le_left _ _).trans (hs0 t ht)
  apply (inversionMajorant_integrable T a).mono'
    (actualKLInversionIntegrand_stronglyMeasurable T r).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with tau htau
  exact actualKLInversionIntegrand_norm_le_majorant T ha hs (min_le_right _ _) htau

def actualKLInverse (T : RadialTest) (r : ℝ) : ℂ :=
  ∫ tau in Ioi (0 : ℝ), actualKLInversionIntegrand T r tau

/-- Continuity of the genuine integral, proved before any a.e. or pointwise
inversion statement. This is what permits an eventual a.e.-to-pointwise upgrade. -/
theorem actualKLInverse_continuous (T : RadialTest) : Continuous (actualKLInverse T) := by
  apply continuous_iff_continuousAt.mpr
  intro r0
  obtain ⟨a0, ha0, hs0⟩ := exists_positive_physical_lower T
  let a : ℝ := min a0 (Real.exp (r0 - 1))
  have ha : 0 < a := lt_min ha0 (Real.exp_pos _)
  have hs : ∀ t ∈ tsupport T.function, a ≤ Real.exp t :=
    fun t ht => (min_le_left _ _).trans (hs0 t ht)
  change Tendsto (fun r : ℝ => ∫ tau in Ioi (0 : ℝ), actualKLInversionIntegrand T r tau)
    (𝓝 r0) (𝓝 (∫ tau in Ioi (0 : ℝ), actualKLInversionIntegrand T r0 tau))
  apply tendsto_integral_filter_of_dominated_convergence (inversionMajorant T a)
  · exact Eventually.of_forall (fun r =>
      (actualKLInversionIntegrand_stronglyMeasurable T r).aestronglyMeasurable)
  · filter_upwards [Ioi_mem_nhds (show r0 - 1 < r0 by linarith)] with r hr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with tau htau
    have har : a ≤ Real.exp r := (min_le_right _ _).trans (Real.exp_le_exp.mpr hr.le)
    exact actualKLInversionIntegrand_norm_le_majorant T ha hs har htau
  · exact inversionMajorant_integrable T a
  · apply Eventually.of_forall
    intro tau
    have hc : Continuous (fun r : ℝ => actualKLInversionIntegrand T r tau) :=
      continuous_const.mul (radialK_C2 ((tau : ℂ) * Complex.I)).continuous
    exact hc.tendsto r0

end
end ImbalancedChen.Part3.ActualKLInversionContinuity20261025a
