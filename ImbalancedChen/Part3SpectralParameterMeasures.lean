import ImbalancedChen.Part3ZExceptionalParameter
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY, 2026-10-24.

A real-parameter measure split, with no automorphic measure supplier.
Regular eigenvalue parameters satisfy lambda >= 1/4; exceptional parameters
satisfy 0 <= lambda < 1/4. Their restrictions split any measure on lambda >= 0.
The imported actual real function is tau(lambda)=2*sqrt(max(1/4-lambda,0)).
Its exceptional pushforward is a.e. concentrated in (0,1]. This is a measure
concentration statement, not a claim that topological support excludes 0.
The 7/32 cap is conditional on lambda >= 975/4096 or built into a restriction.
No spectral gap, spectral identity, Kuznetsov or Plancherel theorem is claimed.
-/

namespace ImbalancedChen.Part3.SpectralParameterMeasures20261024z
noncomputable section

open Set MeasureTheory Filter
open ImbalancedChen.P3ZExceptionalParameter

def regularParameters : Set ℝ := Ici ((1 : ℝ) / 4)

def exceptionalParameters : Set ℝ := Ico (0 : ℝ) ((1 : ℝ) / 4)

theorem regularParameters_measurable : MeasurableSet regularParameters := by
  exact measurableSet_Ici

theorem exceptionalParameters_measurable : MeasurableSet exceptionalParameters := by
  exact measurableSet_Ico

theorem regularParameters_disjoint_exceptional :
    Disjoint regularParameters exceptionalParameters := by
  apply Set.disjoint_left.mpr
  intro lambda hr he
  exact (not_lt_of_ge hr) he.2

theorem regularParameters_union_exceptional :
    regularParameters ∪ exceptionalParameters = Ici (0 : ℝ) := by
  ext lambda
  change ((1 : ℝ) / 4 ≤ lambda ∨ (0 ≤ lambda ∧ lambda < 1 / 4)) ↔ 0 ≤ lambda
  constructor
  · rintro (hr | he)
    · linarith
    · exact he.1
  · intro hnonneg
    by_cases hr : (1 : ℝ) / 4 ≤ lambda
    · exact Or.inl hr
    · exact Or.inr ⟨hnonneg, lt_of_not_ge hr⟩

def nonnegativeParameterMeasure (mu : Measure ℝ) : Measure ℝ :=
  mu.restrict (Ici (0 : ℝ))

def regularParameterMeasure (mu : Measure ℝ) : Measure ℝ :=
  mu.restrict regularParameters

def exceptionalParameterMeasure (mu : Measure ℝ) : Measure ℝ :=
  mu.restrict exceptionalParameters

/-- Literal restriction equality for an arbitrary measure on real lambda. -/
theorem nonnegativeParameterMeasure_split (mu : Measure ℝ) :
    nonnegativeParameterMeasure mu =
      regularParameterMeasure mu + exceptionalParameterMeasure mu := by
  unfold nonnegativeParameterMeasure regularParameterMeasure exceptionalParameterMeasure
  rw [← regularParameters_union_exceptional]
  exact Measure.restrict_union regularParameters_disjoint_exceptional
    exceptionalParameters_measurable

/-- The domain integrability hypothesis supplies integrability on both pieces. -/
theorem integral_nonnegative_split (mu : Measure ℝ) (f : ℝ → ℝ)
    (hf : IntegrableOn f (Ici (0 : ℝ)) mu) :
    (∫ lambda in Ici (0 : ℝ), f lambda ∂mu) =
      (∫ lambda in regularParameters, f lambda ∂mu) +
        ∫ lambda in exceptionalParameters, f lambda ∂mu := by
  change Integrable f (nonnegativeParameterMeasure mu) at hf
  rw [nonnegativeParameterMeasure_split] at hf
  change (∫ lambda, f lambda ∂nonnegativeParameterMeasure mu) =
    (∫ lambda, f lambda ∂regularParameterMeasure mu) +
      ∫ lambda, f lambda ∂exceptionalParameterMeasure mu
  rw [nonnegativeParameterMeasure_split]
  exact integral_add_measure hf.left_of_add_measure hf.right_of_add_measure

/-- A true norm-square quadratic-form split; no coefficient normalization is assumed. -/
theorem norm_sq_integral_nonnegative_split (mu : Measure ℝ) (F : ℝ → ℂ)
    (hF : IntegrableOn (fun lambda => ‖F lambda‖ ^ 2) (Ici (0 : ℝ)) mu) :
    (∫ lambda in Ici (0 : ℝ), ‖F lambda‖ ^ 2 ∂mu) =
      (∫ lambda in regularParameters, ‖F lambda‖ ^ 2 ∂mu) +
        ∫ lambda in exceptionalParameters, ‖F lambda‖ ^ 2 ∂mu := by
  exact integral_nonnegative_split mu (fun lambda => ‖F lambda‖ ^ 2) hF

theorem tau_measurable : Measurable tau := by
  exact continuous_tau.measurable

/-- The imported parameter convention, recorded without a new normalization. -/
theorem tau_eq_doubled_sqrt (lambda : ℝ) :
    tau lambda = 2 * Real.sqrt (max ((1 : ℝ) / 4 - lambda) 0) := by
  rfl

/-- Genuine pushforward of the exceptional restriction of any real measure. -/
def exceptionalTauMeasure (mu : Measure ℝ) : Measure ℝ :=
  (exceptionalParameterMeasure mu).map tau

theorem exceptionalTauMeasure_ae_mem_Ioc (mu : Measure ℝ) :
    ∀ᵐ t ∂exceptionalTauMeasure mu, t ∈ Ioc (0 : ℝ) 1 := by
  unfold exceptionalTauMeasure
  apply (ae_map_iff tau_measurable.aemeasurable
    (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) 1))).mpr
  have hmem : ∀ᵐ lambda ∂exceptionalParameterMeasure mu,
      lambda ∈ exceptionalParameters :=
    ae_restrict_mem exceptionalParameters_measurable
  filter_upwards [hmem] with lambda hlambda
  exact ⟨tau_pos_of_exceptional hlambda.2, tau_le_one hlambda.1⟩

/-- Precise measure support statement: the complement has zero mass. -/
theorem exceptionalTauMeasure_compl_Ioc_eq_zero (mu : Measure ℝ) :
    exceptionalTauMeasure mu ((Ioc (0 : ℝ) 1)ᶜ) = 0 := by
  exact (ae_iff).mp (exceptionalTauMeasure_ae_mem_Ioc mu)

/-- Any actually supplied a.e. lambda bound transports through the pushforward. -/
theorem exceptionalTauMeasure_ae_le_seven_thirtyseconds (mu : Measure ℝ)
    (hlower : ∀ᵐ lambda ∂exceptionalParameterMeasure mu,
      (975 : ℝ) / 4096 ≤ lambda) :
    ∀ᵐ t ∂exceptionalTauMeasure mu, t ≤ (7 : ℝ) / 32 := by
  unfold exceptionalTauMeasure
  apply (ae_map_iff tau_measurable.aemeasurable
    (measurableSet_Iic : MeasurableSet (Iic ((7 : ℝ) / 32)))).mpr
  exact hlower.mono (fun _ h => tau_le_seven_thirtyseconds h)

theorem exceptionalTauMeasure_ae_mem_Ioc_cap (mu : Measure ℝ)
    (hlower : ∀ᵐ lambda ∂exceptionalParameterMeasure mu,
      (975 : ℝ) / 4096 ≤ lambda) :
    ∀ᵐ t ∂exceptionalTauMeasure mu, t ∈ Ioc (0 : ℝ) ((7 : ℝ) / 32) := by
  filter_upwards [exceptionalTauMeasure_ae_mem_Ioc mu,
    exceptionalTauMeasure_ae_le_seven_thirtyseconds mu hlower] with t ht hcap
  exact ⟨ht.1, hcap⟩

/-- Alternatively the threshold can be enforced by an actual measure restriction. -/
def thresholdExceptionalTauMeasure (mu : Measure ℝ) : Measure ℝ :=
  (mu.restrict (Ico ((975 : ℝ) / 4096) ((1 : ℝ) / 4))).map tau

theorem thresholdExceptionalTauMeasure_ae_mem_Ioc (mu : Measure ℝ) :
    ∀ᵐ t ∂thresholdExceptionalTauMeasure mu,
      t ∈ Ioc (0 : ℝ) ((7 : ℝ) / 32) := by
  unfold thresholdExceptionalTauMeasure
  apply (ae_map_iff tau_measurable.aemeasurable
    (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) ((7 : ℝ) / 32)))).mpr
  filter_upwards [ae_restrict_mem
    (measurableSet_Ico : MeasurableSet
      (Ico ((975 : ℝ) / 4096) ((1 : ℝ) / 4)))] with lambda hlambda
  exact ⟨tau_pos_of_exceptional hlambda.2, tau_le_seven_thirtyseconds hlambda.1⟩

end
end ImbalancedChen.Part3.SpectralParameterMeasures20261024z

