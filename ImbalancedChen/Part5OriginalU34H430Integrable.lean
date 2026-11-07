import ImbalancedChen.Part5UpperTableLookup
import ImbalancedChen.CurrentChenSinglePrimeUpperDensity

/-!
Original single-prime U3/U4 H430 coefficient integrability. SOURCE ONLY.
The canonical upper amplitude A(s)=s*F(s)/(2 exp(gamma)) is retained.
The main level is v(t), residual v(t)-t. U3's ideal tail level is 1/2,
residual 1/2-t; its finite level below 1/2 still requires the analytic reserve.
H430 is used here; U11's separate adapter continues to use H248.
No distribution/count estimate or table-feedback soundness is asserted.
-/

namespace ImbalancedChen.Part5UpperTables.OriginalU34

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open MathlibNt.SieveTheory
open Part5OriginalUpsilon5CausalDictionary

def coordinateInterval : Set ℝ := Icc a (1 / 3)
def mainResidual (t : ℝ) : ℝ := VariableEnvelope.v t - t
def tailResidual (t : ℝ) : ℝ := 1 / 2 - t
def tailCutoff : ℝ := 57 / 224

theorem mainResidual_bounds {t : ℝ} (ht : t ∈ coordinateInterval) :
    (11 / 192 : ℝ) ≤ mainResidual t ∧ mainResidual t ≤ 1 / 2 := by
  have ht0 : 0 ≤ t := le_trans (by norm_num [a]) ht.1
  have hlo : t + (11 / 192 : ℝ) ≤ VariableEnvelope.v t := by
    rw [VariableEnvelope.v_eq_min]
    apply le_min <;> dsimp [VariableEnvelope.A, VariableEnvelope.C] <;> linarith [ht.2]
  have hhi : VariableEnvelope.v t ≤ (1 + t) / 2 := by
    rw [VariableEnvelope.v_eq_min]
    exact min_le_left _ _
  dsimp [mainResidual]
  constructor <;> linarith

theorem tailResidual_bounds {t : ℝ} (ht : t ∈ coordinateInterval) :
    (11 / 192 : ℝ) ≤ tailResidual t ∧ tailResidual t ≤ 1 / 2 := by
  have ht0 : 0 ≤ t := le_trans (by norm_num [a]) ht.1
  dsimp [tailResidual]
  constructor <;> linarith [ht.2]

theorem continuous_mainResidual : Continuous mainResidual :=
  VariableEnvelope.continuous_v.sub continuous_id

theorem continuous_tailResidual : Continuous tailResidual := continuous_const.sub continuous_id

def upperAmplitude (s : ℝ) : ℝ :=
  s * suzukiContinuousUpperFactor s / (2 * Real.exp Real.eulerMascheroniConstant)

theorem continuousOn_upperAmplitude : ContinuousOn upperAmplitude (Icc (2 : ℝ) 6) := by
  exact (continuousOn_id.mul (continuousOn_currentChen_upperFactor.mono
    (fun _ hs => by linarith [hs.1]))).div_const _

def rootArgument (r : ℝ → ℝ) (t : ℝ) : ℝ := max 2 (r t / a)
def branchWeight (r : ℝ → ℝ) (t : ℝ) : ℝ := 4 / (r t * t)

def branchCoefficient (nums : Fin 200 → ℤ) (r : ℝ → ℝ) (t : ℝ) : ℝ :=
  (upperAmplitude (rootArgument r t) - upperRoot nums (r t / a)) * branchWeight r t

section Branch

variable {r : ℝ → ℝ} (hr : Continuous r)
  (hR : ∀ t ∈ coordinateInterval, (11 / 192 : ℝ) ≤ r t ∧ r t ≤ 1 / 2)

theorem branch_denominator_pos {t : ℝ} (ht : t ∈ coordinateInterval) :
    0 < r t ∧ 0 < t := by
  exact ⟨lt_of_lt_of_le (by norm_num) (hR t ht).1,
    lt_of_lt_of_le (by norm_num [a]) ht.1⟩

theorem rootArgument_mem {t : ℝ} (ht : t ∈ coordinateInterval) :
    rootArgument r t ∈ Icc (2 : ℝ) 6 := by
  have ha : 0 < a := by norm_num [a]
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  apply (div_le_iff₀ ha).mpr
  have hh := (hR t ht).2
  dsimp [a]
  linarith

theorem continuousOn_branchWeight : ContinuousOn (branchWeight r) coordinateInterval := by
  apply continuousOn_const.div (hr.continuousOn.mul continuousOn_id)
  intro t ht
  obtain ⟨hrp, htp⟩ := branch_denominator_pos hR ht
  exact mul_ne_zero hrp.ne' htp.ne'

theorem integrableOn_branchWeight : IntegrableOn (branchWeight r) coordinateInterval :=
  (continuousOn_branchWeight hr hR).integrableOn_compact isCompact_Icc

theorem continuousOn_branchOrdinary :
    ContinuousOn (fun t => upperAmplitude (rootArgument r t) * branchWeight r t)
      coordinateInterval := by
  have hp : Continuous (rootArgument r) := continuous_const.max (hr.div_const a)
  exact (continuousOn_upperAmplitude.comp hp.continuousOn
    (fun t ht => rootArgument_mem hR ht)).mul (continuousOn_branchWeight hr hR)

/-- The actual finite table is measurable; no continuity premise on it is needed. -/
theorem integrableOn_branchCoefficient (nums : Fin 200 → ℤ) :
    IntegrableOn (branchCoefficient nums r) coordinateInterval := by
  have hordinary := (continuousOn_branchOrdinary hr hR).integrableOn_compact isCompact_Icc
  have hc := integrableOn_upperRoot_mul nums (hr.div_const a).measurable
    measurableSet_Icc (integrableOn_branchWeight hr hR)
  apply (hordinary.sub hc).congr_fun ?_ measurableSet_Icc
  intro t _
  dsimp [branchCoefficient]
  ring

/-- Exact finite-cell integral dictionary for one actual prime coordinate. -/
theorem branchCoefficient_integral_finite_fubini (nums : Fin 200 → ℤ) :
    (∫ t in coordinateInterval, branchCoefficient nums r t) =
      (∫ t in coordinateInterval,
        upperAmplitude (rootArgument r t) * branchWeight r t) -
      ∑ b : FloorAtom, floorAtomValue nums b *
        ∫ t in coordinateInterval ∩ rootAtom (fun t => r t / a) b, branchWeight r t := by
  have ho := (continuousOn_branchOrdinary hr hR).integrableOn_compact isCompact_Icc
  have hc := integrableOn_upperRoot_mul nums (hr.div_const a).measurable
    measurableSet_Icc (integrableOn_branchWeight hr hR)
  calc
    _ = ∫ t in coordinateInterval,
        upperAmplitude (rootArgument r t) * branchWeight r t -
          upperRoot nums (r t / a) * branchWeight r t := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t _
      dsimp [branchCoefficient]
      ring
    _ = _ := by
      rw [integral_sub ho hc, upperRoot_integral_finite_fubini nums
        (hr.div_const a).measurable measurableSet_Icc (integrableOn_branchWeight hr hR)]

end Branch

/-- Original U3 switches to the ideal half-level tail at e=57/224. -/
def U3H430Coefficient (t : ℝ) : ℝ :=
  (Iio tailCutoff).indicator (branchCoefficient H430Numerators mainResidual) t +
    (Ici tailCutoff).indicator (branchCoefficient H430Numerators tailResidual) t

/-- U4 ends before e and always retains the variable-envelope main level. -/
def U4H430Coefficient : ℝ → ℝ := branchCoefficient H430Numerators mainResidual

theorem integrableOn_U3H430Coefficient_closed :
    IntegrableOn U3H430Coefficient coordinateInterval := by
  exact ((integrableOn_branchCoefficient continuous_mainResidual
      (fun _ ht => mainResidual_bounds ht) H430Numerators).indicator measurableSet_Iio).add
    ((integrableOn_branchCoefficient continuous_tailResidual
      (fun _ ht => tailResidual_bounds ht) H430Numerators).indicator measurableSet_Ici)

theorem integrableOn_U3H430Coefficient :
    IntegrableOn U3H430Coefficient (Ico a (1 / 3 : ℝ)) :=
  integrableOn_U3H430Coefficient_closed.mono_set Ico_subset_Icc_self

theorem integrableOn_U4H430Coefficient :
    IntegrableOn U4H430Coefficient (Ico a (59 / 250 : ℝ)) := by
  apply (integrableOn_branchCoefficient continuous_mainResidual
    (fun _ ht => mainResidual_bounds ht) H430Numerators).mono_set
  intro t ht
  exact ⟨ht.1, ht.2.le.trans (by norm_num)⟩

theorem U3_eq_main_on_U4 {t : ℝ} (ht : t ∈ Ico a (59 / 250 : ℝ)) :
    U3H430Coefficient t = U4H430Coefficient t := by
  have hte : t < tailCutoff := ht.2.trans (by norm_num [tailCutoff])
  have hnot : ¬ tailCutoff ≤ t := not_le.mpr hte
  simp [U3H430Coefficient, U4H430Coefficient, hte, hnot]

end
end ImbalancedChen.Part5UpperTables.OriginalU34
