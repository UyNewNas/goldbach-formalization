import ImbalancedChen.P0P3RawHeightIntegrableAPI
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Tactic

/-!
SOURCE_WRITTEN / UNCOMPILED / 20261024z-P0. No acceptance credit.
Full raw-height Gram for actual labelled K atoms on q>0. Integrability of
every cross product is proved before the finite exchanges. This is ordinary
Lebesgue dt over R, with no spectral measure or Plancherel identification.
-/

namespace ImbalancedChen.Part3.P0P3RawHeightFullGramSourceOnly
noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)
open ActualKPacketAdapterSourceOnly
open ActualCommonHeightKGramSourceOnly
open P0P3AllHeightAPISourceOnly
open P0P3RawHeightIntegrableAPISourceOnly

variable {ι : Type*}

/-- The budget is the norm of this atom's actual frozen coefficient and test. -/
def atomBudget (P : PacketData ι) (k : D4 → ℤ) (q : ℝ) (l : RowLabel ι) : ℝ :=
  ‖spectralTest k P.Y0 q *
    ((P.completed k).weight l.2.1 *
      signedCoefficient P.negativeCusp
        (modePacket (P.packet l.1) k P.U P.Z) l.2.2)‖ * (12/q^2)

theorem atomBudget_nonneg (P : PacketData ι) (k : D4 → ℤ)
    (q : ℝ) (l : RowLabel ι) : 0 ≤ atomBudget P k q l := by
  unfold atomBudget
  positivity

/-- Every actual atom has a proved regularized all-height budget. -/
theorem modeAtom_norm_le_regularized (P : PacketData ι) (k : D4 → ℤ)
    {q : ℝ} (hq : 0 < q) (l : RowLabel ι) (t : ℝ) :
    ‖modeAtom P k q l t‖ ≤ atomBudget P k q l/(1+t^2) := by
  unfold modeAtom atomBudget
  rw [norm_mul]
  calc
    _ ≤ ‖spectralTest k P.Y0 q *
        ((P.completed k).weight l.2.1 *
          signedCoefficient P.negativeCusp
            (modePacket (P.packet l.1) k P.U P.Z) l.2.2)‖ *
          (12/(q^2*(1+t^2))) :=
      mul_le_mul_of_nonneg_left (imaginaryOrderK_div_norm_le_allHeight t hq)
        (norm_nonneg _)
    _ = _ := by
      field_simp [hq.ne', ne_of_gt (by positivity : (0 : ℝ) < 1+t^2)]
      <;> ring

theorem modeAtom_norm_le_budget (P : PacketData ι) (k : D4 → ℤ)
    {q : ℝ} (hq : 0 < q) (l : RowLabel ι) (t : ℝ) :
    ‖modeAtom P k q l t‖ ≤ atomBudget P k q l := by
  have hd : (0 : ℝ) < 1+t^2 := by positivity
  have hr : (1+t^2)⁻¹ ≤ 1 := (inv_le_one₀ hd).mpr (by nlinarith [sq_nonneg t])
  calc
    ‖modeAtom P k q l t‖ ≤ atomBudget P k q l * (1+t^2)⁻¹ := by
      simpa only [div_eq_mul_inv] using modeAtom_norm_le_regularized P k hq l t
    _ ≤ atomBudget P k q l * 1 :=
      mul_le_mul_of_nonneg_left hr (atomBudget_nonneg P k q l)
    _ = _ := mul_one _

/-- Global raw-height atom integrability, derived from actual continuity. -/
theorem modeAtom_integrable (P : PacketData ι) (k : D4 → ℤ)
    {q : ℝ} (hq : 0 < q) (l : RowLabel ι) : Integrable (modeAtom P k q l) := by
  exact (raw_height_integrability_budget (modeAtom_continuous P k hq l)
    (atomBudget_nonneg P k q l) (modeAtom_norm_le_regularized P k hq l)).1

/-- Every diagonal and off-diagonal product is globally integrable. -/
theorem gramAtom_integrable (P : PacketData ι) (k : D4 → ℤ)
    {q : ℝ} (hq : 0 < q) (a b : RowLabel ι) :
    Integrable (fun t : ℝ => modeAtom P k q a t * star (modeAtom P k q b t)) := by
  exact (modeAtom_integrable P k hq a).mul_bdd
    (modeAtom_continuous P k hq b).star.aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      simpa only [norm_star] using modeAtom_norm_le_budget P k hq b t))

/-- Every original label and finite copy contributes to this real budget. -/
def rowBudget (P : PacketData ι) (k : D4 → ℤ) (q : ℝ) : ℝ :=
  ∑ l ∈ labelCarrier P, atomBudget P k q l

theorem rowBudget_nonneg (P : PacketData ι) (k : D4 → ℤ) (q : ℝ) :
    0 ≤ rowBudget P k q := by
  exact Finset.sum_nonneg (fun l _hl => atomBudget_nonneg P k q l)

theorem modeRow_norm_le_regularized (P : PacketData ι) (k : D4 → ℤ)
    {q : ℝ} (hq : 0 < q) (t : ℝ) :
    ‖modeRow P k q t‖ ≤ rowBudget P k q/(1+t^2) := by
  calc
    ‖modeRow P k q t‖ ≤ ∑ l ∈ labelCarrier P, ‖modeAtom P k q l t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ l ∈ labelCarrier P, atomBudget P k q l/(1+t^2) :=
      Finset.sum_le_sum (fun l _hl => modeAtom_norm_le_regularized P k hq l t)
    _ = rowBudget P k q/(1+t^2) := by rw [rowBudget, Finset.sum_div]

/-- The actual complete row and its literal energy are globally integrable. -/
theorem modeRow_raw_height_integrability (P : PacketData ι) (k : D4 → ℤ)
    {q : ℝ} (hq : 0 < q) :
    Integrable (modeRow P k q) ∧ Integrable (fun t : ℝ => ‖modeRow P k q t‖^2) ∧
      (∫ t : ℝ, ‖modeRow P k q t‖) ≤ rowBudget P k q*Real.pi ∧
      (∫ t : ℝ, ‖modeRow P k q t‖^2) ≤ (rowBudget P k q)^2*Real.pi := by
  exact raw_height_integrability_budget (modeRow_continuous P k hq)
    (rowBudget_nonneg P k q) (modeRow_norm_le_regularized P k hq)

/-- Whole-R raw Gram identity. All original labelled pairs are retained. -/
theorem actual_raw_height_full_gram (P : PacketData ι) (k : D4 → ℤ)
    {q : ℝ} (hq : 0 < q) :
    ((∫ t : ℝ, ‖modeRow P k q t‖^2) : ℂ) =
      ∑ a ∈ labelCarrier P, ∑ b ∈ labelCarrier P,
        ∫ t : ℝ, modeAtom P k q a t * star (modeAtom P k q b t) := by
  have hinner (a : RowLabel ι) :
      Integrable (fun t : ℝ => ∑ b ∈ labelCarrier P,
        modeAtom P k q a t * star (modeAtom P k q b t)) :=
    integrable_finsetSum (labelCarrier P)
      (fun b _hb => gramAtom_integrable P k hq a b)
  calc
    ((∫ t : ℝ, ‖modeRow P k q t‖^2) : ℂ) =
        ∫ t : ℝ, (‖modeRow P k q t‖^2 : ℂ) := by
      refine (integral_complex_ofReal (f := fun t : ℝ => ‖modeRow P k q t‖^2)
        (μ := (volume : Measure ℝ))).symm.trans ?_
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => Complex.ofReal_pow _ _)
    _ = ∫ t : ℝ, ∑ a ∈ labelCarrier P, ∑ b ∈ labelCarrier P,
        modeAtom P k q a t * star (modeAtom P k q b t) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => modeRow_full_gram P k q t)
    _ = ∑ a ∈ labelCarrier P, ∫ t : ℝ, ∑ b ∈ labelCarrier P,
        modeAtom P k q a t * star (modeAtom P k q b t) :=
      integral_finsetSum (labelCarrier P) (fun a _ha => hinner a)
    _ = ∑ a ∈ labelCarrier P, ∑ b ∈ labelCarrier P,
        ∫ t : ℝ, modeAtom P k q a t * star (modeAtom P k q b t) := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact integral_finsetSum (labelCarrier P)
        (fun b _hb => gramAtom_integrable P k hq a b)

/-- Physical packet support discharges the positive-q guard for consumers. -/
theorem actual_region_raw_height_full_gram (P : PacketData ι) (k : D4 → ℤ)
    (q : ℝ) (hq : q ∈ P.region) :
    Integrable (fun t : ℝ => ‖modeRow P k q t‖^2) ∧
      0 ≤ (∫ t : ℝ, ‖modeRow P k q t‖^2) ∧
      ((∫ t : ℝ, ‖modeRow P k q t‖^2) : ℂ) =
        ∑ a ∈ labelCarrier P, ∑ b ∈ labelCarrier P,
          ∫ t : ℝ, modeAtom P k q a t * star (modeAtom P k q b t) := by
  have hqp : 0 < q := by
    have hl : P.Y0/16 ≤ q := hq.1
    linarith [P.Y0_pos]
  exact ⟨(modeRow_raw_height_integrability P k hqp).2.1,
    integral_nonneg (fun t => sq_nonneg _), actual_raw_height_full_gram P k hqp⟩

end
end ImbalancedChen.Part3.P0P3RawHeightFullGramSourceOnly
