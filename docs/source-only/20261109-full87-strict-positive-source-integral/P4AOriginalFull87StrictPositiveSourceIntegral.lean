import ImbalancedChen.P4AOriginalFull87QuantitativeGapIntegral
import ImbalancedChen.P4AOriginalFull87KernelPositiveWitness
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The original 87 continuous Sources contain a common positive-radius inner
box, hence positive volume.  This permits strict positivity of the SAME
original cap-gap and ideal eighth-kernel integrals.  It is not an
original saved87 numerical endpoint, an N-dependent prime occurrence,
a physical actualParent comparison, or a signed reserve payment.
-/

namespace ImbalancedChen.P4AOriginalFull87StrictPositiveSourceIntegral
noncomputable section
open scoped Classical BigOperators MeasureTheory
open Set MeasureTheory VariableEnvelope
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87FiniteEighthCap
open P4AOriginalFull87EighthKernelControl
open P4AOriginalFull87QuantitativeGapIntegral

def commonRadius : ℝ := 1 / 100000000
def sourceInnerBox (c : Cell) : Set Point :=
  {t | ∀ j : Fin 8,
    |t j - P4AOriginalFull87KernelPositiveWitness.originalCentre c j| < commonRadius}

private theorem commonRadius_pos : 0 < commonRadius := by
  norm_num [commonRadius]

private theorem sourceInnerBox_open (c : Cell) : IsOpen (sourceInnerBox c) := by
  have hj (j : Fin 8) :
      IsOpen {t : Point |
        |t j - P4AOriginalFull87KernelPositiveWitness.originalCentre c j| <
          commonRadius} := by
    exact isOpen_lt (((continuous_apply j).sub continuous_const).abs)
      continuous_const
  simpa only [sourceInnerBox, Set.setOf_forall] using
    (isOpen_iInter_of_finite (fun j : Fin 8 => hj j))

private theorem sourceInnerBox_centre (c : Cell) :
    P4AOriginalFull87KernelPositiveWitness.originalCentre c ∈
      sourceInnerBox c := by
  change ∀ j : Fin 8,
    |P4AOriginalFull87KernelPositiveWitness.originalCentre c j -
       P4AOriginalFull87KernelPositiveWitness.originalCentre c j| < commonRadius
  intro j
  simpa using commonRadius_pos

/-- Shrink all SIX existing original-family witness boxes to radius 1e-8;
the original selected mask, strictness, history and Source are unchanged. -/
theorem innerBox_mem_original_source (c : Cell) (t : Point)
    (ht : t ∈ sourceInnerBox c) : Source c t := by
  have hcoord : ∀ j : Fin 8,
      |t j - P4AOriginalFull87KernelPositiveWitness.originalCentre c j| ≤
        commonRadius := fun j => (ht j).le
  have hlarge : commonRadius ≤ (1 / 100000 : ℝ) := by
    norm_num [commonRadius]
  have hmedium : commonRadius ≤ (1 / 1000000 : ℝ) := by
    norm_num [commonRadius]
  cases c with
  | descending i =>
      exact P4AOriginalFull87DescAscPairInteriors.all15_box_mem_original_source i t (by
        intro j
        simpa [P4AOriginalFull87KernelPositiveWitness.originalCentre, commonRadius]
          using hcoord j)
  | ascendingPair i =>
      exact P4AOriginalFull87DescAscPairInteriors.all13_box_mem_original_source i t (by
        intro j
        simpa [P4AOriginalFull87KernelPositiveWitness.originalCentre, commonRadius]
          using hcoord j)
  | h3 i =>
      exact P4AOriginalFull87H3Interiors.all12_box_mem_original_source i t (by
        intro j
        simpa [P4AOriginalFull87KernelPositiveWitness.originalCentre, commonRadius]
          using hcoord j)
  | remaining d =>
      cases d with
      | ascending i =>
          exact P4AOriginalFull87AscendingAllInteriors.all14_box_mem_original_source i t (by
            intro j
            have hj := (hcoord j).trans hlarge
            simpa [P4AOriginalFull87KernelPositiveWitness.originalCentre] using hj)
      | seed =>
          have hs : Source (.remaining
              (P4AOriginalFull87SeedNineFiftyInteriors.originalCell 0)) t :=
            P4AOriginalFull87SeedNineFiftyInteriors.all16_box_mem_original_source 0 t (by
              intro j
              have hj := (hcoord j).trans hlarge
              simpa [P4AOriginalFull87KernelPositiveWitness.originalCentre] using hj)
          simpa [P4AOriginalFull87SeedNineFiftyInteriors.originalCell] using hs
      | nine i =>
          let ix : Fin 16 := ⟨i.val + 1, by omega⟩
          have hlookup :
              P4AOriginalFull87SeedNineFiftyInteriors.originalCell ix = .nine i := by
            fin_cases i <;> decide
          have hs : Source (.remaining
              (P4AOriginalFull87SeedNineFiftyInteriors.originalCell ix)) t :=
            P4AOriginalFull87SeedNineFiftyInteriors.all16_box_mem_original_source ix t (by
              intro j
              have hj := (hcoord j).trans hlarge
              simpa [P4AOriginalFull87KernelPositiveWitness.originalCentre, ix] using hj)
          simpa [hlookup] using hs
      | fiftyA =>
          have hs : Source (.remaining
              (P4AOriginalFull87SeedNineFiftyInteriors.originalCell 14)) t :=
            P4AOriginalFull87SeedNineFiftyInteriors.all16_box_mem_original_source 14 t (by
              intro j
              have hj := (hcoord j).trans hlarge
              simpa [P4AOriginalFull87KernelPositiveWitness.originalCentre] using hj)
          simpa [P4AOriginalFull87SeedNineFiftyInteriors.originalCell] using hs
      | fiftyD =>
          have hs : Source (.remaining
              (P4AOriginalFull87SeedNineFiftyInteriors.originalCell 15)) t :=
            P4AOriginalFull87SeedNineFiftyInteriors.all16_box_mem_original_source 15 t (by
              intro j
              have hj := (hcoord j).trans hlarge
              simpa [P4AOriginalFull87KernelPositiveWitness.originalCentre] using hj)
          simpa [P4AOriginalFull87SeedNineFiftyInteriors.originalCell] using hs
      | h5 i =>
          let ix : Fin 17 := ⟨i.val, by omega⟩
          have hlookup :
              P4AOriginalFull87H5H7Interiors.originalCell ix = .h5 i := by
            fin_cases i <;> decide
          have hs : Source (.remaining
              (P4AOriginalFull87H5H7Interiors.originalCell ix)) t :=
            P4AOriginalFull87H5H7Interiors.all17_box_mem_original_source ix t (by
              intro j
              have hj := (hcoord j).trans hmedium
              simpa [P4AOriginalFull87KernelPositiveWitness.originalCentre, ix] using hj)
          simpa [hlookup] using hs
      | h7 i =>
          let ix : Fin 17 := ⟨i.val + 7, by omega⟩
          have hlookup :
              P4AOriginalFull87H5H7Interiors.originalCell ix = .h7 i := by
            fin_cases i <;> decide
          have hs : Source (.remaining
              (P4AOriginalFull87H5H7Interiors.originalCell ix)) t :=
            P4AOriginalFull87H5H7Interiors.all17_box_mem_original_source ix t (by
              intro j
              have hj := (hcoord j).trans hmedium
              simpa [P4AOriginalFull87KernelPositiveWitness.originalCentre, ix] using hj)
          simpa [hlookup] using hs

/-- Strictly positive eight-dimensional volume, not point mass. -/
theorem original_source_has_positive_volume (c : Cell) :
    0 < (volume : Measure Point) (sourceSet c) := by
  have hb : 0 < (volume : Measure Point) (sourceInnerBox c) :=
    (sourceInnerBox_open c).measure_pos
      ⟨P4AOriginalFull87KernelPositiveWitness.originalCentre c,
        sourceInnerBox_centre c⟩
  have hi : sourceInnerBox c ⊆ sourceSet c := by
    intro t ht
    exact innerBox_mem_original_source c t ht
  exact hb.trans_le (measure_mono hi)

/-- Same ORIGINAL source and cap-gap. Its integral is strictly positive:
previous pointwise centre positivity alone does not imply this. -/
theorem original_cap_gap_integral_strict_pos (c : Cell) :
    0 < ∫ t in sourceSet c, (newCap c t - comparison c t) := by
  let f : Point → ℝ := fun t => newCap c t - comparison c t
  have hnonneg :
      0 ≤ᵐ[(volume : Measure Point).restrict (sourceSet c)] f := by
    filter_upwards [ae_restrict_mem (sourceSet_measurable c)] with t ht
    exact (sub_pos.mpr (source_improvement_terminal ht).1).le
  have hsupp : sourceInnerBox c ⊆ Function.support f := by
    intro t ht
    have hp :=
      (source_improvement_terminal
        (innerBox_mem_original_source c t ht)).1
    exact ne_of_gt (sub_pos.mpr hp)
  have hboxpos : 0 < (volume : Measure Point) (sourceInnerBox c) :=
    (sourceInnerBox_open c).measure_pos
      ⟨P4AOriginalFull87KernelPositiveWitness.originalCentre c,
        sourceInnerBox_centre c⟩
  have hrestrict :
      ((volume : Measure Point).restrict (sourceSet c)) (sourceInnerBox c) =
        (volume : Measure Point) (sourceInnerBox c) := by
    rw [Measure.restrict_apply (sourceInnerBox_open c).measurableSet]
    rw [Set.inter_eq_left.mpr
      (fun t ht => innerBox_mem_original_source c t ht)]
  have hsupports :
      0 < ((volume : Measure Point).restrict (sourceSet c))
        (Function.support f) := by
    calc
      0 < ((volume : Measure Point).restrict (sourceSet c))
          (sourceInnerBox c) := by rw [hrestrict]; exact hboxpos
      _ ≤ ((volume : Measure Point).restrict (sourceSet c))
          (Function.support f) := measure_mono hsupp
  exact (integral_pos_iff_support_of_nonneg_ae hnonneg
    (integrableOn_original_cap_gap c)).2 hsupports

/-- Strictly positive integral of the original IDEAL eighth residual.
No numerical endpoint or arithmetic actualParent inference is made. -/
theorem original_kernel_integral_strict_pos (c : Cell) :
    0 < ∫ t in sourceSet c, kernel c t := by
  have hmu : 0 < mu := by
    have hs :=
      P4AOriginalFull87KernelPositiveWitness.originalCentre_mem_source c
    have hlo :
        0 < P4AOriginalFull87KernelPositiveWitness.originalCentre c 0 :=
      cutoff_pos.trans (source_coordinate_lower hs 0)
    exact hlo.trans (source_basic hs).1
  have hfactor : 0 < 4 / (9 * mu ^ 10) := by positivity
  have heq :
      (∫ t in sourceSet c, scaledCapGap c t) =
        (4 / (9 * mu ^ 10)) *
          (∫ t in sourceSet c, (newCap c t - comparison c t)) := by
    simpa only [scaledCapGap] using
      (integral_const_mul
        (μ := (volume : Measure Point).restrict (sourceSet c))
        (4 / (9 * mu ^ 10))
        (fun t : Point => newCap c t - comparison c t))
  have hscaled : 0 < ∫ t in sourceSet c, scaledCapGap c t := by
    rw [heq]
    exact mul_pos hfactor (original_cap_gap_integral_strict_pos c)
  exact hscaled.trans_le (original_source_integral_scaled_gap_le_kernel c)

end
end ImbalancedChen.P4AOriginalFull87StrictPositiveSourceIntegral
