import ImbalancedChen.P4AOriginalFull87Other40BoxGapLower
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Quantitative transfer of the EXISTING 87 original source inner-box pointwise
eighth-residual lower bound to an integral on the SAME original Source.
The box is not a substituted geometric Source: it was already proved to
lie in the original Source for each genuine Cell constructor. Its exact
volume is computed using the fixed mathlib real product-Lebesgue measure,
rather than a point-mass or a zero-measure-boundary argument.

This very small uniform lower is NOT the selected saved87 archive endpoint,
the N-dependent prime sum, a signed parent gain or a reserve payment.
-/

namespace ImbalancedChen.P4AOriginalFull87BoxVolumeIntegral
noncomputable section

open scoped Classical BigOperators MeasureTheory
open Set MeasureTheory VariableEnvelope
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87EighthKernelControl
open P4AOriginalFull87QuantitativeGapIntegral
open P4AOriginalFull87StrictPositiveSourceIntegral
open P4AOriginalFull87Other40BoxGapLower

private def boxLo (c : Cell) (j : Fin 8) : ℝ :=
  P4AOriginalFull87KernelPositiveWitness.originalCentre c j - commonRadius

private def boxHi (c : Cell) (j : Fin 8) : ℝ :=
  P4AOriginalFull87KernelPositiveWitness.originalCentre c j + commonRadius

/-- The already-certified inner box is an honest product of eight open
real intervals, with no replacement by a discrete state list. -/
private theorem original_inner_box_eq_pi_Ioo (c : Cell) :
    sourceInnerBox c =
      Set.pi Set.univ (fun j : Fin 8 => Set.Ioo (boxLo c j) (boxHi c j)) := by
  ext t
  simp only [sourceInnerBox, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
    forall_true_left, Set.mem_Ioo, boxLo, boxHi, abs_lt]
  constructor
  · intro ht j
    obtain ⟨hl, hr⟩ := ht j
    constructor <;> linarith
  · intro ht j
    obtain ⟨hl, hr⟩ := ht j
    constructor <;> linarith

/-- Actual eight-dimensional volume of each old inner box: the
Lebesgue measure, rather than a synthetic weight or a point witness. -/
theorem original_inner_box_volume_toReal (c : Cell) :
    ((volume : Measure Point) (sourceInnerBox c)).toReal =
      (2 * commonRadius) ^ 8 := by
  have hr : 0 < commonRadius := by norm_num [commonRadius]
  have hle : boxLo c ≤ boxHi c := by
    intro j
    dsimp [boxLo, boxHi]
    linarith
  rw [original_inner_box_eq_pi_Ioo]
  calc
    ((volume : Measure Point)
      (Set.pi Set.univ (fun j : Fin 8 =>
        Set.Ioo (boxLo c j) (boxHi c j)))).toReal =
        ∏ j : Fin 8, (boxHi c j - boxLo c j) :=
          Real.volume_pi_Ioo_toReal hle
    _ = ∏ _j : Fin 8, (2 * commonRadius) := by
      apply Finset.prod_congr rfl
      intro j _
      dsimp [boxLo, boxHi]
      ring
    _ = (2 * commonRadius) ^ 8 := by simp

/-- Quantitative, integrable comparison on the exact same original
Source as the saved eighth-residual formula. The only fixed lower bound
used here is the 87-family radius-1e-8 *pointwise* certificate. -/
theorem original_full87_source_kernel_integral_box_lower (c : Cell) :
    (2 * commonRadius) ^ 8 *
        ((4 / (9 * mu ^ 10)) * (1 / 125000 : ℝ)) ≤
      ∫ t in sourceSet c, kernel c t := by
  let q : ℝ := (4 / (9 * mu ^ 10)) * (1 / 125000)
  have hsubset : sourceInnerBox c ⊆ sourceSet c := by
    intro t ht
    exact innerBox_mem_original_source c t ht
  have hboxfinite :
      (volume : Measure Point) (sourceInnerBox c) < ⊤ :=
    lt_of_le_of_lt (measure_mono hsubset)
      (P4AOriginalFull87TrimOmission.source_volume_lt_top c)
  have hboxopen : IsOpen (sourceInnerBox c) := by
    have hj (j : Fin 8) :
        IsOpen {t : Point |
          |t j -
            P4AOriginalFull87KernelPositiveWitness.originalCentre c j| <
              commonRadius} := by
      exact isOpen_lt (((continuous_apply j).sub continuous_const).abs)
        continuous_const
    simpa only [sourceInnerBox, Set.setOf_forall] using
      (isOpen_iInter_of_finite (fun j : Fin 8 => hj j))
  have hconst : IntegrableOn (fun _t : Point => q) (sourceInnerBox c) :=
    integrableOn_const hboxfinite.ne
  have hkernelOn : IntegrableOn (kernel c) (sourceInnerBox c) :=
    (integrableOn_kernel c).mono_set hsubset
  have hboxLower :
      (∫ _t in sourceInnerBox c, q) ≤
        ∫ t in sourceInnerBox c, kernel c t := by
    apply setIntegral_mono_on hconst hkernelOn hboxopen.measurableSet
    intro t ht
    exact original_full87_inner_box_kernel_lower c t ht
  have hnonneg :
      0 ≤ᵐ[(volume : Measure Point).restrict (sourceSet c)] kernel c := by
    filter_upwards [ae_restrict_mem (sourceSet_measurable c)] with t ht
    exact (P4AOriginalFull87KernelPositiveWitness.kernel_strict_pos_on_original_source
      ht).le
  have hsourceLower :
      (∫ t in sourceInnerBox c, kernel c t) ≤
        ∫ t in sourceSet c, kernel c t :=
    setIntegral_mono_set (integrableOn_kernel c) hnonneg hsubset.eventuallySubset
  have hconstValue :
      (∫ _t in sourceInnerBox c, q) =
        (2 * commonRadius) ^ 8 * q := by
    rw [setIntegral_const, measureReal_def, original_inner_box_volume_toReal]
    simp only [smul_eq_mul]
  change (2 * commonRadius) ^ 8 * q ≤ ∫ t in sourceSet c, kernel c t
  calc
    (2 * commonRadius) ^ 8 * q =
        ∫ _t in sourceInnerBox c, q := hconstValue.symm
    _ ≤ ∫ t in sourceInnerBox c, kernel c t := hboxLower
    _ ≤ ∫ t in sourceSet c, kernel c t := hsourceLower

end
end ImbalancedChen.P4AOriginalFull87BoxVolumeIntegral
