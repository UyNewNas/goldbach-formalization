import ImbalancedChen.P4AOriginalFull87AscendingAllInteriors
import ImbalancedChen.P4AOriginalFull87SeedNineFiftyInteriors
import ImbalancedChen.P4AOriginalFull87H5H7Interiors
import ImbalancedChen.P4AOriginalFull87DescAscPairInteriors
import ImbalancedChen.P4AOriginalFull87H3Interiors
import ImbalancedChen.P4AOriginalFull87EighthKernelControl
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Connect the EXISTING complete original 87-Cell continuous Source interiors
to the EXISTING manuscript eighth residual kernel.  The centres and their
original row-membership proofs are imported, not regenerated or weakened.

This is a strict ideal-kernel result on continuous original Sources only.
It does NOT authenticate the frozen 87 numerical selected integrals,
assert an N-dependent prime occurrence, change the actual sixth parent,
identify physical signed continuation gains, or pay a reserve.
-/-

namespace ImbalancedChen.P4AOriginalFull87KernelPositiveWitness
noncomputable section

open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87EighthKernelControl

private theorem original_nine_lookup (i : Fin 13) :
    P4AOriginalFull87SeedNineFiftyInteriors.originalCell
      (⟨i.val + 1, by omega⟩ : Fin 16) = .nine i := by
  fin_cases i <;> decide

private theorem original_h5_lookup (i : Fin 7) :
    P4AOriginalFull87H5H7Interiors.originalCell
      (⟨i.val, by omega⟩ : Fin 17) = .h5 i := by
  fin_cases i <;> decide

private theorem original_h7_lookup (i : Fin 10) :
    P4AOriginalFull87H5H7Interiors.originalCell
      (⟨i.val + 7, by omega⟩ : Fin 17) = .h7 i := by
  fin_cases i <;> decide

/-- An actual candidate interior point for EACH original source constructor,
without identifying a numerical archive label with a physical occurrence.
The unequal seed uses its source dictionary position, not archive order. -/
def originalCentre : Cell → Point
  | .remaining (.ascending i) =>
      P4AOriginalFull87AscendingAllInteriors.originalAscendingPoint i
  | .remaining .seed =>
      P4AOriginalFull87SeedNineFiftyInteriors.originalPoint 0
  | .remaining (.nine i) =>
      P4AOriginalFull87SeedNineFiftyInteriors.originalPoint
        ⟨i.val + 1, by omega⟩
  | .remaining .fiftyA =>
      P4AOriginalFull87SeedNineFiftyInteriors.originalPoint 14
  | .remaining .fiftyD =>
      P4AOriginalFull87SeedNineFiftyInteriors.originalPoint 15
  | .remaining (.h5 i) =>
      P4AOriginalFull87H5H7Interiors.originalPoint ⟨i.val, by omega⟩
  | .remaining (.h7 i) =>
      P4AOriginalFull87H5H7Interiors.originalPoint
        ⟨i.val + 7, by omega⟩
  | .descending i =>
      P4AOriginalFull87DescAscPairInteriors.originalDescPoint i
  | .ascendingPair i =>
      P4AOriginalFull87DescAscPairInteriors.originalPairPoint i
  | .h3 i =>
      P4AOriginalFull87H3Interiors.originalH3Point i

/-- Same original 87 Cell cases, exact original Source, no surrogate guard.
Original physical occurrence existence does NOT follow from this theorem. -/
theorem originalCentre_mem_source (c : Cell) :
    Source c (originalCentre c) := by
  cases c with
  | descending i =>
      exact P4AOriginalFull87DescAscPairInteriors.all15_centre_mem_original_source i
  | ascendingPair i =>
      exact P4AOriginalFull87DescAscPairInteriors.all13_centre_mem_original_source i
  | h3 i =>
      exact P4AOriginalFull87H3Interiors.all12_centre_mem_original_source i
  | remaining d =>
      cases d with
      | ascending i =>
          exact P4AOriginalFull87AscendingAllInteriors.all14_witness_mem_original_source i
      | seed =>
          change Source (.remaining .seed)
            (P4AOriginalFull87SeedNineFiftyInteriors.originalPoint (0 : Fin 16))
          simpa [P4AOriginalFull87SeedNineFiftyInteriors.originalCell] using
            (P4AOriginalFull87SeedNineFiftyInteriors.all16_witness_mem_original_source
              (0 : Fin 16))
      | nine i =>
          change Source (.remaining (.nine i))
            (P4AOriginalFull87SeedNineFiftyInteriors.originalPoint
              (⟨i.val + 1, by omega⟩ : Fin 16))
          rw [← original_nine_lookup i]
          exact P4AOriginalFull87SeedNineFiftyInteriors.all16_witness_mem_original_source _
      | fiftyA =>
          change Source (.remaining .fiftyA)
            (P4AOriginalFull87SeedNineFiftyInteriors.originalPoint (14 : Fin 16))
          simpa [P4AOriginalFull87SeedNineFiftyInteriors.originalCell] using
            (P4AOriginalFull87SeedNineFiftyInteriors.all16_witness_mem_original_source
              (14 : Fin 16))
      | fiftyD =>
          change Source (.remaining .fiftyD)
            (P4AOriginalFull87SeedNineFiftyInteriors.originalPoint (15 : Fin 16))
          simpa [P4AOriginalFull87SeedNineFiftyInteriors.originalCell] using
            (P4AOriginalFull87SeedNineFiftyInteriors.all16_witness_mem_original_source
              (15 : Fin 16))
      | h5 i =>
          change Source (.remaining (.h5 i))
            (P4AOriginalFull87H5H7Interiors.originalPoint
              (⟨i.val, by omega⟩ : Fin 17))
          rw [← original_h5_lookup i]
          exact P4AOriginalFull87H5H7Interiors.all17_witness_mem_original_source _
      | h7 i =>
          change Source (.remaining (.h7 i))
            (P4AOriginalFull87H5H7Interiors.originalPoint
              (⟨i.val + 7, by omega⟩ : Fin 17))
          rw [← original_h7_lookup i]
          exact P4AOriginalFull87H5H7Interiors.all17_witness_mem_original_source _

/-- Strictness missing from the pre-existing nonnegative kernel bound:
the ORIGINAL strict cap improvement makes its numerator positive, while
the original eight-prime Source gives both residual denominators positive.
This is not monotonicity of a signed physical sieve saving. -/
theorem kernel_strict_pos_on_original_source {c : Cell} {t : Point}
    (hs : Source c t) : 0 < kernel c t := by
  have hr := source_residual_range hs
  have hP : 0 < comparison c t - total t :=
    (cutoff_pos.trans hr.1).trans hr.2.1
  have hM : 0 < newCap c t - total t :=
    hP.trans (sub_lt_sub_right hr.2.2.1 (total t))
  have hJ : 0 < product t := (source_product_lower hs).2
  have hgain : 0 < newCap c t - comparison c t :=
    sub_pos.mpr hr.2.2.1
  unfold kernel residual
  exact div_pos (mul_pos (by norm_num) hgain)
    (mul_pos (mul_pos hP hM) hJ)

/-- Every single ORIGINAL continuous source has a concrete strict
positive ideal eighth residual kernel point.  This neither replays the
archived quadrature nor establishes an actual prime-labelled occurrence. -/
theorem every_original_cell_ideal_kernel_positive :
    ∀ c : Cell, ∃ t : Point, Source c t ∧ 0 < kernel c t := by
  intro c
  exact ⟨originalCentre c, originalCentre_mem_source c,
    kernel_strict_pos_on_original_source (originalCentre_mem_source c)⟩

end
end ImbalancedChen.P4AOriginalFull87KernelPositiveWitness
