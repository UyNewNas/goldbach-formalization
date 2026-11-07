import ImbalancedChen.P5OriginalDescending33ActualOmission
import ImbalancedChen.P5OriginalElevenRetestedParentGain

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Catalog13's `actual_cap` component, not all of catalog13 and not a new cap.
The independent original semantics fixes pattern1371 and mask34; its final
cap is A34-eta or D34-eta. The extra strict row is G>D33, where G is the
old selected33 remaining-slot4 gate. The two comparison caps in the
correction kernel are R0 and UNBUFFERED D33. D33 is not licensed here.

This file reads that independent source and proves its complete local
three-cap density identity, strict residual range and separation from
the G descending33 source. It also excludes each actual all11 supplier.
No source is silently added to the immutable E constructor. No numerical
gain, positive prime mass, finite common realization or full22 identity
is asserted. The one point below is already printed in the original note;
its proof term is proposed only, and has not been executed.
-/
namespace ImbalancedChen.P5Z.OriginalActualCapCorrectionSource
noncomputable section
open Classical
open scoped BigOperators
open Certificates.P2OriginalSixthElevenLogSemantics
open P1OriginalVariableFourthContinuation
open OriginalDescending33ActualOmission
open OriginalElevenRetestedParentGain

inductive Chart where
  | ascending | descending
  deriving DecidableEq, Repr

def descending34 (t : Physical) : ℝ := 57/64-3*(t 1+t 5)/2

/-- The unchanged FINAL mask34 cap in the original source, not D33. -/
def finalCap (c : Chart) (t : Physical) : ℝ :=
  (match c with | .ascending => ascending34 t | .descending => descending34 t)-eta

def chartSide (c : Chart) (t : Physical) : Prop :=
  match c with
  | .ascending => ascending34 t < descending34 t
  | .descending => descending34 t < ascending34 t

/-- The source's robustly failed OLD selected33 gate, physical slot4. -/
def oldSelectedGate (t : Physical) : ℝ := t 0+t 1+t 2+t 5+2*t 3

theorem oldSelectedGate_eq_original_remainingSquare (t : Physical) :
    oldSelectedGate t = remainingSquare 33 (3 : Fin 6) t := by
  norm_num [oldSelectedGate,remainingSquare,selectedSum,bit,Fin.sum_univ_succ]
  <;> ring

/-- Literal independent `semantic(t,1371,'actual_cap',ch)` interior.
The old branch planes are closed, as in G and the original closed source
enclosure; the chart and action boundaries have their strict policy form. -/
structure Source (c : Chart) (t : Physical) : Prop where
  rpos : 0 < t 5
  order : t 5 < t 4 ∧ t 4 < t 3 ∧ t 3 < t 2 ∧ t 2 < t 1 ∧ t 1 < t 0
  largest : t 0 < mu
  oldCutoff : t 5 < 1/50
  compactCutoff : 53/4608 < t 5
  history3 : H3 t < R0 t
  history5 : H5 t < R0 t
  oldW : W t ≤ R0 t
  oldBranches : ∀ m ∈ Finset.Icc 1 31,
    branchLicense (Cell.tent33_1371.descending m) (R0 t) (subsetSum m t)
  clipAboveAscending : ascending33 t < clippedCap t
  comparisonAbove : R0 t < descending33 t
  side : chartSide c t
  finalAboveComparison : descending33 t < finalCap c t
  aboveHalf : 1/2 < finalCap c t
  selectedAscending : finalCap c t < ascending34 t
  selectedDescending : finalCap c t < descending34 t
  fullSquares : ∀ j : Fin 6, fullSquare j t < finalCap c t
  remainingSquares : ∀ j : Fin 6, bit 34 j.val = false →
    remainingSquare 34 j t < finalCap c t
  oldArgument : t 5 < R0 t-S6 t
  newArgument : finalCap c t-S6 t < 3*t 5
  robustFailure : descending33 t < oldSelectedGate t

theorem Source.coordinates_pos {c : Chart} {t : Physical} (h : Source c t) :
    ∀ i : Fin 6, 0 < t i := by
  intro i
  fin_cases i <;> linarith [h.rpos,h.order.1,h.order.2.1,h.order.2.2.1,
    h.order.2.2.2.1,h.order.2.2.2.2]

/-- Independently specified full fifth raw envelope: all31 plus W. -/
def fullOldEnvelope (t : Physical) : ℝ :=
  finiteMax (Finset.Icc 1 31) (fun _ => True) (fun m => tent (subsetSum m t)) (W t)

theorem Source.fullOldEnvelope_eq_R0 {c : Chart} {t : Physical} (h : Source c t) :
    fullOldEnvelope t = R0 t := by
  apply le_antisymm
  · exact finiteMax_le _ _ _ _ _ h.oldW
      (fun m hm _ => branchLicense_sound (h.oldBranches m hm))
  · have hw := finiteMax_row_le (Finset.Icc 1 31) (fun _ => True)
      (fun m => tent (subsetSum m t)) (W t) 1 (by norm_num) trivial
    rw [subsetSum_one,tent_ascending h.largest.le] at hw
    exact hw

theorem Source.residual_chain {c : Chart} {t : Physical} (h : Source c t) :
    t 5 < R0 t-S6 t ∧ R0 t-S6 t < descending33 t-S6 t ∧
      descending33 t-S6 t < finalCap c t-S6 t ∧ finalCap c t-S6 t < 3*t 5 :=
  ⟨h.oldArgument,sub_lt_sub_right h.comparisonAbove _,
    sub_lt_sub_right h.finalAboveComparison _,h.newArgument⟩

theorem Source.argument_chain {c : Chart} {t : Physical} (h : Source c t) :
    1 < (R0 t-S6 t)/t 5 ∧
      (R0 t-S6 t)/t 5 < (descending33 t-S6 t)/t 5 ∧
      (descending33 t-S6 t)/t 5 < (finalCap c t-S6 t)/t 5 ∧
      (finalCap c t-S6 t)/t 5 < 3 := by
  exact ⟨(one_lt_div h.rpos).mpr h.oldArgument,
    (div_lt_div_iff_of_pos_right h.rpos).mpr h.residual_chain.2.1,
    (div_lt_div_iff_of_pos_right h.rpos).mpr h.residual_chain.2.2.1,
    (div_lt_iff₀ h.rpos).mpr h.newArgument⟩

theorem Source.finalCap_lt_originalTheta {c : Chart} {t : Physical} (h : Source c t) :
    finalCap c t < (299/500 : ℝ) := by
  have ha := h.selectedAscending
  have hd := h.selectedDescending
  dsimp [ascending34,descending34] at ha hd
  have hb : finalCap c t < (153/256 : ℝ) := by linarith
  exact hb.trans (by norm_num)

/-- Even the unbuffered comparison D33 fails this original physical gate. -/
theorem Source.no_descending33_gate {c : Chart} {t : Physical} (h : Source c t)
    (L : ℝ) (hL : L ≤ descending33 t) :
    ¬remainingSquare 33 (3 : Fin 6) t < L := by
  rw [←oldSelectedGate_eq_original_remainingSquare]
  exact not_lt_of_ge (hL.trans h.robustFailure.le)

/-- Catalog13's correction is disjoint from BOTH original catalog8 cells.
This follows from the original gate, not merely different catalog names. -/
theorem Source.not_descending33_source {c : Chart} {t : Physical} (h : Source c t)
    (p : Pattern) : ¬PhysicalSource p t := by
  intro hd
  have hg := hd.remainingSquares (3 : Fin 6) (by norm_num [bit])
  exact h.no_descending33_gate (descendingNewCap t) (by
    dsimp [descendingNewCap,eta]; linarith) hg

theorem Source.no_all11_supplier {c : Chart} {t : Physical} (h : Source c t)
    (cell : Cell) : ¬PhysicalCell cell t := by
  have htent : tent (selectedSum cell.selectedMask t) ≤ ascending33 t := by
    rw [all11_selected_sum_split]
    calc
      _ ≤ tent (subsetSum (firstFiveSelectedMask cell) t)+t 5/2 :=
        tent_add_last_le _ _ h.rpos.le
      _ ≤ R0 t+t 5/2 := add_le_add_right
        (branchLicense_sound (h.oldBranches _ (firstFiveSelectedMask_mem cell))) _
      _ = _ := by dsimp [R0,ascending33]; ring
  intro hc
  by_cases ht : cell.family = .tent33
  · have hm : cell.selectedMask = 33 := by
      cases cell <;> simp_all [Cell.family,Cell.selectedMask]
    have hs : selectedSum 33 t = t 0+t 5 := by
      norm_num [selectedSum,bit,Fin.sum_univ_succ]
    have hd := hc.selectedDescending
    rw [newCap,if_pos ht,hm,hs] at hd
    change ascending33 t-eta < descending33 t at hd
    have ha : finalCap c t ≤ ascending34 t-eta := by
      cases c with
      | ascending => exact le_refl _
      | descending => exact sub_le_sub_right h.side.le eta
    have hu := h.finalAboveComparison
    dsimp [ascending33,ascending34] at hd ha
    linarith [h.order.2.2.2.2]
  · have hl : newCap cell t < tent (selectedSum cell.selectedMask t) :=
      lt_min hc.selectedAscending hc.selectedDescending
    rw [newCap,if_neg ht] at hl
    linarith [h.clipAboveAscending]

def comparisonKernel (c : Chart) (t : Physical) : ℝ :=
  primeBoxInitialSavingProfile (descending33 t) (finalCap c t) t/coordinateProduct t

def correctionKernel (t : Physical) : ℝ :=
  primeBoxInitialSavingProfile (R0 t) (descending33 t) t/coordinateProduct t

def fullEndpointKernel (c : Chart) (t : Physical) : ℝ :=
  primeBoxInitialSavingProfile (R0 t) (finalCap c t) t/coordinateProduct t

/-- The exact factors returned by independent density(t,'actual_cap',ch).
They use D33, not finalCap and not descendingNewCap. -/
def correctionFactors (t : Physical) : Fin 8 → ℝ :=
  ![R0 t-S6 t,descending33 t-S6 t,t 0,t 1,t 2,t 3,t 4,t 5]

theorem correctionKernel_eq_literal_source (t : Physical) :
    correctionKernel t = 4*(descending33 t-R0 t)/(∏ i,correctionFactors t i) := by
  have hp : (∏ i,correctionFactors t i) =
      (R0 t-S6 t)*(descending33 t-S6 t)*coordinateProduct t := by
    simp [correctionFactors,coordinateProduct,Fin.prod_univ_succ] <;> ring
  rw [hp]
  unfold correctionKernel primeBoxInitialSavingProfile
  rw [←S6_eq_sum t,div_div]

/-- Complete local source identity. The added component is exactly the
discarded intermediate comparison difference, with the SAME final cap. -/
theorem Source.full_source_density_identity {c : Chart} {t : Physical} (h : Source c t) :
    fullEndpointKernel c t = comparisonKernel c t+correctionKernel t := by
  have hR : 0 < R0 t-S6 t := h.rpos.trans h.oldArgument
  have hD : 0 < descending33 t-S6 t := hR.trans h.residual_chain.2.1
  have hM : 0 < finalCap c t-S6 t := hD.trans h.residual_chain.2.2.1
  have ht := three_cap_profile_telescope t (R0 t) (descending33 t) (finalCap c t)
    (by rw [←S6_eq_sum t]; exact hR.ne')
    (by rw [←S6_eq_sum t]; exact hD.ne')
    (by rw [←S6_eq_sum t]; exact hM.ne')
  unfold fullEndpointKernel comparisonKernel correctionKernel
  rw [ht,add_div,add_comm]

theorem Source.correctionKernel_pos {c : Chart} {t : Physical} (h : Source c t) :
    0 < correctionKernel t := by
  have hR : 0 < R0 t-S6 t := h.rpos.trans h.oldArgument
  have hD : 0 < descending33 t-S6 t := hR.trans h.residual_chain.2.1
  unfold correctionKernel primeBoxInitialSavingProfile
  rw [←S6_eq_sum t]
  exact div_pos (div_pos (mul_pos (by norm_num) (sub_pos.mpr h.comparisonAbove))
    (mul_pos hR hD)) (Finset.prod_pos (fun i _ => h.coordinates_pos i))

/-- The one explicit physical point already printed in the source note.
This is not a replay of the690-simplex certificate or a gain proof. -/
def printedPoint : Physical :=
  ![361735962/2000000000,352846926/2000000000,149501450/2000000000,
    145057601/2000000000,55760730/2000000000,35556148/2000000000]

theorem printedPoint_in_original_ascending_correction : Source .ascending printedPoint := by
  constructor
  all_goals first
    | (intro m hm; have hb := Finset.mem_Icc.mp hm; interval_cases m <;>
        norm_num [printedPoint,branchLicense,Cell.descending,Cell.family,Cell.pattern,
          variableMasks,subsetSum,bit,Fin.sum_univ_succ,R0])
    | (intro j; fin_cases j <;>
        norm_num [printedPoint,fullSquare,finalCap,ascending34,eta,Fin.sum_univ_succ])
    | (intro j hj; fin_cases j <;>
        norm_num [printedPoint,remainingSquare,selectedSum,bit,finalCap,ascending34,
          eta,Fin.sum_univ_succ] at hj ⊢)
    | norm_num [printedPoint,mu,H3,H5,R0,W,clippedCap,S5,S6,ascending33,descending33,
        chartSide,ascending34,descending34,finalCap,eta,oldSelectedGate]

end
end ImbalancedChen.P5Z.OriginalActualCapCorrectionSource
