import ImbalancedChen.P4AAll22OriginalKLedger
import ImbalancedChen.P5OriginalCommonRefinedConstructor
import Mathlib.Tactic.FinCases

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal inventory of the twenty-two SELECTED SAVING entries of
adopted-evidence-catalog.json, not twenty-two cap families and not 11+11.
The source/field/endpoint data below are serialized from those actual
independent records, pinned by raw SHA in REGISTRY. Endpoint agreement
with the existing quoted 18+4 ledger is finite rational bookkeeping only.
No domain, enclosure, archived saving or complete common-policy identity
is inferred from an endpoint or filename.

The constructor's actual sixth finiteMax is tagged through its REAL
allCells supplier. That candidate image is exactly entry 7. The remaining
sixth source entries are exhibited explicitly. Entries 21/22 are same-domain
increments and are never tagged as new cap actions. The original 87 slot
inventory is the original eight consecutive group blocks; it does not
supply missing affine-cell geometry, exclusivity or archived ownership.
-/
namespace ImbalancedChen.P5Z.OriginalFull22SourceInventory
noncomputable section
open Classical
open scoped BigOperators
open P4AAll22OriginalKLedger20261024zSourceOnly

abbrev SavingTag := Fin 22

def sourceNumber (i : SavingTag) : ℕ := i.val+1

theorem original_source_numbers_exhaust :
    (Finset.univ : Finset SavingTag).image sourceNumber = Finset.Icc 1 22 := by
  ext n
  constructor
  · intro hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    apply Finset.mem_Icc.mpr
    have := i.isLt
    constructor <;> dsimp [sourceNumber] <;> omega
  · intro hn
    have h := Finset.mem_Icc.mp hn
    refine Finset.mem_image.mpr ⟨⟨n-1, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp [sourceNumber]
    omega

def catalogID : SavingTag → String :=
  !["replacement_fourth",
    "replacement_old_fifth",
    "new_disjoint_fifth",
    "replacement_old_sixth",
    "above_mu_second_coarse_only",
    "above_mu_third",
    "eleven_sixth_cells_final_log",
    "new_descending33",
    "ascending34_actual_parent",
    "descending34_actual_parent",
    "lower_clip_window",
    "lower_descending34_window",
    "selected_local_corrections",
    "four_nonsingleton_sixth",
    "original_eighth_radial_max",
    "fourteen_ascending_eighth",
    "fifteen_descending_eighth",
    "fifteen_unequal_eighth_final_log",
    "thirteen_third_minorant_final_log",
    "twentynine_history_final_log",
    "seed_curvature_only_increment",
    "seed_mixed_only_increment"]

def sourceFile : SavingTag → String :=
  !["stronger-fourth-independent-replay.json",
    "independent_fifth_subdivision_replay.json",
    "fifth-new-coverage-independent-audit.json",
    "sixth-prefix-expanded-independent-audit.json",
    "second-prefix-upper-fallback-independent-review-20261009.json",
    "third-prefix-upper-fallback-independent-review-20261009.json",
    "sixth-log-moment-jensen-independent-20261009.json",
    "sixth-tent33-descending-independent-20261009.json",
    "sixth-tent34-ascending-independent-20261009.json",
    "sixth-tent34-descending-independent-20261009.json",
    "sixth-lower-clip-window-independent-20261009.json",
    "sixth-lower-desc34-window-independent-20261009.json",
    "sixth-lower-local-additions-independent-20261009.json",
    "sixth-nonsingleton-independent-20261009.json",
    "eighth-radial-independent-20261009.json",
    "eighth-prefix-family-independent-20261009.json",
    "eighth-prefix-descending-independent-20261009.json",
    "eighth-unequal-moment-independent-20261009.json",
    "eighth-third-moment-refinement-independent-20261009.json",
    "eighth-history-moment-independent-20261009.json",
    "eighth-joint-affine-curvature-independent-20261009.json",
    "eighth-joint-transverse-mixed-independent-20261009.json"]

def endpointField : SavingTag → String :=
  !["gain_lower",
    "stored_gain_verified",
    "gains.new_disjoint",
    "gain_lower",
    "no_grid_coarse_lower",
    "selected_lower",
    "new_gain",
    "gain_lower",
    "gain_lower",
    "gain_lower",
    "gain_lower",
    "gain_lower",
    "selected_gain",
    "gain_lower",
    "whole_cell_max",
    "new_gain_lower",
    "gain_lower",
    "new_gain",
    "new_gain",
    "new_gain",
    "increment_over_adopted_log",
    "increment"]

def catalogEndpoint : SavingTag → ℝ :=
  ![10601625247768616959055 / 302231454903657293676544,
    3037921066812732539869 / 302231454903657293676544,
    1648717268323516459667 / 1208925819614629174706176,
    145496122603609407505 / 151115727451828646838272,
    640339 / 15210735000,
    3097012678584315027795429 / 79228162514264337593543950336,
    1208544915921356327515701 / 79228162514264337593543950336,
    148834609033428677786865 / 79228162514264337593543950336,
    306737545112876482463163 / 79228162514264337593543950336,
    187277743940187526723019 / 79228162514264337593543950336,
    670429887277013841791829 / 79228162514264337593543950336,
    198410119216276585672773 / 39614081257132168796771975168,
    5023185001132087792027 / 9903520314283042199192993792,
    581521529176619227721 / 4951760157141521099596496896,
    74558208451675327462975 / 79228162514264337593543950336,
    1222997719565324892497827 / 79228162514264337593543950336,
    467454156274267811817033 / 79228162514264337593543950336,
    1033407531585213315823239 / 79228162514264337593543950336,
    283388722705335806564439 / 79228162514264337593543950336,
    14750615007945677662815 / 39614081257132168796771975168,
    77410436074156865471 / 79228162514264337593543950336,
    481322793305152847935 / 79228162514264337593543950336]

/-- This is the pre-existing QUOTED ledger; it has no policy hypothesis. -/
def quotedEndpoint (i : SavingTag) : ℝ :=
  if h : i.val < 18 then currentUpperEighteenGains ⟨i.val,h⟩
  else finalFourGains ⟨i.val-18, by have := i.isLt; omega⟩

theorem catalogEndpoint_eq_existing_quoted (i : SavingTag) :
    catalogEndpoint i = quotedEndpoint i := by
  fin_cases i <;> norm_num [catalogEndpoint, quotedEndpoint,
    currentUpperEighteenGains, finalFourGains]

theorem catalog_sum_eq_existing_eighteen_plus_four :
    (∑ i, catalogEndpoint i) =
      (∑ i, currentUpperEighteenGains i)+(∑ i, finalFourGains i) := by
  norm_num [catalogEndpoint, currentUpperEighteenGains, finalFourGains, Fin.sum_univ_succ]

theorem quoted_raw_ledger_preserves_all_twenty_two_once :
    quotedAll22Raw = (∑ i, currentUpperEighteenPositive i)-(∑ i, catalogEndpoint i) := by
  rw [catalog_sum_eq_existing_eighteen_plus_four]
  unfold quotedAll22Raw currentUpperEighteenRaw
  ring

/-- A primary saving record may itself be a replacement estimate or a
same-tree partial correction. This classification does not assert that
every primary record activates an independent new cap. -/
inductive AccountingRole where
  | selectedSaving | sameDomainOnlyIncrement
  deriving DecidableEq, Repr

def accountingRole (i : SavingTag) : AccountingRole :=
  if 20 ≤ i.val then .sameDomainOnlyIncrement else .selectedSaving

def sameDomainIncrementTags : Finset SavingTag := {20,21}

theorem increment_tags_exact (i : SavingTag) :
    accountingRole i = .sameDomainOnlyIncrement ↔ i ∈ sameDomainIncrementTags := by
  simp only [accountingRole, sameDomainIncrementTags, Finset.mem_insert,
    Finset.mem_singleton]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

theorem two_same_domain_increments :
    sourceNumber 20 = 21 ∧ sourceNumber 21 = 22 ∧
      endpointField 20 = "increment_over_adopted_log" ∧
      endpointField 21 = "increment" := by decide

/-- These are the actual SIXTH source ledger tags, not all entries 1..22.
Entry 7 contains the original eleven named cells. -/
def originalSixthSourceTags : Finset SavingTag := {3,6,7,8,9,10,11,12,13}

def elevenCellSourceTag (_c : Certificates.P2OriginalSixthElevenLogSemantics.Cell) : SavingTag := 6

/-- Actual typed supplier of the independently frozen constructor. There
is no hypothetical full22 selector, and the true fifth seed stays separate. -/
def constructorSixthSupplierTags : Finset SavingTag :=
  Certificates.P2OriginalSixthElevenLogSemantics.allCells.toFinset.image elevenCellSourceTag

theorem constructor_sixth_supplier_tags_exact : constructorSixthSupplierTags = {6} := by
  simp [constructorSixthSupplierTags, elevenCellSourceTag,
    Certificates.P2OriginalSixthElevenLogSemantics.allCells]

theorem constructor_actual_sixth_formula
    (d : P5OriginalCommonRefinedConstructor.OriginalData) (N : ℝ) (pre : List ℕ) :
    P5OriginalCommonRefinedConstructor.lambda6 d N pre =
      P1OriginalVariableFourthContinuation.finiteMax
        Certificates.P2OriginalSixthElevenLogSemantics.allCells.toFinset
        (fun c => P5OriginalCommonRefinedConstructor.eligibleSixth d N c pre)
        (fun c => Certificates.P2OriginalSixthElevenLogSemantics.newCap c
          (primeHistoryLogCoordinates N 6 pre))
        (P5OriginalCommonRefinedConstructor.actualParent5 d N pre) := rfl

def missingSixthSupplierTags : Finset SavingTag :=
  originalSixthSourceTags \ constructorSixthSupplierTags

theorem missing_sixth_supplier_tags_exact :
    missingSixthSupplierTags = {3,7,8,9,10,11,12,13} := by
  rw [missingSixthSupplierTags, constructor_sixth_supplier_tags_exact]
  decide

theorem missing_sixth_source_numbers_exact :
    missingSixthSupplierTags.image sourceNumber = {4,8,9,10,11,12,13,14} := by
  rw [missing_sixth_supplier_tags_exact]
  decide

theorem old_sixth_is_missing : (3 : SavingTag) ∈ missingSixthSupplierTags := by
  rw [missing_sixth_supplier_tags_exact]
  decide

theorem same_domain_increments_are_not_sixth_suppliers :
    Disjoint sameDomainIncrementTags constructorSixthSupplierTags := by
  rw [constructor_sixth_supplier_tags_exact]
  decide

/-- Source blocks stated by the original 30+15+13+29 inventory and the
held adopted87 module. No geometric equality between two slots follows. -/
inductive EighthGroup where
  | equalParent | unequalWinner9 | unequal50A | unequal50D
  | ascendingPair | history3 | history5 | history7
  deriving DecidableEq, Repr

def eighthGroup (i : P5OriginalAdoptedEighthPhysicalMasks.Cell) : EighthGroup :=
  if i.val < 30 then .equalParent
  else if i.val < 43 then .unequalWinner9
  else if i.val = 43 then .unequal50A
  else if i.val = 44 then .unequal50D
  else if i.val < 58 then .ascendingPair
  else if i.val < 70 then .history3
  else if i.val < 77 then .history5
  else .history7

def sourceGroupCount : EighthGroup → ℕ
  | .equalParent => 30
  | .unequalWinner9 => 13
  | .unequal50A => 1
  | .unequal50D => 1
  | .ascendingPair => 13
  | .history3 => 12
  | .history5 => 7
  | .history7 => 10

/-- The three equal-parent ledger entries share the original 30-slot
bank; an arbitrary seed/cell ordering is not invented here. The two last
ledger increments refine one unequal seed, not a further slot group. -/
def primaryLedgerTags : EighthGroup → Finset SavingTag
  | .equalParent => {14,15,16}
  | .unequalWinner9 | .unequal50A | .unequal50D => {17}
  | .ascendingPair => {18}
  | .history3 | .history5 | .history7 => {19}

theorem original_eighth_group_counts :
    sourceGroupCount .equalParent + sourceGroupCount .unequalWinner9 +
      sourceGroupCount .unequal50A + sourceGroupCount .unequal50D +
      sourceGroupCount .ascendingPair + sourceGroupCount .history3 +
      sourceGroupCount .history5 + sourceGroupCount .history7 = 87 := rfl

/-- Counts of the actual held index blocks, not a count of disjoint
geometric cells proved by a numerical certificate. This closed finite
source term has not been run or compiled. -/
theorem held_eighth_group_slot_counts :
    ((Finset.univ : Finset P5OriginalAdoptedEighthPhysicalMasks.Cell).filter
      (fun i => eighthGroup i = .equalParent)).card = 30 ∧
    ((Finset.univ : Finset P5OriginalAdoptedEighthPhysicalMasks.Cell).filter
      (fun i => eighthGroup i = .unequalWinner9)).card = 13 ∧
    ((Finset.univ : Finset P5OriginalAdoptedEighthPhysicalMasks.Cell).filter
      (fun i => eighthGroup i = .unequal50A)).card = 1 ∧
    ((Finset.univ : Finset P5OriginalAdoptedEighthPhysicalMasks.Cell).filter
      (fun i => eighthGroup i = .unequal50D)).card = 1 ∧
    ((Finset.univ : Finset P5OriginalAdoptedEighthPhysicalMasks.Cell).filter
      (fun i => eighthGroup i = .ascendingPair)).card = 13 ∧
    ((Finset.univ : Finset P5OriginalAdoptedEighthPhysicalMasks.Cell).filter
      (fun i => eighthGroup i = .history3)).card = 12 ∧
    ((Finset.univ : Finset P5OriginalAdoptedEighthPhysicalMasks.Cell).filter
      (fun i => eighthGroup i = .history5)).card = 7 ∧
    ((Finset.univ : Finset P5OriginalAdoptedEighthPhysicalMasks.Cell).filter
      (fun i => eighthGroup i = .history7)).card = 10 := by decide

theorem actual_adopted_mask_by_source_group (i : P5OriginalAdoptedEighthPhysicalMasks.Cell) :
    P5OriginalAdoptedEighthPhysicalMasks.selectedMask i =
      match eighthGroup i with
      | .equalParent => P5OriginalAdoptedEighthPhysicalMasks.mask129
      | .unequal50A => P5OriginalAdoptedEighthPhysicalMasks.mask184
      | .unequal50D => P5OriginalAdoptedEighthPhysicalMasks.mask134
      | _ => P5OriginalAdoptedEighthPhysicalMasks.mask138 := by
  unfold eighthGroup P5OriginalAdoptedEighthPhysicalMasks.selectedMask
  split_ifs <;> first | rfl | omega

/-- Actual selected-sixth value exhaustion INSIDE the constructor: either
the real fifth seed survives, or an eligible member of the REAL all11
supplier attains the value. This is not original full22 exhaustion. -/
theorem actual_sixth_value_witness
    (d : P5OriginalCommonRefinedConstructor.OriginalData) (N : ℝ) (pre : List ℕ) :
    P5OriginalCommonRefinedConstructor.lambda6 d N pre =
      P5OriginalCommonRefinedConstructor.actualParent5 d N pre ∨
    ∃ c ∈ Certificates.P2OriginalSixthElevenLogSemantics.allCells.toFinset,
      P5OriginalCommonRefinedConstructor.eligibleSixth d N c pre ∧
      P5OriginalCommonRefinedConstructor.lambda6 d N pre =
        Certificates.P2OriginalSixthElevenLogSemantics.newCap c
          (primeHistoryLogCoordinates N 6 pre) := by
  have hm : P5OriginalCommonRefinedConstructor.lambda6 d N pre ∈
      P1OriginalVariableFourthContinuation.finiteValues
        Certificates.P2OriginalSixthElevenLogSemantics.allCells.toFinset
        (fun c => P5OriginalCommonRefinedConstructor.eligibleSixth d N c pre)
        (fun c => Certificates.P2OriginalSixthElevenLogSemantics.newCap c
          (primeHistoryLogCoordinates N 6 pre))
        (P5OriginalCommonRefinedConstructor.actualParent5 d N pre) := by
    exact Finset.max'_mem _ _
  rcases Finset.mem_insert.mp hm with hseed | hrow
  · exact Or.inl hseed
  · obtain ⟨c, hc, heq⟩ := Finset.mem_image.mp hrow
    exact Or.inr ⟨c, (Finset.mem_filter.mp hc).1, (Finset.mem_filter.mp hc).2, heq.symm⟩

theorem actual_sixth_strict_raise_has_original_entry7_witness
    (d : P5OriginalCommonRefinedConstructor.OriginalData) (N : ℝ) (pre : List ℕ)
    (hraise : P5OriginalCommonRefinedConstructor.actualParent5 d N pre <
      P5OriginalCommonRefinedConstructor.lambda6 d N pre) :
    ∃ c ∈ Certificates.P2OriginalSixthElevenLogSemantics.allCells.toFinset,
      P5OriginalCommonRefinedConstructor.eligibleSixth d N c pre ∧
      P5OriginalCommonRefinedConstructor.lambda6 d N pre =
        Certificates.P2OriginalSixthElevenLogSemantics.newCap c
          (primeHistoryLogCoordinates N 6 pre) ∧ sourceNumber (elevenCellSourceTag c) = 7 := by
  rcases actual_sixth_value_witness d N pre with hseed | ⟨c,hc,heligible,heq⟩
  · exact False.elim ((ne_of_gt hraise) hseed)
  · exact ⟨c,hc,heligible,heq,rfl⟩

/-- Actual chosen eighth source: the fallback remains the actual sixth
ancestor, while every chosen record carries its real PhysicalRows tests.
No omitted original affine-domain record is manufactured by this witness. -/
theorem actual_eighth_value_witness
    (d : P5OriginalCommonRefinedConstructor.OriginalData) (N : ℝ) (pre : List ℕ) :
    P5OriginalAdoptedEighthPhysicalMasks.raisedExponent N
      (P5OriginalCommonRefinedConstructor.lambda3 d N)
      (P5OriginalCommonRefinedConstructor.lambda6 d N) pre =
        P5OriginalCommonRefinedConstructor.lambda6 d N (rosserAncestor 6 pre) ∨
    ∃ i : P5OriginalAdoptedEighthPhysicalMasks.Cell,
      P5OriginalAdoptedEighthPhysicalMasks.PhysicalRows i (primeHistoryLogCoordinates N 8 pre)
        (P5OriginalCommonRefinedConstructor.lambda3 d N (rosserAncestor 3 pre))
        (P5OriginalCommonRefinedConstructor.lambda6 d N (rosserAncestor 6 pre)) ∧
      P5OriginalAdoptedEighthPhysicalMasks.raisedExponent N
        (P5OriginalCommonRefinedConstructor.lambda3 d N)
        (P5OriginalCommonRefinedConstructor.lambda6 d N) pre =
          P5OriginalAdoptedEighthPhysicalMasks.newCap i (primeHistoryLogCoordinates N 8 pre) := by
  unfold P5OriginalAdoptedEighthPhysicalMasks.raisedExponent
  split_ifs with h
  · exact Or.inr ⟨Classical.choose h,Classical.choose_spec h,rfl⟩
  · exact Or.inl rfl

end
end ImbalancedChen.P5Z.OriginalFull22SourceInventory
