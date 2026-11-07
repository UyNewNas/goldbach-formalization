import ImbalancedChen.P2OriginalCompactBoundaryCapFloor
import ImbalancedChen.ActualThirdOriginalPositive256LogRange32
import ImbalancedChen.Certificates.OriginalNodeArraysV1.All40CheckedTable
import ImbalancedChen.P4AClosedCutTreePositionalChargeBinding
import ImbalancedChen.P2OriginalInitialClosedTree

/-!
SOURCEONLY / UNCOMPILED / ORIGINAL ADAPTIVE ENDPOINT OPEN.

The actual original coordinate box is used throughout. The new boundary
supplier constructs both log/mass and clipped-gap bounds from existing
literal arithmetic and the fixed all40 reader; no semantic leaf bound is
assumed. Full range reduction, up to32, covers every original root and its
positive-width descendants, rather than imposing a spurious ratio<=2.

This is an alternative sound enclosure of an original-domain leaf. Its
P160 cost is NOT identified with the original P80 source cost. Paying a
particular original charge requires the displayed INTEGER comparison.
The positional consumer preserves closedLeaves/attachCharges exactly.
No adaptive tree, charge list, integer sum, or final endpoint is supplied.
-/

namespace ImbalancedChen.P2OriginalCompactBoundaryChargeSourceOnly

noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdSymmetricMassCeilSourceOnly
open OriginalThirdP4AOriginalClippedGapSourceOnly
open P2OriginalCompactBoundaryCapFloorSourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly
open P4AOriginalInitialSeedInventorySourceOnly
open P4AClosedCutTreePositionalChargeBindingSourceOnly
open P4AOriginalClosedTreeStructuralAggregationSourceOnly
open OriginalU2All40CheckedTable20261024wSourceOnly

local notation "D₀" => (48000*2^24:ℤ)

theorem decodeCoordinates_eq_original_scale (v : Fin 3 → ℤ) (i : Fin 3) :
    decodeCoordinates v i=(v i:ℝ)/(D₀:ℝ) := by
  norm_num [decodeCoordinates,coordinateDenominator]

/-- Primitive integer geometry only. The author's positive-residual
assertion is derived below, not a field of this record. -/
structure SourceBox (lo hi : Fin 3 → ℤ) : Prop where
  lower : ∀ i, H≤lo i
  upper : ∀ i, hi i≤R
  width : ∀ i, lo i<hi i
  muCut : hi 0≤M ∨ M≤lo 0

theorem sourceBox_residual {lo hi : Fin 3 → ℤ} (g : SourceBox lo hi) :
    hi 0+hi 1<authorCapLower lo hi :=
  authorCapLower_residual_of_original_cube lo hi (g.lower 0) g.upper

theorem sourceBox_positive {lo hi : Fin 3 → ℤ} (g : SourceBox lo hi) :
    ∀ i, 0<decodeCoordinates lo i := by
  intro i
  have hh : (0:ℤ)<lo i := (by norm_num [H] : (0:ℤ)<H).trans_le (g.lower i)
  exact div_pos (by exact_mod_cast hh) (by norm_num [coordinateDenominator])

theorem sourceBox_width {lo hi : Fin 3 → ℤ} (g : SourceBox lo hi) :
    ∀ i, decodeCoordinates lo i<decodeCoordinates hi i := by
  intro i
  exact (div_lt_div_iff_of_pos_right
    (by norm_num [coordinateDenominator] : (0:ℝ)<coordinateDenominator)).2
      (by exact_mod_cast g.width i)

/-- The original compact box bounds imply the whole range-reduction domain.
This also covers the first root's ratios mu/h=19.53125. -/
theorem sourceBox_log_range {lo hi : Fin 3 → ℤ} (g : SourceBox lo hi) (i : Fin 3) :
    1≤(hi i:ℝ)/(lo i:ℝ) ∧ (hi i:ℝ)/(lo i:ℝ)≤32 := by
  have hlow : (H:ℝ)≤(lo i:ℝ) := by exact_mod_cast g.lower i
  have hupp : (hi i:ℝ)≤(R:ℝ) := by exact_mod_cast g.upper i
  have hwidth : (lo i:ℝ)<(hi i:ℝ) := by exact_mod_cast g.width i
  have hp : (0:ℝ)<(lo i:ℝ) := (by norm_num [H] : (0:ℝ)<(H:ℝ)).trans_le hlow
  constructor
  · exact (le_div_iff₀ hp).2 (by simpa only [one_mul] using hwidth.le)
  · apply (div_le_iff₀ hp).2
    have hfixed : (R:ℝ)≤32*(H:ℝ) := by norm_num [R,H]
    exact hupp.trans (hfixed.trans (mul_le_mul_of_nonneg_left hlow (by norm_num)))

def boundaryMass (lo hi : Fin 3 → ℤ) : IV :=
  mul (mul (originalLn32 ((hi 0:ℝ)/(lo 0:ℝ)))
    (originalLn32 ((hi 1:ℝ)/(lo 1:ℝ)))) (literalMassZ (lo 2) (hi 2))

/-- Exact reciprocal/log mass, including its factor4 once. The interval
operation order is the later independent producer's full rectangle order. -/
theorem boundaryMass_encloses (lo hi : Fin 3 → ℤ) (g : SourceBox lo hi) :
    Encloses (boundaryMass lo hi)
      (4*boxMass (decodeCoordinates lo) (decodeCoordinates hi)) := by
  have hD : (0:ℝ)<(D₀:ℝ) := by norm_num
  have hposLo (i : Fin 3) : 0<lo i :=
    (by norm_num [H] : (0:ℤ)<H).trans_le (g.lower i)
  have hposHi (i : Fin 3) : 0<hi i := (hposLo i).trans (g.width i)
  have hratio (i : Fin 3) :
      decodeCoordinates hi i/decodeCoordinates lo i=(hi i:ℝ)/(lo i:ℝ) := by
    rw [decodeCoordinates_eq_original_scale hi i,decodeCoordinates_eq_original_scale lo i]
    exact producer_log_ratio (D₀:ℝ) (lo i:ℝ) (hi i:ℝ) hD.ne'
      (by exact_mod_cast (hposLo i).ne')
  have hlog (i : Fin 3) : Encloses (originalLn32 ((hi i:ℝ)/(lo i:ℝ)))
      (Real.log (decodeCoordinates hi i/decodeCoordinates lo i)) := by
    rw [hratio]
    exact originalLn32_sound (sourceBox_log_range g i).1 (sourceBox_log_range g i).2
  have hraw := mul_sound (mul_sound (hlog 0) (hlog 1))
    (literalMassZ_sound (hposLo 2) (hposHi 2))
  have hz0 : (lo 2:ℝ)≠0 := by exact_mod_cast (hposLo 2).ne'
  have hz1 : (hi 2:ℝ)≠0 := by exact_mod_cast (hposHi 2).ne'
  have hfactor : (((4*D₀*(hi 2-lo 2):ℤ):ℝ)/((lo 2*hi 2:ℤ):ℝ))=
      4*(decodeCoordinates hi 2-decodeCoordinates lo 2)/
        (decodeCoordinates lo 2*decodeCoordinates hi 2) := by
    rw [decodeCoordinates_eq_original_scale hi 2,decodeCoordinates_eq_original_scale lo 2]
    push_cast
    field_simp [hD.ne',hz0,hz1] <;> ring
  have heq :
      Real.log (decodeCoordinates hi 0/decodeCoordinates lo 0)*
        Real.log (decodeCoordinates hi 1/decodeCoordinates lo 1)*
        (((4*D₀*(hi 2-lo 2):ℤ):ℝ)/((lo 2*hi 2:ℤ):ℝ))=
      4*boxMass (decodeCoordinates lo) (decodeCoordinates hi) := by
    rw [hfactor]
    unfold boxMass zMass
    ring
  rw [heq] at hraw
  exact hraw

def boundaryHigh (lo hi : Fin 3 → ℤ) : ℤ :=
  clippedHigh literalCheckedBlockTable lo hi (authorCapLower lo hi)

def boundaryCost160 (lo hi : Fin 3 → ℤ) : ℤ :=
  up (boundaryHigh lo hi*(boundaryMass lo hi).hi) P160

/-- Genuine boundary-leaf analytic payment: the cap bound, two table queries,
two logarithms, mass and final integer ceiling are all supplied internally. -/
theorem boundary_integral_le_cost160 (lo hi : Fin 3 → ℤ) (g : SourceBox lo hi) :
    (∫ t in compactRegion ∩ Icc (decodeCoordinates lo) (decodeCoordinates hi),
      compactKernel t)≤value (boundaryCost160 lo hi) := by
  have hf := author_boundary_clipped_integral literalCheckedBlockTable lo hi
    (decodeCoordinates lo) (decodeCoordinates hi)
    (decodeCoordinates_eq_original_scale lo) (decodeCoordinates_eq_original_scale hi)
    (sourceBox_positive g) (sourceBox_width g) (fun i => (g.width i).le)
    g.muCut (sourceBox_residual g)
  have hm := (boundaryMass_encloses lo hi g).2
  have hh : 0≤value (boundaryHigh lo hi) := clippedHigh_nonneg _ _ _ _
  calc
    (∫ t in compactRegion ∩ Icc (decodeCoordinates lo) (decodeCoordinates hi),
        compactKernel t)≤
        4*boxMass (decodeCoordinates lo) (decodeCoordinates hi)*value (boundaryHigh lo hi) := hf
    _≤value (boundaryMass lo hi).hi*value (boundaryHigh lo hi) :=
      mul_le_mul_of_nonneg_right hm hh
    _=value (boundaryHigh lo hi)*value (boundaryMass lo hi).hi := by ring
    _≤value (boundaryCost160 lo hi) := literal_product_UP_ge _ _

/-- Exact units bridge. This is an arithmetic comparison with a PARTICULAR
original P80 charge, not an identification of the two producers' outputs. -/
theorem cost160_le_charge80 (p q : ℤ) (h : p≤q*2^80) :
    value p≤(q:ℝ)/(2:ℝ)^80 := by
  calc
    value p≤value (q*2^80) := value_mono h
    _=(q:ℝ)/(2:ℝ)^80 := by
      unfold value P160
      push_cast
      rw [show (160:ℕ)=80+80 by omega,pow_add]
      field_simp <;> ring

theorem boundary_integral_le_original_charge (lo hi : Fin 3 → ℤ)
    (g : SourceBox lo hi) (q : ℤ) (hcharge : boundaryCost160 lo hi≤q*2^80) :
    (∫ t in compactRegion ∩ Icc (decodeCoordinates lo) (decodeCoordinates hi),
      compactKernel t)≤(q:ℝ)/(2:ℝ)^80 :=
  (boundary_integral_le_cost160 lo hi g).trans (cost160_le_charge80 _ _ hcharge)

/-- This is source geometry plus an integer comparison, not an assumed
integral certificate. The whole original list still needs these witnesses. -/
def BoundaryChargeWitness (s : Set Point) (q : ℤ) : Prop :=
  ∃ lo hi : Fin 3 → ℤ,
    s=compactRegion ∩ Icc (decodeCoordinates lo) (decodeCoordinates hi) ∧
    SourceBox lo hi ∧ boundaryCost160 lo hi≤q*2^80

theorem positional_boundary_payment (cells : List (Set Point)) (charges : List ℤ)
    (h : List.Forall₂ BoundaryChargeWitness cells charges) :
    List.Forall₂ (fun s q => (∫ t in s,compactKernel t)≤(q:ℝ)/(2:ℝ)^80)
      cells charges := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hhead htail ih =>
      apply List.Forall₂.cons _ ih
      obtain ⟨lo,hi,rfl,g,hcharge⟩ := hhead
      exact boundary_integral_le_original_charge lo hi g _ hcharge

/-- The existing positional binder is consumed without sorting, deduplicating
or dropping closed leaves. No assertion is made that all actual leaves have
the clipped bound below their original, possibly tighter, stored charge. -/
theorem attachCharges_local_of_boundary_witnesses (tree : ClosedCutTree)
    (charges : List ℤ) (hsize : charges.length=splitCount tree+1)
    (h : List.Forall₂ BoundaryChargeWitness (closedLeaves tree compactRegion) charges) :
    LocalChargeBound (attachCharges tree charges hsize).val compactRegion := by
  apply (attachCharges_local_iff tree charges hsize compactRegion).2
  exact positional_boundary_payment _ _ h

/-- A concrete ORIGINAL seed, not a manufactured replacement test box.
It crosses both order walls and is not an OrdinaryGrid. No table evaluation
or logarithmic finite replay is needed to establish its primitive geometry. -/
theorem original_seed0_sourceBox : SourceBox (![H,H,H]) (![M,M,2*H]) := by
  constructor
  · intro i; fin_cases i <;> norm_num
  · intro i; fin_cases i <;> norm_num [H,M,R]
  · intro i; fin_cases i <;> norm_num [H,M]
  · exact Or.inl le_rfl

/-- Closed theorem for the first actual source root, with no enclosure or
integral assumptions. Its cost stays symbolic; no endpoint has been replayed. -/
theorem original_seed0_boundary_integral :
    (∫ t in rootCell (recordAt ⟨0,by omega⟩),compactKernel t)≤
      value (boundaryCost160 (![H,H,H]) (![M,M,2*H])) := by
  change (∫ t in compactRegion ∩ Icc (decodeCoordinates (![H,H,H]))
    (decodeCoordinates (![M,M,2*H])),compactKernel t)≤_
  exact boundary_integral_le_cost160 (![H,H,H]) (![M,M,2*H]) original_seed0_sourceBox

end
end ImbalancedChen.P2OriginalCompactBoundaryChargeSourceOnly
