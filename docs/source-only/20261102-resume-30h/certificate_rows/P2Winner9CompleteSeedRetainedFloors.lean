import ImbalancedChen.P2Winner9CompleteSeedGapReserve
import ImbalancedChen.P2Winner9CompleteSeedAnalyticPorts
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual original cap bounds are extended from the 201 vertices to every
complete-family support. The common inward crop has strict original cap
separation, and the already proved two Q96 rows survive under ONE common
allowance. This is not all-row selected-floor soundness, the remaining
97-policy licence, a triangulation proof or current-c assembly.
-/

namespace ImbalancedChen.P2Winner9CompleteSeedRetainedFloors

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2Winner9CompleteSeedData
open ImbalancedChen.P2Winner9CompleteSeedPositiveDomains
open ImbalancedChen.P2Winner9CompleteSeedAnalyticPorts
open ImbalancedChen.P2Winner9CompleteSeedGapReserve
open ImbalancedChen.P2Winner9SelectedRowRealJacobian
open ImbalancedChen.P2Winner9SelectedRowIntegerScales
open ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9PhysicalVertexInterpolation

theorem all_actual_cap_upper (i : RowIndex) {z : Ambient} (hz : z ∈ actualSupport i) :
    physicalR z ≤ 153 / 256 ∧ physicalM z ≤ 299 / 500 := by
  have hv (k : Fin 9) :
      physicalR (realVertices (physicalVertices i) k) ≤ 153 / 256 ∧
      physicalM (realVertices (physicalVertices i) k) ≤ 299 / 500 := by
    let v : VertexIndex := ⟨(entry i).vertexIds k, vertex_id_bound i k⟩
    have he : physicalVertices i k = originalPoint v := actual_vertex_lookup i k
    have hR : rawR (physicalVertices i) k = rawR (constantFamily (originalPoint v)) 0 := by
      simp only [rawR, constantFamily, he]
    have hM : rawM (physicalVertices i) k = rawM (constantFamily (originalPoint v)) 0 := by
      simp only [rawM, constantFamily, he]
    constructor
    · rw [← rawR_cast, hR]
      exact_mod_cast (original_vertex_analytic_guards.2 v).2.1
    · rw [← rawM_cast, hM]
      exact_mod_cast (original_vertex_analytic_guards.2 v).2.2
  rcases hz with ⟨x, hx, rfl⟩
  constructor
  · rw [physicalR_vertexMap]
    exact affine_upper hx _ _ (fun k => (hv k).1)
  · rw [physicalM_vertexMap]
    exact affine_upper hx _ _ (fun k => (hv k).2)

/-- The middle strict inequality in the original eighth-saving display,
with its quantitative margin and the SAME physical last coordinate t8.
The other square/cube/ancestral licence inequalities are not inferred. -/
theorem retained_original_cap_separation (i : RowIndex) {δ : ℝ} (hδ : 0 ≤ δ)
    {z : Ambient} (hz : z ∈ retainedSupport i δ) :
    0 < z 7 ∧ physicalR z < physicalM z ∧
      (physicalR z - coordinateSum z) / z 7 + δ / z 7 <
        (physicalM z - coordinateSum z) / z 7 := by
  have hmem := (mem_retainedSupport_iff i δ z).1 hz
  have ht : 0 < z 7 := by
    simpa only [physicalFactor_succ_succ] using
      ((all_actual_support_positive i hmem.1).2 (7 : Fin 8).succ.succ).2
  have hgap : δ < physicalM z - physicalR z := hmem.2
  refine ⟨ht, by linarith, ?_⟩
  rw [← add_div]
  apply (div_lt_div_iff_of_pos_right ht).2
  linarith

theorem row21_full_floor :
    ((entry row21Index).mixedSelected : ℝ) / 79228162514264337593543950336 ≤
      fullMass row21Index := by
  exact actual_row21_selected_floor

theorem row22_full_floor :
    ((entry row22Index).mixedSelected : ℝ) / 79228162514264337593543950336 ≤
      fullMass row22Index := by
  exact actual_row22_selected_floor

theorem original_row_indices_ne : row21Index ≠ row22Index := by
  intro h
  have hv := congrArg Fin.val h
  norm_num [row21Index, row22Index] at hv

/-- Both old analytic rows use one family reserve, never one reserve EACH. -/
theorem two_row_loss_le_family (δ : ℝ) :
    lostMass row21Index δ + lostMass row22Index δ ≤ familyLoss δ := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ ({row21Index, row22Index} : Finset RowIndex))
    (fun i _ _ => lostMass_nonneg i δ)
  simpa only [Finset.sum_pair original_row_indices_ne] using h

/-- F's genuine T10/Jensen/full-Q6 physical floors remain valid after the
same actual inward operation used on every one of the 11026 rows.
The right side is a sum of two original-domain integrals, not an unproved
disjoint-union integral or either of the ledger-slot21/22 total gains. -/
theorem two_original_floors_after_common_crop {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 ≤ δ) (hsmall : δ ≤ reserveCutoff ε) :
    (((entry row21Index).mixedSelected : ℝ) / 79228162514264337593543950336 +
      ((entry row22Index).mixedSelected : ℝ) / 79228162514264337593543950336) - ε <
        retainedMass row21Index δ + retainedMass row22Index δ := by
  rw [retainedMass_eq, retainedMass_eq]
  have htotal := common_gap_reserve hε hδ hsmall
  have hpair := two_row_loss_le_family δ
  linarith [row21_full_floor, row22_full_floor]

/-- Explicit common positive margin and reserve for the complete original
family, with the two established source floors attached as consumers. -/
theorem exists_common_margin_with_original_floors {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ familyLoss δ < ε ∧
      (∀ i : RowIndex, ∀ z ∈ retainedSupport i δ,
        physicalR z < physicalM z) ∧
      (((entry row21Index).mixedSelected : ℝ) / 79228162514264337593543950336 +
        ((entry row22Index).mixedSelected : ℝ) / 79228162514264337593543950336) - ε <
          retainedMass row21Index δ + retainedMass row22Index δ := by
  let δ := reserveCutoff ε
  have hδ : 0 < δ := reserveCutoff_pos hε
  refine ⟨δ, hδ, common_gap_reserve hε hδ.le le_rfl, ?_,
    two_original_floors_after_common_crop hε hδ.le le_rfl⟩
  intro i z hz
  exact (retained_original_cap_separation i hδ.le hz).2.1

end

end ImbalancedChen.P2Winner9CompleteSeedRetainedFloors
