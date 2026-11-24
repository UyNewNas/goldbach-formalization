import ImbalancedChen.P2Winner9CompleteSeedVertices
import ImbalancedChen.P2Winner9SelectedRowAnalyticCaps

/-! Uniform analytic guards on the original Winner9 seed vertex table. -/

namespace ImbalancedChen.P2Winner9SeedVertexAnalyticGuards

open P2Winner9CompleteSeedVertices
open P2Winner9SelectedRowRealJacobian
open P2Winner9SelectedRowIntegerScales
open P2Winner9SelectedRowAnalyticCaps (affine_lower affine_upper)
open P2Winner9PhysicalAffineTransfer
open P2Winner9PhysicalVertexInterpolation

abbrev VertexIndex := Fin 201

def originalPoint (v : VertexIndex) : Fin 8 → ℚ := coordinates[v.val]!

def constantFamily (p : Fin 8 → ℚ) : RationalVertices := fun _ => p

private def guardAt (n : ℕ) : Prop :=
  let v := constantFamily coordinates[n]!
  0 ≤ rawGap v 0 ∧ rawR v 0 ≤ 153 / 256 ∧ rawM v 0 ≤ 299 / 500 ∧
    ∀ j : Fin 10, (53 / 13824 : ℚ) ≤ rawFactor v 0 j

private def chunkSize (c : Fin 7) : ℕ := min 32 (201 - 32 * c.val)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
private theorem guards_chunk (c : Fin 7) : ∀ i : Fin (chunkSize c),
    guardAt (32 * c.val + i.val) := by
  fin_cases c <;> unfold guardAt chunkSize <;> decide +kernel

/-- Every original vertex has nonnegative physical gap, respects both raw
caps, and gives the original lower cutoff for each of the ten factors. -/
theorem original_vertex_analytic_guards : ∀ v : VertexIndex,
    0 ≤ rawGap (constantFamily (originalPoint v)) 0 ∧
      rawR (constantFamily (originalPoint v)) 0 ≤ 153 / 256 ∧
      rawM (constantFamily (originalPoint v)) 0 ≤ 299 / 500 ∧
      ∀ j : Fin 10, (53 / 13824 : ℚ) ≤ rawFactor (constantFamily (originalPoint v)) 0 j := by
  intro v
  change guardAt v.val
  let c : Fin 7 := ⟨v.val / 32, by have := v.isLt; omega⟩
  have he : 32 * c.val + v.val % 32 = v.val := Nat.div_add_mod v.val 32
  have hi : v.val % 32 < chunkSize c := by
    apply Nat.lt_min.mpr
    exact ⟨Nat.mod_lt _ (by decide), by have := v.isLt; omega⟩
  exact he ▸ guards_chunk c ⟨v.val % 32, hi⟩

/-- Every simplex assembled from the original table inherits the same gap,
caps, and factor bounds throughout its closed physical support. -/
theorem original_support_analytic_guards (v : RationalVertices) (ids : Fin 9 → VertexIndex)
    (h : ∀ i, v i = originalPoint (ids i)) {z : Ambient} (hz : z ∈ sourceSupport v) :
    0 ≤ physicalGap z ∧ physicalR z ≤ 153 / 256 ∧ physicalM z ≤ 299 / 500 ∧
      ∀ j : Fin 10, (53 / 13824 : ℝ) ≤ physicalFactor j z := by
  have hv (i : Fin 9) :
      0 ≤ rawGap v i ∧ rawR v i ≤ 153 / 256 ∧ rawM v i ≤ 299 / 500 ∧
        ∀ j : Fin 10, (53 / 13824 : ℚ) ≤ rawFactor v i j := by
    simpa [rawFactor, rawGap, rawR, rawM, rawSum, constantFamily, h i] using
      original_vertex_analytic_guards (ids i)
  obtain ⟨x, hx, rfl⟩ := hz
  refine ⟨?_, ?_, ?_, fun j => ?_⟩
  · rw [physicalGap_vertexMap]
    apply affine_lower hx
    intro i
    rw [← rawGap_cast]
    exact_mod_cast (hv i).1
  · rw [physicalR_vertexMap]
    apply affine_upper hx
    intro i
    rw [← rawR_cast]
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_le.mpr (hv i).2.1 : (rawR v i : ℝ) ≤ ((153 / 256 : ℚ) : ℝ))
  · rw [physicalM_vertexMap]
    apply affine_upper hx
    intro i
    rw [← rawM_cast]
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_le.mpr (hv i).2.2.1 : (rawM v i : ℝ) ≤ ((299 / 500 : ℚ) : ℝ))
  · rw [physicalFactor_vertexMap]
    apply affine_lower hx
    intro i
    rw [← rawFactor_cast]
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_le.mpr ((hv i).2.2.2 j) : ((53 / 13824 : ℚ) : ℝ) ≤ (rawFactor v i j : ℝ))

end ImbalancedChen.P2Winner9SeedVertexAnalyticGuards
