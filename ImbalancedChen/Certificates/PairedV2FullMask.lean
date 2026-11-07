import ImbalancedChen.Certificates.PairedV2FullMaskData

namespace ImbalancedChen.Certificates.PairedV2.FullMask

open MeasureTheory Set
open scoped BigOperators Interval

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem firstU_bounds : ∀ i : Fin 186, 321 ≤ firstU i ∧ firstU i < 512 := by
  decide +kernel

/-- Each strip contains exactly the decoded consecutive u-indices. -/
abbrev Row := (i : Fin 186) × Fin (512 - firstU i)

def indices (r : Row) : ℕ × ℕ := (326 + r.1.val, firstU r.1 + r.2.val)

theorem row_count : Fintype.card Row = 17572 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  decide +kernel

theorem indices_injective : Function.Injective indices := by
  rintro ⟨i,j⟩ ⟨k,l⟩ he
  have hi : i = k := Fin.ext (Nat.add_left_cancel (congrArg Prod.fst he))
  subst k
  have hj : j = l := Fin.ext (Nat.add_left_cancel (congrArg Prod.snd he))
  subst l
  rfl

theorem indices_bounds (r : Row) :
    (indices r).1 < 512 ∧ 0 < (indices r).2 ∧ (indices r).2 < 512 := by
  have hi := r.1.isLt
  have hj := r.2.isLt
  have hlo := firstU_bounds r.1
  dsimp [indices]
  omega

/-- Coverage of the complete adopted strip mask, in the actual grid
coordinates.  It is not coverage of merely a source ordinal interval. -/
theorem indices_cover (i j : ℕ) :
    (∃ r : Row, indices r = (i,j)) ↔
      ∃ k : Fin 186, i = 326 + k.val ∧ firstU k ≤ j ∧ j < 512 := by
  constructor
  · rintro ⟨⟨k,l⟩, he⟩
    have hi := congrArg Prod.fst he
    have hj := congrArg Prod.snd he
    have hl := l.isLt
    have hk := firstU_bounds k
    dsimp [indices] at hi hj
    refine ⟨k, hi.symm, ?_, ?_⟩ <;> omega
  · rintro ⟨k, hi, hlo, hhi⟩
    have hlocal : j - firstU k < 512 - firstU k := by omega
    refine ⟨⟨k, ⟨j - firstU k, hlocal⟩⟩, ?_⟩
    apply Prod.ext
    · exact hi.symm
    · dsimp [indices]
      omega

def cutoff (r : Row) : ℚ :=
  min (uLower (indices r).2)
    (3 * (1 - tUpper (indices r).1 - uUpper (indices r).2) / 13)

def support (r : Row) : Set (Fin 4 → ℝ) :=
  openFibreSet (indices r).1 (indices r).2 (cutoff r)

def region : Set (Fin 4 → ℝ) := ⋃ r, support r

theorem supports_pairwise_disjoint : Pairwise (fun r s => Disjoint (support r) (support s)) :=
  openFibreSet_pairwiseDisjoint indices cutoff indices_injective

/-- The full 17572-cell adopted region has exactly one owner per point. -/
theorem region_unique_owner (x : Fin 4 → ℝ) :
    x ∈ region ↔ ∃! r : Row, x ∈ support r :=
  mem_adopted_fibre_union_iff_existsUnique indices cutoff indices_injective x

/-- The unnormalised finite assembly contains all adopted fibres, each
exactly once.  Its numerical bound is a separate certificate obligation. -/
noncomputable def integral : ℝ :=
  ∑ r : Row, pairedLocalIntegral (K : ℝ) a
    (tLower (indices r).1) (tUpper (indices r).1)
    (uLower (indices r).2) (uUpper (indices r).2) (cutoff r)

theorem integral_semantics : integral = ((K : ℝ) / 80) * ∑ r : Row,
    ∫ t in (tLower (indices r).1 : ℝ)..(tUpper (indices r).1 : ℝ),
    ∫ u in (uLower (indices r).2 : ℝ)..(uUpper (indices r).2 : ℝ),
    ∫ z in (a : ℝ)..(cutoff r : ℝ), ∫ w in (a : ℝ)..z,
      1 / (t * u * z ^ 2 * w) := by
  simp only [integral, pairedLocalIntegral, pairedFibreKernel_eq, Finset.mul_sum]

end ImbalancedChen.Certificates.PairedV2.FullMask
