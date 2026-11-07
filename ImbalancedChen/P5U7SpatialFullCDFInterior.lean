import ImbalancedChen.P5U7SpatialNativeRoughErrors

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Literal full spatial-CDF interior and its actual marked collar. The mixed
rough-good interior is identified with the prime and ordered-semiprime
physical cutoff families. Its lost CDF mass is bounded by the original-N
joint arithmetic collar, preserving every marked label and endpoint.
-/
namespace ImbalancedChen
noncomputable section
open scoped BigOperators
open Classical

def p5U7SpatialInteriorSemiprimeMass (N M : ℕ) (eta : ℝ) : ℝ :=
  (((p5U7SpatialFour N M).filter (fun x => x.1 ∈ p5U7InteriorSelector N eta)).card : ℝ)

theorem p5U7SpatialInteriorSemiprimeMass_eq_window_sum {N M : ℕ} (hMN : M ≤ N) (eta : ℝ) :
    p5U7SpatialInteriorSemiprimeMass N M eta =
      ∑ t ∈ p5U7InteriorSelector N eta,((p5U7MassSemiprimeWindow N M t).card : ℝ) := by
  have hset : (p5U7SpatialFour N M).filter (fun x => x.1 ∈ p5U7InteriorSelector N eta) =
      (p5U7InteriorSelector N eta).sigma (p5U7MassSemiprimeWindow N M) := by
    rw [p5U7SpatialFour_eq_mixed_windows hMN]
    ext x
    constructor
    · intro hx
      obtain ⟨hx,hi⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_sigma.mpr ⟨hi,(Finset.mem_sigma.mp hx).2⟩
    · intro hx
      obtain ⟨hi,hu⟩ := Finset.mem_sigma.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨(Finset.mem_filter.mp hi).1,hu⟩,hi⟩
  rw [p5U7SpatialInteriorSemiprimeMass,hset]
  simp only [Finset.card_sigma,Nat.cast_sum]

/-- The actual mixed rough-good source is EXACTLY both physical cutoff
families on the same marked interior, including repeated terminal factors. -/
theorem p5U7SpatialInteriorFullMass_eq_components {N M : ℕ} (hMN : M ≤ N) (eta : ℝ) :
    p5U7SpatialInteriorFullMass N M eta =
      p5U7SpatialInteriorPrimeMass N M eta+p5U7SpatialInteriorSemiprimeMass N M eta := by
  rw [p5U7SpatialInteriorFullMass,p5U7SpatialInteriorPrimeMass_eq_window_sum hMN,
    p5U7SpatialInteriorSemiprimeMass_eq_window_sum hMN,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have h := p5U7SpatialGoodRough_card_eq_components hMN (Finset.mem_filter.mp ht).1
  exact_mod_cast h

theorem p5U7SpatialSemiprimeMass_interior_gap (N M : ℕ) (eta : ℝ) :
    0 ≤ ((p5U7SpatialFour N M).card : ℝ)-p5U7SpatialInteriorSemiprimeMass N M eta ∧
      ((p5U7SpatialFour N M).card : ℝ)-p5U7SpatialInteriorSemiprimeMass N M eta ≤
        ((p5U7ActualSemiprimeCollar N eta).card : ℝ) := by
  let K := (p5U7SpatialFour N M).filter (fun x => x.1 ∉ p5U7InteriorSelector N eta)
  have hsplit := Finset.card_filter_add_card_filter_not (s := p5U7SpatialFour N M)
    (p := fun x => x.1 ∈ p5U7InteriorSelector N eta)
  have hsplitR : p5U7SpatialInteriorSemiprimeMass N M eta+(K.card : ℝ) =
      ((p5U7SpatialFour N M).card : ℝ) := by exact_mod_cast hsplit
  have hsub : K ⊆ p5U7ActualSemiprimeCollar N eta := by
    intro x hx
    obtain ⟨hx,hn⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,hn⟩
  have hcard : (K.card : ℝ) ≤ ((p5U7ActualSemiprimeCollar N eta).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact ⟨by linarith only [hsplitR,Nat.cast_nonneg K.card],by linarith only [hsplitR,hcard]⟩

/-- The actual full spatial CDF collar is paid by the same original-N
joint collar used in eta-before-N removal. This is an arithmetic subset
argument; no analytic null-wall deletion occurs. -/
theorem p5U7SpatialFullCDF_interior_gap {N M : ℕ} (hMN : M ≤ N) (eta : ℝ) :
    0 ≤ (∑ m ∈ Finset.range M,p5U7ArithmeticProductWeight N m)-p5U7SpatialInteriorFullMass N M eta ∧
      (∑ m ∈ Finset.range M,p5U7ArithmeticProductWeight N m)-p5U7SpatialInteriorFullMass N M eta ≤
        p5U7ActualComponentCollarMass N eta := by
  have hp := p5U7SpatialPrimeMass_interior_gap N M eta
  have hs := p5U7SpatialSemiprimeMass_interior_gap N M eta
  simp only [p5U7ArithmeticProductWeight_eq_components,Finset.sum_add_distrib]
  rw [p5U7SpatialPrimeProductWeight_mass,p5U7SpatialSemiprimeProductWeight_mass,
    p5U7SpatialInteriorFullMass_eq_components hMN]
  unfold p5U7ActualComponentCollarMass
  constructor <;> linarith only [hp.1,hp.2,hs.1,hs.2]

end
end ImbalancedChen
