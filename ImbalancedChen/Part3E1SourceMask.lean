import ImbalancedChen.Part3E1FiniteCauchy

/-!
# Extending the finite E1 carriers by zero

The coefficient cutoffs preserve both ordered copies of the factor and
sample indices, including all original primitive gates.
-/

namespace ImbalancedChen.Part3.E1Finite

noncomputable section

open Classical Finset
open scoped BigOperators

private theorem primitive_eq_filter_of_subset (a : ℤ) {S T : Finset ℕ} (hST : S ⊆ T) :
    primitive a S = (primitive a T).filter (fun n => n ∈ S) := by
  ext n
  simp only [primitive, mem_filter]
  exact ⟨fun h => ⟨⟨hST h.1, h.2⟩, h.1⟩, fun h => ⟨h.2, h.1.2⟩⟩

/-- Extend the source carriers with the same coefficient masks on each
of the two ordered copies. The frequency carrier and modulus weights are
identical after the extension. -/
theorem source_subsets_eq_zero_extend (Q₀ Q₁ R₀ R₁ N₀ N₁ : Finset ℕ)
    (hQ : Q₀ ⊆ Q₁) (hR : R₀ ⊆ R₁) (hN : N₀ ⊆ N₁) (H : Finset ℤ)
    (a : ℤ) (M : ℝ) (ψhat : ℝ → ℂ) (lambda : ℕ → ℕ → ℂ) (alpha : ℕ → ℂ) :
    source Q₀ R₀ N₀ H a M ψhat lambda alpha =
      source Q₁ R₁ N₁ H a M ψhat
        (fun q r => if q ∈ Q₀ ∧ r ∈ R₀ then lambda q r else 0)
        (fun n => if n ∈ N₀ then alpha n else 0) := by
  have hNF : N₀ = N₁.filter (fun n => n ∈ N₀) := by
    ext n
    simp only [mem_filter]
    exact ⟨fun hn => ⟨hN hn, hn⟩, And.right⟩
  unfold source
  conv_lhs =>
    rw [primitive_eq_filter_of_subset a hQ, primitive_eq_filter_of_subset a hR, hNF]
  simp_rw [sum_filter]
  apply sum_congr rfl
  intro q _
  by_cases hq : q ∈ Q₀
  · rw [if_pos hq]
    apply sum_congr rfl
    intro n _
    by_cases hn : n ∈ N₀
    · rw [if_pos hn]
      apply sum_congr rfl
      intro s _
      by_cases hs : s ∈ R₀
      · rw [if_pos hs]
        apply sum_congr rfl
        intro n' _
        by_cases hn' : n' ∈ N₀
        · rw [if_pos hn']
          apply sum_congr rfl
          intro r _
          by_cases hr : r ∈ R₀
          · rw [if_pos hr]
            exact sum_congr rfl (fun h _ => by simp only [hq, hn, hs, hn', hr, and_self, if_true])
          · simp [hq, hn, hs, hn', hr]
        · simp [hn']
      · simp [hq, hs]
    · simp [hn]
  · simp [hq]

end

end ImbalancedChen.Part3.E1Finite
