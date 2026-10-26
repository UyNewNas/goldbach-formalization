import ImbalancedChen.P5U7ActualRoughTargetExclusion

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Reverse reconstruction of the ACTUAL original U7 prime/ordered-semiprime
row from the rough mother. Unit, inclusive endpoint and target-divisor
losses are retained explicitly. Ordered repeated terminal factors remain
legal; outer marked labels are unchanged and no half-factor is inserted.
-/

namespace ImbalancedChen

noncomputable section

open LiLiuPrereqBuchstab
open scoped BigOperators
open Classical

def p5U7ActualEndpoint (N : ℕ) (t : ℕ × ℕ) : Finset ℕ :=
  (roughNumbers ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) (t.2 : ℝ)).filter
    fun n => t.1 * t.2 * n = N

theorem p5U7ActualEndpoint_card_le_one {N : ℕ} {t : ℕ × ℕ}
    (hb : 0 < t.1 * t.2) : (p5U7ActualEndpoint N t).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro n hn m hm
  have hnE := (Finset.mem_filter.mp hn).2
  have hmE := (Finset.mem_filter.mp hm).2
  exact Nat.eq_of_mul_eq_mul_left hb (hnE.trans hmE.symm)

theorem p5U7Actual_rough_row_le_source_add_losses {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))) :
    (roughCount ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) (t.2 : ℝ) : ℝ) ≤
      ((p5U7MassPrimeFibre N (t.1 * t.2) t.2).card : ℝ) +
      ((p5U7MassSemiprimePairs N t).card : ℝ) +
      ((p5U7ActualBadRough N ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) (t.2 : ℝ)).card : ℝ) + 2 := by
  let R := roughNumbers ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) (t.2 : ℝ)
  let P := p5U7MassPrimeFibre N (t.1 * t.2) t.2
  let S := p5U7MassSemiprimePairs N t
  let Q := S.image (fun u : ℕ × ℕ => u.1 * u.2)
  let B := p5U7ActualBadRough N ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) (t.2 : ℝ)
  let E := p5U7ActualEndpoint N t
  have hg := p5U7Mass_outer_geometry ht
  have hbR : (0 : ℝ) < ((t.1 * t.2 : ℕ) : ℝ) := by exact_mod_cast hg.1
  have hcover : R ⊆ P ∪ Q ∪ B ∪ ({1} : Finset ℕ) ∪ E := by
    intro n hn
    obtain ⟨hn0, hnx, hnrough⟩ := mem_roughNumbers.mp hn
    by_cases hone : n = 1
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (by simp only [hone, Finset.mem_singleton]))))
    by_cases hcop : Nat.Coprime n N
    · have hmulR : ((t.1 * t.2 : ℕ) : ℝ) * (n : ℝ) ≤ N := by
        have hh := (le_div_iff₀ hbR).mp hnx
        simpa only [mul_comm] using hh
      have hmul : t.1 * t.2 * n ≤ N := by exact_mod_cast hmulR
      by_cases hstrict : t.1 * t.2 * n < N
      · have hsource := p5U7Arithmetic_rough_nonunit_mem_three_or_four ht hn0 hone hcop hstrict hnrough
        have hPQ : n ∈ P ∪ Q := by
          rcases hsource with hprime | ⟨r, s, hprod, hpair⟩
          · exact Finset.mem_union.mpr (Or.inl ((Finset.mem_sigma.mp hprime).2))
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
              ⟨(r,s), (Finset.mem_sigma.mp hpair).2, hprod.symm⟩))
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inl (Finset.mem_union.mpr (Or.inl hPQ)))))
      · have hEq : t.1 * t.2 * n = N := le_antisymm hmul (Nat.le_of_not_gt hstrict)
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hn, hEq⟩))
    · have hnB : n ∈ B := Finset.mem_filter.mpr ⟨hn, hcop⟩
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_union.mpr (Or.inr hnB)))))
  have hR := Finset.card_le_card hcover
  have hPQ := Finset.card_union_le P Q
  have hPQB := Finset.card_union_le (P ∪ Q) B
  have hUnit := Finset.card_union_le (P ∪ Q ∪ B) ({1} : Finset ℕ)
  have hEnd := Finset.card_union_le (P ∪ Q ∪ B ∪ ({1} : Finset ℕ)) E
  have hQ : Q.card ≤ S.card := Finset.card_image_le
  have hE : E.card ≤ 1 := p5U7ActualEndpoint_card_le_one hg.1
  have hOne : ({1} : Finset ℕ).card = 1 := Finset.card_singleton 1
  have hcard : R.card ≤ P.card + S.card + B.card + 2 := by omega
  change (R.card : ℝ) ≤ (P.card : ℝ) + (S.card : ℝ) + (B.card : ℝ) + 2
  exact_mod_cast hcard

/-- Both directions concern the SAME actual row and retain the exact
original source multiplicity. The reverse correction is now quantitative. -/
theorem p5U7Actual_rough_row_gap_le {N : ℕ} (hN : 0 < N) {t : ℕ × ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))) :
    0 ≤ (roughCount ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) (t.2 : ℝ) : ℝ) -
      (((p5U7MassPrimeFibre N (t.1 * t.2) t.2).card : ℝ) + ((p5U7MassSemiprimePairs N t).card : ℝ)) ∧
    (roughCount ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) (t.2 : ℝ) : ℝ) -
      (((p5U7MassPrimeFibre N (t.1 * t.2) t.2).card : ℝ) + ((p5U7MassSemiprimePairs N t).card : ℝ)) ≤
        (Real.log (N : ℝ) / Real.log 2) *
          (((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) / (t.2 : ℝ)) + 2 := by
  have hg := p5U7Mass_outer_geometry ht
  have hc := (Finset.mem_filter.mp ht).1
  have hp := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).2).2.1
  have hz : (0 : ℝ) < t.2 := by exact_mod_cast hp.pos
  have hx : (0 : ℝ) ≤ (N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ) := by positivity
  have hbad := p5U7ActualBadRough_card_le_log hN hx hz
  have hcover := p5U7Actual_rough_row_le_source_add_losses ht
  exact ⟨sub_nonneg.mpr (p5U7Mass_row_le_roughCount ht), by linarith only [hbad, hcover]⟩

end

end ImbalancedChen
