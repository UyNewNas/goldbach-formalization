import ImbalancedChen.P5ActualHBMediumBranchPartition
import ImbalancedChen.Part3TwoLongActualHBShortMass

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

Five original finite-geometry declarations from
P4BOriginalNoMediumPairRows, in their original namespace. Only
`group_has_long` changes visibility from private to public. Declaration
statements and proof bodies are otherwise preserved byte for byte.
The complementary old-provider postimage is recorded beside this file.
-/
namespace ImbalancedChen.P4BOriginalNoMediumPairRows
noncomputable section
open Classical
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.ActualHBMediumBranchPartition (Medium longBlocks)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open Part3.TwoLongActualHBShortMass (ShortPositions)

def longPositions {t : ℕ} (B : ℝ) (bs : Fin t → Block) : Finset (Fin t) :=
  Finset.univ.filter (fun i => B < (lower (bs i) : ℝ))

private theorem long_length_sum (B : ℝ) : ∀ t (bs : Fin t → Block),
    (longBlocks B (List.ofFn bs)).length =
      ∑ i : Fin t, if B < (lower (bs i) : ℝ) then 1 else 0 := by
  intro t
  induction t with
  | zero => intro bs; simp [longBlocks]
  | succ t ih =>
      intro bs
      have H := ih (fun i => bs i.succ)
      simp only [longBlocks] at H
      by_cases h : B < (lower (bs 0) : ℝ) <;>
        simp [longBlocks,List.ofFn_succ,Fin.sum_univ_succ,h,H,Nat.add_comm]

theorem long_card_eq_length {t : ℕ} (B : ℝ) (bs : Fin t → Block) :
    (longPositions B bs).card = (longBlocks B (List.ofFn bs)).length := by
  rw [long_length_sum]
  simp [longPositions,Finset.card_eq_sum_ones,Finset.sum_filter]

theorem short_card {t : ℕ} (i j : Fin t) (hij : i ≠ j) :
    Fintype.card (ShortPositions i j) + 2 = t := by
  let E : ShortPositions i j ≃ {a : Fin t // a ∈ (Finset.univ \ {i,j})} :=
    Equiv.subtypeEquivRight (fun a => by simp [not_or])
  have H := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ ({i,j} : Finset (Fin t)))
  have hc : Fintype.card (ShortPositions i j) = (Finset.univ \ {i,j}).card := by
    simpa using Fintype.card_congr E
  simpa [hc,hij] using H

theorem group_has_long {t : ℕ} (ht : t ≤ 6) {A B : ℝ} (hA : 1 ≤ A)
    (bs : Fin t → Block) (n : Fin t → ℕ)
    (hn : ∀ i, (n i : ℝ) ≤ 2*(lower (bs i) : ℝ))
    (hbranch : ∀ i, ¬Medium A B (bs i))
    (hlarge : 64*A^6 < (completeProduct n : ℝ)) :
    ∃ i : Fin t, B < (lower (bs i) : ℝ) := by
  by_contra! hnot
  have hlo (i : Fin t) : (lower (bs i) : ℝ) < A := by
    by_contra! hh
    exact hbranch i ⟨hh,hnot i⟩
  have hprod : (completeProduct n : ℝ) ≤ (2*A)^t := by
    calc
      _ = ∏ i : Fin t, (n i : ℝ) := by simp [completeProduct]
      _ ≤ ∏ _i : Fin t, 2*A := Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
        (fun i _ => (hn i).trans (by linarith [hlo i]))
      _ = _ := by simp
  have hpow := pow_le_pow_right₀ (by linarith : 1 ≤ 2*A) ht
  have heq : (2*A)^6 = 64*A^6 := by ring
  linarith

end
end ImbalancedChen.P4BOriginalNoMediumPairRows
