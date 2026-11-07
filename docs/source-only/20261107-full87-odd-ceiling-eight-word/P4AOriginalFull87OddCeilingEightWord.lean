import ImbalancedChen.P4AOriginalFull87HistoricalCapMargin
import ImbalancedChen.P4AOriginalFull87RankNineHistoryRisk
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4: identify the literal finite historical odd-square tests on an
eight-prime STRICTLY ordered word. This is the combinatorial part of
the missing bridge between the physical Rosser history ceiling and
the original four 3*t_j source inequalities.

The word is the real selectedPrefix storage order: youngest/smallest
first. There is no setification of any first-exit occurrence, and
the toFinset operation below is used ONLY inside the original
literal historical-square predicate. Its Nodup property is derived
from the strict inequalities, not assumed as a replacement policy.

This packet does not assert exponentiation from primeHistoryLogCoordinates
to the four gates, J < parent, a numeric crossing invoice, or reserve
payment. The proof bodies below are source candidates; elaboration has
not been run.
-/

namespace ImbalancedChen.P4AOriginalFull87OddCeilingEightWord
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87RankNineHistoryRisk
  (historyOddSquareTerms historyOddSquareCeiling)

/-- An upper suffix is EXACTLY the literal order filter, provided
the omitted prefix is smaller and every suffix element is above the
cut. No primality, Rosser gate, or new source certificate is assumed. -/
private theorem ordered_filter_append
    (pre suf : List ℕ) (cut : ℕ)
    (hpre : ∀ x ∈ pre, x < cut)
    (hsuf : ∀ x ∈ suf, cut ≤ x) :
    (pre ++ suf).toFinset.filter (fun x => cut ≤ x) = suf.toFinset := by
  ext x
  simp only [Finset.mem_filter, List.mem_toFinset, List.mem_append]
  constructor
  · rintro ⟨hx, hcut⟩
    rcases hx with hp | hs
    · exact ((not_le_of_gt (hpre x hp)) hcut).elim
    · exact hs
  · intro hs
    exact ⟨Or.inr hs, hsuf x hs⟩

/-- A local finite-list cardinality argument, so the parity
calculations do not depend on an unverified toFinset-card lemma name. -/
private theorem card_toFinset_of_nodup (xs : List ℕ)
    (hn : xs.Nodup) : xs.toFinset.card = xs.length := by
  induction xs with
  | nil => simp
  | cons x ys ih =>
      have hnot : x ∉ ys := (List.nodup_cons.mp hn).1
      have htail : ys.Nodup := (List.nodup_cons.mp hn).2
      simp only [List.toFinset_cons, List.length_cons]
      rw [Finset.card_insert_of_not_mem (by simpa using hnot)]
      exact congrArg Nat.succ (ih htail)

/-- The eight finite filters include EXACTLY 8,7,...,1 distinct
history entries. Positions of odd cardinality are p6,p4,p2,p0,
not p7,p5,p3,p1. Each equality follows from the same word,
rather than from an abstract equivalence supplied as a premise. -/
theorem actual_eight_odd_square_terms
    (p0 p1 p2 p3 p4 p5 p6 p7 : ℕ)
    (h01 : p1 < p0) (h12 : p2 < p1)
    (h23 : p3 < p2) (h34 : p4 < p3)
    (h45 : p5 < p4) (h56 : p6 < p5)
    (h67 : p7 < p6) :
    historyOddSquareTerms [p7,p6,p5,p4,p3,p2,p1,p0] =
      [0,
       ((([p6,p5,p4,p3,p2,p1,p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) * (p6 : ℝ)^2,
       0,
       ((([p4,p3,p2,p1,p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) * (p4 : ℝ)^2,
       0,
       ((([p2,p1,p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) * (p2 : ℝ)^2,
       0,
       ((([p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) * (p0 : ℝ)^2] := by
  let H : List ℕ := [p7,p6,p5,p4,p3,p2,p1,p0]
  have hcut7 : H.toFinset.filter (fun x => p7 ≤ x) = H.toFinset := by
    simpa [H] using
      (ordered_filter_append ([] : List ℕ) [p7,p6,p5,p4,p3,p2,p1,p0] p7
        (by intro x hx; simp at hx)
        (by intro x hx; simp at hx; omega))
  have hcut6 : H.toFinset.filter (fun x => p6 ≤ x) =
      ([p6,p5,p4,p3,p2,p1,p0] : List ℕ).toFinset := by
    simpa [H] using
      (ordered_filter_append [p7] [p6,p5,p4,p3,p2,p1,p0] p6
        (by intro x hx; simp at hx; omega)
        (by intro x hx; simp at hx; omega))
  have hcut5 : H.toFinset.filter (fun x => p5 ≤ x) =
      ([p5,p4,p3,p2,p1,p0] : List ℕ).toFinset := by
    simpa [H] using
      (ordered_filter_append [p7,p6] [p5,p4,p3,p2,p1,p0] p5
        (by intro x hx; simp at hx; omega)
        (by intro x hx; simp at hx; omega))
  have hcut4 : H.toFinset.filter (fun x => p4 ≤ x) =
      ([p4,p3,p2,p1,p0] : List ℕ).toFinset := by
    simpa [H] using
      (ordered_filter_append [p7,p6,p5] [p4,p3,p2,p1,p0] p4
        (by intro x hx; simp at hx; omega)
        (by intro x hx; simp at hx; omega))
  have hcut3 : H.toFinset.filter (fun x => p3 ≤ x) =
      ([p3,p2,p1,p0] : List ℕ).toFinset := by
    simpa [H] using
      (ordered_filter_append [p7,p6,p5,p4] [p3,p2,p1,p0] p3
        (by intro x hx; simp at hx; omega)
        (by intro x hx; simp at hx; omega))
  have hcut2 : H.toFinset.filter (fun x => p2 ≤ x) =
      ([p2,p1,p0] : List ℕ).toFinset := by
    simpa [H] using
      (ordered_filter_append [p7,p6,p5,p4,p3] [p2,p1,p0] p2
        (by intro x hx; simp at hx; omega)
        (by intro x hx; simp at hx; omega))
  have hcut1 : H.toFinset.filter (fun x => p1 ≤ x) =
      ([p1,p0] : List ℕ).toFinset := by
    simpa [H] using
      (ordered_filter_append [p7,p6,p5,p4,p3,p2] [p1,p0] p1
        (by intro x hx; simp at hx; omega)
        (by intro x hx; simp at hx; omega))
  have hcut0 : H.toFinset.filter (fun x => p0 ≤ x) =
      ([p0] : List ℕ).toFinset := by
    simpa [H] using
      (ordered_filter_append [p7,p6,p5,p4,p3,p2,p1] [p0] p0
        (by intro x hx; simp at hx; omega)
        (by intro x hx; simp at hx; omega))
  have hcard7 : H.toFinset.card = 8 := by
    simpa [H] using
      (card_toFinset_of_nodup H (by simp [H, List.nodup_cons]; omega))
  have hcard6 : ([p6,p5,p4,p3,p2,p1,p0] : List ℕ).toFinset.card = 7 := by
    simpa using (card_toFinset_of_nodup [p6,p5,p4,p3,p2,p1,p0]
      (by simp [List.nodup_cons]; omega))
  have hcard5 : ([p5,p4,p3,p2,p1,p0] : List ℕ).toFinset.card = 6 := by
    simpa using (card_toFinset_of_nodup [p5,p4,p3,p2,p1,p0]
      (by simp [List.nodup_cons]; omega))
  have hcard4 : ([p4,p3,p2,p1,p0] : List ℕ).toFinset.card = 5 := by
    simpa using (card_toFinset_of_nodup [p4,p3,p2,p1,p0]
      (by simp [List.nodup_cons]; omega))
  have hcard3 : ([p3,p2,p1,p0] : List ℕ).toFinset.card = 4 := by
    simpa using (card_toFinset_of_nodup [p3,p2,p1,p0]
      (by simp [List.nodup_cons]; omega))
  have hcard2 : ([p2,p1,p0] : List ℕ).toFinset.card = 3 := by
    simpa using (card_toFinset_of_nodup [p2,p1,p0]
      (by simp [List.nodup_cons]; omega))
  have hcard1 : ([p1,p0] : List ℕ).toFinset.card = 2 := by
    simpa using (card_toFinset_of_nodup [p1,p0]
      (by simp [List.nodup_cons]; omega))
  have hcard0 : ([p0] : List ℕ).toFinset.card = 1 := by
    simpa using (card_toFinset_of_nodup [p0] (by simp))
  -- Only the original toFinset historical-square calculation uses
  -- these suffix sets. The physical event history remains the List H.
  dsimp [historyOddSquareTerms]
  simp [hcut7, hcut6, hcut5, hcut4, hcut3, hcut2, hcut1, hcut0,
    hcard7, hcard6, hcard5, hcard4, hcard3, hcard2, hcard1, hcard0]

/-- No historical contribution is discarded: the even-cardinality
positions become literal zero, and the four odd suffix positions
survive in their actual physical order. -/
theorem actual_eight_odd_square_ceiling
    (p0 p1 p2 p3 p4 p5 p6 p7 : ℕ)
    (h01 : p1 < p0) (h12 : p2 < p1)
    (h23 : p3 < p2) (h34 : p4 < p3)
    (h45 : p5 < p4) (h56 : p6 < p5)
    (h67 : p7 < p6) :
    historyOddSquareCeiling [p7,p6,p5,p4,p3,p2,p1,p0] =
      max
        (((( [p6,p5,p4,p3,p2,p1,p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) * (p6 : ℝ)^2)
        (max
          (((( [p4,p3,p2,p1,p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) * (p4 : ℝ)^2)
          (max
            (((( [p2,p1,p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) * (p2 : ℝ)^2)
            (((( [p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) * (p0 : ℝ)^2))) := by
  unfold historyOddSquareCeiling
  rw [actual_eight_odd_square_terms p0 p1 p2 p3 p4 p5 p6 p7
    h01 h12 h23 h34 h45 h56 h67]
  have h6 : 0 ≤
      ((([p6,p5,p4,p3,p2,p1,p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) * (p6 : ℝ)^2 :=
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have h4 : 0 ≤
      ((([p4,p3,p2,p1,p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) * (p4 : ℝ)^2 :=
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have h2 : 0 ≤
      ((([p2,p1,p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) * (p2 : ℝ)^2 :=
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have h0 : 0 ≤
      ((([p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) * (p0 : ℝ)^2 :=
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  simp [h6, h4, h2, h0, max_assoc]

/-- Four concrete, strictly bounded original odd tests suffice for
the EXACT inherited historical ceiling on an ordered eight-prime word.
Unlike a caller-supplied ceiling inequality, the premises are the four
distinct primitive physical gates which can be obtained from the
original Source history exponents after the remaining log bridge. -/
theorem actual_eight_odd_square_ceiling_lt
    (p0 p1 p2 p3 p4 p5 p6 p7 : ℕ)
    (h01 : p1 < p0) (h12 : p2 < p1)
    (h23 : p3 < p2) (h34 : p4 < p3)
    (h45 : p5 < p4) (h56 : p6 < p5)
    (h67 : p7 < p6) (R : ℝ)
    (h6 : ((([p6,p5,p4,p3,p2,p1,p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) * (p6 : ℝ)^2 < R)
    (h4 : ((([p4,p3,p2,p1,p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) * (p4 : ℝ)^2 < R)
    (h2 : ((([p2,p1,p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) * (p2 : ℝ)^2 < R)
    (h0 : ((([p0] : List ℕ).toFinset.prod id : ℕ) : ℝ) * (p0 : ℝ)^2 < R) :
    historyOddSquareCeiling [p7,p6,p5,p4,p3,p2,p1,p0] < R := by
  rw [actual_eight_odd_square_ceiling p0 p1 p2 p3 p4 p5 p6 p7
    h01 h12 h23 h34 h45 h56 h67]
  exact max_lt h6 (max_lt h4 (max_lt h2 h0))

end
end ImbalancedChen.P4AOriginalFull87OddCeilingEightWord
