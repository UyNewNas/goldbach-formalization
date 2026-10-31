import ImbalancedChen.CurrentChenMeanLedger

/-!
# One actual source for the current tenth and eleventh rows

The fourth prime below `H` belongs to row ten. At and above `H` it
belongs to row eleven, whose full upper endpoint is `D` and whose mask
is the complement of `E` on the last pair. The common support retains
all four prime labels and the second-prime quotient cutoff.

The identities below are finite and apply to arbitrary signed weights.
They supply a joint source for a later estimate, with no analytic mean,
numerical coefficient, distribution input or sieve bound assumed here.
-/

namespace ImbalancedChen

open scoped BigOperators
open Classical

noncomputable section

/-- Literal joint support: the low fourth-prime band is unmasked and
the high fourth-prime band retains precisely the original complement. -/
def chenY1011JointPrimeSelector (N : ℕ) (A H D : ℝ)
    (E : ℕ × ℕ → Prop) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N) ×ˢ
    (chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N)).filter fun t =>
    A ≤ (t.1.1 : ℝ) ∧ t.1.1 < t.1.2 ∧ t.1.2 < t.2.1 ∧ t.2.1 < t.2.2 ∧
    (t.2.1 : ℝ) < H ∧ (t.2.2 : ℝ) < D ∧
    ((t.2.2 : ℝ) < H ∨ ¬ E t.2)

/-- The exact boundary at `H` makes the original two full selectors
disjoint, before any mask or quotient condition is imposed. -/
theorem chenY10PrimeSelector_disjoint_chenY11FullPrimeSelector
    (N : ℕ) (A H D : ℝ) :
    Disjoint (chenY10PrimeSelector N A H) (chenY11FullPrimeSelector N A H D) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t h10 h11
  rcases (Finset.mem_filter.mp h10).2 with ⟨_, _, _, _, h4H⟩
  rcases (Finset.mem_filter.mp h11).2 with ⟨_, _, _, _, hH4, _⟩
  exact (not_lt_of_ge hH4) h4H

/-- An exact partition on the literal common carrier. In particular the
weak lower wall of row eleven owns equality at the fourth-prime cutoff. -/
theorem chenY1011JointPrimeSelector_eq_union (N : ℕ) (A H D : ℝ)
    (E : ℕ × ℕ → Prop) (hHD : H ≤ D) :
    chenY1011JointPrimeSelector N A H D E =
      chenY10PrimeSelector N A H ∪
        (chenY11FullPrimeSelector N A H D).filter (fun t => ¬ E t.2) := by
  classical
  ext t
  simp only [chenY1011JointPrimeSelector, chenY10PrimeSelector,
    chenY11FullPrimeSelector, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hT, hA, h12, h23, h34, h3H, h4D, hgate⟩
    by_cases h4H : (t.2.2 : ℝ) < H
    · exact Or.inl ⟨hT, hA, h12, h23, h34, h4H⟩
    · exact Or.inr ⟨⟨hT, hA, h12, h23, h3H, le_of_not_gt h4H, h4D⟩,
        hgate.resolve_left h4H⟩
  · rintro (⟨hT, hA, h12, h23, h34, h4H⟩ |
      ⟨⟨hT, hA, h12, h23, h3H, hH4, h4D⟩, hE⟩)
    · have h34R : (t.2.1 : ℝ) < (t.2.2 : ℝ) := by exact_mod_cast h34
      exact ⟨hT, hA, h12, h23, h34, h34R.trans h4H,
        h4H.trans_le hHD, Or.inl h4H⟩
    · have h34 : t.2.1 < t.2.2 := by exact_mod_cast h3H.trans_le hH4
      exact ⟨hT, hA, h12, h23, h34, h3H, h4D, Or.inr hE⟩

/-- Every signed real weight regroups without a positivity loss, an
extra multiplicity or a separate estimate for either row. -/
theorem sum_chenY1011JointPrimeSelector (N : ℕ) (A H D : ℝ)
    (E : ℕ × ℕ → Prop) (hHD : H ≤ D)
    (f : ((ℕ × ℕ) × (ℕ × ℕ)) → ℝ) :
    (∑ t ∈ chenY1011JointPrimeSelector N A H D E, f t) =
      (∑ t ∈ chenY10PrimeSelector N A H, f t) +
        ∑ t ∈ (chenY11FullPrimeSelector N A H D).filter (fun t => ¬ E t.2),
          f t := by
  classical
  rw [chenY1011JointPrimeSelector_eq_union N A H D E hHD]
  apply Finset.sum_union
  apply Finset.disjoint_left.mpr
  intro t h10 h11
  exact (Finset.disjoint_left.mp
    (chenY10PrimeSelector_disjoint_chenY11FullPrimeSelector N A H D))
      h10 (Finset.mem_filter.mp h11).1

/-- The combined literal receiver counts equal one sum of actual
four-factor quotient sources. Squareful receivers are retained. -/
theorem sum_chenY10_add_chenY11_compl_eq_joint_source
    (N : ℕ) (A H D : ℝ) (E : ℕ × ℕ → Prop) (hHD : H ≤ D) :
    (∑ P ∈ chenAdditivePrimeCarrier N, (chenY10 (N - P) A H : ℝ)) +
      (∑ P ∈ chenAdditivePrimeCarrier N,
        (chenY11Selected (N - P) A H D (fun t => ¬ E t) : ℝ)) =
      ∑ t ∈ chenY1011JointPrimeSelector N A H D E,
        ((chenSiftedQuotientPrimeSource N (t.1.1 * t.1.2 * t.2.1 * t.2.2)
          (t.1.2 : ℝ)).card : ℝ) := by
  rw [sum_chenY10_eq_siftedQuotientPrimeSource,
    sum_chenY11Selected_eq_siftedQuotientPrimeSource]
  convert (sum_chenY1011JointPrimeSelector N A H D E hHD
    (fun t => ((chenSiftedQuotientPrimeSource N
      (t.1.1 * t.1.2 * t.2.1 * t.2.2) (t.1.2 : ℝ)).card : ℝ))).symm using 1 <;>
    congr 2 <;> ext t <;> simp only [Finset.mem_filter]

/-- The original current cutoffs and the original last-pair complement
mask give the same joint source, with no independent row bounds needed. -/
theorem currentChenUpsilon10_add_11_eq_joint_source (N : ℕ)
    (E : ℕ × ℕ → Prop) (hN : 1 ≤ (N : ℝ)) :
    currentChenUpsilon10 N + currentChenUpsilon11 N E =
      ∑ t ∈ chenY1011JointPrimeSelector N
          ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ (19 / 125 : ℝ))
          ((N : ℝ) ^ (59 / 250 : ℝ)) E,
        ((chenSiftedQuotientPrimeSource N (t.1.1 * t.1.2 * t.2.1 * t.2.2)
          (t.1.2 : ℝ)).card : ℝ) := by
  have hHD : (N : ℝ) ^ (19 / 125 : ℝ) ≤ (N : ℝ) ^ (59 / 250 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  rw [currentChenUpsilon10_eq_siftedQuotientPrimeSource,
    currentChenUpsilon11_eq_siftedQuotientPrimeSource,
    sum_chenY1011JointPrimeSelector N _ _ _ E hHD]

end

end ImbalancedChen
