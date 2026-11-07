import ImbalancedChen.P2EnhancedPrefixMaskDefect

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The finite 21-term inequality is transported to physical quotient counts.
The existing mother already proves the four-band scalar inequality and
the exact Gamma7,...,Gamma21 word dictionary. We reuse it unchanged.
The new operation is the finite event-count comparison at EVERY marked
tuple, followed by summation with the original words and multiplicities.

Each switched quotient retains the next-to-last specified prime as its
physical cutoff. The source-prefix mask difference is paid by the literal
selected-prime-square collision carrier, including all multiplicities.
The three original negative bad-prime windows are also displayed. Unit
quotients remain in the quotient terms and are absent from the collision
cost, so the Gamma20/21 unit surfaces have not been discarded.

This is a finite count inequality. It supplies neither ordinary signed
distribution at an enhanced level nor a positive K product estimate.
It does not license any retained Upsilon6 lower mean: the independent
p1*p2 product restriction for that mean remains a required analytic gate.
-/

namespace ImbalancedChen.P2EnhancedTwentyOneQuotientFinite

noncomputable section

open Finset Wu2008DoubleSieve
open P2EnhancedPrefixMaskDefect
open scoped Classical

/-- The original labelled domain, now with the actual old-mask quotient. -/
def quotientPrefixTerm (N d M : ℕ) (a b c e f : ℝ) (cs : List ℕ) : ℝ :=
  ∑ l ∈ secondFunctionalMotherTuples (primeWindow M a f) cs.length,
    if l.map (secondFunctionalMotherColour b c e) = cs then
      ((quotientCarrier N d l).card : ℝ) else 0

/-- The same labels and domain, with only their selected-square event cost. -/
def collisionPrefixTerm (N d M : ℕ) (a b c e f : ℝ) (cs : List ℕ) : ℝ :=
  ∑ l ∈ secondFunctionalMotherTuples (primeWindow M a f) cs.length,
    if l.map (secondFunctionalMotherColour b c e) = cs then
      ((collisionCarrier N d l).card : ℝ) else 0

theorem quotientPrefixTerm_nonneg (N d M : ℕ) (a b c e f : ℝ) (cs : List ℕ) :
    0 ≤ quotientPrefixTerm N d M a b c e f cs := by
  apply sum_nonneg
  intro l _
  split_ifs <;> positivity

theorem collisionPrefixTerm_nonneg (N d M : ℕ) (a b c e f : ℝ) (cs : List ℕ) :
    0 ≤ collisionPrefixTerm N d M a b c e f cs := by
  apply sum_nonneg
  intro l _
  split_ifs <;> positivity

/-- Cardinality comparison for an actual marked colour word, at any arity. -/
theorem prefixTerm_le_quotient_add_collision (N d M : ℕ)
    (a b c e f : ℝ) (cs : List ℕ) :
    secondFunctionalMotherPrefixTerm N d M a b c e f cs ≤
      quotientPrefixTerm N d M a b c e f cs +
        collisionPrefixTerm N d M a b c e f cs := by
  unfold secondFunctionalMotherPrefixTerm quotientPrefixTerm collisionPrefixTerm
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro l _
  by_cases hc : l.map (secondFunctionalMotherColour b c e) = cs
  · simp only [if_pos hc]
    exact_mod_cast prefix_card_le_quotient_add_collision N d l
  · simp only [if_neg hc, add_zero, le_refl]

/-- All fifteen switched occurrences keep the original 21-term dictionary. -/
def quotientSwitched (N d M : ℕ) (a b c e f : ℝ) : ℝ :=
  (secondFunctionalMotherPrefixIndices.map fun i =>
    ((secondFunctionalMotherGammaWords i).map
      (quotientPrefixTerm N d M a b c e f)).sum).sum

def collisionSwitched (N d M : ℕ) (a b c e f : ℝ) : ℝ :=
  (secondFunctionalMotherPrefixIndices.map fun i =>
    ((secondFunctionalMotherGammaWords i).map
      (collisionPrefixTerm N d M a b c e f)).sum).sum

/-- The new cost is nonnegative before any asymptotic estimate is sought. -/
theorem collisionSwitched_nonneg (N d M : ℕ) (a b c e f : ℝ) :
    0 ≤ collisionSwitched N d M a b c e f := by
  unfold collisionSwitched
  apply List.sum_nonneg
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  apply List.sum_nonneg
  intro y hy
  obtain ⟨cs, _, rfl⟩ := List.mem_map.mp hy
  exact collisionPrefixTerm_nonneg N d M a b c e f cs

/-- Finite transport of all switched words; no target count bound is an input. -/
theorem switched_le_quotient_add_collision (N d M : ℕ) (a b c e f : ℝ) :
    (secondFunctionalMotherPrefixIndices.map fun i =>
      ((secondFunctionalMotherGammaWords i).map
        (secondFunctionalMotherPrefixTerm N d M a b c e f)).sum).sum ≤
      quotientSwitched N d M a b c e f + collisionSwitched N d M a b c e f := by
  have hword (i : ℕ) :
      ((secondFunctionalMotherGammaWords i).map
        (secondFunctionalMotherPrefixTerm N d M a b c e f)).sum ≤
      ((secondFunctionalMotherGammaWords i).map
        (quotientPrefixTerm N d M a b c e f)).sum +
      ((secondFunctionalMotherGammaWords i).map
        (collisionPrefixTerm N d M a b c e f)).sum := by
    have h := secondFunctionalMother_list_sum_mono (secondFunctionalMotherGammaWords i)
      (secondFunctionalMotherPrefixTerm N d M a b c e f)
      (fun cs => quotientPrefixTerm N d M a b c e f cs +
        collisionPrefixTerm N d M a b c e f cs)
      (fun cs _ => prefixTerm_le_quotient_add_collision N d M a b c e f cs)
    simpa only [List.sum_map_add] using h
  have h := secondFunctionalMother_list_sum_mono secondFunctionalMotherPrefixIndices
    (fun i => ((secondFunctionalMotherGammaWords i).map
      (secondFunctionalMotherPrefixTerm N d M a b c e f)).sum)
    (fun i => ((secondFunctionalMotherGammaWords i).map
      (quotientPrefixTerm N d M a b c e f)).sum +
      ((secondFunctionalMotherGammaWords i).map
        (collisionPrefixTerm N d M a b c e f)).sum)
    (fun i _ => hword i)
  simpa only [List.sum_map_add, quotientSwitched, collisionSwitched] using h

/-- The complete 21-term RHS: original occurrences 1--6 and quotient
occurrences 7--21. Original scalar signs and multiplicities are unchanged. -/
def quotientLocal (N d M : ℕ) (a b c e f : ℝ) : ℝ :=
  4 * (sourceSieveCount N d (d * N) a : ℝ) +
    (sourceSieveCount N d (d * N) b : ℝ) -
    fourthRowMotherSingle N d M a f - fourthRowMotherSingle N d M a c -
    fourthRowMotherSingle N d M a e + fourthRowMotherPair N d M a c a c +
    fourthRowMotherPair N d M a b c e + quotientSwitched N d M a b c e f

theorem originalLocal_le_quotient_add_collision (N d M : ℕ) (a b c e f : ℝ) :
    secondFunctionalMotherLocal N d M a b c e f ≤
      quotientLocal N d M a b c e f + collisionSwitched N d M a b c e f := by
  rw [secondFunctionalMother_local_expand]
  have h := switched_le_quotient_add_collision N d M a b c e f
  unfold quotientLocal
  linarith

/-- Actual finite repaired 21-term quotient inequality. Every exception
is an explicit event count, and all three negative original windows remain. -/
theorem twentyOne_quotient_finite (N d : ℕ) {a b c e f : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e) (hef : e ≤ f) :
    5 * (sourceSieveCount N d (d * N) f : ℝ) ≤
      quotientLocal N d N a b c e f + collisionSwitched N d N a b c e f +
        fourthRowMotherBadPrime N d a f + fourthRowMotherBadPrime N d a c +
        fourthRowMotherBadPrime N d a e := by
  have hsource := secondFunctionalMother_original_windows N d hab hbc hce hef
  have hswitch := originalLocal_le_quotient_add_collision N d N a b c e f
  linarith

end
end ImbalancedChen.P2EnhancedTwentyOneQuotientFinite
