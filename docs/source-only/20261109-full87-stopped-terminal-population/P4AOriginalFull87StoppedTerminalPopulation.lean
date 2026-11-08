import ImbalancedChen.P4AOriginalFull87SeventhExhaustion
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The fifth/sixth exclusive events in the previous packet still carried an
opaque stoppedTest 8 value. This packet exposes their EXACT original physical
terminal population, including the selected prefix, sign, mass, and every
List occurrence, without replacing the source by a convenient sieve bound.

The terminal list follows the real stoppedTest recursion: a carrier skip keeps
the old prefix; an admitted candidate uses the genuine post-candidate tail.
No additional mask or density hypothesis is inserted. These are internal
finite source lemmas, not an asymptotic o(H_N) payment.
-/

namespace ImbalancedChen.P4AOriginalFull87StoppedTerminalPopulation

noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (stoppedTest attachedLeafTest)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87SeventhExhaustion
  (seventh_terminal_zero_below_full_modulus
   seventh_terminal_nonzero_has_physical_highq_witness)

/-- A real stopped leaf, not a structural assumption about its value.
Its sign and mass are inherited from the actual first-exit recursion. -/
structure StoppedTerminal (α : Type*) where
  selected : List α
  positive : Bool
  mass : ℝ

/-- Every actual pre-k terminal occurrence, keeping repeated carriers as
repeated List occurrences. The second recursive call is made ONLY after
the actual gate admits the candidate, with the literal remaining tail. -/
def stoppedTerminals {α : Type*} (k : ℕ)
    (R : Bool → List α → Bool) (h : α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ) :
    List α → List (StoppedTerminal α)
  | [] =>
      if k ≤ pre.length then [] else [⟨pre, positive, mass⟩]
  | p :: ps =>
      if k ≤ pre.length then [] else
        stoppedTerminals k R h pre positive mass ps ++
        (if R (!positive) (p :: pre) = true then
          stoppedTerminals k R h (p :: pre) (!positive) (mass * h p) ps
         else [])

/-- Source equality: the original stoppedTest is a sum of its ORIGINAL
selected-prefix terminal occurrences. No change of beta, sign, or policy. -/
theorem stoppedTest_eq_stoppedTerminals {α : Type*}
    (k : ℕ) (R : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) :
    stoppedTest k R h T pre positive mass remaining =
      ((stoppedTerminals k R h pre positive mass remaining).map
        (fun t => signedTreeCoefficient t.positive t.mass *
          T t.positive t.selected)).sum := by
  induction remaining generalizing pre positive mass with
  | nil =>
      by_cases hk : k ≤ pre.length <;>
        simp [stoppedTest, stoppedTerminals, hk]
  | cons p ps ih =>
      by_cases hk : k ≤ pre.length
      · simp [stoppedTest, stoppedTerminals, hk]
      · by_cases hr : R (!positive) (p :: pre) = true
        · simp only [stoppedTest, stoppedTerminals, if_neg hk,
            if_pos hr, List.map_append, List.sum_append]
          rw [ih pre positive mass, ih (p :: pre) (!positive) (mass * h p)]
        · simp only [stoppedTest, stoppedTerminals, if_neg hk,
            if_neg hr, List.append_nil]
          exact ih pre positive mass

/-- No pre-k stopped source is misclassified as rank eight. This applies
in particular to fifth- and sixth-exclusive stopped subtrees. -/
theorem mem_stoppedTerminals_depth_lt {α : Type*}
    (k : ℕ) (R : Bool → List α → Bool) (h : α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) (t : StoppedTerminal α)
    (ht : t ∈ stoppedTerminals k R h pre positive mass remaining) :
    t.selected.length < k := by
  induction remaining generalizing pre positive mass with
  | nil =>
      by_cases hk : k ≤ pre.length
      · simp [stoppedTerminals, hk] at ht
      · have hsingle : t = ⟨pre, positive, mass⟩ := by
          simpa [stoppedTerminals, hk] using ht
        subst t
        exact Nat.lt_of_not_ge hk
  | cons p ps ih =>
      by_cases hk : k ≤ pre.length
      · simp [stoppedTerminals, hk] at ht
      · by_cases hr : R (!positive) (p :: pre) = true
        · have hpart :
            t ∈ stoppedTerminals k R h pre positive mass ps ∨
            t ∈ stoppedTerminals k R h (p :: pre) (!positive)
              (mass * h p) ps := by
              simpa [stoppedTerminals, hk, hr] using ht
          rcases hpart with hl | hr'
          · exact ih pre positive mass hl
          · exact ih (p :: pre) (!positive) (mass * h p) hr'
        · have hleft :
            t ∈ stoppedTerminals k R h pre positive mass ps := by
              simpa [stoppedTerminals, hk, hr] using ht
          exact ih pre positive mass hleft

/-- A terminal's selected word genuinely extends the SAME incoming
selected history. No reparenting or unrelated saved-box word occurs. -/
theorem mem_stoppedTerminals_extends_original_prefix {α : Type*}
    (k : ℕ) (R : Bool → List α → Bool) (h : α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) (t : StoppedTerminal α)
    (ht : t ∈ stoppedTerminals k R h pre positive mass remaining) :
    ∃ chosen : List α, t.selected = chosen ++ pre := by
  induction remaining generalizing pre positive mass with
  | nil =>
      by_cases hk : k ≤ pre.length
      · simp [stoppedTerminals, hk] at ht
      · have hsingle : t = ⟨pre, positive, mass⟩ := by
          simpa [stoppedTerminals, hk] using ht
        subst t
        exact ⟨[], by simp⟩
  | cons p ps ih =>
      by_cases hk : k ≤ pre.length
      · simp [stoppedTerminals, hk] at ht
      · by_cases hr : R (!positive) (p :: pre) = true
        · have hpart :
            t ∈ stoppedTerminals k R h pre positive mass ps ∨
            t ∈ stoppedTerminals k R h (p :: pre) (!positive)
              (mass * h p) ps := by
              simpa [stoppedTerminals, hk, hr] using ht
          rcases hpart with hl | hr'
          · exact ih pre positive mass hl
          · obtain ⟨chosen, hc⟩ :=
              ih (p :: pre) (!positive) (mass * h p) hr'
            refine ⟨chosen ++ [p], ?_⟩
            simpa [List.append_assoc] using hc
        · have hleft :
            t ∈ stoppedTerminals k R h pre positive mass ps := by
              simpa [stoppedTerminals, hk, hr] using ht
          exact ih pre positive mass hleft

/-- Apply the ORIGINAL sign-selected Rosser beta to the entire modulus
a * selected.prod, with the strict high-q test on that full modulus. -/
def stoppedPhysicalTerm
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (t : StoppedTerminal ℕ) : ℝ :=
  signedTreeCoefficient t.positive t.mass *
    attachedLeafTest N cap 1 w L (highQTest X F)
      t.positive t.selected

theorem actual_stopped_eq_physical_terminal_sum
    (R : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (pre : List ℕ) (positive : Bool) (mass : ℝ)
    (remaining : List ℕ) :
    stoppedTest 8 R h
        (attachedLeafTest N cap 1 w L (highQTest X F))
        pre positive mass remaining =
      ((stoppedTerminals 8 R h pre positive mass remaining).map
        (stoppedPhysicalTerm N cap w L X F)).sum := by
  simpa [stoppedPhysicalTerm] using
    stoppedTest_eq_stoppedTerminals 8 R h
      (attachedLeafTest N cap 1 w L (highQTest X F))
      pre positive mass remaining

private theorem map_sum_zero_of_every_zero {α : Type*}
    (xs : List α) (f : α → ℝ) :
    (∀ t ∈ xs, f t = 0) → (xs.map f).sum = 0 := by
  induction xs with
  | nil => intro _; simp
  | cons x xs ih =>
      intro hz
      have hx : f x = 0 := hz x (by simp)
      have htail : (xs.map f).sum = 0 :=
        ih (by
          intro y hy
          exact hz y (by simp [hy]))
      simp [hx, htail]

/-- Exact arithmetic cutoff for the fifth/sixth one-sided stopped
subtrees. Merely knowing the seventh terminal cutoff was insufficient:
EVERY actual stopped terminal's full modulus must be checked. -/
theorem stopped_zero_of_every_actual_terminal_below_cut
    (R : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (pre : List ℕ) (positive : Bool) (mass : ℝ)
    (remaining : List ℕ)
    (hsmall :
      ∀ t ∈ stoppedTerminals 8 R h pre positive mass remaining,
        ∀ a ∈ actualSmallRosserSupport N cap w,
          a * t.selected.prod ≤ X) :
    stoppedTest 8 R h
      (attachedLeafTest N cap 1 w L (highQTest X F))
      pre positive mass remaining = 0 := by
  rw [actual_stopped_eq_physical_terminal_sum]
  apply map_sum_zero_of_every_zero
  intro t ht
  exact seventh_terminal_zero_below_full_modulus
    N cap w L X F t.selected t.positive t.mass (hsmall t ht)

private theorem map_sum_nonzero_has_witness {α : Type*}
    (xs : List α) (f : α → ℝ)
    (hnz : (xs.map f).sum ≠ 0) :
    ∃ t ∈ xs, f t ≠ 0 := by
  induction xs with
  | nil => simp at hnz
  | cons x xs ih =>
      by_cases hx : f x = 0
      · have htail : (xs.map f).sum ≠ 0 := by
          simpa [hx] using hnz
        obtain ⟨t, ht, hne⟩ := ih htail
        exact ⟨t, by simp [ht], hne⟩
      · exact ⟨x, by simp, hx⟩

/-- A NONZERO fifth/sixth stopped subtree is not an anonymous error.
It contains a REAL terminal from the ORIGINAL admitted policy, at rank
strictly below eight, extending the supplied original selected history,
and a supported beta factor at STRICT full-q high mass. This is still
only a necessary witness, not an H_N-relative quantitative estimate. -/
theorem nonzero_stopped_has_actual_ancestor_highq_witness
    (R : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (pre : List ℕ) (positive : Bool) (mass : ℝ)
    (remaining : List ℕ)
    (hnz : stoppedTest 8 R h
      (attachedLeafTest N cap 1 w L (highQTest X F))
      pre positive mass remaining ≠ 0) :
    ∃ t ∈ stoppedTerminals 8 R h pre positive mass remaining,
      t.selected.length < 8 ∧
      (∃ chosen : List ℕ, t.selected = chosen ++ pre) ∧
      ∃ a ∈ actualSmallRosserSupport N cap w,
        X < a * t.selected.prod ∧
        (if t.positive then actualSmallRosserPlus N cap w L a
         else actualSmallRosserMinus N cap w L a) ≠ 0 ∧
        F (a * t.selected.prod) ≠ 0 := by
  rw [actual_stopped_eq_physical_terminal_sum] at hnz
  obtain ⟨t, ht, hnonzero⟩ := map_sum_nonzero_has_witness
    (stoppedTerminals 8 R h pre positive mass remaining)
    (stoppedPhysicalTerm N cap w L X F) hnz
  have hdepth := mem_stoppedTerminals_depth_lt
    8 R h pre positive mass remaining t ht
  obtain ⟨chosen, hchosen⟩ :=
    mem_stoppedTerminals_extends_original_prefix
      8 R h pre positive mass remaining t ht
  have hterminal : signedTreeCoefficient t.positive t.mass *
      attachedLeafTest N cap 1 w L (highQTest X F)
        t.positive t.selected ≠ 0 := by
    simpa [stoppedPhysicalTerm] using hnonzero
  obtain ⟨a, ha, hcut, hbeta, hF⟩ :=
    seventh_terminal_nonzero_has_physical_highq_witness
      N cap w L X F t.selected t.positive t.mass hterminal
  exact ⟨t, ht, hdepth, ⟨chosen, hchosen⟩,
    a, ha, hcut, hbeta, hF⟩

end
end ImbalancedChen.P4AOriginalFull87StoppedTerminalPopulation
