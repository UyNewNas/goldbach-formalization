import ImbalancedChen.P4AOriginalFull87SixthBothInvoice
import ImbalancedChen.P4AOriginalFull87StoppedTerminalPopulation
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

For each actual fifth-only or sixth-only stopped subtree, its genuine
accepted rank-seven terminals have zero FULL a*b high-q value under the
already established original rank-seven Rosser gate. Thus the ORIGINAL
stoppedTest 8 equals stoppedTest 7 on these literal one-sided subtrees.

This reduces any surviving nonzero high-q witness to a real rank-FIVE
or rank-SIX terminal, with its original sign, mass, history, and strict
full-modulus beta witness. In particular, the unchecked even rank-six
terminal is NOT silently bounded by the odd rank-seven gate.

No arbitrary policy smallness field, external analytic input, source
mask, signed gain monotonicity, or density reserve is introduced.
-/

namespace ImbalancedChen.P4AOriginalFull87RankSevenTerminalPruning
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (stoppedTest attachedLeafTest)
open P4AOriginalFull87SeventhExhaustion
  (stopped_seven_eq_literal_terminal
   seventh_terminal_nonzero_has_physical_highq_witness)
open P4AOriginalFull87RankSevenStoppedHighQ
  (actual_admitted_seventh_terminal_highq_zero)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87StoppedTerminalPopulation
  (StoppedTerminal stoppedTerminals stoppedTest_eq_stoppedTerminals
   mem_stoppedTerminals_depth_lt
   mem_stoppedTerminals_extends_original_prefix)

/-- Above any chosen cutoff, there is no stopped-before-cut terminal.
This is a direct property of the original stoppedTest, not a hypothesis. -/
private theorem stopped_zero_at_cut {α : Type*}
    (k : ℕ) (R : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ) (pre : List α)
    (positive : Bool) (mass : ℝ) (remaining : List α)
    (hk : k ≤ pre.length) :
    stoppedTest k R h T pre positive mass remaining = 0 := by
  cases remaining with
  | nil => simp [stoppedTest, hk]
  | cons p ps => simp [stoppedTest, hk]

/-- At a real even sixth history, the ONLY rank-seven terms which could
distinguish cutoff 8 from cutoff 7 are actual accepted seventh children.
If each such child's literal terminal value vanishes, both cutoffs have
the same value. The rank-six terminal itself is fully retained. -/
private theorem stopped8_eq_stopped7_at_six
    (R : Bool → List ℕ → Bool) (T : Bool → List ℕ → ℝ)
    (pre : List ℕ) (hlen : pre.length = 6)
    (mass : ℝ) (remaining : List ℕ)
    (hseven : ∀ p, R false (p :: pre) = true →
      T false (p :: pre) = 0) :
    stoppedTest 8 R (fun _ : ℕ => (1 : ℝ))
      T pre true mass remaining =
    stoppedTest 7 R (fun _ : ℕ => (1 : ℝ))
      T pre true mass remaining := by
  have h8 : ¬ 8 ≤ pre.length := by omega
  have h7 : ¬ 7 ≤ pre.length := by omega
  induction remaining with
  | nil =>
      simp [stoppedTest, h8, h7]
  | cons p ps ih =>
      have hp7 : (p :: pre).length = 7 := by simp [hlen]
      have hshort :
          stoppedTest 7 R (fun _ : ℕ => (1 : ℝ))
            T (p :: pre) false (mass * (1 : ℝ)) ps = 0 :=
        stopped_zero_at_cut 7 R (fun _ : ℕ => (1 : ℝ))
          T (p :: pre) false (mass * (1 : ℝ)) ps (by omega)
      by_cases hr : R false (p :: pre) = true
      · have hlong :
            stoppedTest 8 R (fun _ : ℕ => (1 : ℝ))
              T (p :: pre) false (mass * (1 : ℝ)) ps = 0 := by
          rw [stopped_seven_eq_literal_terminal R
            (fun _ : ℕ => (1 : ℝ)) T
            (p :: pre) false (mass * (1 : ℝ)) ps hp7]
          simp [hseven p hr]
        simp [stoppedTest, h8, h7, hr, hlong, hshort, ih]
      · simp [stoppedTest, h8, h7, hr, ih]

/-- The real fifth-only branch may still select sixth children.
The rank-six lemma is applied on the ACTUAL post-sixth suffix.
Consequently the fifth and sixth terminal populations survive, but no
seventh terminal is lost by cancellation of distinct occurrences. -/
private theorem stopped8_eq_stopped7_at_five
    (R : Bool → List ℕ → Bool) (T : Bool → List ℕ → ℝ)
    (pre : List ℕ) (hlen : pre.length = 5)
    (mass : ℝ) (remaining : List ℕ)
    (hseven : ∀ s, s.length = 7 →
      R false s = true → T false s = 0) :
    stoppedTest 8 R (fun _ : ℕ => (1 : ℝ))
      T pre false mass remaining =
    stoppedTest 7 R (fun _ : ℕ => (1 : ℝ))
      T pre false mass remaining := by
  have h8 : ¬ 8 ≤ pre.length := by omega
  have h7 : ¬ 7 ≤ pre.length := by omega
  induction remaining with
  | nil =>
      simp [stoppedTest, h8, h7]
  | cons p ps ih =>
      have hp6 : (p :: pre).length = 6 := by simp [hlen]
      have hchild := stopped8_eq_stopped7_at_six
        R T (p :: pre) hp6 (mass * (1 : ℝ)) ps (by
          intro q hgate
          exact hseven (q :: p :: pre) (by simp [hlen]) hgate)
      by_cases hr : R true (p :: pre) = true
      · simp [stoppedTest, h8, h7, hr, ih, hchild]
      · simp [stoppedTest, h8, h7, hr, ih]

/-- Applies to exactly the TWO original sixth producer policies and their
actual fifth-negative/sixth-positive subtree roots. No claim is made
for arbitrary policy words or for a terminal at the even sixth gate.
The beta coefficient is still the original sign-selected one. -/
theorem actual_one_sided_stopped8_eq_stopped7
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) (R : Bool → List ℕ → Bool)
    (hR : R =
        P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ) ∨
      R = P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ))
    (pre : List ℕ) (positive : Bool) (mass : ℝ)
    (remaining : List ℕ)
    (hlevel : (pre.length = 5 ∧ positive = false) ∨
      (pre.length = 6 ∧ positive = true)) :
    stoppedTest 8 R (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
        (highQTest X F)) pre positive mass remaining =
    stoppedTest 7 R (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
        (highQTest X F)) pre positive mass remaining := by
  have hz : ∀ s : List ℕ, s.length = 7 →
      R false s = true →
      attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
        (highQTest X F) false s = 0 := by
    intro s hs hg
    rcases hR with hr | hl
    · rw [hr] at hg
      exact actual_admitted_seventh_terminal_highq_zero
        delta n e q om N cap w he hN epsilon heps X hX F
        s hs (Or.inl hg)
    · rw [hl] at hg
      exact actual_admitted_seventh_terminal_highq_zero
        delta n e q om N cap w he hN epsilon heps X hX F
        s hs (Or.inr hg)
  rcases hlevel with ⟨hfive, hp⟩ | ⟨hsix, hp⟩
  · subst positive
    exact stopped8_eq_stopped7_at_five R
      (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
        (highQTest X F)) pre hfive mass remaining hz
  · subst positive
    exact stopped8_eq_stopped7_at_six R
      (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
        (highQTest X F)) pre hsix mass remaining
        (by intro p hg; exact hz (p :: pre) (by simp [hsix]) hg)

/-- Finite sum nonvanishing is witnessed by an ORIGINAL occurrence.
This is used only as a necessary witness, never to supply a numerical
mean or an analytic saving. -/
private theorem nonzero_sum_has_member {α : Type*}
    (xs : List α) (f : α → ℝ)
    (hne : (xs.map f).sum ≠ 0) :
    ∃ t ∈ xs, f t ≠ 0 := by
  induction xs with
  | nil => simp at hne
  | cons x xs ih =>
      by_cases hx : f x = 0
      · have htail : (xs.map f).sum ≠ 0 := by
          simpa [hx] using hne
        obtain ⟨t, ht, hn⟩ := ih htail
        exact ⟨t, by simp [ht], hn⟩
      · exact ⟨x, by simp, hx⟩

/-- A genuinely nonzero surviving fifth- or sixth-exclusive HIGH-Q
stopped subtree contains an ORIGINAL rank-five OR rank-six terminal,
with original selected history, sign and mass, plus a nonzero original
beta on a strictly large FULL modulus a*prod. It cannot hide a
rank-seven residual. Nothing here asserts that rank-six even gates
satisfy the odd seventh product cap. -/
theorem actual_one_sided_nonzero_has_short_physical_witness
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) (R : Bool → List ℕ → Bool)
    (hR : R =
        P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ) ∨
      R = P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ))
    (pre : List ℕ) (positive : Bool) (mass : ℝ)
    (remaining : List ℕ)
    (hlevel : (pre.length = 5 ∧ positive = false) ∨
      (pre.length = 6 ∧ positive = true))
    (hnz : stoppedTest 8 R (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
        (highQTest X F)) pre positive mass remaining ≠ 0) :
    ∃ t ∈ stoppedTerminals 7 R (fun _ : ℕ => (1 : ℝ))
        pre positive mass remaining,
      (t.selected.length = 5 ∨ t.selected.length = 6) ∧
      (∃ chosen : List ℕ, t.selected = chosen ++ pre) ∧
      ∃ a ∈ actualSmallRosserSupport N cap w,
        X < a * t.selected.prod ∧
        (if t.positive then
          actualSmallRosserPlus N cap w ((N : ℝ) ^ epsilon) a
         else actualSmallRosserMinus N cap w
          ((N : ℝ) ^ epsilon) a) ≠ 0 ∧
        F (a * t.selected.prod) ≠ 0 := by
  have hcollapse := actual_one_sided_stopped8_eq_stopped7
    delta n e q om N cap w he hN epsilon heps X hX F
    R hR pre positive mass remaining hlevel
  rw [hcollapse] at hnz
  rw [stoppedTest_eq_stoppedTerminals] at hnz
  obtain ⟨t, ht, htne⟩ := nonzero_sum_has_member
    (stoppedTerminals 7 R (fun _ : ℕ => (1 : ℝ))
      pre positive mass remaining)
    (fun t => signedTreeCoefficient t.positive t.mass *
      attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
        (highQTest X F) t.positive t.selected) hnz
  have hlt : t.selected.length < 7 :=
    mem_stoppedTerminals_depth_lt 7 R
      (fun _ : ℕ => (1 : ℝ))
      pre positive mass remaining t ht
  obtain ⟨chosen, hchosen⟩ :=
    mem_stoppedTerminals_extends_original_prefix 7 R
      (fun _ : ℕ => (1 : ℝ))
      pre positive mass remaining t ht
  have hbase : 5 ≤ pre.length := by
    rcases hlevel with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hprefix : pre.length ≤ t.selected.length := by
    rw [hchosen, List.length_append]
    omega
  have hshort : t.selected.length = 5 ∨
      t.selected.length = 6 := by omega
  obtain ⟨a, ha, hcut, hbeta, hF⟩ :=
    seventh_terminal_nonzero_has_physical_highq_witness
      N cap w ((N : ℝ) ^ epsilon) X F
      t.selected t.positive t.mass htne
  exact ⟨t, ht, hshort, ⟨chosen, hchosen⟩,
    a, ha, hcut, hbeta, hF⟩

end
end ImbalancedChen.P4AOriginalFull87RankSevenTerminalPruning
