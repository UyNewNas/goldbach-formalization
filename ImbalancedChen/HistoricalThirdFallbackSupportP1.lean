import ImbalancedChen.HistoricalThirdCoarsePolicy

/-!
Exact fallback support for the actual finite historical third coarse rule.

The support is the conjunction of the literal rank-three rough activation
and membership in the union of the selected HALF-OPEN joint mesh cells.
It is a necessary support condition, not a claim that every supported point
has a nonzero difference. The initial fallback uses Theta = 299/500;
the different geometry ceiling Lambda = 153/256 is never substituted for it.

These are finite identities for the actual rawLevel, frozenLevel and policy.
They assert no integral evaluation, asymptotic mean, or density saving.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical BigOperators
open HistoricalThirdCoarse

namespace P1ThirdFallbackSupport

/-- The union retains the source mesh's simultaneous coordinate ownership. -/
def jointCells (e chi : ℝ) (m : ℕ) : Set (Fin 3 → ℝ) :=
  {t | ∃ j ∈ cells e chi m, t ∈ logPrimeMeshCell 0 (19 / 96) m j}

/-- Actual support, before freezing at an ancestor. -/
def supported (e chi : ℝ) (m : ℕ) (omega N : ℝ) (history : List ℕ) : Prop :=
  active omega N history ∧
    primeHistoryLogCoordinates N 3 history ∈ jointCells e chi m

/-- Actual support seen by all later descendants of the third history. -/
def frozenSupported (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) : Prop :=
  supported e chi m omega N (rosserAncestor 3 history)

theorem mem_jointCells (e chi : ℝ) (m : ℕ) (t : Fin 3 → ℝ) :
    t ∈ jointCells e chi m ↔
      ∃ j ∈ cells e chi m, t ∈ logPrimeMeshCell 0 (19 / 96) m j := by
  rfl

theorem not_mem_jointCells (e chi : ℝ) (m : ℕ) (t : Fin 3 → ℝ) :
    t ∉ jointCells e chi m ↔
      ∀ j ∈ cells e chi m, t ∉ logPrimeMeshCell 0 (19 / 96) m j := by
  simp only [jointCells, Set.mem_setOf_eq, not_exists, not_and]

theorem supported_triple (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (p1 p2 p3 : ℕ) :
    supported e chi m omega N [p3, p2, p1] ↔
      N ^ omega ≤ (p3 : ℝ) ∧
        ∃ j ∈ cells e chi m,
          primeHistoryLogCoordinates N 3 [p3, p2, p1] ∈
            logPrimeMeshCell 0 (19 / 96) m j := by
  rw [supported, active_triple]
  rfl

theorem initial_uses_theta (e : ℝ) :
    initial e = (299 / 500 : ℝ) - 2 * e := by
  rfl

theorem theta_sub_lambda :
    (299 / 500 : ℝ) - VariableEnvelope.cap = 11 / 32000 := by
  norm_num [VariableEnvelope.cap]

theorem theta_ne_lambda :
    (299 / 500 : ℝ) ≠ VariableEnvelope.cap := by
  norm_num [VariableEnvelope.cap]

/-- Neither small rough primes nor unselected joint cells can change rawLevel. -/
theorem rawLevel_fallback (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) (hs : ¬ supported e chi m omega N history) :
    rawLevel e chi m omega N history = N ^ initial e := by
  by_cases ha : active omega N history
  · apply rawLevel_outside
    intro j hj ht
    exact hs ⟨ha, j, hj, ht⟩
  · exact rawLevel_inactive e chi m omega N history ha

theorem rawLevel_eq_ite_supported (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) :
    rawLevel e chi m omega N history =
      if supported e chi m omega N history then
        N ^ exponent e chi m (primeHistoryLogCoordinates N 3 history)
      else N ^ initial e := by
  by_cases hs : supported e chi m omega N history
  · rw [if_pos hs, rawLevel, if_pos hs.1]
  · rw [if_neg hs]
    exact rawLevel_fallback e chi m omega N history hs

theorem frozenLevel_fallback (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) (hs : ¬ frozenSupported e chi m omega N history) :
    frozenLevel e chi m omega N history = N ^ initial e := by
  exact rawLevel_fallback e chi m omega N (rosserAncestor 3 history) hs

theorem frozenLevel_eq_ite_supported (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) :
    frozenLevel e chi m omega N history =
      if frozenSupported e chi m omega N history then
        N ^ exponent e chi m
          (primeHistoryLogCoordinates N 3 (rosserAncestor 3 history))
      else N ^ initial e := by
  exact rawLevel_eq_ite_supported e chi m omega N (rosserAncestor 3 history)

/-- The actual policy reverts to its actual first-stop initial policy. -/
theorem policy_fallback (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (positive : Bool) (history : List ℕ)
    (hs : ¬ frozenSupported e chi m omega N history) :
    policy e chi m omega N positive history = initialPolicy e m N positive history := by
  by_cases hlen : history.length ≤ 2
  · exact policy_through_two e chi m omega N positive history hlen
  · have hne : history.length ≠ 1 := by omega
    have hraw := rawLevel_fallback e chi m omega N (rosserAncestor 3 history) hs
    simp [policy, thirdCappedUpperPolicy, firstExitDepthSplicePolicy, hlen,
      frozenParityRosserPolicy, ancestorFrozenPolicy, hraw,
      ordinaryParityRosserPolicy, initialPolicy, oddFirstExitPolicy, hne]

/-- New minus initial level, with the original Theta-based fallback. -/
def rawDifference (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) : ℝ :=
  rawLevel e chi m omega N history - N ^ initial e

def frozenDifference (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) : ℝ :=
  frozenLevel e chi m omega N history - N ^ initial e

/-- Literal policy admission difference; no analytic continuation is inserted. -/
def policyDifference (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (positive : Bool) (history : List ℕ) : ℝ :=
  (if policy e chi m omega N positive history then 1 else 0) -
    (if initialPolicy e m N positive history then 1 else 0)

theorem rawDifference_zero (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) (hs : ¬ supported e chi m omega N history) :
    rawDifference e chi m omega N history = 0 := by
  unfold rawDifference
  rw [rawLevel_fallback e chi m omega N history hs, sub_self]

theorem frozenDifference_zero (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) (hs : ¬ frozenSupported e chi m omega N history) :
    frozenDifference e chi m omega N history = 0 := by
  unfold frozenDifference
  rw [frozenLevel_fallback e chi m omega N history hs, sub_self]

theorem policyDifference_zero (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (positive : Bool) (history : List ℕ)
    (hs : ¬ frozenSupported e chi m omega N history) :
    policyDifference e chi m omega N positive history = 0 := by
  unfold policyDifference
  rw [policy_fallback e chi m omega N positive history hs, sub_self]

theorem rawDifference_eq_ite (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) :
    rawDifference e chi m omega N history =
      if supported e chi m omega N history then
        N ^ exponent e chi m (primeHistoryLogCoordinates N 3 history) - N ^ initial e
      else 0 := by
  unfold rawDifference
  rw [rawLevel_eq_ite_supported]
  split_ifs <;> simp only [sub_self]

/-- Nonzero support is derived from the concrete rule, never assumed as a field. -/
theorem rawDifference_ne_zero_supported (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) (hd : rawDifference e chi m omega N history ≠ 0) :
    supported e chi m omega N history := by
  by_contra hs
  exact hd (rawDifference_zero e chi m omega N history hs)

theorem frozenDifference_ne_zero_supported (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) (hd : frozenDifference e chi m omega N history ≠ 0) :
    frozenSupported e chi m omega N history := by
  by_contra hs
  exact hd (frozenDifference_zero e chi m omega N history hs)

theorem policyDifference_ne_zero_supported (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (positive : Bool) (history : List ℕ)
    (hd : policyDifference e chi m omega N positive history ≠ 0) :
    frozenSupported e chi m omega N history := by
  by_contra hs
  exact hd (policyDifference_zero e chi m omega N positive history hs)

theorem rawLevel_ne_initial_supported (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ)
    (hd : rawLevel e chi m omega N history ≠ N ^ initial e) :
    active omega N history ∧
      ∃ j ∈ cells e chi m, primeHistoryLogCoordinates N 3 history ∈
        logPrimeMeshCell 0 (19 / 96) m j := by
  by_contra hs
  exact hd (rawLevel_fallback e chi m omega N history hs)

theorem policy_ne_initial_supported (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (positive : Bool) (history : List ℕ)
    (hd : policy e chi m omega N positive history ≠ initialPolicy e m N positive history) :
    active omega N (rosserAncestor 3 history) ∧
      ∃ j ∈ cells e chi m,
        primeHistoryLogCoordinates N 3 (rosserAncestor 3 history) ∈
          logPrimeMeshCell 0 (19 / 96) m j := by
  by_contra hs
  exact hd (policy_fallback e chi m omega N positive history hs)

/-- On each actually selected cell the difference uses that cell's Gamma. -/
theorem rawDifference_on_cell (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (history : List ℕ) (ha : active omega N history) (j : Cell m)
    (hj : j ∈ cells e chi m)
    (ht : primeHistoryLogCoordinates N 3 history ∈ logPrimeMeshCell 0 (19 / 96) m j) :
    rawDifference e chi m omega N history =
      N ^ levelExponent e (box m j) - N ^ initial e := by
  unfold rawDifference
  rw [rawLevel_on_cell e chi m omega N history ha j hj ht]

theorem rawDifference_small_third (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (p1 p2 p3 : ℕ) (hp : (p3 : ℝ) < N ^ omega) :
    rawDifference e chi m omega N [p3, p2, p1] = 0 := by
  unfold rawDifference
  rw [rawLevel_small_third e chi m omega N p1 p2 p3 hp, sub_self]

/-- Equality at the rough cutoff stays active, exactly as in the source rule. -/
theorem rawDifference_triple_eq_ite (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (p1 p2 p3 : ℕ) :
    rawDifference e chi m omega N [p3, p2, p1] =
      if N ^ omega ≤ (p3 : ℝ) ∧
          ∃ j ∈ cells e chi m,
            primeHistoryLogCoordinates N 3 [p3, p2, p1] ∈
              logPrimeMeshCell 0 (19 / 96) m j then
        N ^ exponent e chi m (primeHistoryLogCoordinates N 3 [p3, p2, p1]) - N ^ initial e
      else 0 := by
  rw [rawDifference_eq_ite, supported_triple]

/-- Finite sums need no convergence or positivity hypotheses for cancellation. -/
theorem sum_weighted_rawDifference_eq_filter (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (H : Finset (List ℕ)) (weight : List ℕ → ℝ) :
    (∑ history ∈ H, weight history * rawDifference e chi m omega N history) =
      ∑ history ∈ H.filter (supported e chi m omega N),
        weight history * rawDifference e chi m omega N history := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro history hH
  by_cases hs : supported e chi m omega N history
  · rw [if_pos hs]
  · rw [if_neg hs, rawDifference_zero e chi m omega N history hs, mul_zero]

theorem sum_weighted_frozenDifference_eq_filter (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (H : Finset (List ℕ)) (weight : List ℕ → ℝ) :
    (∑ history ∈ H, weight history * frozenDifference e chi m omega N history) =
      ∑ history ∈ H.filter (frozenSupported e chi m omega N),
        weight history * frozenDifference e chi m omega N history := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro history hH
  by_cases hs : frozenSupported e chi m omega N history
  · rw [if_pos hs]
  · rw [if_neg hs, frozenDifference_zero e chi m omega N history hs, mul_zero]

theorem sum_weighted_policyDifference_eq_filter (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (positive : Bool) (H : Finset (List ℕ)) (weight : List ℕ → ℝ) :
    (∑ history ∈ H, weight history * policyDifference e chi m omega N positive history) =
      ∑ history ∈ H.filter (frozenSupported e chi m omega N),
        weight history * policyDifference e chi m omega N positive history := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro history hH
  by_cases hs : frozenSupported e chi m omega N history
  · rw [if_pos hs]
  · rw [if_neg hs, policyDifference_zero e chi m omega N positive history hs, mul_zero]

end P1ThirdFallbackSupport
end
end ImbalancedChen
