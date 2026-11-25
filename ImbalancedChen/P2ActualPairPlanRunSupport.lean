import ImbalancedChen.P2OriginalPairRootRoughProducer

/-!
# Cap and accepted-word support of the actual finite run

Extracted verbatim from P2ActualPairPlanRawSupport, preserving its namespace.
The accepted-run lemma is public; its statement and proof are unchanged.
Source only; elaboration and kernel verification are pending.
-/

namespace ImbalancedChen.P2ActualPairPlanRawSupport

noncomputable section
open scoped Classical BigOperators
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention

/-- A local finite cap check; it supplies no retained-modulus bound. -/
def PlanCeiling {depth mesh : ℕ} (P : CapPlan depth mesh) (nu : ℝ) : Prop :=
  ∀ rank code incoming, incoming ≤ nu → (P.choose rank code).freeze incoming ≤ nu

theorem step_cap_le {depth mesh : ℕ} (P : CapPlan depth mesh) (nu : ℝ)
    (hP : PlanCeiling P nu) (a b : ℝ) (H : Trace) (x : ℝ)
    (hcap : H.cap ≤ nu) : (step P a b H x).cap ≤ nu := by
  change (planChoice P a b (H.word ++ [x])).freeze H.cap ≤ nu
  unfold planChoice
  split_ifs
  · unfold incomingChoice
    exact hP _ _ _ hcap
  · exact hcap

theorem run_cap_le {depth mesh : ℕ} (P : CapPlan depth mesh) (nu : ℝ)
    (hP : PlanCeiling P nu) (a b : ℝ) (H : Trace) (xs : List ℝ)
    (hcap : H.cap ≤ nu) : (run P a b H xs).cap ≤ nu := by
  induction xs generalizing H with
  | nil => exact hcap
  | cons x xs ih =>
      exact ih (step P a b H x) (step_cap_le P nu hP a b H x hcap)

/-- Every accepted even cube creates two copies of the last exponent in
reserve. At the next odd bypass, decreasing order spends at most one copy.
No odd cube or tail-modulus conclusion is supplied as a premise. -/
theorem accepted_run_sum_le {depth mesh : ℕ} (P : CapPlan depth mesh)
    (nu : ℝ) (hP : PlanCeiling P nu) (a b : ℝ) (xs : List ℝ) :
    ∀ (H : Trace) (ceiling : ℝ), 0 < H.word.length → H.cap ≤ nu →
      H.word.sum ≤ nu →
      (H.word.length % 2 = 0 → H.word.sum + 2 * ceiling ≤ nu) →
      (H.word.length % 2 = 0 → ∀ x ∈ xs, x ≤ ceiling) →
      xs.Pairwise (· ≥ ·) → (∀ x ∈ xs, 0 ≤ x) →
      (run P a b H xs).accepted = true → (run P a b H xs).word.sum ≤ nu := by
  induction xs with
  | nil => intros; assumption
  | cons x xs ih =>
      intro H ceiling hlen hcap hsum hcarry hceil hsort hnonneg haccept
      have hacc : (step P a b H x).accepted = true :=
        P2LowerIntegerRetainedSupport.run_accepted_incoming P a b _ _ haccept
      have hadm := ((step_accepted_iff P a b H x).mp hacc).2
      have hx0 := hnonneg x (List.mem_cons_self x xs)
      have hcube (he : (H.word.length + 1) % 2 = 0) :
          H.word.sum + 3 * x < H.cap := by
        have hn : H.word.length ≠ 0 := by omega
        simpa only [admission, if_neg hn, if_pos he] using hadm
      have hword : (step P a b H x).word.sum = H.word.sum + x := by
        simp only [step, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
      have hnextsum : (step P a b H x).word.sum ≤ nu := by
        rw [hword]
        by_cases he : (H.word.length + 1) % 2 = 0
        · linarith [hcube he]
        · have hprev : H.word.length % 2 = 0 := by omega
          have hc := hcarry hprev
          have hx := hceil hprev x (List.mem_cons_self x xs)
          linarith
      have hnextcarry : (step P a b H x).word.length % 2 = 0 →
          (step P a b H x).word.sum + 2 * x ≤ nu := by
        intro he
        have he' : (H.word.length + 1) % 2 = 0 := by
          simpa only [step, List.length_append, List.length_singleton] using he
        rw [hword]
        linarith [hcube he']
      have hnextceil : (step P a b H x).word.length % 2 = 0 →
          ∀ y ∈ xs, y ≤ x := by
        intro _ y hy
        exact (List.pairwise_cons.mp hsort).1 y hy
      have hnextlen : 0 < (step P a b H x).word.length := by
        simp only [step, List.length_append, List.length_singleton]
        omega
      exact ih (step P a b H x) x hnextlen
        (step_cap_le P nu hP a b H x hcap) hnextsum hnextcarry hnextceil
        (List.pairwise_cons.mp hsort).2
        (fun y hy => hnonneg y (List.mem_cons_of_mem x hy)) haccept

end
end ImbalancedChen.P2ActualPairPlanRawSupport
