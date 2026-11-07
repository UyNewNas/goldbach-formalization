import ImbalancedChen.FrozenRosserPolicy
import ImbalancedChen.FirstExitFrontierInvariants

/-!
# Admission and inherited validity at the actual parent frontier

Every positive-rank frontier state has passed its parent's own admission
test. For the full ordinary policy that test is the complete prefix
predicate. For the parity-safe policy an inactive test alone is insufficient;
the proof instead propagates complete validity through every actual selection
using the ordinary one-step dictionary, sorted prime labels and the lower
first-prime level condition. Root corollaries pay the initial validity.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical

/-- A returned frontier state has passed the original policy's last
selection. An entry already at the stopping rank must itself be admitted. -/
theorem mem_firstExitDepthFrontier_admitted
    {α : Type*} (k : ℕ) (parent : Bool → List α → Bool) (h : α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ)
    (hentry : parent positive pre = true ∨ pre.length < k)
    (state : FirstExitDepthState α)
    (hstate : state ∈ firstExitDepthFrontier k parent h pre positive mass remaining) :
    parent state.positive state.selectedPrefix = true := by
  induction remaining generalizing pre positive mass with
  | nil =>
      by_cases hk : k ≤ pre.length
      · simp only [firstExitDepthFrontier, if_pos hk, List.mem_singleton] at hstate
        subst state
        exact hentry.resolve_right (Nat.not_lt.mpr hk)
      · simp [firstExitDepthFrontier, hk] at hstate
  | cons p ps ih =>
      by_cases hk : k ≤ pre.length
      · rw [firstExitDepthFrontier_of_rank_le_length k parent h pre (p :: ps)
          positive mass hk, List.mem_singleton] at hstate
        subst state
        exact hentry.resolve_right (Nat.not_lt.mpr hk)
      · by_cases hp : parent (!positive) (p :: pre) = true
        · rw [firstExitDepthFrontier, if_neg hk, if_pos hp, List.mem_append] at hstate
          rcases hstate with hskip | hselect
          · exact ih pre positive mass hentry hskip
          · exact ih (p :: pre) (!positive) (mass * h p) (Or.inl hp) hselect
        · rw [firstExitDepthFrontier, if_neg hk, if_neg hp, List.append_nil] at hstate
          exact ih pre positive mass hentry hstate

theorem mem_firstExitDepthFrontier_root_admitted
    {α : Type*} (k : ℕ) (hk : 0 < k) (parent : Bool → List α → Bool)
    (h : α → ℝ) (carrier : List α) (state : FirstExitDepthState α)
    (hstate : state ∈ firstExitDepthFrontier k parent h [] true 1 carrier) :
    parent state.positive state.selectedPrefix = true :=
  mem_firstExitDepthFrontier_admitted k parent h [] carrier true 1
    (Or.inr hk) state hstate

/-- No initial total-level hypothesis is needed at positive rank: the
actual full policy itself checked every returned complete prefix. -/
theorem mem_firstExitDepthFrontier_ordinaryRosser_admissible_of_pos
    (lower : Bool) (Q : ℝ) (k : ℕ) (hk : 0 < k)
    (h : ℕ → ℝ) (carrier : List ℕ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k (ordinaryRosserRetainedPolicy lower Q)
      h [] true 1 carrier) :
    ordinaryRosserPrefixAdmissible lower Q state.selectedPrefix := by
  exact of_decide_eq_true
    (mem_firstExitDepthFrontier_root_admitted k hk _ h carrier state hstate)

/-- With `Q > 1`, the full ordinary root is valid even when rank zero is
requested. All higher ranks are derived from actual admissions. -/
theorem mem_firstExitDepthFrontier_ordinaryRosser_admissible
    (lower : Bool) (Q : ℝ) (hQ : 1 < Q) (k : ℕ)
    (h : ℕ → ℝ) (carrier : List ℕ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k (ordinaryRosserRetainedPolicy lower Q)
      h [] true 1 carrier) :
    ordinaryRosserPrefixAdmissible lower Q state.selectedPrefix := by
  apply of_decide_eq_true
  exact mem_firstExitDepthFrontier_admitted k _ h [] carrier true 1
    (Or.inl (decide_eq_true (ordinaryRosserPrefixAdmissible_nil lower hQ))) state hstate

/-- A full-prefix frozen policy checks its complete history at the actual
ancestor's level. This is not a claim about arbitrary parity-safe policies. -/
theorem mem_firstExitDepthFrontier_frozenOrdinary_admissible
    (lower : Bool) (freezeRank k : ℕ) (hk : 0 < k) (Q : List ℕ → ℝ)
    (h : ℕ → ℝ) (carrier : List ℕ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k (frozenOrdinaryRosserPolicy lower freezeRank Q)
      h [] true 1 carrier) :
    ordinaryRosserPrefixAdmissible lower
      (Q (rosserAncestor freezeRank state.selectedPrefix)) state.selectedPrefix := by
  exact of_decide_eq_true
    (mem_firstExitDepthFrontier_root_admitted k hk _ h carrier state hstate)

/-- Complete validity, rather than merely the inactive-parity Boolean test,
is propagated through every real recursive selection. -/
theorem mem_firstExitDepthFrontier_ordinaryParityRosser_valid
    (lower : Bool) (Q : ℝ) (k : ℕ) (h : ℕ → ℝ)
    (pre carrier : List ℕ) (positive : Bool) (mass : ℝ)
    (hpre : ordinaryRosserPrefixAdmissible lower Q pre)
    (hsign : positive = evenListLength pre)
    (hprime : ∀ p ∈ carrier, p.Prime)
    (hlevel : lower = true → ∀ p ∈ carrier, (p : ℝ) < Q)
    (hsort : (carrier.reverse ++ pre).Pairwise (· < ·))
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k (ordinaryParityRosserPolicy lower Q)
      h pre positive mass carrier) :
    ordinaryRosserPrefixAdmissible lower Q state.selectedPrefix ∧
      state.positive = evenListLength state.selectedPrefix := by
  induction carrier generalizing pre positive mass with
  | nil =>
      by_cases hk : k ≤ pre.length
      · simp only [firstExitDepthFrontier, if_pos hk, List.mem_singleton] at hstate
        subst state
        exact ⟨hpre, hsign⟩
      · simp [firstExitDepthFrontier, hk] at hstate
  | cons q qs ih =>
      by_cases hk : k ≤ pre.length
      · rw [firstExitDepthFrontier_of_rank_le_length k _ h pre (q :: qs)
          positive mass hk, List.mem_singleton] at hstate
        subst state
        exact ⟨hpre, hsign⟩
      · have hsort' : (qs.reverse ++ q :: pre).Pairwise (· < ·) := by
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hsort
        have hskipSort : (qs.reverse ++ pre).Pairwise (· < ·) :=
          hsort'.sublist ((List.Sublist.refl qs.reverse).append ((List.Sublist.refl pre).cons q))
        have hprime' : ∀ p ∈ qs, p.Prime :=
          fun p hp => hprime p (List.mem_cons_of_mem q hp)
        have hlevel' : lower = true → ∀ p ∈ qs, (p : ℝ) < Q :=
          fun hl p hp => hlevel hl p (List.mem_cons_of_mem q hp)
        by_cases ht : ordinaryParityRosserPolicy lower Q (!positive) (q :: pre) = true
        · rw [firstExitDepthFrontier, if_neg hk, if_pos ht, List.mem_append] at hstate
          rcases hstate with hskip | hselect
          · exact ih pre positive mass hpre hsign hprime' hlevel' hskipSort hskip
          · have heq := ordinaryParityRosserPolicy_eq_full_on_valid_prefix lower Q
              pre positive q hpre hsign (hprime q (by simp))
              (fun hl => hlevel hl q (by simp)) (List.pairwise_append.mp hsort').2.1
            have hnext : ordinaryRosserPrefixAdmissible lower Q (q :: pre) := by
              rw [heq] at ht
              exact of_decide_eq_true ht
            have hsign' : (!positive) = evenListLength (q :: pre) := by rw [hsign]; rfl
            exact ih (q :: pre) (!positive) (mass * h q) hnext hsign'
              hprime' hlevel' hsort' hselect
        · rw [firstExitDepthFrontier, if_neg hk, if_neg ht, List.append_nil] at hstate
          exact ih pre positive mass hpre hsign hprime' hlevel' hskipSort hstate

/-- The ordinary parity-safe root supplies complete inherited validity at
every selected rank, including zero. The lower first-prime cutoff remains
an explicit and genuine input. -/
theorem mem_firstExitDepthFrontier_ordinaryParityRosser_admissible
    (lower : Bool) (Q : ℝ) (hQ : 1 < Q) (k : ℕ)
    (h : ℕ → ℝ) (carrier : List ℕ)
    (hsort : carrier.Pairwise (· > ·)) (hprime : ∀ p ∈ carrier, p.Prime)
    (hlevel : lower = true → ∀ p ∈ carrier, (p : ℝ) < Q)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k (ordinaryParityRosserPolicy lower Q)
      h [] true 1 carrier) :
    ordinaryRosserPrefixAdmissible lower Q state.selectedPrefix := by
  exact (mem_firstExitDepthFrontier_ordinaryParityRosser_valid lower Q k h [] carrier
    true 1 (ordinaryRosserPrefixAdmissible_nil lower hQ) rfl hprime hlevel
    (by simpa only [List.append_nil, List.pairwise_reverse] using hsort) state hstate).1

/-- Actual prime carriers pay primality and sorting, so no prefix-validity
hypothesis is needed to use an ordinary parity-safe parent frontier. -/
theorem actualPrimeFrontier_ordinaryParityRosser_admissible
    (lower : Bool) (Q : ℝ) (hQ : 1 < Q) (k : ℕ)
    (N cap : ℕ) (z : ℝ) (hzQ : lower = true → z ≤ Q)
    (h : ℕ → ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k (ordinaryParityRosserPolicy lower Q)
      h [] true 1 (roughPrimeUniverse N cap 0 z)) :
    ordinaryRosserPrefixAdmissible lower Q state.selectedPrefix := by
  exact mem_firstExitDepthFrontier_ordinaryParityRosser_admissible lower Q hQ k h _
    (roughPrimeUniverse_pairwise_gt N cap 0 z) (fun _ hp => mem_roughPrimeUniverse_prime hp)
    (fun hl _ hp => (mem_roughPrimeUniverse_upper hp).trans_le (hzQ hl)) state hstate

end

end ImbalancedChen
