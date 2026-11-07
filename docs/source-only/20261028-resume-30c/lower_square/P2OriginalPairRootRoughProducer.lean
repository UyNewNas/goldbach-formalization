import ImbalancedChen.P2LowerIntegerRetainedSupport
import ImbalancedChen.CurrentChenP5CausalRhoFactorization

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The marked L5/L6 pair is an incoming root, not an ordinary L1/L2 word
on which new initial pair-cube tests may be imposed. Its two external
prime labels occur in decreasing physical order. A concrete continuation
policy runs the actual finite CapPlan from this stored root. The root
has even length two, so even rough rank and even full rank agree.

Retained rough support for this computed policy yields a real carrier
subword and its actual accepted trace. No hRoughSupport or modulus-bound
licence is a premise. The relation of the root cap and finite plan to
all original selected branches remains an explicit integration task.
-/

namespace ImbalancedChen.P2OriginalPairRootRoughProducer
noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2LowerIntegerRetainedSupport P5CausalRhoFactorization

/-- External marked primes start the continuation; no new ordinary
    first-square or second-cube predicate is invented for this root. -/
def pairRoot (N : ℕ) (p : ℕ × ℕ) (seedCap : ℝ) : Trace :=
  ⟨[coordinate N p.2, coordinate N p.1], seedCap, [], true⟩

def warmTrace {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (base : Trace) (N : ℕ) (pre : List ℕ) : Trace :=
  run P a b base (physicalWord N pre)

def warmRetain {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (base : Trace) (N : ℕ) (pre : List ℕ) : Bool :=
  (warmTrace P a b base N pre).accepted

def pairPolicy {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b seedCap : ℝ) (N : ℕ) (p : ℕ × ℕ) : List ℕ → Bool :=
  warmRetain P a b (pairRoot N p seedCap) N

@[simp] theorem warmTrace_word {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (base : Trace) (N : ℕ) (pre : List ℕ) :
    (warmTrace P a b base N pre).word = base.word ++ physicalWord N pre :=
  run_word P a b base (physicalWord N pre)

theorem warmTrace_cons {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (base : Trace) (N p : ℕ) (pre : List ℕ) :
    warmTrace P a b base N (p::pre) =
      step P a b (warmTrace P a b base N pre) (coordinate N p) := by
  unfold warmTrace
  rw [physicalWord_cons, run_append]
  rfl

theorem warmRetain_cons_iff {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (base : Trace) (N p : ℕ) (pre : List ℕ) :
    warmRetain P a b base N (p::pre) = true ↔
      warmRetain P a b base N pre = true ∧
        admission (warmTrace P a b base N pre) (coordinate N p) := by
  unfold warmRetain
  rw [warmTrace_cons, step_accepted_iff]

private theorem evenListLength_eq (pre : List ℕ) :
    evenListLength pre = decide (Even pre.length) := by
  induction pre with
  | nil => simp [evenListLength]
  | cons p pre ih =>
      simp only [evenListLength, ih, List.length_cons, Nat.even_add_one, decide_not]

/-- The odd rough bypass is exactly the full-word odd bypass, because
    the frozen incoming marked root has two slots. -/
private theorem next_policy_iff_warm {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (base : Trace) (hlen : base.word.length = 2)
    (N p : ℕ) (pre : List ℕ)
    (hpre : warmRetain P a b base N pre = true) :
    evenFirstExitPolicy (warmRetain P a b base N) (!(evenListLength pre))
      (p::pre) = true ↔ warmRetain P a b base N (p::pre) = true := by
  cases hs : evenListLength pre with
  | false =>
      simp only [hs, Bool.not_false, evenFirstExitPolicy, Bool.not_true, Bool.false_or]
  | true =>
      have he : Even pre.length := by
        have hs' := hs
        rw [evenListLength_eq] at hs'
        exact of_decide_eq_true hs'
      have hwlen : (warmTrace P a b base N pre).word.length = 2 + pre.length := by
        simp [warmTrace_word, physicalWord, hlen]
      have hnonempty : (warmTrace P a b base N pre).word.length ≠ 0 := by omega
      have hodd : ((warmTrace P a b base N pre).word.length + 1) % 2 ≠ 0 := by
        rw [Nat.even_iff] at he
        omega
      have hnext : warmRetain P a b base N (p::pre) = true := by
        apply (warmRetain_cons_iff P a b base N p pre).mpr
        exact ⟨hpre, by simp [admission, hnonempty, hodd]⟩
      simp only [hs, Bool.not_true, evenFirstExitPolicy, Bool.not_false, Bool.true_or]
      exact iff_of_true trivial hnext

/-- This constructive equivalence recovers acceptance from the actual
    first-exit generator, including every earlier frozen cap test. -/
theorem validSelection_iff_warm_trace {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (base : Trace) (hlen : base.word.length = 2)
    (N : ℕ) (chosen : List ℕ) :
    ∀ pre : List ℕ, warmRetain P a b base N pre = true →
      (FirstExitValidSelection (evenFirstExitPolicy (warmRetain P a b base N))
        pre (evenListLength pre) chosen ↔
        warmRetain P a b base N (chosen.reverse ++ pre) = true) := by
  induction chosen with
  | nil =>
      intro pre hpre
      simp only [FirstExitValidSelection, List.reverse_nil, List.nil_append, hpre]
  | cons p ps ih =>
      intro pre hpre
      have hnext := next_policy_iff_warm P a b base hlen N p pre hpre
      rw [FirstExitValidSelection]
      constructor
      · rintro ⟨hpass, hvalid⟩
        have hpassed := hnext.mp hpass
        have htail : FirstExitValidSelection
            (evenFirstExitPolicy (warmRetain P a b base N))
            (p::pre) (evenListLength (p::pre)) ps := hvalid
        have hfinal := (ih (p::pre) hpassed).mp htail
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hfinal
      · intro hfinal
        have hfinal' : warmRetain P a b base N (ps.reverse ++ p::pre) = true := by
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using hfinal
        have hpassed : warmRetain P a b base N (p::pre) = true := by
          unfold warmRetain warmTrace at hfinal' ⊢
          have hw : physicalWord N (ps.reverse ++ p::pre) =
              physicalWord N (p::pre) ++ physicalWord N ps.reverse := by
            simp only [physicalWord, List.reverse_append, List.map_append]
          rw [hw, run_append] at hfinal'
          exact run_accepted_incoming P a b _ _ hfinal'
        exact ⟨hnext.mpr hpassed, (ih (p::pre) hpassed).mpr hfinal'⟩

/-- Concrete retained rough moduli, with both directions of the actual
    tree-to-trace correspondence. No initial cutoff-square margin is
    required at this marked pair root. -/
theorem pair_policy_support_iff {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b seedCap : ℝ) (N enum : ℕ) (p : ℕ × ℕ) (z0 z : ℝ) (r : ℕ) :
    r ∈ fixedEvenRoughSupport (pairPolicy P a b seedCap N p) N enum z0 z ↔
      ∃ chosen : List ℕ, chosen <+ roughPrimeUniverse N enum z0 z ∧
        (run P a b (pairRoot N p seedCap)
          (chosen.map (coordinate N))).accepted = true ∧ chosen.prod = r := by
  rw [fixedEvenRoughSupport, mem_firstExitRetainedModuli_iff_validSelection]
  have hbase : warmRetain P a b (pairRoot N p seedCap) N [] = true := rfl
  have heq (chosen : List ℕ) :
      warmRetain P a b (pairRoot N p seedCap) N chosen.reverse =
        (run P a b (pairRoot N p seedCap) (chosen.map (coordinate N))).accepted := by
    simp [warmRetain, warmTrace, physicalWord]
  constructor
  · rintro ⟨chosen, hsub, hvalid, hprod⟩
    have haccept := (validSelection_iff_warm_trace P a b (pairRoot N p seedCap)
      rfl N chosen [] hbase).mp hvalid
    exact ⟨chosen, hsub, by simpa only [List.append_nil, heq] using haccept, hprod⟩
  · rintro ⟨chosen, hsub, haccept, hprod⟩
    refine ⟨chosen, hsub, ?_, hprod⟩
    apply (validSelection_iff_warm_trace P a b (pairRoot N p seedCap)
      rfl N chosen [] hbase).mpr
    simpa only [List.append_nil, heq] using haccept

/-- The actual signed lower coefficient supplies the actual rough word;
    neither that word nor its accepted run is an input licence. -/
theorem pair_rho_nonzero_rough_word {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b seedCap : ℝ) (N enum : ℕ) (p : ℕ × ℕ) (z0 z L : ℝ) {k : ℕ}
    (hk : actualLowerSmallRoughRho (pairPolicy P a b seedCap N p)
      N enum z0 z L k ≠ 0) :
    ∃ s ∈ actualSmallRosserSupport N enum z0,
      ∃ r ∈ fixedEvenRoughSupport (pairPolicy P a b seedCap N p) N enum z0 z,
        ∃ chosen : List ℕ, chosen <+ roughPrimeUniverse N enum z0 z ∧
          chosen.prod = r ∧ k = s*r ∧
          (run P a b (pairRoot N p seedCap)
            (chosen.map (coordinate N))).accepted = true ∧
          actualLowerSmallRoughRho (pairPolicy P a b seedCap N p)
              N enum z0 z L k =
            coefficient (pairPolicy P a b seedCap N p) N enum z0 z L (s,r) := by
  obtain ⟨s, hs, r, hr, hkprod, _, _⟩ :=
    actualLowerSmallRoughRho_ne_zero_factors (pairPolicy P a b seedCap N p)
      N enum z0 z L hk
  obtain ⟨chosen, hsub, haccept, hprod⟩ :=
    (pair_policy_support_iff P a b seedCap N enum p z0 z r).mp hr
  have hpairs : (s,r) ∈ pairs (pairPolicy P a b seedCap N p) N enum z0 z :=
    Finset.mem_product.mpr ⟨hs,hr⟩
  refine ⟨s, hs, r, hr, chosen, hsub, hprod, hkprod, haccept, ?_⟩
  rw [hkprod]
  exact rho_at_pair (pairPolicy P a b seedCap N p) N enum z0 z L hpairs

end
end ImbalancedChen.P2OriginalPairRootRoughProducer
