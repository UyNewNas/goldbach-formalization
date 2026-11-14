import ImbalancedChen.Part5OriginalH430OriginalReceiptMemberPullback
import ImbalancedChen.P2OriginalPairChildWindowDictionary

/-!
The original root receiver is rough at N^a.  Every actual chosen path
either still has the original one-prime word, or its old word contains
a prime strictly below N^a.  This is an arithmetic statement about the
original request recursion, not a replacement Member or count licence.

SOURCE_ONLY / UNCOMPILED.  No distribution estimate is claimed.
-/
namespace ImbalancedChen.Part5OriginalH430FirstReceiptExit

noncomputable section
open Set
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2OriginalPairChildWindowDictionary
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430IntegerItineraries Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430BankSlotTargets Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedBranches Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedAdmission Part5OriginalH430RequestedMember
open Part5OriginalH430TaggedArithmeticReceivers

private theorem a_pos : (0 : ℝ) < a := by norm_num [a]

/-- The only possibly closed first-prime boundary is Buchstab's.
An actual prime coprime to N cannot lie at N^(417/5000). -/
theorem prime_lt_original_cutoff {N q : ℕ} (hN : 1 < N)
    (hq : q.Prime) (hc : q.Coprime N) (hx : physicalPrime N q ≤ a) :
    (q : ℝ) < (N : ℝ)^a := by
  have hpow : (N : ℝ)^physicalPrime N q = (q : ℝ) :=
    actualPrimeTupleLog_rpow hN (fun _ : Fin 1 => q) (fun _ => hq.pos) 0
  have hne : physicalPrime N q ≠ a := by
    intro he
    have heR : (q : ℝ)^5000 = (N : ℝ)^417 := by
      calc
        (q : ℝ)^5000 = (N : ℝ)^(physicalPrime N q * (5000 : ℝ)) := by
          rw [Real.rpow_mul (Nat.cast_nonneg N), Real.rpow_natCast, hpow]
        _ = (N : ℝ)^417 := by
          rw [he]
          norm_num [a]
    have heNat : q^5000 = N^417 := by exact_mod_cast heR
    have hdiv : q ∣ q^5000 := by
      exact ⟨q^4999, by rw [show 5000 = 4999+1 from rfl, pow_succ, Nat.mul_comm]⟩
    rw [heNat] at hdiv
    exact (hq.coprime_iff_not_dvd.mp hc) (hq.dvd_of_dvd_pow hdiv)
  rw [← hpow]
  have hlt : physicalPrime N q < a := by
    by_contra hh
    exact hne (le_antisymm hx (le_of_not_gt hh))
  exact Real.rpow_lt_rpow_of_exponent_lt
    (by exact_mod_cast hN : (1 : ℝ) < N) hlt

private theorem singleton_below_target (j : Fin 36) (k : Fin 3) {x : ℝ}
    (hx : x ∈ W2SingletonDomain (originalW2At j) k) :
    x < 1/(originalW2At j).s := by
  obtain ⟨hs,h3,_,_,_,_⟩ :=
    P2AllW2SameQRawCountAction.original_W2_order _ (originalW2At_mem j)
  have hrec : a3 (originalW2At j) ≤ 1/(originalW2At j).s :=
    one_div_le_one_div_of_le (by linarith) h3
  have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  fin_cases k
  · exact hx.2
  · exact hx.2.trans_le (hg.2.2.2.1.trans hrec)
  · exact hx.2.trans_le hrec

private theorem normalized_le_a {L x s target : ℝ}
    (hL : 0 < L) (hs : 0 < s) (hst : s ≤ target)
    (hcap : L ≤ a*s) (hx : x/L < 1/target) : x ≤ a := by
  have ht : 0 < target := hs.trans_le hst
  have hm := (div_lt_div_iff₀ hL ht).mp hx
  have hbound := mul_le_mul_of_nonneg_left hst a_pos.le
  have hxl : x < L/target := (lt_div_iff₀ ht).mpr (by simpa only [one_mul] using hm)
  have hla : L/target ≤ a := (div_le_iff₀ ht).mpr (hcap.trans hbound)
  exact hxl.le.trans hla

/-- Before the first prime append, the actual retained/fixed requests
can only lower the comparison cutoff.  Every other chosen edge appends
an actual small prime.  All 70+36 rows and both Buchstab directions are
read from the original LocalDomain and original_W2_order. -/
theorem child_first_receipt_exit {N g : ℕ} {Q : ℝ} {r : Request} {e : Edge N}
    (hr : Coherent N Q r) (he : e ∈ children N Q g r)
    (hs : 2 ≤ r.node.physical.argument)
    (hcap : residual r.node.physical ≤ a*r.node.physical.argument) :
    (appendedWord (edgeShape e) (edgePrimes e) = [] ∧
      2 ≤ (nextRequest r e).node.physical.argument ∧
      residual (nextRequest r e).node.physical ≤
        a*(nextRequest r e).node.physical.argument) ∨
    ∃ q ∈ appendedWord (edgeShape e) (edgePrimes e),
      q.Prime ∧ (q : ℝ) < (N : ℝ)^a := by
  have had := child_admission hr he
  have hd := had.2.1
  have hsmall (q : ℕ) (hm : q ∈ appendedWord (edgeShape e) (edgePrimes e))
      (hx : physicalPrime N q ≤ a) :
      ∃ q ∈ appendedWord (edgeShape e) (edgePrimes e),
        q.Prime ∧ (q : ℝ) < (N : ℝ)^a :=
    ⟨q,hm,(had.2.2 q hm).1,
      prime_lt_original_cutoff hr.target_gt_one (had.2.2 q hm).1 (had.2.2 q hm).2 hx⟩
  have hs0 : 0 < r.node.physical.argument := by linarith
  cases e with
  | retained i =>
      exact Or.inl ⟨by simp [edgeShape,appendedWord],hs,hcap⟩
  | w1Fixed i j =>
      have harg := hd.2.1.trans (W1_target_le_anchor i j)
      exact Or.inl ⟨by simp [edgeShape,appendedWord],hs.trans harg,
        hcap.trans (mul_le_mul_of_nonneg_left harg a_pos.le)⟩
  | w2Fixed j anchor =>
      have harg := hd.2.1.trans (W2_target_le_fixed j anchor)
      exact Or.inl ⟨by simp [edgeShape,appendedWord],hs.trans harg,
        hcap.trans (mul_le_mul_of_nonneg_left harg a_pos.le)⟩
  | buchstab up q =>
      apply Or.inr
      apply hsmall q.val (by cases up <;> simp [edgeShape,edgePrimes,appendedWord])
      have hdata : 0 < physicalPrime N q.val ∧
          r.node.physical.argument - 1 ≤
            residual r.node.physical / physicalPrime N q.val - 1 := by
        cases up
        · exact ⟨hd.2.2.1.1,hd.2.2.2.1⟩
        · exact ⟨hd.2.1.1,(le_max_right 2 _).trans hd.2.2.1⟩
      have hh : r.node.physical.argument ≤
          residual r.node.physical / physicalPrime N q.val := by linarith [hdata.2]
      have hm := (le_div_iff₀ hdata.1).mp hh
      apply (mul_le_mul_left hs0).mp
      exact (hm.trans hcap).trans_eq (mul_comm _ _)
  | w1Prime i j q =>
      apply Or.inr
      apply hsmall q.val (by simp [edgeShape,edgePrimes,appendedWord])
      exact normalized_le_a hd.1 hs0 hd.2.2.2.1 hcap hd.2.2.1.2
  | w2Prime j k q =>
      apply Or.inr
      apply hsmall q.val (by simp [edgeShape,edgePrimes,appendedWord])
      exact normalized_le_a hd.1 hs0 hd.2.2.2.1 hcap
        (singleton_below_target j k hd.2.2.1)
  | w2Pair j k q =>
      apply Or.inr
      apply hsmall q.1.val (by simp [edgeShape,edgePrimes,appendedWord])
      have hx := (pairHalf_below_target j k
        ((strict_pair_iff_half_not_wall j k _).mp hd.2.2.1).1).1
      exact normalized_le_a hd.1 hs0 hd.2.2.2.1 hcap hx

/-- This invariant only records the concrete ordered old word. It makes
no assertion about the cardinality or density of an ordinary child. -/
def ReceiptState (N p : ℕ) (r : Request) : Prop :=
  ∃ xs : List ℕ, r.old = p::xs ∧
    ((xs = [] ∧ 2 ≤ r.node.physical.argument ∧
        residual r.node.physical ≤ a*r.node.physical.argument) ∨
     ∃ q ∈ xs, q.Prime ∧ (q : ℝ) < (N : ℝ)^a)

theorem receiptState_child {N p g : ℕ} {Q : ℝ} {r : Request} {e : Edge N}
    (hr : Coherent N Q r) (he : e ∈ children N Q g r)
    (hs : ReceiptState N p r) : ReceiptState N p (nextRequest r e) := by
  obtain ⟨xs,hw,hxs⟩ := hs
  let ys := appendedWord (edgeShape e) (edgePrimes e)
  refine ⟨xs++ys,by simp only [nextRequest,hw,List.cons_append]; rfl,?_⟩
  rcases hxs with ⟨rfl,harg,hcap⟩ | ⟨q,hq,hpr,hsmall⟩
  · rcases child_first_receipt_exit hr he harg hcap with h | ⟨q,hq,hpr,hsmall⟩
    · exact Or.inl ⟨by simpa only [List.nil_append,ys] using h.1,h.2⟩
    · exact Or.inr ⟨q,by simpa only [List.nil_append,ys] using hq,hpr,hsmall⟩
  · exact Or.inr ⟨q,List.mem_append.mpr (Or.inl hq),hpr,hsmall⟩

theorem receiptState_replay {N p g : ℕ} {Q : ℝ} {r : Request} {es : List (Edge N)}
    (hr : Coherent N Q r) (hc : ChosenPath N Q g r es)
    (hs : ReceiptState N p r) : ReceiptState N p (replay r es) := by
  induction es generalizing g r with
  | nil => exact hs
  | cons e es ih =>
      cases g with
      | zero => exact False.elim hc
      | succ g => exact ih (child_coherent hr hc.1) hc.2 (receiptState_child hr hc.1 hs)

/-- Both literal U3/U4 roots, their immutable 430-round selection and
every generated occurrence.  The same small prime remains in the
prefix through all later full/selected inherited filters. -/
theorem actual_history_receipt_state {N n p : ℕ} {k : Root} {t : ℝ}
    {o : Occurrence N} (hN : 2 ≤ N) (ht : 0 ≤ t) (hu : t ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) (hp : p ∈ originalBand N k)
    (ho : o ∈ rootHistory N n k t p) : ReceiptState N p o.current := by
  have hroot := root_coherent (by omega : 1 < N) ht hu hn
    (original_band_prime hp) (original_band_geometry hN hp)
  have hs : ReceiptState N p (rootRequest N n k t p) := by
    refine ⟨[],rfl,Or.inl ⟨rfl,?_,?_⟩⟩
    · exact le_max_left 2 _
    · change residual (frozenRoot n k t (physicalPrime N p)).physical ≤ _
      rw [frozenRoot_residual]
      change frozenLevel n (sourceRoot k t (physicalPrime N p)).physical.total - physicalPrime N p ≤
        a * max 2 ((frozenLevel n (sourceRoot k t (physicalPrime N p)).physical.total -
          physicalPrime N p)/a)
      simpa only [mul_comm] using
        (div_le_iff₀ a_pos).mp (le_max_right 2
          ((frozenLevel n (sourceRoot k t (physicalPrime N p)).physical.total -
            physicalPrime N p)/a))
  rw [(history_facts ho).2.2]
  exact receiptState_replay hroot (history_facts ho).1 hs

end
end ImbalancedChen.Part5OriginalH430FirstReceiptExit
