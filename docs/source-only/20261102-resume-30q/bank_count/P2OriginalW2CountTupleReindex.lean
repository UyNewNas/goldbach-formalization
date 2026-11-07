import ImbalancedChen.P2OriginalW2MotherOccurrenceReindex
import ImbalancedChen.P2OriginalHalfOpenProfileCarrier
import ImbalancedChen.P2OriginalLiteralW1OldProfile

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The finite count-side bridge to O's existing pairHalf carrier. Every
summand may be an actual old count, a count remainder, or an arbitrary
selected-history test. No count/profile comparison is a premise.
The same Q and the literal two physical square gates are retained.
-/
namespace ImbalancedChen.P2OriginalW2CountTupleReindex

noncomputable section
open Finset Wu2008DoubleSieve
open scoped Classical BigOperators
open P5OriginalActionMassBound P2OriginalBankChildPrimeMass
open P2OriginalHalfOpenProfileCarrier P2W2PhysicalChildFeedback
open P2OriginalW2MotherOccurrenceReindex
open P2AllW1SameQRawCountInduction
open P2OriginalW2ComplementAction P2FrozenReceiverCountActions
open P2EnhancedTwentyOneSameQWeighted (cutoff)

/-- Physical gates on the actual integer primes, with no reset of Q. -/
theorem pairGate_iff_normalized {N d : ℕ} {Q L : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hL : 0 < L)
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) (p : Fin 2 → ℕ) (hp : ∀ i, 0 < p i) :
    PairGate Q d (p 0) (p 1) ↔
      2*normalizedLog N L p 1 < 1 ∧
        2*normalizedLog N L p 0+normalizedLog N L p 1 < 1 := by
  have hNR : (1:ℝ) < N := by exact_mod_cast hN
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hg := P2OriginalChildPhysicalNormalization.physical_pair_squares hNR
    0 L (normalizedLog N L p 0) (normalizedLog N L p 1) hL
  simp only [Real.rpow_zero, one_mul, zero_add,
    normalizedLog_rpow hN hL p hp 0, normalizedLog_rpow hN hL p hp 1] at hg
  unfold PairGate
  rw [hQ, mul_assoc (d:ℝ), mul_lt_mul_left hdR, mul_lt_mul_left hdR]
  exact hg

theorem pairWindows_primes {N : ℕ} {L : ℝ} {a : W2Parameters}
    {p : Fin 2 → ℕ} {k : Fin 4} (hw : pairWindows N L a p k) :
    ∀ i, (p i).Prime ∧ ¬ p i ∣ N := by
  fin_cases k <;> simp only [pairWindows] at hw
  all_goals
    intro i
    fin_cases i
    · have hh := mem_primeWindow.mp hw.1
      exact ⟨hh.1,hh.1.coprime_iff_not_dvd.mp hh.2.1⟩
    · have hh := mem_primeWindow.mp hw.2
      exact ⟨hh.1,hh.1.coprime_iff_not_dvd.mp hh.2.1⟩

/-- Both directions include prime-box admission. O's membership lemma
alone did not supply this finite count carrier bijection. -/
theorem pair_count_carrier_membership {N d : ℕ} {Q L : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hL : 0 < L)
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) {a : W2Parameters} (ha : W2Geometry a)
    (k : Fin 4) (p : Fin 2 → ℕ) :
    p ∈ (actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5)).filter
      (fun p => normalizedLog N L p ∈ pairHalf a k) ↔
      pairWindows N L a p k ∧ p 0 < p 1 ∧ PairGate Q d (p 0) (p 1) := by
  rw [mem_filter]
  constructor
  · rintro ⟨hp,hx⟩
    have hprime : ∀ i, (p i).Prime ∧ ¬ p i ∣ N :=
      fun i => ⟨(mem_actualPrimeBoxTuples_iff.mp hp i).1,
        (mem_actualPrimeBoxTuples_iff.mp hp i).2.1⟩
    have hw := (pair_windows_membership hN hL ha k p hprime).mp hx
    have hg := pairHalf_geometry ha k hx
    exact ⟨hw.1,hw.2.1,(pairGate_iff_normalized hN hd hL hQ p
      (fun i => (hprime i).1.pos)).mpr ⟨hg.2.2.1,hg.2.2.2⟩⟩
  · rintro ⟨hw,horder,hgate⟩
    have hprime := pairWindows_primes hw
    have hpos : ∀ i, 0 < p i := fun i => (hprime i).1.pos
    have hg := (pairGate_iff_normalized hN hd hL hQ p hpos).mp hgate
    have hx := (pair_windows_membership hN hL ha k p hprime).mpr
      ⟨hw,horder,hg.2⟩
    refine ⟨mem_actualPrimeBoxTuples_iff.mpr (fun i => ?_),hx⟩
    have hc := mem_logPrimeBox.mp (pairHalf_in_cube ha k hx) i
    have hb := (normalizedLog_window hN hL p hpos i (1/10) (3/5)).mp hc
    refine ⟨(hprime i).1,(hprime i).2,?_,?_⟩
    · convert hb.1 using 1 <;> congr 1 <;> ring
    · convert hb.2 using 1 <;> congr 1 <;> ring

/-- This elementary bijection preserves the ordered pair, rather than
its product; an arbitrary pair summand can carry the entire old history. -/
theorem ordered_pair_sum_bijection (S : Finset (Fin 2 → ℕ)) (P R : Finset ℕ)
    (G : ℕ → ℕ → Prop) (F : ℕ → ℕ → ℝ)
    (hS : ∀ t, t ∈ S ↔ t 0 ∈ P ∧ t 1 ∈ R ∧ G (t 0) (t 1)) :
    (∑ p ∈ P, ∑ q ∈ R, if G p q then F p q else 0) =
      ∑ t ∈ S, F (t 0) (t 1) := by
  rw [← sum_product, ← sum_filter]
  symm
  apply sum_bij (fun t _ => (t 0,t 1))
  · intro t ht
    have hh := (hS t).mp ht
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hh.1,hh.2.1⟩,hh.2.2⟩
  · intro t ht u hu he
    have he0 := congrArg Prod.fst he
    have he1 := congrArg Prod.snd he
    funext i
    fin_cases i
    · exact he0
    · exact he1
  · intro pq hpq
    obtain ⟨hmem,hg⟩ := mem_filter.mp hpq
    obtain ⟨hp,hq⟩ := mem_product.mp hmem
    refine ⟨![pq.1,pq.2],?_,by simp⟩
    exact (hS _).mpr (by simpa using And.intro hp (And.intro hq hg))
  · intro t ht
    rfl

/-- The four literal source rectangles, written as sums only to expose
the original count occurrence. The existing pairWindows/pairHalf data
remain the authority for their geometry. There is no new action bank. -/
def windowOccurrence (N : ℕ) (Q L : ℝ) (d : ℕ) (a : W2Parameters)
    (k : Fin 4) (F : ℕ → ℕ → ℝ) : ℝ :=
  let win (x y : ℝ) := primeWindow N ((N:ℝ)^(L*x)) ((N:ℝ)^(L*y))
  let pair (P R : Finset ℕ) := ∑ p ∈ P, ∑ q ∈ R,
    if p < q ∧ PairGate Q d p q then F p q else 0
  match k with
  | 0 => pair (win (a0 a) (a2 a)) (win (a0 a) (a2 a))
  | 1 => pair (win (a0 a) (a1 a)) (win (a2 a) (a3 a))
  | 2 => pair (win (a0 a) (a1 a)) (win (a0 a) (a1 a))
  | 3 => pair (win (a0 a) (a1 a)) (win (a1 a) (a2 a))

/-- All four full arithmetic sums, with the lower walls still present.
Specializing F to old.upper, an old remainder, or a selected-history
indicator needs no additional source-count equality. -/
theorem all_four_window_occurrences_reindex {N d : ℕ} {Q L : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hL : 0 < L)
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) {a : W2Parameters} (ha : W2Geometry a)
    (k : Fin 4) (F : ℕ → ℕ → ℝ) :
    windowOccurrence N Q L d a k F =
      ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5),
        if normalizedLog N L p ∈ pairHalf a k then F (p 0) (p 1) else 0 := by
  rw [← sum_filter]
  fin_cases k <;> simp only [windowOccurrence]
  all_goals
    apply ordered_pair_sum_bijection
    intro p
    simpa only [pairWindows, and_assoc] using
      pair_count_carrier_membership hN hd hL hQ ha _ p

/-- The actual fixed/first-prime cutoffs of Gamma5/6 and Gamma7/8. -/
def occurrenceCutoff (Q : ℝ) (d : ℕ) (a : W2Parameters) (k : Fin 4)
    (p q : ℕ) : ℝ :=
  if k.val < 2 then cutoff Q d a.s0 else (p:ℝ)

def sourceGoodOccurrence (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) (a : W2Parameters) (k : Fin 4) : ℝ :=
  let A := cutoff Q d a.s0
  let B := cutoff Q d a.phi1
  let C := cutoff Q d a.phi2
  let D := cutoff Q d a.phi3
  match k with
  | 0 => goodPairCount Q old d (primeWindow N A C) (primeWindow N A C) (fun _ _ => A)
  | 1 => goodPairCount Q old d (primeWindow N A B) (primeWindow N C D) (fun _ _ => A)
  | 2 => goodPairCount Q old d (primeWindow N A B) (primeWindow N A B) (fun p _ => (p:ℝ))
  | 3 => goodPairCount Q old d (primeWindow N A B) (primeWindow N B C) (fun p _ => (p:ℝ))

theorem sourceGoodOccurrence_eq_window {N d : ℕ} {Q L : ℝ}
    (hd : 0 < d) (hQ : Q = (d:ℝ)*(N:ℝ)^L) (old : PhysicalState)
    (a : W2Parameters) (k : Fin 4) :
    sourceGoodOccurrence N Q old d a k =
      windowOccurrence N Q L d a k
        (fun p q => old.upper (d*p*q) (occurrenceCutoff Q d a k p q)) := by
  have hc (s : ℝ) : cutoff Q d s = (N:ℝ)^(L*(1/s)) := by
    rw [P2OriginalLiteralW1OldProfile.cutoff_eq_physical_power hd hQ]
    congr 1
    ring
  fin_cases k <;>
    simp only [sourceGoodOccurrence, windowOccurrence, goodPairCount, occurrenceCutoff,
      hc, a0, a1, a2, a3]
  all_goals norm_num

/-- A literal old count-state occurrence, not a table/profile surrogate.
The theorem holds for the actual immutable iterate as well as any state. -/
theorem all_four_old_count_occurrences_reindex {N d : ℕ} {Q L : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hL : 0 < L)
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) (old : PhysicalState)
    {a : W2Parameters} (ha : W2Geometry a) (k : Fin 4) :
    sourceGoodOccurrence N Q old d a k =
      ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5),
        if normalizedLog N L p ∈ pairHalf a k then
          old.upper (d*p 0*p 1) (occurrenceCutoff Q d a k (p 0) (p 1)) else 0 := by
  rw [sourceGoodOccurrence_eq_window hd hQ]
  exact all_four_window_occurrences_reindex hN hd hL hQ ha k _

/-- In particular the excluded D5 cost is retained as a positive raw
count. No old defect is evaluated on any rejected pair. -/
def sourceRejectedOccurrence (N : ℕ) (Q : ℝ) (d : ℕ)
    (a : W2Parameters) (k : Fin 4) : ℝ :=
  let A := cutoff Q d a.s0
  let B := cutoff Q d a.phi1
  let C := cutoff Q d a.phi2
  let D := cutoff Q d a.phi3
  match k with
  | 0 => rejectedPairCount N Q d (primeWindow N A C) (primeWindow N A C) (fun _ _ => A)
  | 1 => rejectedPairCount N Q d (primeWindow N A B) (primeWindow N C D) (fun _ _ => A)
  | 2 => rejectedPairCount N Q d (primeWindow N A B) (primeWindow N A B) (fun p _ => (p:ℝ))
  | 3 => rejectedPairCount N Q d (primeWindow N A B) (primeWindow N B C) (fun p _ => (p:ℝ))

/-- This binds the four finite slots to the existing paid mother, once
each. In particular Gamma7/8 are not counted again as switched tails. -/
theorem four_original_occurrences_split (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) (j : Fin 36) (hR : 1 ≤ Q/(d:ℝ)) :
    let a := originalW2At j
    let A := cutoff Q d a.s0
    let B := cutoff Q d a.phi1
    let C := cutoff Q d a.phi2
    let D := cutoff Q d a.phi3
    let Z := cutoff Q d a.s
    paidPairs N Q old d A C A C + paidPairs N Q old d A B C D +
      paidPrefix N Q old d A B C D Z [0,0] +
      paidPrefix N Q old d A B C D Z [0,1] =
        (∑ k : Fin 4, sourceGoodOccurrence N Q old d a k) +
        (∑ k : Fin 4, sourceRejectedOccurrence N Q d a k) := by
  dsimp only
  obtain ⟨hAB,hBC,hCD,hDZ⟩ := P2AllW2SameQRawCountAction.bank_cutoff_order j hR
  rw [paidPairs_split, paidPairs_split,
    paidPrefix_seven_split N Q old d (hBC.trans (hCD.trans hDZ)),
    paidPrefix_eight_split N Q old d hAB (hBC.trans (hCD.trans hDZ)) (hCD.trans hDZ)]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, sourceGoodOccurrence,
    sourceRejectedOccurrence]
  <;> ring

/-- Everything outside the four good pairs remains explicit: the three
old lower children, rejected counts, long quotient words, collisions,
and the three restored-window bad-prime costs. No analytic payment. -/
def countRemainder (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) (a : W2Parameters) : ℝ :=
  let A := cutoff Q d a.s0
  let B := cutoff Q d a.phi1
  let C := cutoff Q d a.phi2
  let D := cutoff Q d a.phi3
  let Z := cutoff Q d a.s
  -negativeWindow N Q (P5OriginalU5FrozenSource.receiver N) old d A Z -
    negativeWindow N Q (P5OriginalU5FrozenSource.receiver N) old d A C -
    negativeWindow N Q (P5OriginalU5FrozenSource.receiver N) old d A D +
    (∑ k : Fin 4, sourceRejectedOccurrence N Q d a k) +
    higherPaidSwitched N Q old d A B C D Z +
    P2EnhancedTwentyOneQuotientFinite.collisionSwitched N d N A B C D Z +
    fourthRowMotherBadPrime N d A Z + fourthRowMotherBadPrime N d A C +
    fourthRowMotherBadPrime N d A D

theorem paidW2_eq_four_good_counts (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) (j : Fin 36) (hR : 1 ≤ Q/(d:ℝ)) :
    paidW2 N Q old d j =
      (4*old.upper d (cutoff Q d (originalW2At j).s0) +
        old.upper d (cutoff Q d (originalW2At j).phi1) +
        (∑ k : Fin 4, sourceGoodOccurrence N Q old d (originalW2At j) k) +
        countRemainder N Q old d (originalW2At j))/5 := by
  have h4 := four_original_occurrences_split N Q old d j hR
  dsimp only at h4
  unfold paidW2 paidRest countRemainder
  dsimp only
  rw [paidSwitched_occurrences]
  linarith

theorem paidW2_eq_four_tuple_counts {N d : ℕ} {Q L : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hL : 0 < L)
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) (old : PhysicalState) (j : Fin 36) :
    paidW2 N Q old d j =
      (4*old.upper d (cutoff Q d (originalW2At j).s0) +
        old.upper d (cutoff Q d (originalW2At j).phi1) +
        (∑ k : Fin 4,
          ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5),
            if normalizedLog N L p ∈ pairHalf (originalW2At j) k then
              old.upper (d*p 0*p 1)
                (occurrenceCutoff Q d (originalW2At j) k (p 0) (p 1)) else 0) +
        countRemainder N Q old d (originalW2At j))/5 := by
  have hR := P2OriginalPositiveSameQMassLift.sameQ_residual_gt_one hN hd hL hQ
  rw [paidW2_eq_four_good_counts N Q old d j hR.le]
  simp_rw [all_four_old_count_occurrences_reindex hN hd hL hQ old
    (originalRepairedW2Bank_geometry _ (originalW2At_mem j))]

/-- The previous-generation enclosure is supplied by the existing
actual Rosser/count recursion. No old table licence, final count bound,
seed equality, or PP estimate is an input of this exported count theorem. -/
theorem iterate_original_W2_count_tuple_upper {N d : ℕ} {Q L : ℝ}
    (hN : 1 < N) (hd : 0 < d) (hL : 0 < L)
    (hQ : Q = (d:ℝ)*(N:ℝ)^L) (bank : List P2ActualMarkedCountState.Query)
    (rounds : ℕ) (j : Fin 36) :
    let old := P2AllW2ImmutableCountRecursion.iterate N Q
      (P5OriginalU5FrozenSource.receiver N) bank rounds
    (frozenCount N d (P5OriginalU5FrozenSource.receiver N)
      (cutoff Q d (originalW2At j).s) : ℝ) ≤
      (4*old.upper d (cutoff Q d (originalW2At j).s0) +
        old.upper d (cutoff Q d (originalW2At j).phi1) +
        (∑ k : Fin 4,
          ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5),
            if normalizedLog N L p ∈ pairHalf (originalW2At j) k then
              old.upper (d*p 0*p 1)
                (occurrenceCutoff Q d (originalW2At j) k (p 0) (p 1)) else 0) +
        countRemainder N Q old d (originalW2At j))/5 + W2Charge N Q d j/5 := by
  dsimp only
  rw [← paidW2_eq_four_tuple_counts hN hd hL hQ]
  exact iterate_W2_upper N Q bank rounds j hd
    (P2OriginalPositiveSameQMassLift.sameQ_residual_gt_one hN hd hL hQ)

end
end ImbalancedChen.P2OriginalW2CountTupleReindex
