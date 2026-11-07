import ImbalancedChen.P2AllW2SameQRawCountAction

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual W2 child substitutions, before any analytic normalization. The three
negative windows use old lower counts at the INHERITED cutoff a. The two
ordinary pair occurrences use old upper counts at a; the two-prime quotient
words (Gamma7/8) use old upper counts at the FIRST prime. Both full square
tests are required for pair feedback. Every rejected pair, every longer
quotient word, every collision and every restored bad-prime term stays raw.

The original mother currently has receiver True. Its transport to a frozen
E below is deliberately one-sided: parent and positive-child complement
counts are kept explicitly, and negative complement counts are discarded
in the safe direction. This is not a sharp E-filtered mother theorem.
-/
namespace ImbalancedChen.P2W2PhysicalChildFeedback

noncomputable section
open Finset Wu2008DoubleSieve
open scoped Classical BigOperators
open P2FrozenReceiverCountActions
open P2AllW1SameQRawCountInduction
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedTwentyOneQuotientFinite
open P2EnhancedPrefixMaskDefect (quotientCarrier)
open P5OriginalActionMassBound (originalW2At originalW2At_mem)
open P2AllW2SameQRawCountAction (bank_cutoff_order original_W2_order)

/-- Used only as the induction invariant of the concrete recursion. -/
def Encloses (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState) : Prop :=
  ∀ d z, QueryAdmitted Q d z →
    old.lower d z ≤ (frozenCount N d E z : ℝ) ∧
      (frozenCount N d E z : ℝ) ≤ old.upper d z

def complementCount (N d : ℕ) (E : ℕ → Prop) (z : ℝ) : ℝ :=
  (frozenCount N d (fun ell => ¬ E ell) z : ℝ)

theorem count_partition (N d : ℕ) (E : ℕ → Prop) (z : ℝ) :
    (frozenCount N d (fun _ => True) z : ℝ) =
      (frozenCount N d E z : ℝ) + complementCount N d E z := by
  have h := card_filter_add_card_filter_not (s := sourceSieveCarrier N d (d*N) z) E
  simpa [frozenCount, frozenCarrier, complementCount] using
    (show ((sourceSieveCarrier N d (d*N) z).card : ℝ) =
      (((sourceSieveCarrier N d (d*N) z).filter E).card : ℝ) +
        (((sourceSieveCarrier N d (d*N) z).filter (fun ell => ¬ E ell)).card : ℝ) by
          exact_mod_cast h.symm)

theorem count_le_true (N d : ℕ) (E : ℕ → Prop) (z : ℝ) :
    (frozenCount N d E z : ℝ) ≤ (frozenCount N d (fun _ => True) z : ℝ) := by
  have h : (frozenCarrier N d E z).card ≤ (sourceSieveCarrier N d (d*N) z).card :=
    card_le_card (filter_subset _ _)
  simpa [frozenCount, frozenCarrier] using (show
    ((frozenCarrier N d E z).card : ℝ) ≤ (sourceSieveCarrier N d (d*N) z).card by
      exact_mod_cast h)

@[simp] theorem complement_true (N d : ℕ) (z : ℝ) :
    complementCount N d (fun _ => True) z = 0 := by
  simp [complementCount, frozenCount, frozenCarrier]

/-- Adding a selected prime ABOVE the strict cutoff leaves the source
prime product unchanged; this statement is about unscaled source counts. -/
theorem source_mask_prime (N D M : ℕ) {p : ℕ} {z : ℝ}
    (hp : p.Prime) (hz : z ≤ (p:ℝ)) :
    sourceSieveCarrier N D (p*M) z = sourceSieveCarrier N D M z := by
  have he : ordinarySievePrimeProduct (p*M) z = ordinarySievePrimeProduct M z := by
    unfold ordinarySievePrimeProduct
    rw [primeWindow_mul_of_prime_above M hp hz]
  ext ell
  simp only [sourceSieveCarrier, mem_filter, sifted_iff_product_coprime, he]

theorem source_single_eq_frozen (N d : ℕ) {p : ℕ} {a : ℝ}
    (hp : p.Prime) (ha : a ≤ (p:ℝ)) :
    (sourceSieveCount N (d*p) (d*N) a : ℝ) =
      (frozenCount N (d*p) (fun _ => True) a : ℝ) := by
  have hc : sourceSieveCarrier N (d*p) ((d*p)*N) a =
      sourceSieveCarrier N (d*p) (d*N) a := by
    rw [show (d*p)*N = p*(d*N) by ring]
    exact source_mask_prime N (d*p) (d*N) hp ha
  simp [frozenCount, frozenCarrier, sourceSieveCount, hc]

theorem source_pair_eq_frozen (N d : ℕ) {p q : ℕ} {a : ℝ}
    (hp : p.Prime) (hq : q.Prime) (hap : a ≤ (p:ℝ)) (haq : a ≤ (q:ℝ)) :
    (sourceSieveCount N (d*p*q) (d*N) a : ℝ) =
      (frozenCount N (d*p*q) (fun _ => True) a : ℝ) := by
  have hc : sourceSieveCarrier N (d*p*q) ((d*p*q)*N) a =
      sourceSieveCarrier N (d*p*q) (d*N) a := by
    rw [show (d*p*q)*N = q*(p*(d*N)) by ring,
      source_mask_prime N (d*p*q) (p*(d*N)) hq haq,
      source_mask_prime N (d*p*q) (d*N) hp hap]
  simp [frozenCount, frozenCarrier, sourceSieveCount, hc]

/-- The literal two-prime quotient keeps cutoff p, never q or a reset Q. -/
theorem quotient_pair_eq_frozen (N d : ℕ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    ((quotientCarrier N d [p,q]).card : ℝ) =
      (frozenCount N (d*p*q) (fun _ => True) (p:ℝ) : ℝ) := by
  have hpqR : (p:ℝ) ≤ q := by exact_mod_cast hpq.le
  have hsel : Sifted (d*N) (d*p*q) (p:ℝ) := by
    rw [sifted_mul_iff, sifted_mul_iff]
    refine ⟨⟨?_, sifted_prime_of_le hp le_rfl⟩, sifted_prime_of_le hq hpqR⟩
    intro r hr hc hrz
    exact siftedLE_of_dvd_modulus (dvd_mul_right d N) (p:ℝ) r hr hc hrz.le
  have he := sourceSieveCarrier_eq_ite N (d*p*q) (d*N) (p:ℝ)
  rw [if_pos hsel] at he
  have hs := source_pair_eq_frozen N d hp hq le_rfl hpqR
  have hc : ((sieveCarrier N (d*p*q) (d*N) (p:ℝ)).card : ℝ) =
      (frozenCount N (d*p*q) (fun _ => True) (p:ℝ) : ℝ) := by
    simpa only [sourceSieveCount, Int.cast_natCast, he] using hs
  simpa [quotientCarrier, mul_assoc] using hc

/-- Exactly the two physical full-square gates. No excluded D5 point
gets a child-state estimate. -/
def PairGate (Q : ℝ) (d p q : ℕ) : Prop :=
  (d:ℝ)*(q:ℝ)^2 < Q ∧ (d:ℝ)*(p:ℝ)^2*(q:ℝ) < Q

theorem pair_query {Q a : ℝ} {d p q : ℕ} (hd : 0<d)
    (hp : p.Prime) (hq : q.Prime) (hg : PairGate Q d p q)
    (ha : a ≤ (p:ℝ)) : QueryAdmitted Q (d*p*q) a := by
  have hD : (0:ℝ)<(d*p*q:ℕ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos hd hp.pos) hq.pos
  have hr : (p:ℝ)<Q/(d*p*q:ℕ) := by
    apply (lt_div_iff₀ hD).mpr
    simpa only [Nat.cast_mul, pow_two, mul_assoc, mul_comm, mul_left_comm] using hg.2
  have hfloor : Q/(d*p*q:ℕ)<(P2ActualMarkedCountState.rootLevel Q (d*p*q):ℝ) := by
    simpa only [P2ActualMarkedCountState.rootLevel, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one (Q/(d*p*q:ℕ))
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  exact ⟨Nat.mul_pos (Nat.mul_pos hd hp.pos) hq.pos,
    hp1.trans hr, ha.trans (hr.trans hfloor).le⟩

def negativeChild (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    (d p : ℕ) (a : ℝ) : ℝ :=
  if QueryAdmitted Q (d*p) a then old.lower (d*p) a
  else (frozenCount N (d*p) E a : ℝ)

def negativeWindow (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    (d : ℕ) (a u : ℝ) : ℝ :=
  ∑ p ∈ primeWindow N a u, negativeChild N Q E old d p a

/-- The entire restored N-window is physically admitted, including old
prefix primes. Coprimality with d is not silently added to a negative term. -/
theorem window_child_query {N d p : ℕ} {Q s a u : ℝ}
    (hd : 0<d) (hR : 1<Q/(d:ℝ)) (hs : 2≤s)
    (hu : u≤cutoff Q d s) (hp : p∈primeWindow N a u) :
    QueryAdmitted Q (d*p) a := by
  have hpm := mem_primeWindow.mp hp
  have hdR : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hs0 : 0<s := by linarith
  have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr hpm.1.pos
  have hnonneg : (0:ℝ)≤Q/(d:ℝ) := by linarith
  have he : (1/s)*2≤1 := by
    have hh := (div_le_one hs0).mpr hs
    simpa [div_eq_mul_inv,mul_comm] using hh
  have hcutsq : (cutoff Q d s)^2≤Q/(d:ℝ) := by
    unfold cutoff
    rw [←Real.rpow_two,←Real.rpow_mul hnonneg]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hR.le he
  have hpcut := hpm.2.2.2.trans_le hu
  have hz0 : 0≤cutoff Q d s := Real.rpow_nonneg hnonneg _
  have hpsq : (p:ℝ)^2<Q/(d:ℝ) := by nlinarith
  have hfull : (d:ℝ)*(p:ℝ)^2<Q := by
    have hh := (lt_div_iff₀ hdR).mp hpsq
    nlinarith
  exact child_query_of_square hd hpm.1 hfull hpm.2.2.1

theorem negativeWindow_eq_old_children (N : ℕ) (Q : ℝ) (E : ℕ → Prop)
    (old : PhysicalState) {d : ℕ} {s a u : ℝ}
    (hd : 0<d) (hR : 1<Q/(d:ℝ)) (hs : 2≤s) (hu : u≤cutoff Q d s) :
    negativeWindow N Q E old d a u =
      ∑ p∈primeWindow N a u, old.lower (d*p) a := by
  apply sum_congr rfl
  intro p hp
  simp only [negativeChild, if_pos (window_child_query hd hR hs hu hp)]

/-- In every original bank row all THREE restored negative windows use
actual old lower children. The fallback is absent on these parent queries. -/
theorem all36_negative_children (N : ℕ) (Q : ℝ) (E : ℕ → Prop)
    (old : PhysicalState) {d : ℕ} (j : Fin 36)
    (hd : 0<d) (hR : 1<Q/(d:ℝ)) :
    let a := cutoff Q d (originalW2At j).s0
    (negativeWindow N Q E old d a (cutoff Q d (originalW2At j).s) =
      ∑ p∈primeWindow N a (cutoff Q d (originalW2At j).s),old.lower (d*p) a) ∧
    (negativeWindow N Q E old d a (cutoff Q d (originalW2At j).phi2) =
      ∑ p∈primeWindow N a (cutoff Q d (originalW2At j).phi2),old.lower (d*p) a) ∧
    (negativeWindow N Q E old d a (cutoff Q d (originalW2At j).phi3) =
      ∑ p∈primeWindow N a (cutoff Q d (originalW2At j).phi3),old.lower (d*p) a) := by
  have hp := original_W2_order _ (originalW2At_mem j)
  obtain ⟨_,_,hce,hef⟩ := bank_cutoff_order j hR.le
  exact ⟨negativeWindow_eq_old_children N Q E old hd hR hp.1 le_rfl,
    negativeWindow_eq_old_children N Q E old hd hR hp.1 (hce.trans hef),
    negativeWindow_eq_old_children N Q E old hd hR hp.1 hef⟩

theorem negativeWindow_le (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    (d : ℕ) (a u : ℝ) (hold : Encloses N Q E old) :
    negativeWindow N Q E old d a u ≤ fourthRowMotherSingle N d N a u := by
  apply sum_le_sum
  intro p hp
  have hpm := mem_primeWindow.mp hp
  rw [source_single_eq_frozen N d hpm.1 hpm.2.2.1]
  apply le_trans _ (count_le_true N (d*p) E a)
  unfold negativeChild
  split_ifs with hg
  · exact (hold (d*p) a hg).1
  · exact le_rfl

/-- A positive pair uses the old upper count only on the actual good
square domain. The complement is an explicit arithmetic count for E. -/
def positiveChild (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    (d p q : ℕ) (a : ℝ) : ℝ :=
  if PairGate Q d p q then old.upper (d*p*q) a + complementCount N (d*p*q) E a
  else (frozenCount N (d*p*q) (fun _ => True) a : ℝ)

theorem positiveChild_upper (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    {d p q : ℕ} {a : ℝ} (hd : 0<d) (hp : p.Prime) (hq : q.Prime)
    (ha : a ≤ (p:ℝ)) (hold : Encloses N Q E old) :
    (frozenCount N (d*p*q) (fun _ => True) a : ℝ) ≤
      positiveChild N Q E old d p q a := by
  unfold positiveChild
  split_ifs with hg
  · rw [count_partition N (d*p*q) E a]
    exact add_le_add_right (hold (d*p*q) a (pair_query hd hp hq hg ha)).2 _
  · exact le_rfl

def positivePairs (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    (d : ℕ) (a u v w : ℝ) : ℝ :=
  ∑ q ∈ primeWindow N v w, ∑ p ∈ primeWindow N a u,
    if p<q then positiveChild N Q E old d p q a else 0

theorem positivePairs_upper (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    {d : ℕ} (a u v w : ℝ) (hd : 0<d) (hold : Encloses N Q E old) :
    fourthRowMotherPair N d N a u v w ≤ positivePairs N Q E old d a u v w := by
  apply sum_le_sum
  intro q hq
  apply sum_le_sum
  intro p hp
  split_ifs with hpq
  · have hp' := mem_primeWindow.mp hp
    have hq' := mem_primeWindow.mp hq
    have hap := hp'.2.2.1
    have haq : a≤(q:ℝ) := hap.trans (by exact_mod_cast hpq.le)
    rw [source_pair_eq_frozen N d hp'.1 hq'.1 hap haq]
    exact positiveChild_upper N Q E old hd hp'.1 hq'.1 hap hold
  · exact le_rfl

/-- Only literal length-two quotient words can enter pair feedback. -/
def quotientFeedback (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    (d : ℕ) (l : List ℕ) : ℝ :=
  match l with
  | [p,q] => if p.Prime ∧ q.Prime ∧ p<q then
      positiveChild N Q E old d p q (p:ℝ)
    else ((quotientCarrier N d l).card : ℝ)
  | _ => ((quotientCarrier N d l).card : ℝ)

theorem quotientFeedback_long (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    (d : ℕ) (l : List ℕ) (hl : l.length≠2) :
    quotientFeedback N Q E old d l = ((quotientCarrier N d l).card : ℝ) := by
  cases l with
  | nil => rfl
  | cons p l =>
    cases l with
    | nil => rfl
    | cons q l =>
      cases l with
      | nil => exact False.elim (hl rfl)
      | cons r l => rfl

theorem positiveChild_bad (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    (d p q : ℕ) (a : ℝ) (hg : ¬ PairGate Q d p q) :
    positiveChild N Q E old d p q a =
      (frozenCount N (d*p*q) (fun _ => True) a : ℝ) := by
  simp only [positiveChild, if_neg hg]

theorem quotientFeedback_upper (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    {d : ℕ} (l : List ℕ) (hd : 0<d) (hold : Encloses N Q E old) :
    ((quotientCarrier N d l).card : ℝ) ≤ quotientFeedback N Q E old d l := by
  cases l with
  | nil => exact le_rfl
  | cons p l =>
    cases l with
    | nil => exact le_rfl
    | cons q l =>
      cases l with
      | cons r l => exact le_rfl
      | nil =>
        unfold quotientFeedback
        split_ifs with hg
        · rw [quotient_pair_eq_frozen N d hg.1 hg.2.1 hg.2.2]
          exact positiveChild_upper N Q E old hd hg.1 hg.2.1 le_rfl hold
        · exact le_rfl

def prefixFeedback (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    (d : ℕ) (a b c e f : ℝ) (cs : List ℕ) : ℝ :=
  ∑ l ∈ secondFunctionalMotherTuples (primeWindow N a f) cs.length,
    if l.map (secondFunctionalMotherColour b c e)=cs then
      quotientFeedback N Q E old d l else 0

def switchedFeedback (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    (d : ℕ) (a b c e f : ℝ) : ℝ :=
  (secondFunctionalMotherPrefixIndices.map fun i =>
    ((secondFunctionalMotherGammaWords i).map
      (prefixFeedback N Q E old d a b c e f)).sum).sum

theorem switchedFeedback_upper (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    {d : ℕ} (a b c e f : ℝ) (hd : 0<d) (hold : Encloses N Q E old) :
    quotientSwitched N d N a b c e f ≤ switchedFeedback N Q E old d a b c e f := by
  apply secondFunctionalMother_list_sum_mono
  intro i _
  apply secondFunctionalMother_list_sum_mono
  intro cs _
  apply sum_le_sum
  intro l _
  split_ifs
  · exact quotientFeedback_upper N Q E old l hd hold
  · exact le_rfl

/-- All residual costs are still literal original count expressions. -/
def feedbackRest (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    (d : ℕ) (a b c e f : ℝ) : ℝ :=
  -negativeWindow N Q E old d a f-negativeWindow N Q E old d a c-
    negativeWindow N Q E old d a e+
    positivePairs N Q E old d a c a c+positivePairs N Q E old d a b c e+
    switchedFeedback N Q E old d a b c e f+
    collisionSwitched N d N a b c e f+
    fourthRowMotherBadPrime N d a f+fourthRowMotherBadPrime N d a c+
    fourthRowMotherBadPrime N d a e

theorem rawRest_le_feedbackRest (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    {d : ℕ} (a b c e f : ℝ) (hd : 0<d) (hold : Encloses N Q E old) :
    P2AllW2SameQRawCountAction.rawRest N d a b c e f ≤
      feedbackRest N Q E old d a b c e f := by
  have h1 := negativeWindow_le N Q E old d a f hold
  have h2 := negativeWindow_le N Q E old d a c hold
  have h3 := negativeWindow_le N Q E old d a e hold
  have h5 := positivePairs_upper N Q E old a c a c hd hold
  have h6 := positivePairs_upper N Q E old a b c e hd hold
  have hs := switchedFeedback_upper N Q E old a b c e f hd hold
  unfold P2AllW2SameQRawCountAction.rawRest feedbackRest
  linarith

def W2Bound (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    (d : ℕ) (j : Fin 36) : ℝ :=
  let p := originalW2At j
  let a := cutoff Q d p.s0
  let b := cutoff Q d p.phi1
  (4*(old.upper d a+complementCount N d E a)+
    (old.upper d b+complementCount N d E b)+
    feedbackRest N Q E old d a b (cutoff Q d p.phi2)
      (cutoff Q d p.phi3) (cutoff Q d p.s))/5

/-- All36 actual mother inequalities, with old child counts and no
supplied enhanced endpoint, seed, count identity, or analytic licence. -/
theorem W2Bound_upper (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    {d : ℕ} (j : Fin 36) (hd : 0<d) (hR : 1<Q/(d:ℝ))
    (hold : Encloses N Q E old) :
    (frozenCount N d E (cutoff Q d (originalW2At j).s) : ℝ) ≤
      W2Bound N Q E old d j := by
  have hp := original_W2_order _ (originalW2At_mem j)
  have ha := (hold d (cutoff Q d (originalW2At j).s0)
    (cutoff_query hd hR (by linarith [hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1]))).2
  have hb := (hold d (cutoff Q d (originalW2At j).phi1)
    (cutoff_query hd hR (by linarith [hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1]))).2
  have hs := P2AllW2SameQRawCountAction.all36_local_raw N Q d j hR.le
  have he := count_le_true N d E (cutoff Q d (originalW2At j).s)
  have hr := rawRest_le_feedbackRest N Q E old
    (cutoff Q d (originalW2At j).s0) (cutoff Q d (originalW2At j).phi1)
    (cutoff Q d (originalW2At j).phi2) (cutoff Q d (originalW2At j).phi3)
    (cutoff Q d (originalW2At j).s) hd hold
  rw [count_partition N d E (cutoff Q d (originalW2At j).s0),
    count_partition N d E (cutoff Q d (originalW2At j).phi1)] at hs
  unfold P2AllW2SameQRawCountAction.localRest at hs
  unfold W2Bound
  dsimp only
  linarith

end
end ImbalancedChen.P2W2PhysicalChildFeedback
