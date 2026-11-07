import ImbalancedChen.P2AllW1FrozenReceiverFiniteAction
import ImbalancedChen.P2ActualMarkedCountState

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The missing finite count induction after the G all70 W1 actions. A state
is evaluated at the physical cutoff, so the negative W1 child keeps the
parent anchor cutoff while its complete prefix becomes d*q. All states
retain ONE Q and ONE frozen receiver E. Both signs of ordinary Buchstab
and all70 W1 candidates read only the preceding generation. The initial
state consists of the actual finite Rosser polynomials, including their
signed discrepancies. No supplied Sound/count enclosure, seed, H248, or
whole enhancement theorem is an input.

The positive term is literally G.rawTripleCount, with mask d*N*q1. It is
not replaced by a strict tail or a K I/8 cost. This arithmetic induction
does not prove the uniform analytic child means, W2, or the adopted
finite-table defects. Arbitrary E is legitimate here because every
polynomial and every count still uses E; no distribution theorem for an
arbitrary receiver is asserted.
-/
namespace ImbalancedChen.P2AllW1SameQRawCountInduction

noncomputable section
open Finset Wu2008DoubleSieve
open scoped Classical BigOperators
open P2FrozenReceiverCountActions
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedActualBuchstabTransfer (childWindow child_squared_prefix child_level_geometry)
open P2AllW1FrozenReceiverFiniteAction
open P2ActualMarkedCountState (Query rootLevel root_level_geometry)
open P5OriginalActionMassBound (W1Target W1Anchor)

/-- A physical query: d is the complete current prefix, z is its actual
sifting cutoff. The level remains floor(Q/d)+1. -/
def QueryAdmitted (Q : ℝ) (d : ℕ) (z : ℝ) : Prop :=
  0<d ∧ 1<Q/(d:ℝ) ∧ z≤(rootLevel Q d:ℝ)

structure PhysicalState where
  upper : ℕ → ℝ → ℝ
  lower : ℕ → ℝ → ℝ

def initial (N : ℕ) (Q : ℝ) (E : ℕ → Prop) : PhysicalState :=
  ⟨fun d z => frozenPolynomial true N d (rootLevel Q d) E z,
   fun d z => frozenPolynomial false N d (rootLevel Q d) E z⟩

theorem initial_encloses (N : ℕ) (Q : ℝ) (E : ℕ → Prop) {d : ℕ} {z : ℝ}
    (hq : QueryAdmitted Q d z) :
    (initial N Q E).lower d z≤(frozenCount N d E z:ℝ) ∧
    (frozenCount N d E z:ℝ)≤(initial N Q E).upper d z := by
  exact ⟨frozenRosser_lower_finite E hq.2.2,
    frozenRosser_upper_finite E (root_level_geometry hq.2.1 (by norm_num : (1:ℝ)≤1)).1 hq.2.2⟩

theorem cutoff_query {Q s : ℝ} {d : ℕ} (hd : 0<d)
    (hR : 1<Q/(d:ℝ)) (hs : 1≤s) : QueryAdmitted Q d (cutoff Q d s) :=
  ⟨hd,hR,(root_level_geometry hR hs).2⟩

/-- A strict full square makes the actual new residual level exceed q.
This is the same Q/(d*q), not a newly chosen descendant level. -/
theorem child_query_of_square {Q : ℝ} {d q : ℕ} {z : ℝ}
    (hd : 0<d) (hq : q.Prime) (hsq : (d:ℝ)*(q:ℝ)^2<Q)
    (hz : z≤(q:ℝ)) : QueryAdmitted Q (d*q) z := by
  have hdq : (0:ℝ)<(d*q:ℕ) := Nat.cast_pos.mpr (Nat.mul_pos hd hq.pos)
  have hres : (q:ℝ)<Q/((d*q:ℕ):ℝ) := by
    apply (lt_div_iff₀ hdq).mpr
    simpa only [Nat.cast_mul,pow_two,mul_assoc,mul_comm,mul_left_comm] using hsq
  have hq1 : (1:ℝ)<q := by exact_mod_cast hq.one_lt
  have hfloor : Q/((d*q:ℕ):ℝ)<(rootLevel Q (d*q):ℝ) := by
    simpa only [rootLevel,Nat.cast_add,Nat.cast_one] using
      Nat.lt_floor_add_one (Q/((d*q:ℕ):ℝ))
  exact ⟨Nat.mul_pos hd hq.pos,hq1.trans hres,hz.trans (hres.trans hfloor).le⟩

/-- Both original negative-child cutoffs are admitted: q for Buchstab,
and the unchanged parent anchor for W1. -/
theorem W1_child_queries {N d q : ℕ} {Q : ℝ} (i : Fin 7) (j : Fin 10)
    (hd : 0<d) (hR : 1<Q/(d:ℝ))
    (hq : q∈childWindow N d Q (W1Target i) (W1Anchor j)) :
    QueryAdmitted Q (d*q) (q:ℝ) ∧
    QueryAdmitted Q (d*q) (cutoff Q d (W1Anchor j)) := by
  have hp := mem_primeWindow.mp hq
  have hs := child_squared_prefix hd hR (original_W1_parameters i j).1 hq
  exact ⟨child_query_of_square hd hp.1 hs le_rfl,
    child_query_of_square hd hp.1 hs hp.2.2.1⟩

theorem ordinary_child_query {N d q : ℕ} {Q z a : ℝ}
    (hd : 0<d) (hz : 0≤z) (hsq : z^2≤Q/(d:ℝ))
    (hq : q∈primeWindow (d*N) a z) : QueryAdmitted Q (d*q) (q:ℝ) := by
  have hp := mem_primeWindow.mp hq
  have hqpos : (0:ℝ)<q := Nat.cast_pos.mpr hp.1.pos
  have hqr : (q:ℝ)^2<Q/(d:ℝ) := by nlinarith [hp.2.2.2]
  have hdpos : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hfull : (d:ℝ)*(q:ℝ)^2<Q := by
    have h := (lt_div_iff₀ hdpos).mp hqr
    nlinarith
  exact child_query_of_square hd hp.1 hfull le_rfl

def bestUpper (fallback : ℝ) : List ℝ → ℝ
  | [] => fallback
  | x::xs => min x (bestUpper fallback xs)

def bestLower (fallback : ℝ) : List ℝ → ℝ
  | [] => fallback
  | x::xs => max x (bestLower fallback xs)

theorem le_bestUpper {c fallback : ℝ} (hbase : c≤fallback)
    (xs : List ℝ) (hxs : ∀x∈xs,c≤x) : c≤bestUpper fallback xs := by
  induction xs with
  | nil => exact hbase
  | cons x xs ih =>
      exact le_min (hxs x (by simp)) (ih (fun y hy => hxs y (by simp [hy])))

theorem bestLower_le {c fallback : ℝ} (hbase : fallback≤c)
    (xs : List ℝ) (hxs : ∀x∈xs,x≤c) : bestLower fallback xs≤c := by
  induction xs with
  | nil => exact hbase
  | cons x xs ih =>
      exact max_le (hxs x (by simp)) (ih (fun y hy => hxs y (by simp [hy])))

theorem bestUpper_le_fallback (fallback : ℝ) (xs : List ℝ) :
    bestUpper fallback xs≤fallback := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih => exact (min_le_right _ _).trans ih

theorem fallback_le_bestLower (fallback : ℝ) (xs : List ℝ) :
    fallback≤bestLower fallback xs := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih => exact ih.trans (le_max_right _ _)

theorem bestUpper_le_member (fallback : ℝ) {xs : List ℝ} {x : ℝ}
    (hx : x∈xs) : bestUpper fallback xs≤x := by
  induction xs generalizing x with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | h
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (ih h)

/-- Every ordinary candidate also reads both child signs from old.
The square test is a finite arithmetic gate, not a count hypothesis. -/
def ordinaryCandidate (side : Bool) (N : ℕ) (Q : ℝ) (old : PhysicalState)
    (d : ℕ) (z : ℝ) (anchor : Query) : ℝ :=
  let a := cutoff Q d anchor.val
  if a≤z ∧ 0≤z ∧ z^2≤Q/(d:ℝ) then
    if side then old.upper d a-
      ∑ q∈primeWindow (d*N) a z,old.lower (d*q) (q:ℝ)
    else old.lower d a-
      ∑ q∈primeWindow (d*N) a z,old.upper (d*q) (q:ℝ)
  else if side then old.upper d z else old.lower d z

abbrev W1Action := Fin 7 × Fin 10

/-- The original Cartesian bank, all7*10 actions, with no producer replay. -/
def allW1 : List W1Action := (Finset.univ : Finset W1Action).toList

theorem original_action_mem (i : Fin 7) (j : Fin 10) : (i,j)∈allW1 := by
  simp [allW1]

def W1Candidate (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    (d : ℕ) (z : ℝ) (a : W1Action) : ℝ :=
  if z=cutoff Q d (W1Target a.1) then
    old.upper d (cutoff Q d (W1Anchor a.2))-
      (∑ q∈childWindow N d Q (W1Target a.1) (W1Anchor a.2),
        old.lower (d*q) (cutoff Q d (W1Anchor a.2)))/2+
      (rawTripleCount N d (d*N) E (cutoff Q d (W1Anchor a.2))
        (cutoff Q d (W1Target a.1)):ℝ)/2
  else old.upper d z

def upperCandidates (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    (bank : List Query) (d : ℕ) (z : ℝ) : List ℝ :=
  (bank.map (ordinaryCandidate true N Q old d z))++
    (allW1.map (W1Candidate N Q E old d z))

def oneRound (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (bank : List Query)
    (old : PhysicalState) : PhysicalState :=
  ⟨fun d z => bestUpper (old.upper d z) (upperCandidates N Q E old bank d z),
   fun d z => bestLower (old.lower d z) (bank.map (ordinaryCandidate false N Q old d z))⟩

def iterate (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (bank : List Query) : ℕ → PhysicalState
  | 0 => initial N Q E
  | n+1 => oneRound N Q E bank (iterate N Q E bank n)

/-- Actual simultaneous induction. The inductive enclosure is proved
from the initial arithmetic polynomials; it is not a public premise. -/
theorem iterate_encloses (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (bank : List Query)
    (rounds : ℕ) : ∀d z,QueryAdmitted Q d z →
    (iterate N Q E bank rounds).lower d z≤(frozenCount N d E z:ℝ) ∧
    (frozenCount N d E z:ℝ)≤(iterate N Q E bank rounds).upper d z := by
  induction rounds with
  | zero => exact fun _ _ h => initial_encloses N Q E h
  | succ n ih =>
      intro d z hdz
      let old := iterate N Q E bank n
      have hordinary (a : Query) :
          ordinaryCandidate false N Q old d z a≤(frozenCount N d E z:ℝ) ∧
          (frozenCount N d E z:ℝ)≤ordinaryCandidate true N Q old d z a := by
        unfold ordinaryCandidate
        dsimp only
        by_cases hg : cutoff Q d a.val≤z ∧ 0≤z ∧ z^2≤Q/(d:ℝ)
        · simp only [if_pos hg,Bool.false_eq_true,if_false,if_true]
          have ha := ih d (cutoff Q d a.val)
            (cutoff_query hdz.1 hdz.2.1 a.property.1)
          have hc : ∀q∈primeWindow (d*N) (cutoff Q d a.val) z,
              QueryAdmitted Q (d*q) (q:ℝ) :=
            fun q hq => ordinary_child_query hdz.1 hg.2.1 hg.2.2 hq
          have hl := sum_le_sum (fun q hq => (ih (d*q) (q:ℝ) (hc q hq)).1)
          have hu := sum_le_sum (fun q hq => (ih (d*q) (q:ℝ) (hc q hq)).2)
          have hb : (frozenCount N d E (cutoff Q d a.val):ℝ)=
              (frozenCount N d E z:ℝ)+
                ∑ q∈primeWindow (d*N) (cutoff Q d a.val) z,
                  (frozenCount N (d*q) E (q:ℝ):ℝ) := by
            exact_mod_cast frozen_selected_buchstab N d E hg.1
          change old.lower d (cutoff Q d a.val)≤_ ∧
            _≤old.upper d (cutoff Q d a.val) at ha
          change (∑ q∈primeWindow (d*N) (cutoff Q d a.val) z,
            old.lower (d*q) (q:ℝ))≤_ at hl
          change _≤∑ q∈primeWindow (d*N) (cutoff Q d a.val) z,
            old.upper (d*q) (q:ℝ) at hu
          constructor <;> linarith
        · simpa only [if_neg hg,Bool.false_eq_true,if_false,if_true] using ih d z hdz
      have hw1 (a : W1Action) :
          (frozenCount N d E z:ℝ)≤W1Candidate N Q E old d z a := by
        unfold W1Candidate
        split_ifs with hz
        · rw [hz]
          have hp := original_W1_parameters a.1 a.2
          have ha := (ih d (cutoff Q d (W1Anchor a.2))
            (cutoff_query hdz.1 hdz.2.1 (by linarith : 1≤W1Anchor a.2))).2
          have hl := sum_le_sum (fun q hq =>
            (ih (d*q) (cutoff Q d (W1Anchor a.2))
              (W1_child_queries a.1 a.2 hdz.1 hdz.2.1 hq).2).1)
          have hcut : cutoff Q d (W1Anchor a.2)≤cutoff Q d (W1Target a.1) :=
            Real.rpow_le_rpow_of_exponent_le hdz.2.1.le
              (one_div_le_one_div_of_le (by linarith : 0<W1Target a.1) hp.2.1)
          have hc : 2*(frozenCount N d E (cutoff Q d (W1Target a.1)):ℝ)≤
              2*(frozenCount N d E (cutoff Q d (W1Anchor a.2)):ℝ)-
                (∑ q∈childWindow N d Q (W1Target a.1) (W1Anchor a.2),
                  (frozenCount N (d*q) E (cutoff Q d (W1Anchor a.2)):ℝ))+
                (rawTripleCount N d (d*N) E (cutoff Q d (W1Anchor a.2))
                  (cutoff Q d (W1Target a.1)):ℝ) := by
            exact_mod_cast frozen_selected_three_prime_weight N d E hcut
          change (frozenCount N d E (cutoff Q d (W1Anchor a.2)):ℝ)≤
            old.upper d (cutoff Q d (W1Anchor a.2)) at ha
          change (∑ q∈childWindow N d Q (W1Target a.1) (W1Anchor a.2),
            old.lower (d*q) (cutoff Q d (W1Anchor a.2)))≤_ at hl
          linarith
        · exact (ih d z hdz).2
      constructor
      · apply bestLower_le (ih d z hdz).1
        intro x hx
        obtain ⟨a,_,rfl⟩ := List.mem_map.mp hx
        exact (hordinary a).1
      · apply le_bestUpper (ih d z hdz).2
        intro x hx
        rcases List.mem_append.mp hx with ho | hw
        · obtain ⟨a,_,rfl⟩ := List.mem_map.mp ho
          exact (hordinary a).2
        · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hw
          exact hw1 a

/-- Every one of the70 original W1 candidates is actually used by the
next state. This is not only an abstract list of available licences. -/
theorem iterate_upper_le_each_W1 (N : ℕ) (Q : ℝ) (E : ℕ → Prop)
    (bank : List Query) (rounds d : ℕ) (i : Fin 7) (j : Fin 10) :
    (iterate N Q E bank (rounds+1)).upper d (cutoff Q d (W1Target i))≤
      (iterate N Q E bank rounds).upper d (cutoff Q d (W1Anchor j))-
        (∑ q∈childWindow N d Q (W1Target i) (W1Anchor j),
          (iterate N Q E bank rounds).lower (d*q) (cutoff Q d (W1Anchor j)))/2+
        (rawTripleCount N d (d*N) E (cutoff Q d (W1Anchor j))
          (cutoff Q d (W1Target i)):ℝ)/2 := by
  have hm : W1Candidate N Q E (iterate N Q E bank rounds) d
      (cutoff Q d (W1Target i)) (i,j)∈upperCandidates N Q E
        (iterate N Q E bank rounds) bank d (cutoff Q d (W1Target i)) := by
    apply List.mem_append.mpr
    exact Or.inr (List.mem_map.mpr ⟨(i,j),original_action_mem i j,rfl⟩)
  simpa only [iterate,oneRound,W1Candidate,if_pos rfl] using
    bestUpper_le_member ((iterate N Q E bank rounds).upper d (cutoff Q d (W1Target i))) hm

theorem iterate_retains_previous (N : ℕ) (Q : ℝ) (E : ℕ → Prop)
    (bank : List Query) (rounds d : ℕ) (z : ℝ) :
    (iterate N Q E bank rounds).lower d z≤(iterate N Q E bank (rounds+1)).lower d z ∧
    (iterate N Q E bank (rounds+1)).upper d z≤(iterate N Q E bank rounds).upper d z := by
  exact ⟨fallback_le_bestLower _ _,bestUpper_le_fallback _ _⟩

end
end ImbalancedChen.P2AllW1SameQRawCountInduction
