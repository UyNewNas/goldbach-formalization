import ImbalancedChen.P2AllW1StablePrefixRawInduction
import ImbalancedChen.P2EnhancedTwentyOneQuotientFinite

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

All36 original repaired W2 tuples are attached to the actual source
21-term inequality at the SAME Q. This file uses the unrestricted
receiver E=true. The true old state is the arithmetic all70 W1/Buchstab
state, not an assumed enhanced table. All36 alternatives are actually
minimized against the old count bound.

Negative singles, positive pairs, all switched words, selected-square
collisions and the three restored-window bad-prime counts remain in the
raw correction. It is not a numerical W2 base, nor the full four-pair
feedback induction. No W2 analytic licence, H248, K, PP, small error,
or raw-to-strict tail equality is assumed.
-/
namespace ImbalancedChen.P2AllW2SameQRawCountAction

noncomputable section
open Finset Wu2008DoubleSieve
open scoped Classical BigOperators
open P5OriginalActionMassBound
open P2EnhancedTwentyOneQuotientFinite
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2FrozenReceiverCountActions
open P2ActualMarkedCountState (Query)
open P2AllW1StablePrefixRawInduction (markedState markedState_encloses)
open P2AllW1SameQRawCountInduction (bestUpper le_bestUpper bestUpper_le_member)

/-- Small rational parameter proof over the existing production list;
no new bank data and no certificate replay are introduced. Unevaluated. -/
theorem original_W2_order (p : W2Parameters) (hp : p∈originalRepairedW2Bank) :
    2≤p.s ∧ p.s≤p.phi3 ∧ p.phi3≤p.phi2 ∧ p.phi2≤p.phi1 ∧
      p.phi1≤p.s0 ∧ p.s0≤5 := by
  simp only [originalRepairedW2Bank,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num

theorem bank_cutoff_order (j : Fin 36) {Q : ℝ} {d : ℕ} (hR : 1≤Q/(d:ℝ)) :
    cutoff Q d (originalW2At j).s0≤cutoff Q d (originalW2At j).phi1 ∧
    cutoff Q d (originalW2At j).phi1≤cutoff Q d (originalW2At j).phi2 ∧
    cutoff Q d (originalW2At j).phi2≤cutoff Q d (originalW2At j).phi3 ∧
    cutoff Q d (originalW2At j).phi3≤cutoff Q d (originalW2At j).s := by
  obtain ⟨hs,h3,h2,h1,h0,_⟩ := original_W2_order _ (originalW2At_mem j)
  refine ⟨?_,?_,?_,?_⟩ <;>
    apply Real.rpow_le_rpow_of_exponent_le hR <;>
    apply one_div_le_one_div_of_le <;> linarith

def target (j : Fin 36) : Query :=
  ⟨(originalW2At j).s,by
    obtain ⟨hs,h3,h2,h1,h0,h5⟩ := original_W2_order _ (originalW2At_mem j)
    constructor <;> linarith⟩

def anchorA (j : Fin 36) : Query :=
  ⟨(originalW2At j).s0,by
    obtain ⟨hs,h3,h2,h1,h0,h5⟩ := original_W2_order _ (originalW2At_mem j)
    constructor <;> linarith⟩

def anchorB (j : Fin 36) : Query :=
  ⟨(originalW2At j).phi1,by
    obtain ⟨hs,h3,h2,h1,h0,h5⟩ := original_W2_order _ (originalW2At_mem j)
    constructor <;> linarith⟩

/-- Original occurrences2--21, together with the exact currently
necessary selected-square and restored-negative-window corrections. -/
def rawRest (N d : ℕ) (a b c e f : ℝ) : ℝ :=
  -fourthRowMotherSingle N d N a f-fourthRowMotherSingle N d N a c-
    fourthRowMotherSingle N d N a e+fourthRowMotherPair N d N a c a c+
    fourthRowMotherPair N d N a b c e+quotientSwitched N d N a b c e f+
    collisionSwitched N d N a b c e f+fourthRowMotherBadPrime N d a f+
    fourthRowMotherBadPrime N d a c+fourthRowMotherBadPrime N d a e

def localRest (N : ℕ) (Q : ℝ) (d : ℕ) (j : Fin 36) : ℝ :=
  rawRest N d (cutoff Q d (originalW2At j).s0) (cutoff Q d (originalW2At j).phi1)
    (cutoff Q d (originalW2At j).phi2) (cutoff Q d (originalW2At j).phi3)
    (cutoff Q d (originalW2At j).s)

theorem true_frozen_count (N d : ℕ) (z : ℝ) :
    frozenCount N d (fun _ => True) z=sourceSieveCount N d (d*N) z := by
  simp [frozenCount,frozenCarrier,sourceSieveCount]

theorem all36_local_raw (N : ℕ) (Q : ℝ) (d : ℕ) (j : Fin 36)
    (hR : 1≤Q/(d:ℝ)) :
    5*(frozenCount N d (fun _ => True) (cutoff Q d (originalW2At j).s):ℝ)≤
      4*(frozenCount N d (fun _ => True) (cutoff Q d (originalW2At j).s0):ℝ)+
        (frozenCount N d (fun _ => True) (cutoff Q d (originalW2At j).phi1):ℝ)+
        localRest N Q d j := by
  obtain ⟨h01,h12,h23,h3s⟩ := bank_cutoff_order j hR
  have h := twentyOne_quotient_finite N d h01 h12 h23 h3s
  simp only [true_frozen_count]
  unfold localRest rawRest
  unfold quotientLocal at h
  linarith

def markedRest {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (j : Fin 36) : ℝ :=
  ∑ a∈L,sigma a*localRest N Q (B a) j

/-- The original positive marked sigma and all equal-product label
multiplicities are retained. This is a finite arithmetic theorem. -/
theorem all36_marked_raw {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (j : Fin 36)
    (hsigma : ∀a∈L,0≤sigma a) (hR : ∀a∈L,1≤Q/(B a:ℝ)) :
    5*markedPhi N Q L B sigma (fun _ _ => True) (originalW2At j).s≤
      4*markedPhi N Q L B sigma (fun _ _ => True) (originalW2At j).s0+
        markedPhi N Q L B sigma (fun _ _ => True) (originalW2At j).phi1+
        markedRest N Q L B sigma j := by
  calc
    _ = ∑ a∈L,sigma a*
        (5*(frozenCount N (B a) (fun _ => True) (cutoff Q (B a) (originalW2At j).s):ℝ)) := by
      unfold markedPhi
      rw [mul_sum]
      apply sum_congr rfl
      intro a _
      ring
    _ ≤ ∑ a∈L,sigma a*
        (4*(frozenCount N (B a) (fun _ => True) (cutoff Q (B a) (originalW2At j).s0):ℝ)+
          (frozenCount N (B a) (fun _ => True) (cutoff Q (B a) (originalW2At j).phi1):ℝ)+
          localRest N Q (B a) j) :=
      sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left
        (all36_local_raw N Q (B a) j (hR a ha)) (hsigma a ha))
    _ = _ := by
      unfold markedPhi markedRest
      rw [mul_sum,←sum_add_distrib,←sum_add_distrib]
      apply sum_congr rfl
      intro a _
      ring

def oldW2Bound {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (bank : List Query) (rounds : ℕ) (j : Fin 36) : ℝ :=
  (4*(markedState N Q L B sigma (fun _ _ => True) bank rounds).upper (anchorA j)+
    (markedState N Q L B sigma (fun _ _ => True) bank rounds).upper (anchorB j)+
    markedRest N Q L B sigma j)/5

/-- Both parent anchors come from one proved old generation; the true
raw signed correction, not a final action bound premise, supplies W2. -/
theorem all36_old_state_raw_bound {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (bank : List Query) (rounds : ℕ) (j : Fin 36)
    (hB : ∀a∈L,0<B a) (hsigma : ∀a∈L,0≤sigma a)
    (hR : ∀a∈L,1<Q/(B a:ℝ)) :
    markedPhi N Q L B sigma (fun _ _ => True) (originalW2At j).s≤
      oldW2Bound N Q L B sigma bank rounds j := by
  have h := all36_marked_raw N Q L B sigma j hsigma (fun a ha => (hR a ha).le)
  have ha := (markedState_encloses N Q L B sigma (fun _ _ => True) bank rounds
    (anchorA j) hB hsigma hR).2
  have hb := (markedState_encloses N Q L B sigma (fun _ _ => True) bank rounds
    (anchorB j) hB hsigma hR).2
  change markedPhi N Q L B sigma (fun _ _ => True) (originalW2At j).s0≤_ at ha
  change markedPhi N Q L B sigma (fun _ _ => True) (originalW2At j).phi1≤_ at hb
  unfold oldW2Bound
  linarith

def W2Candidate {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (bank : List Query) (rounds : ℕ)
    (s : Query) (j : Fin 36) : ℝ :=
  if s.val=(originalW2At j).s then oldW2Bound N Q L B sigma bank rounds j
  else (markedState N Q L B sigma (fun _ _ => True) bank rounds).upper s

def all36Upper {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (bank : List Query) (rounds : ℕ) (s : Query) : ℝ :=
  bestUpper ((markedState N Q L B sigma (fun _ _ => True) bank rounds).upper s)
    ((Finset.univ : Finset (Fin 36)).toList.map (W2Candidate N Q L B sigma bank rounds s))

/-- Actual finite minimum with full fallback. This is one W2 action
layer above the W1/Buchstab induction, not the adopted 430 recursion. -/
theorem all36Upper_actual_count {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (bank : List Query) (rounds : ℕ) (s : Query)
    (hB : ∀a∈L,0<B a) (hsigma : ∀a∈L,0≤sigma a)
    (hR : ∀a∈L,1<Q/(B a:ℝ)) :
    markedPhi N Q L B sigma (fun _ _ => True) s.val≤all36Upper N Q L B sigma bank rounds s := by
  apply le_bestUpper (markedState_encloses N Q L B sigma (fun _ _ => True)
    bank rounds s hB hsigma hR).2
  intro x hx
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
  unfold W2Candidate
  split_ifs with hs
  · rw [hs]
    exact all36_old_state_raw_bound N Q L B sigma bank rounds j hB hsigma hR
  · exact (markedState_encloses N Q L B sigma (fun _ _ => True)
      bank rounds s hB hsigma hR).2

theorem all36Upper_uses_each_action {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (bank : List Query) (rounds : ℕ) (j : Fin 36) :
    all36Upper N Q L B sigma bank rounds (target j)≤oldW2Bound N Q L B sigma bank rounds j := by
  have hm : W2Candidate N Q L B sigma bank rounds (target j) j∈
      (Finset.univ : Finset (Fin 36)).toList.map
        (W2Candidate N Q L B sigma bank rounds (target j)) := by
    exact List.mem_map.mpr ⟨j,by simp,rfl⟩
  simpa only [all36Upper,W2Candidate,target,if_pos rfl] using
    bestUpper_le_member ((markedState N Q L B sigma (fun _ _ => True) bank rounds).upper (target j)) hm

end
end ImbalancedChen.P2AllW2SameQRawCountAction
