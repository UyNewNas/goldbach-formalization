import ImbalancedChen.P2EnhancedW1OrderedTripleGlobalPayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A finite action bank is a LIST of occurrences at each B. Its entries carry
an actual integer old word, its frozen receiver mask, and one of the literal
7*10 W1 actions. Different
entries may have the same B, old word, action, or positive triple product.
They are never deduplicated. The triple fibre within each entry is exactly
the PhaseB4 strictly ordered positive word, including its label multiplicity.

The exact budget is the marked reciprocal mass weighted by bank length.
A uniform bound M on this actual length gives M times the former budget;
M is absorbed into the power-saving threshold before N and the bank.
The complete 70-action W1 bank is constructed and its size and label
coverage proved. No assertion is made that ALL alternatives should be
added in the manuscript's maximum-based induction: this theorem pays the
finite list that a fixed selected policy actually supplies.
-/

namespace ImbalancedChen.P2EnhancedW1FiniteActionBankPayment

noncomputable section
open Finset Filter Wu2008DoubleSieve
open scoped Classical Topology BigOperators
open P2EnhancedW1OrderedTripleGlobalPayment (repeatedTripleMass
  repeatedTripleMass_le_squareEvent)
open P2EnhancedW1SquareExceptionPower (squareEvent_card_le_power)
open P2EnhancedLowerPrimeChildCarriers (parentWindow)
open P2EnhancedTwentyOneSameQWeighted (cutoff Theta)
open P2EnhancedThetaReciprocalMass (Theta_lower)
open P5OriginalActionMassBound (W1Anchor)
open MathlibNt.SieveTheory.SingularSeries

/-- One occurrence, retaining the complete integer word even when its
product agrees with other entries in the bank. -/
structure W1Occurrence where
  old : List ℕ
  target : Fin 7
  anchor : Fin 10
  frozenMask : ℕ → ℕ → Prop

def occurrenceMass (N : ℕ) (Q : ℝ) (E : ℕ → ℕ → Prop)
    (a : W1Occurrence) : ℝ :=
  repeatedTripleMass N Q a.old a.target a.anchor
    (fun B ell => E B ell ∧ a.frozenMask B ell)

def localBankMass (N : ℕ) (Q : ℝ) (E : ℕ → ℕ → Prop)
    (bank : List W1Occurrence) : ℝ :=
  (bank.map (occurrenceMass N Q E)).sum

def markedBankMass (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (E : ℕ → ℕ → Prop)
    (bank : ℕ → List W1Occurrence) : ℝ :=
  ∑ B ∈ D, sigma B * localBankMass N Q E (bank B)

/-- Exact occurrence budget, including repeated words/actions at B. -/
def occurrenceReciprocalBudget (D : Finset ℕ) (sigma : ℕ → ℝ)
    (bank : ℕ → List W1Occurrence) : ℝ :=
  ∑ B ∈ D, sigma B * ((bank B).length : ℝ) / (B : ℝ)

@[simp] theorem localBankMass_append (N : ℕ) (Q : ℝ)
    (E : ℕ → ℕ → Prop) (a b : List W1Occurrence) :
    localBankMass N Q E (a ++ b) =
      localBankMass N Q E a + localBankMass N Q E b := by
  simp [localBankMass, List.map_append, List.sum_append]

/-- Repeating an occurrence adds its entire triple mass again. -/
@[simp] theorem localBankMass_repeat_two (N : ℕ) (Q : ℝ)
    (E : ℕ → ℕ → Prop) (a : W1Occurrence) :
    localBankMass N Q E [a,a] = 2 * occurrenceMass N Q E a := by
  simp only [localBankMass, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  ring

theorem markedBankMass_append (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (E : ℕ → ℕ → Prop)
    (a b : ℕ → List W1Occurrence) :
    markedBankMass N Q D sigma E (fun B => a B ++ b B) =
      markedBankMass N Q D sigma E a +
        markedBankMass N Q D sigma E b := by
  simp only [markedBankMass, localBankMass_append, mul_add,
    Finset.sum_add_distrib]

/-- The power saving for one entry is uniform in its actual action and
cutoff; the unchanged old product B supplies the physical denominator. -/
theorem occurrenceMass_le_power {N B : ℕ} {Q chi eta : ℝ}
    (E : ℕ → ℕ → Prop) (a : W1Occurrence)
    (hprod : a.old.prod = B) (hw : parentWindow N Q a.old chi)
    (heta : 0 < eta)
    (hcut : (N : ℝ)^eta ≤ cutoff Q B (W1Anchor a.anchor))
    (hz : 2 ≤ (N : ℝ)^eta) :
    occurrenceMass N Q E a ≤
      (1/eta)^3 * (2 * (N : ℝ) / ((B : ℝ) * (N : ℝ)^eta)) := by
  have hcut' : (N : ℝ)^eta ≤
      cutoff Q a.old.prod (W1Anchor a.anchor) := by
    simpa only [hprod] using hcut
  have hfirst := repeatedTripleMass_le_squareEvent
    a.target a.anchor (fun B ell => E B ell ∧ a.frozenMask B ell)
    hw heta hcut'
  rw [hprod] at hfirst
  have hB : 0 < B := by rw [← hprod]; exact hw.2.1
  exact hfirst.trans (mul_le_mul_of_nonneg_left
    (squareEvent_card_le_power N B
      (fun B ell => E B ell ∧ a.frozenMask B ell)
      (cutoff Q B (W1Anchor a.anchor)) hB hz) (by positivity))

/-- Summing a LIST preserves each separate occurrence. No injection,
distinct-product condition, or one-action-per-B premise is required. -/
theorem localBankMass_le_length_power {N B : ℕ} {Q chi eta : ℝ}
    (E : ℕ → ℕ → Prop) (bank : List W1Occurrence)
    (heta : 0 < eta) (hz : 2 ≤ (N : ℝ)^eta)
    (hprod : ∀ a ∈ bank, a.old.prod = B)
    (hw : ∀ a ∈ bank, parentWindow N Q a.old chi)
    (hcut : ∀ a ∈ bank,
      (N : ℝ)^eta ≤ cutoff Q B (W1Anchor a.anchor)) :
    localBankMass N Q E bank ≤
      (bank.length : ℝ) * (1/eta)^3 *
        (2 * (N : ℝ) / ((B : ℝ) * (N : ℝ)^eta)) := by
  revert hprod hw hcut
  induction bank with
  | nil => intro _ _ _; simp [localBankMass]
  | cons a bank ih =>
      intro hprod hw hcut
      have ha := occurrenceMass_le_power E a
        (hprod a (by simp)) (hw a (by simp)) heta
        (hcut a (by simp)) hz
      have hb := ih
        (fun b hb => hprod b (by simp [hb]))
        (fun b hb => hw b (by simp [hb]))
        (fun b hb => hcut b (by simp [hb]))
      simp only [localBankMass, List.map_cons, List.sum_cons,
        List.length_cons, Nat.cast_add, Nat.cast_one] at *
      nlinarith only [ha,hb]

/-- Exact finite all-B budget, with the actual action/word multiplicity
left in the reciprocal mass rather than erased or assumed to be one. -/
theorem markedBankMass_le_occurrenceBudget {N : ℕ} {Q chi eta : ℝ}
    (D : Finset ℕ) (sigma : ℕ → ℝ) (E : ℕ → ℕ → Prop)
    (bank : ℕ → List W1Occurrence)
    (heta : 0 < eta) (hz : 2 ≤ (N : ℝ)^eta)
    (hsigma : ∀ B ∈ D, 0 ≤ sigma B)
    (hprod : ∀ B ∈ D, ∀ a ∈ bank B, a.old.prod = B)
    (hw : ∀ B ∈ D, ∀ a ∈ bank B, parentWindow N Q a.old chi)
    (hcut : ∀ B ∈ D, ∀ a ∈ bank B,
      (N : ℝ)^eta ≤ cutoff Q B (W1Anchor a.anchor)) :
    markedBankMass N Q D sigma E bank ≤
      (1/eta)^3 * (2 * (N : ℝ) / (N : ℝ)^eta) *
        occurrenceReciprocalBudget D sigma bank := by
  unfold markedBankMass occurrenceReciprocalBudget
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro B hB
  have hlocal := localBankMass_le_length_power E (bank B) heta hz
    (hprod B hB) (hw B hB) (hcut B hB)
  have hweighted := mul_le_mul_of_nonneg_left hlocal (hsigma B hB)
  convert hweighted using 1 <;> ring

/-- An explicit M occurrences at each B gives the precise M-fold error
budget against the ORIGINAL marked reciprocal mass. -/
theorem occurrenceBudget_le_cap (D : Finset ℕ) (sigma : ℕ → ℝ)
    (bank : ℕ → List W1Occurrence) (M : ℕ)
    (hsigma : ∀ B ∈ D, 0 ≤ sigma B)
    (hsize : ∀ B ∈ D, (bank B).length ≤ M) :
    occurrenceReciprocalBudget D sigma bank ≤
      (M : ℝ) * (∑ B ∈ D, sigma B / (B : ℝ)) := by
  unfold occurrenceReciprocalBudget
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro B hB
  have hlen : ((bank B).length : ℝ) ≤ M := by
    exact_mod_cast hsize B hB
  have h := mul_le_mul_of_nonneg_left hlen
    (div_nonneg (hsigma B hB) (Nat.cast_nonneg B))
  convert h using 1 <;> ring

/-- The actual finite-bank multiplicity is absorbed into the threshold.
M is frozen first; N, Q, support, weights, and the occurrence lists follow.
Empty banks and M=0 are included. No K bound is an input. -/
theorem markedBankMass_theta_payment (M : ℕ) {eta epsilon : ℝ}
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (Q chi : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
        (E : ℕ → ℕ → Prop) (bank : ℕ → List W1Occurrence),
      (∀ B ∈ D, 0 < B) →
      (∀ B ∈ D, 0 ≤ sigma B) →
      (∀ B ∈ D, (bank B).length ≤ M) →
      (∀ B ∈ D, ∀ a ∈ bank B, a.old.prod = B) →
      (∀ B ∈ D, ∀ a ∈ bank B, parentWindow N Q a.old chi) →
      (∀ B ∈ D, ∀ a ∈ bank B,
        (N : ℝ)^eta ≤ cutoff Q B (W1Anchor a.anchor)) →
      (∀ B ∈ D, 1 < Q / (B : ℝ) ∧ Q / (B : ℝ) ≤ (N : ℝ)) →
      markedBankMass N Q D sigma E bank ≤ epsilon * Theta N Q D sigma := by
  let C : ℝ := (1/eta)^3
  obtain ⟨T1,hT1,hpay⟩ := ninth_power_log_error_budget 0
    (C := 2*C*((M : ℝ)+1)) (α := eta)
    (ε := 2 * liuUniversalProduct * epsilon)
    (by dsimp [C]; positivity) heta (by positivity)
  have hcut : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ)^eta :=
    ((tendsto_rpow_atTop heta).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2 : ℝ))
  obtain ⟨T2,hT2⟩ := eventually_atTop.mp hcut
  refine ⟨max T1 T2,by omega,?_⟩
  intro N hNT Q chi D sigma E bank hd hsigma hsize hprod hw hcutBank hR
  have hN1 := (le_max_left T1 T2).trans hNT
  have hN4 : 4 ≤ N := by omega
  have hz := hT2 N ((le_max_right T1 T2).trans hNT)
  have hfirst := markedBankMass_le_occurrenceBudget
    D sigma E bank heta hz hsigma hprod hw hcutBank
  have hbudget := occurrenceBudget_le_cap D sigma bank M hsigma hsize
  have hmass : 0 ≤ ∑ B ∈ D, sigma B / (B : ℝ) :=
    Finset.sum_nonneg (fun B hB =>
      div_nonneg (hsigma B hB) (Nat.cast_nonneg B))
  have htheta := Theta_lower hN4 Q D sigma hd hsigma hR
  have hpower : (2*C*(M : ℝ)) * (N : ℝ) / (N : ℝ)^eta ≤
      (2 * liuUniversalProduct * epsilon) * (N : ℝ) /
        Real.log N ^ 2 := by
    have hpayN : (2*C*((M : ℝ)+1)) * (N : ℝ) / (N : ℝ)^eta ≤
        (2 * liuUniversalProduct * epsilon) * (N : ℝ) /
          Real.log N ^ 2 := by
      simpa using hpay N hN1
    have hcoeff : 2*C*(M : ℝ) ≤ 2*C*((M : ℝ)+1) := by
      have hC : 0 ≤ 2*C := by dsimp [C]; positivity
      nlinarith only [hC]
    apply le_trans ?_ hpayN
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg N))
      (Real.rpow_nonneg (Nat.cast_nonneg N) eta)
  calc
    markedBankMass N Q D sigma E bank ≤
        C * (2 * (N : ℝ) / (N : ℝ)^eta) *
          occurrenceReciprocalBudget D sigma bank := hfirst
    _ ≤ C * (2 * (N : ℝ) / (N : ℝ)^eta) *
          ((M : ℝ) * (∑ B ∈ D, sigma B / (B : ℝ))) :=
      mul_le_mul_of_nonneg_left hbudget (by dsimp [C]; positivity)
    _ = ((2*C*(M : ℝ)) * (N : ℝ) / (N : ℝ)^eta) *
          (∑ B ∈ D, sigma B / (B : ℝ)) := by ring
    _ ≤ ((2 * liuUniversalProduct * epsilon) * (N : ℝ) /
          Real.log N ^ 2) * (∑ B ∈ D, sigma B / (B : ℝ)) :=
      mul_le_mul_of_nonneg_right hpower hmass
    _ = epsilon * ((2 * liuUniversalProduct * (N : ℝ) /
          Real.log N ^ 2) * (∑ B ∈ D, sigma B / (B : ℝ))) := by ring
    _ ≤ epsilon * Theta N Q D sigma :=
      mul_le_mul_of_nonneg_left htheta hepsilon.le

/-- The manuscript's literal 7-by-10 one-step W1 bank. The finite slot
index is retained, so it is not an unproved 'at most 70' licence. -/
def fullW1Occurrence (old : List ℕ) (k : Fin 70) : W1Occurrence where
  old := old
  target := ⟨k.val / 10, by have := k.isLt; omega⟩
  anchor := ⟨k.val % 10, Nat.mod_lt _ (by norm_num)⟩
  frozenMask := fun _ _ => True

def fullW1Bank (old : List ℕ) : List W1Occurrence :=
  List.ofFn (fullW1Occurrence old)

@[simp] theorem fullW1Bank_length (old : List ℕ) :
    (fullW1Bank old).length = 70 := by simp [fullW1Bank]

/-- Every original target/anchor pair has an actual finite bank slot. -/
theorem fullW1Bank_contains (old : List ℕ) (i : Fin 7) (j : Fin 10) :
    (⟨old,i,j,fun _ _ => True⟩ : W1Occurrence) ∈ fullW1Bank old := by
  let k : Fin 70 := ⟨10*i.val+j.val,by have := i.isLt; have := j.isLt; omega⟩
  apply List.mem_ofFn.mpr
  refine ⟨k,?_⟩
  have hi : k.val / 10 = i.val := by
    dsimp [k]; have := j.isLt; omega
  have hj : k.val % 10 = j.val := by
    dsimp [k]; have := j.isLt; omega
  have hit : (fullW1Occurrence old k).target = i := by
    apply Fin.ext; exact hi
  have hja : (fullW1Occurrence old k).anchor = j := by
    apply Fin.ext; exact hj
  cases hiold : fullW1Occurrence old k with
  | mk old' i' j' mask' =>
      have ho : old' = old := by
        have hh := congrArg W1Occurrence.old hiold
        simpa [fullW1Occurrence] using hh.symm
      have hm : mask' = (fun _ _ => True) := by
        have hh := congrArg W1Occurrence.frozenMask hiold
        simpa [fullW1Occurrence] using hh.symm
      simp_all

@[simp] theorem fullW1Occurrence_mass (N : ℕ) (Q : ℝ)
    (E : ℕ → ℕ → Prop) (old : List ℕ) (k : Fin 70) :
    occurrenceMass N Q E (fullW1Occurrence old k) =
      repeatedTripleMass N Q old
        (fullW1Occurrence old k).target (fullW1Occurrence old k).anchor E := by
  simp [occurrenceMass, fullW1Occurrence]

/-- The 70 literal slots do not accidentally collapse distinct action
labels; a repeated occurrence can only arise when the supplied bank
explicitly repeats it. -/
theorem fullW1Occurrence_injective (old : List ℕ) :
    Function.Injective (fullW1Occurrence old) := by
  intro k l h
  have hi := congrArg (fun a : W1Occurrence => a.target.val) h
  have hj := congrArg (fun a : W1Occurrence => a.anchor.val) h
  simp only [fullW1Occurrence] at hi hj
  apply Fin.ext
  omega

/-- The complete bank's total marked budget is exactly 70 times the
original one, before tuning the final epsilon threshold. -/
theorem fullW1Bank_reciprocalBudget (D : Finset ℕ) (sigma : ℕ → ℝ)
    (old : ℕ → List ℕ) :
    occurrenceReciprocalBudget D sigma (fun B => fullW1Bank (old B)) =
      70 * (∑ B ∈ D, sigma B / (B : ℝ)) := by
  unfold occurrenceReciprocalBudget
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  simp only [fullW1Bank_length, Nat.cast_ofNat]
  ring

/-- Literal full bank, not a hypothetical multiplicity premise: all 70
actions can occur at B, and their entire exceptional word masses receive
one chosen epsilon reserve by the finite-bank threshold with M=70. -/
theorem fullW1Bank_theta_payment {eta epsilon : ℝ}
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (Q chi : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
        (E : ℕ → ℕ → Prop) (old : ℕ → List ℕ),
      (∀ B ∈ D, (old B).prod = B) →
      (∀ B ∈ D, parentWindow N Q (old B) chi) →
      (∀ B ∈ D, 0 ≤ sigma B) →
      (∀ B ∈ D, ∀ j : Fin 10,
        (N : ℝ)^eta ≤ cutoff Q B (W1Anchor j)) →
      (∀ B ∈ D, 1 < Q / (B : ℝ) ∧ Q / (B : ℝ) ≤ (N : ℝ)) →
      markedBankMass N Q D sigma E (fun B => fullW1Bank (old B)) ≤
        epsilon * Theta N Q D sigma := by
  obtain ⟨T,hT,hpay⟩ := markedBankMass_theta_payment 70 heta hepsilon
  refine ⟨T,hT,?_⟩
  intro N hNT Q chi D sigma E old hprod hw hsigma hcut hR
  have hd : ∀ B ∈ D, 0 < B := by
    intro B hB
    rw [← hprod B hB]
    exact (hw B hB).2.1
  apply hpay N hNT Q chi D sigma E (fun B => fullW1Bank (old B))
    hd hsigma
  · intro B hB
    simp only [fullW1Bank_length]
  · intro B hB a ha
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ha
    exact hprod B hB
  · intro B hB a ha
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ha
    exact hw B hB
  · intro B hB a ha
    exact hcut B hB a.anchor
  · exact hR

end
end ImbalancedChen.P2EnhancedW1FiniteActionBankPayment
