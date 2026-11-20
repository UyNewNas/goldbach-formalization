import ImbalancedChen.P2CausalSuccessorBadGamma5Payment
import ImbalancedChen.P2EnhancedExactExceptionTheta
import ImbalancedChen.P2EnhancedTwentyOneQuotientFinite

/-! SOURCE ONLY / UNEVALUATED. Pay the ACTUAL RAW Gamma5 repeat and
center events once by the original same-Q causal Theta budget. This
is not a bound for the thetaConversion-weighted exceptions; the raw and
converted normalizations are kept separate. -/
namespace ImbalancedChen.P2CausalGamma5RawExceptionPayment
noncomputable section
open Set Finset Filter Wu2008DoubleSieve
open scoped Classical BigOperators Topology
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalSuccessorTheta
open P2CausalSuccessorBadGamma5Payment
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2EnhancedSwitchedUnsiftedSource P2EnhancedSwitchedTrueNormalization
open P2EnhancedTwentyOneSameQWeighted P2EnhancedTwentyOneQuotientFinite
open P2EnhancedReceiverRoughPurification P2EnhancedExactExceptionFinite
open P2EnhancedBadGamma5ArithmeticGeometry
open P2EnhancedExactExceptionTheta

def rawBadExceptions (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d * badExceptions N Q d

def rawActualBad (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d * originalBadPairCount N Q d

def rawOrdinaryBad (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d * ordinaryBad N Q d

/-- Exact same ordered bad-list fibres and inclusive bad gate. -/
theorem badExceptions_eq_exact_pair_events (N : ℕ) (Q : ℝ) (d : ℕ) :
    badExceptions N Q d = badPairRepeat N Q d + badPairCenter N Q d := by
  unfold badExceptions badPairRepeat badPairCenter badLabels
  rw [Finset.sum_add_distrib]

/-- Gamma9--21 occurrences in `localErrors` are cardinalities and are
nonnegative even when a word is repeated in distinct original groups. -/
theorem switched_exact_exception_tail_nonneg (N : ℕ) (Q : ℝ) (d : ℕ) :
    0 ≤ ∑ j : Fin 13, ((secondFunctionalMotherGammaWords (9+j.val)).map
      (fun cs => repeatWordMass N Q d cs + centerWordMass N Q d cs)).sum := by
  apply Finset.sum_nonneg
  intro j hj
  apply List.sum_nonneg
  intro z hz
  obtain ⟨cs,hcs,rfl⟩ := List.mem_map.mp hz
  apply add_nonneg
  · unfold repeatWordMass
    exact Finset.sum_nonneg (fun l hl => Nat.cast_nonneg _)
  · unfold centerWordMass
    exact Finset.sum_nonneg (fun l hl => Nat.cast_nonneg _)

theorem badExceptions_le_exact_localErrors (N : ℕ) (Q : ℝ) (d : ℕ) :
    badExceptions N Q d ≤ localErrors N Q d := by
  rw [badExceptions_eq_exact_pair_events]
  unfold localErrors
  have h := switched_exact_exception_tail_nonneg N Q d
  linarith only [h]

theorem rawBadExceptions_le_weightedErrors (N : ℕ) (Q : ℝ)
    (D : Finset ℕ) (sigma : ℕ → ℝ) (hsigma : ∀ d ∈ D, 0 ≤ sigma d) :
    rawBadExceptions N Q D sigma ≤ weightedErrors N Q D sigma := by
  unfold rawBadExceptions weightedErrors
  apply Finset.sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left (badExceptions_le_exact_localErrors N Q d) (hsigma d hd)

theorem weightedCollisions_nonnegative (N : ℕ) (Q : ℝ)
    (D : Finset ℕ) (sigma : ℕ → ℝ) (hsigma : ∀ d ∈ D, 0 ≤ sigma d) :
    0 ≤ weightedCollisions N Q D sigma := by
  unfold weightedCollisions localCollisions
  apply Finset.sum_nonneg
  intro d hd
  exact mul_nonneg (hsigma d hd) (collisionSwitched_nonneg _ _ _ _ _ _ _ _)

/-- Actual causal successor family, original raw repeat+center budget.
The threshold precedes N, nu, all labels, marks and successor choices. -/
theorem causal_successor_raw_badGamma5_exception_payment {eta epsilon : ℝ}
    (he : 0 < eta) (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (I : Type*) (A : Finset I) (marks : I → Mark) (choices : I → SuccessorChoice),
      (∀ a ∈ A, (marks a).BoxRows nu eta horizon) →
      let next := fun a => advance (marks a) (choices a)
      let Q := (N:ℝ)^nu
      let D := sourceSupport A next N nu
      let sigma := sourceSigma A next N nu
      rawBadExceptions N Q D sigma ≤ epsilon * Theta N Q D sigma := by
  obtain ⟨T,hT,hpay⟩ := causal_exception_payment he heps (horizon+1)
  refine ⟨T,hT,?_⟩
  intro N hN heven nu hnu I A marks choices hm
  dsimp only
  let next := fun a => advance (marks a) (choices a)
  let D := sourceSupport A next N nu
  let sigma := sourceSigma A next N nu
  have hnext : ∀ a ∈ A, (next a).BoxRows nu eta (horizon+1) := by
    intro a ha
    exact advance_boxRows (marks a) (choices a) (hm a ha)
  have hsigma : ∀ d ∈ D, 0 ≤ sigma d := by
    intro d hd
    exact sourceSigma_nonneg A next N nu (fun a ha => (hnext a ha).2.2.2.2) d
  have hs := rawBadExceptions_le_weightedErrors N ((N:ℝ)^nu) D sigma hsigma
  have hc := weightedCollisions_nonnegative N ((N:ℝ)^nu) D sigma hsigma
  have hp := hpay N hN heven nu hnu I A next hnext
  dsimp only [next,D,sigma] at hs hc hp ⊢
  linarith only [hs,hc,hp]

/-- The literal raw sieve count is bounded by the literal inclusive
ordinary bad count plus this one paid raw exception budget. No
`thetaConversion` occurs on either of these two raw counts. -/
theorem causal_successor_raw_badGamma5_sieve_le_ordinary {eta epsilon : ℝ}
    (he : 0 < eta) (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (I : Type*) (A : Finset I) (marks : I → Mark) (choices : I → SuccessorChoice),
      (∀ a ∈ A, (marks a).BoxRows nu eta horizon) →
      let next := fun a => advance (marks a) (choices a)
      let Q := (N:ℝ)^nu
      let D := sourceSupport A next N nu
      let sigma := sourceSigma A next N nu
      rawActualBad N Q D sigma ≤ rawOrdinaryBad N Q D sigma + epsilon * Theta N Q D sigma := by
  obtain ⟨T,hT,hpayment⟩ := causal_successor_raw_badGamma5_exception_payment he heps horizon
  refine ⟨T,hT,?_⟩
  intro N hN heven nu hnu I A marks choices hm
  dsimp only
  let next := fun a => advance (marks a) (choices a)
  let D := sourceSupport A next N nu
  let sigma := sourceSigma A next N nu
  have hN4 : 4 ≤ N := hT.trans hN
  have hnext : ∀ a ∈ A, (next a).BoxRows nu eta (horizon+1) := by
    intro a ha
    exact advance_boxRows (marks a) (choices a) (hm a ha)
  have hdata (d : ℕ) (hd : d ∈ D) :=
    source_support_data (by omega : 1 < N) he A next hnext hd
  have hsigma (d : ℕ) (hd : d ∈ D) : 0 ≤ sigma d :=
    sourceSigma_nonneg A next N nu (fun a ha => (hnext a ha).2.2.2.2) d
  have hraw : rawActualBad N ((N:ℝ)^nu) D sigma ≤
      rawOrdinaryBad N ((N:ℝ)^nu) D sigma + rawBadExceptions N ((N:ℝ)^nu) D sigma := by
    unfold rawActualBad rawOrdinaryBad rawBadExceptions
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro d hd
    calc
      _ ≤ sigma d * (ordinaryBad N ((N:ℝ)^nu) d + badExceptions N ((N:ℝ)^nu) d) :=
        mul_le_mul_of_nonneg_left
          (actual_bad_le_ordinary_add_exceptions hN4 heven (hdata d hd).1) (hsigma d hd)
      _ = _ := by ring
  have hp := hpayment N hN heven nu hnu I A marks choices hm
  dsimp only [next,D,sigma] at hraw hp ⊢
  linarith only [hraw,hp]

end
end ImbalancedChen.P2CausalGamma5RawExceptionPayment
