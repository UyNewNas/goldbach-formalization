import ImbalancedChen.P2CausalSuccessorTheta
import ImbalancedChen.P2EnhancedBadGamma5CostTheta
import ImbalancedChen.P2EnhancedReceiverRoughPurification

/-! SOURCE ONLY / UNEVALUATED. The fixed original bad Gamma5 ordinary
cost is instantiated at the actual labelled causal successor support,
with the same Q and Theta. The original sieve count is bounded with its
repeat and center costs explicitly retained. This does not pay those
exceptions, replace the original positive-product cost, or license an
entire W2 action or any H247 endpoint. -/
namespace ImbalancedChen.P2CausalSuccessorBadGamma5Payment
noncomputable section
open Finset Filter Set Wu2008DoubleSieve
open scoped Classical BigOperators Topology
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalSuccessorTheta
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2EnhancedSwitchedTrueNormalization P2EnhancedSwitchedUnsiftedSource
open P2EnhancedTwentyOneSameQWeighted
open P2EnhancedReceiverRoughPurification
open P2EnhancedBadGamma5ArithmeticGeometry P2EnhancedBadGamma5CostTheta

/-- Both original purification exceptions are kept per original ordered
bad pair. `badLabels` uses the physical inclusive Q≤d*p^2*q gate. -/
def badExceptions (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  ∑ l ∈ badLabels N Q d,
    ((repeatReceiver N d (d*l.prod) (cutoff Q d (227/50))).card : ℝ) +
    ((centerReceiver N d (d*l.prod) (cutoff Q d (227/50))).card : ℝ)

/-- Exact three-way split; neither unit, repeat nor center is erased or
charged a second time. The ordinary term includes its unit atom. -/
theorem badPurified_eq_ordinary_add_exceptions (N : ℕ) (Q : ℝ) (d : ℕ) :
    badPairPurifiedUpper N Q d = ordinaryBad N Q d + badExceptions N Q d := by
  unfold badPairPurifiedUpper ordinaryBad badExceptions badLabels
  simp only [Finset.sum_add_distrib]
  ring

/-- The actual original masked Gamma5 count enters with the sign of a
positive cost. Its two extra exception carriers remain explicit. -/
theorem actual_bad_le_ordinary_add_exceptions {N d : ℕ} {Q : ℝ}
    (hN : 4 ≤ N) (heven : Even N) (hd : 0 < d) :
    originalBadPairCount N Q d ≤ ordinaryBad N Q d + badExceptions N Q d := by
  exact (original_badPair_upper hN heven hd Q).trans_eq
    (badPurified_eq_ordinary_add_exceptions N Q d)

def convertedActualBad (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d * thetaConversion N d * originalBadPairCount N Q d

def convertedBadExceptions (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, sigma d * thetaConversion N d * badExceptions N Q d

/-- The original positive marked-family normalization, including the
literal scale floor and true-alpha row, bounds the actual sieve count by
the paid ordinary component plus the separately retained exceptions. -/
theorem converted_actual_bad_le_paid_ordinary_add_exceptions {N : ℕ} {Q : ℝ}
    {eta : ℝ} (hN : 4 ≤ N) (heven : Even N) (heta : 0 < eta)
    (D : Finset ℕ) (sigma : ℕ → ℝ)
    (hd : ∀ d ∈ D, 0 < d) (hsigma : ∀ d ∈ D, 0 ≤ sigma d)
    (hscale : ∀ d ∈ D, (N:ℝ)^eta ≤ Q/d) :
    convertedActualBad N Q D sigma ≤ convertedBad N Q D sigma +
      convertedBadExceptions N Q D sigma := by
  have hp (d : ℕ) (hm : d ∈ D) :
      sigma d * thetaConversion N d * originalBadPairCount N Q d ≤
        sigma d * thetaConversion N d * ordinaryBad N Q d +
        sigma d * thetaConversion N d * badExceptions N Q d := by
    have hR : 1 < Q/d :=
      (Real.one_lt_rpow (by exact_mod_cast (show 1 < N by omega)) heta).trans_le (hscale d hm)
    have hw : 0 ≤ sigma d * thetaConversion N d :=
      mul_nonneg (hsigma d hm)
        (P2EnhancedUnitSourceMass.thetaConversion_nonneg hN (hd d hm) hR)
    calc
      _ ≤ (sigma d * thetaConversion N d) * (ordinaryBad N Q d + badExceptions N Q d) :=
        mul_le_mul_of_nonneg_left (actual_bad_le_ordinary_add_exceptions hN heven (hd d hm)) hw
      _ = _ := by ring
  have h := Finset.sum_le_sum (s := D) hp
  simpa only [convertedActualBad,convertedBad,convertedBadExceptions,Finset.sum_add_distrib] using h

/-- A filtered actual successor support retains all external marks and
all labelled tuple occurrences, even when products coincide. -/
theorem actual_bad_labelled_exact {I : Type*} (A : Finset I) (marks : I → Mark)
    (choices : I → SuccessorChoice) (N : ℕ) (nu : ℝ) :
    let next := fun a => advance (marks a) (choices a)
    convertedActualBad N ((N:ℝ)^nu) (sourceSupport A next N nu) (sourceSigma A next N nu) =
      ∑ a ∈ A, ∑ t ∈ (next a).source N nu,
        (next a).weight * (thetaConversion N (parentProduct (oldWord t)) *
          originalBadPairCount N ((N:ℝ)^nu) (parentProduct (oldWord t))) := by
  dsimp only
  unfold convertedActualBad
  have h := sourceSigma_test A (fun a => advance (marks a) (choices a)) N nu
    (fun d => thetaConversion N d * originalBadPairCount N ((N:ℝ)^nu) d)
  calc
    _ = ∑ d ∈ sourceSupport A (fun a => advance (marks a) (choices a)) N nu,
        sourceSigma A (fun a => advance (marks a) (choices a)) N nu d *
          (thetaConversion N d * originalBadPairCount N ((N:ℝ)^nu) d) := by
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = _ := by
      rw [h]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro t ht
      rw [oldWord_product]

/-- Actual causal successor Gamma5, original row 0 parameters, same Q,
one shared pre-N threshold. The ordinary bad-square price is paid by
`badRawCost`; repeat and center remain on the RHS exactly once. -/
theorem causal_successor_actual_badGamma5_payment {eta epsilon : ℝ}
    (he : 0 < eta) (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (I : Type*) (A : Finset I) (marks : I → Mark) (choices : I → SuccessorChoice),
      (∀ a ∈ A, (marks a).BoxRows nu eta horizon) →
      let next := fun a => advance (marks a) (choices a)
      let Q := (N:ℝ)^nu
      let D := sourceSupport A next N nu
      let sigma := sourceSigma A next N nu
      convertedActualBad N Q D sigma ≤ badRawCost * Theta N Q D sigma +
        epsilon * Theta N Q D sigma + convertedBadExceptions N Q D sigma := by
  have hfloor : 0 < floorAt eta (horizon+1) := floorAt_pos he _
  obtain ⟨T,hT,hordinary⟩ := original_badGamma5_cost_theta hfloor heps
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
  have hd : ∀ d ∈ D, 0 < d := by intro d hd; exact (hdata d hd).1
  have hsigma : ∀ d ∈ D, 0 ≤ sigma d := by
    intro d hd
    exact sourceSigma_nonneg A next N nu (fun a ha => (hnext a ha).2.2.2.2) d
  have hscale : ∀ d ∈ D, (N:ℝ)^(floorAt eta (horizon+1)) ≤ (N:ℝ)^nu/d := by
    intro d hd
    exact (hdata d hd).2.2.1
  have halpha : ∀ d ∈ D, 2 ≤ trueAlpha N ((N:ℝ)^nu) d := by
    intro d hd
    exact (hdata d hd).2.2.2
  have hraw := converted_actual_bad_le_paid_ordinary_add_exceptions hN4 heven hfloor
    D sigma hd hsigma hscale
  have hpaid := hordinary N hN ((N:ℝ)^nu) D sigma hd hsigma hscale halpha
  dsimp only [next,D,sigma] at hraw hpaid ⊢
  linarith only [hraw,hpaid]

end
end ImbalancedChen.P2CausalSuccessorBadGamma5Payment
