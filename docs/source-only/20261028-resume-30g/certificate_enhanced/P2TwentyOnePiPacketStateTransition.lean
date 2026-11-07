import ImbalancedChen.P2ActualTwentyOneStateTransition
import ImbalancedChen.P2EnhancedNegativeChildModulusPrimePayment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Consume the independently proved uniform modulus-prime payment on the
same real physical coefficient. The21 count candidate now keeps the
finite exact-coprime mean and the genuine pi-centered signed AP packet;
only their true modulus-prime difference is paid. Positive pair/switch,
the entire alpha fallback and the actual AP packet remain unbounded.
This is the unrestricted-receiver second-seed tuple, not all36W2 or an
adopted H248/seed licence. PNT/distribution/internalK/PP are not premises.
-/
namespace ImbalancedChen.P2TwentyOnePiPacketStateTransition

noncomputable section
open Finset
open scoped Classical BigOperators
open P2EnhancedTwentyOneSameQWeighted
open P2EnhancedTwentyOneChildCorrection
open P2EnhancedTwentyOnePhysicalReceiver (alphaAdmitted alphaFallback Phi_exact_alpha_split)
open P2EnhancedNegativeChildModulusPrimePayment
open P2ActualMarkedCountState
open P2ActualTwentyOneStateTransition (ordinaryState target anchorA anchorB markedPhi_true_eq_native)

def piPacketUpper (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (bank : List Query) (rounds : ℕ) (epsilon : ℝ) : ℝ :=
  let A := alphaAdmitted N Q D
  (4*(ordinaryState N Q A sigma bank rounds).upper anchorA+
    (ordinaryState N Q A sigma bank rounds).upper anchorB-
    negativeFiniteCoprimeMean N Q A sigma-piCenteredPhysicalError N Q A sigma+
    positivePairs N Q A sigma+switchedCount N Q A sigma+
    5*(ordinaryState N Q (alphaFallback N Q D) sigma bank rounds).upper target+
    epsilon*Theta N Q A sigma)/5

/-- Two independent common thresholds are fixed before N,Q,D,sigma.
Half the error pays the original source exceptions, half pays the real
finite-to-pi signed discrepancy. Nothing is charged to a new measure. -/
theorem actual_piPacket_state_transition {eta epsilon : ℝ}
    (heta : 0<eta) (hepsilon : 0<epsilon) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ),Q≤(N:ℝ) →
      (∀d∈D,0<d) → (∀d∈D,0≤sigma d) → (∀d∈D,1<Q/(d:ℝ)) →
      (∀d∈D,∀q∈d.primeFactors,(N:ℝ)^eta≤(q:ℝ)) →
      (∀d∈D,(N:ℝ)^eta≤cutoff Q d (227/50)) →
      ∀ (bank : List Query) (rounds : ℕ),Phi N Q D sigma (11/5)≤
        min ((ordinaryState N Q D sigma bank rounds).upper target)
          (piPacketUpper N Q D sigma bank rounds epsilon) := by
  have hhalf : (0:ℝ)<epsilon/2 := by linarith
  obtain ⟨Ts,hTs,hsource⟩ := actual_sameQ_signed_child_correction heta hhalf
  obtain ⟨Tp,hTp,hpay⟩ := actual_finite_error_to_pi_packet_payment heta hhalf
  refine ⟨max Ts Tp,hTs.trans (le_max_left _ _),?_⟩
  intro N hNT he Q D sigma hQN hd hsigma hR hold hcut bank rounds
  let A := alphaAdmitted N Q D
  have hAD : A⊆D := filter_subset _ _
  have hNsrc : Ts≤N := (le_max_left _ _).trans hNT
  have hNpay : Tp≤N := (le_max_right _ _).trans hNT
  have hs := hsource N hNsrc he Q A sigma hQN
    (fun d hmem => hd d (hAD hmem)) (fun d hmem => hsigma d (hAD hmem))
    (fun d hmem => hR d (hAD hmem)) (fun d hmem => hold d (hAD hmem))
    (fun d hmem => hcut d (hAD hmem))
  rw [signedChildCorrection_eq_finite_coprime_split] at hs
  have hp := hpay N hNpay Q A sigma hQN
    (fun d hmem => hd d (hAD hmem)) (fun d hmem => hsigma d (hAD hmem))
    (fun d hmem => hR d (hAD hmem)) (fun d hmem => hcut d (hAD hmem))
  have hn := neg_abs_le (negativeFiniteSignedRemainder N Q A sigma-piCenteredPhysicalError N Q A sigma)
  have hcount : 5*Phi N Q D sigma (11/5)≤
      4*Phi N Q A sigma (227/50)+Phi N Q A sigma (353/100)-
      negativeFiniteCoprimeMean N Q A sigma-piCenteredPhysicalError N Q A sigma+
      positivePairs N Q A sigma+switchedCount N Q A sigma+
      5*Phi N Q (alphaFallback N Q D) sigma (11/5)+epsilon*Theta N Q A sigma := by
    rw [Phi_exact_alpha_split N Q D sigma (11/5)]
    change 5*(Phi N Q A sigma (11/5)+Phi N Q (alphaFallback N Q D) sigma (11/5))≤_
    linarith
  have hu (S : Finset ℕ) (hSD : S⊆D) (s : Query) :
      Phi N Q S sigma s.val≤(ordinaryState N Q S sigma bank rounds).upper s := by
    have hc := (iterate_actual_count_enclosure N Q S (fun d => d) sigma (fun _ _ => True)
      bank (fun d hmem => hd d (hSD hmem)) (fun d hmem => hsigma d (hSD hmem))
      (fun d hmem => hR d (hSD hmem)) rounds s).2
    rw [markedPhi_true_eq_native] at hc
    exact hc
  apply le_min
  · exact hu D (fun _ hmem => hmem) target
  · have ha := hu A hAD anchorA
    have hb := hu A hAD anchorB
    have hf := hu (alphaFallback N Q D) (filter_subset _ _) target
    change Phi N Q A sigma (227/50)≤_ at ha
    change Phi N Q A sigma (353/100)≤_ at hb
    change Phi N Q (alphaFallback N Q D) sigma (11/5)≤_ at hf
    unfold piPacketUpper
    dsimp only
    change Phi N Q D sigma (11/5)≤
      (4*(ordinaryState N Q A sigma bank rounds).upper anchorA+
        (ordinaryState N Q A sigma bank rounds).upper anchorB-
        negativeFiniteCoprimeMean N Q A sigma-piCenteredPhysicalError N Q A sigma+
        positivePairs N Q A sigma+switchedCount N Q A sigma+
        5*(ordinaryState N Q (alphaFallback N Q D) sigma bank rounds).upper target+
        epsilon*Theta N Q A sigma)/5
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<5)).mpr
    linarith

end
end ImbalancedChen.P2TwentyOnePiPacketStateTransition
