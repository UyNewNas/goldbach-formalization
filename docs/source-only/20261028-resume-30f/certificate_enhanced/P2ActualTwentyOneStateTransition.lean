import ImbalancedChen.P2ActualMarkedCountState
import ImbalancedChen.P2EnhancedTwentyOnePhysicalReceiver

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The genuine 21-term physical signed coefficient is inserted into an
actual count-state candidate. All anchors and the entire alpha fallback
read the same preceding ordinary count-state generation. Pair/switched
counts and the signed physical AP count remain explicit arithmetic costs.
This does not pay them by K, infer the adopted numerical seed, identify
arithmetic alpha fallback with an adopted policy branch, or license all
36 W2 actions. The unrestricted receiver specialization is explicit.
-/
namespace ImbalancedChen.P2ActualTwentyOneStateTransition

noncomputable section
open Finset
open scoped Classical BigOperators
open P2EnhancedTwentyOneSameQWeighted
open P2FrozenReceiverCountActions
open P2ActualMarkedCountState
open P2EnhancedTwentyOnePhysicalReceiver
open P2EnhancedTwentyOneChildCorrection (positivePairs switchedCount)
open P2EnhancedNegativeChildSignedModulus (modulusSupport physicalCoefficient)
open P2EnhancedNegativeChildRosser (rawPrimeAPCount)

def target : Query := ⟨11/5,by norm_num⟩
def anchorA : Query := ⟨227/50,by norm_num⟩
def anchorB : Query := ⟨353/100,by norm_num⟩

theorem markedPhi_true_eq_native (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (s : ℝ) :
    markedPhi N Q D (fun d => d) sigma (fun _ _ => True) s=Phi N Q D sigma s := by
  unfold markedPhi Phi
  apply sum_congr rfl
  intro d _
  have hc : frozenCount N d (fun _ => True) (cutoff Q d s)=
      Wu2008DoubleSieve.sourceSieveCount N d (d*N) (cutoff Q d s) := by
    simp [frozenCount,frozenCarrier,Wu2008DoubleSieve.sourceSieveCount]
  rw [hc]

theorem markedTheta_native (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) :
    markedTheta N Q D (fun d => d) sigma=Theta N Q D sigma := rfl

def ordinaryState (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (bank : List Query) (rounds : ℕ) : CountState :=
  iterate N Q D (fun d => d) sigma (fun _ _ => True) bank rounds

/-- The same old generation is read for the two admitted-family anchors
and for the complete actual alpha-fallback count. No current candidate
feeds another anchor and no fallback term is declared negligible. -/
def twentyOneUpper (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ)
    (bank : List Query) (rounds : ℕ) (epsilon : ℝ) : ℝ :=
  let A := alphaAdmitted N Q D
  (4*(ordinaryState N Q A sigma bank rounds).upper anchorA+
    (ordinaryState N Q A sigma bank rounds).upper anchorB-
    (∑ q∈modulusSupport N Q A,physicalCoefficient N Q A sigma q*rawPrimeAPCount N q)+
    positivePairs N Q A sigma+switchedCount N Q A sigma+
    5*(ordinaryState N Q (alphaFallback N Q D) sigma bank rounds).upper target+
    epsilon*Theta N Q A sigma)/5

/-- A concrete actual count transition with independently proved initial
states. There is no supplied old-state/Sound count premise. The threshold
comes from the genuine source inequality before the family and Q; all
finite ordinary depths/banks are allowed because their full arithmetic
remainders have been retained. -/
theorem actual_twentyOne_state_transition {eta epsilon : ℝ}
    (heta : 0<eta) (hepsilon : 0<epsilon) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → Even N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ),Q≤(N:ℝ) →
      (∀d∈D,0<d) → (∀d∈D,0≤sigma d) → (∀d∈D,1<Q/(d:ℝ)) →
      (∀d∈D,∀q∈d.primeFactors,(N:ℝ)^eta≤(q:ℝ)) →
      (∀d∈D,(N:ℝ)^eta≤cutoff Q d (227/50)) →
      ∀ (bank : List Query) (rounds : ℕ),Phi N Q D sigma (11/5)≤
        min ((ordinaryState N Q D sigma bank rounds).upper target)
          (twentyOneUpper N Q D sigma bank rounds epsilon) := by
  obtain ⟨T,hT,hsource⟩ := actual_receiver_with_alpha_fallback heta hepsilon
  refine ⟨T,hT,?_⟩
  intro N hNT he Q D sigma hQN hd hsigma hR hold hcut bank rounds
  have h := hsource N hNT he Q D sigma hQN hd hsigma hR hold hcut
  dsimp only at h
  have hu (S : Finset ℕ) (hSD : S⊆D) (s : Query) :
      Phi N Q S sigma s.val≤(ordinaryState N Q S sigma bank rounds).upper s := by
    have hc := (iterate_actual_count_enclosure N Q S (fun d => d) sigma (fun _ _ => True)
      bank (fun d hmem => hd d (hSD hmem)) (fun d hmem => hsigma d (hSD hmem))
      (fun d hmem => hR d (hSD hmem)) rounds s).2
    rw [markedPhi_true_eq_native] at hc
    exact hc
  apply le_min
  · exact hu D (fun _ hmem => hmem) target
  · have ha := hu (alphaAdmitted N Q D) (filter_subset _ _) anchorA
    have hb := hu (alphaAdmitted N Q D) (filter_subset _ _) anchorB
    have hf := hu (alphaFallback N Q D) (filter_subset _ _) target
    unfold twentyOneUpper
    dsimp only
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<5)).mpr
    change Phi N Q (alphaAdmitted N Q D) sigma (227/50)≤_ at ha
    change Phi N Q (alphaAdmitted N Q D) sigma (353/100)≤_ at hb
    change Phi N Q (alphaFallback N Q D) sigma (11/5)≤_ at hf
    linarith

end
end ImbalancedChen.P2ActualTwentyOneStateTransition
