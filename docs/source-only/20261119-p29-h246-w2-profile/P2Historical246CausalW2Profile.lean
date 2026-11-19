import ImbalancedChen.P2CausalSuccessorTheta
import ImbalancedChen.P2HistoricalW2ArchivedPairWindows
import ImbalancedChen.P2OriginalProfileThetaNormalization

/-!
SOURCE ONLY / UNCOMPILED. The 246th original predecessor is bound to
the 36-row historical W2 parameter/ordered-pair dictionary and to the
existing same-Q W2 old-profile integral passage for a constructed causal
successor book. No H247 endpoint, old H/h count licence, signed base or
full W2 mother/count estimate follows from this profile statement alone.
-/
namespace ImbalancedChen.P2Historical246CausalW2Profile

noncomputable section
open Set Finset
open scoped Classical BigOperators
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply
open P2CausalBankOccurrenceBinding P2CausalSuccessorTheta
open P2EnhancedSwitchedTrueNormalization
open P2OriginalChildPhysicalNormalization P2OriginalProfileThetaNormalization
open P2OriginalBankOldProfilePassage P2EnhancedTwentyOneSameQWeighted
open P2HistoricalSourceJSON P2Historical248Authentication
open P2HistoricalScheduledPointReads P2HistoricalNativePointCounts
open P2HistoricalW2ArchivedPairWindows
open P5OriginalActionMassBound
open Part5OriginalH430W2UpperPolygons (parameterQ)
open Part5OriginalH430W2UpperArchiveData (weights)

/-- The original action read at generation 246 remains tied to its
literal parameter tuple and four ordered archived pair lanes. The old
arrays in the profile are precisely that same generation's H/h arrays.
The common threshold is chosen before N, marks, choices and tagged row.
The physical profiles here are the imported half-open N-window profiles;
no unqualified identification with open coprime child sets is made. -/
theorem historical_246_successor_book_W2_old_profile
    {eta epsilon : ℝ} (he : 0 < eta) (heps : 0 < epsilon) (horizon : ℕ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ nu : ℝ, nu ≤ 1 →
      ∀ (I : Type*) (A : Finset I) (marks : I → Mark)
        (choices : I → SuccessorChoice),
      (∀ a ∈ A, (marks a).BoxRows nu eta horizon) →
      ∀ (b : Tagged), b ∈ taggedW2 246 →
      ∃ j : Fin 36,
        parameters b.1 = List.ofFn (parameterQ j) ∧ b.2.pairRows.length = 4 ∧
        (∀ k : Fin 4, encode (lane b.2 k) = weights j k) ∧
        let next := fun a => advance (marks a) (choices a)
        let D := sourceSupport A next N nu
        let sigma := sourceSigma A next N nu
        |(∑ d ∈ D, sigma d * W2ThetaOldProfile N ((N : ℝ)^nu)
            (residualExponent N d nu) d (originalW2At j)
            (outputAt 246 true) (outputAt 246 false)) -
          Theta N ((N : ℝ)^nu) D sigma *
            W2OldIntegral (originalW2At j) (outputAt 246 true) (outputAt 246 false)| ≤
          epsilon * Theta N ((N : ℝ)^nu) D sigma := by
  have hfloor := floorAt_pos he (horizon+1)
  obtain ⟨T0,hprofile⟩ := all106_sameQ_Theta_profile_passage
    hfloor (le_max_right (1 : ℝ) (floorAt eta (horizon+1))) heps
    (outputAt 246 true) (outputAt 246 false)
  refine ⟨max 4 T0,le_max_left _ _,?_⟩
  intro N hN nu hnu I A marks choices hm b hb
  let next := fun a => advance (marks a) (choices a)
  have hN1 : 1 < N := by omega
  have hn : ∀ a ∈ A, (next a).BoxRows nu eta (horizon+1) := by
    intro a ha
    exact advance_boxRows (marks a) (choices a) (hm a ha)
  have hs := source_support_data hN1 he A next hn
  have hres (d : ℕ) (hd : d ∈ sourceSupport A next N nu) :
      residualExponent N d nu ∈ Set.Icc (floorAt eta (horizon+1))
        (max 1 (floorAt eta (horizon+1))) := by
    obtain ⟨a,ha,hd'⟩ := mem_biUnion.mp hd
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hd'
    have hf := facts_trueAlpha hN1 hfloor ((next a).source_facts hN1 he (hn a ha) ht)
    have hd1 : (1 : ℝ) ≤ Part3.labelledProduct t := by exact_mod_cast hf.1
    have hb0 : 0 ≤ prefixExponent N (Part3.labelledProduct t) :=
      div_nonneg (Real.log_nonneg hd1) (Real.log_pos (by exact_mod_cast hN1)).le
    refine ⟨by linarith only [hf.2.1,hfloor],?_⟩
    have hu : residualExponent N (Part3.labelledProduct t) nu ≤ 1 := by
      unfold residualExponent
      linarith only [hnu,hb0]
    exact hu.trans (le_max_left _ _)
  obtain ⟨j,hparam,hlen,hlanes⟩ := actual_pair_lists 246 hb
  refine ⟨j,hparam,hlen,hlanes,?_⟩
  have hrow := (hprofile N ((le_max_right _ _).trans hN) ((N : ℝ)^nu)
    (sourceSupport A next N nu) (fun d => residualExponent N d nu) (fun d => d)
    (sourceSigma A next N nu) hres (fun d hd => (hs hd).1)
    (fun d hd => actual_sameQ hN1 (hs hd).1 nu)
    (fun d _ => sourceSigma_nonneg A next N nu (fun a ha => (hn a ha).2.2.2.2) d)).2 j
  simpa only [Theta_eq_sum_atoms] using hrow

end
end ImbalancedChen.P2Historical246CausalW2Profile
