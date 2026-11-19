import ImbalancedChen.P2Historical246PairProductGate
import ImbalancedChen.P2CausalSuccessorTheta

/-!
SOURCE ONLY / UNEVALUATED. A genuine one-edge successor mark has its
actual parentWindow from the existing root geometry and source facts.
This does not establish arbitrary root/selected-history admission or
pay any endpoint, collision, ceiling, signed base, or count estimate.
-/
namespace ImbalancedChen.P2Historical246SuccessorParentWindow

noncomputable section
open Finset
open scoped Classical BigOperators
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply P2CausalBankOccurrenceBinding
open P2CausalSuccessorTheta P2EnhancedSwitchedTrueNormalization
open P2Historical246PairCarrierPartition P2Historical246BoundedPairBridge
open P2Historical246PairProductGate P2OriginalProfileThetaNormalization
open P2HistoricalScheduledPointReads P2HistoricalNativePointCounts
open P2Historical248Authentication P2HistoricalW2ArchivedPairWindows
open P5OriginalActionMassBound
open Part5OriginalH430W2UpperPolygons (parameterQ)
open Part5OriginalH430W2UpperArchiveData (weights)

/-- A real successor history uses its last appended prime as its own
ceiling. Its positive lower face is obtained from the existing actual
source facts, not postulated as an extra ceiling licence. -/
theorem successor_ceiling_pos {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (m : Mark) (choice : SuccessorChoice)
    (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu) :
    0 < (advance m choice).history.ceiling (advance m choice).ceiling t := by
  have hn := advance_boxRows m choice hm
  have hf := (advance m choice).source_facts hN he hn ht
  have hfloor := floorAt_pos he (horizon+1)
  cases choice with
  | inl rule =>
      change 0 < physicalPrime N (t (Fin.last m.rank)).val
      exact hfloor.trans_le ((hf.1 _).2.2)
  | inr p =>
      rcases p with ⟨bank,piece⟩
      change 0 < physicalPrime N (t (Fin.last (m.rank+1))).val
      exact hfloor.trans_le ((hf.1 _).2.2)

/-- The original parent test is derived for every actual tuple of this
successor. The independent root-box and half-level rows remain present
inside BoxRows, and nu≤1 supplies the original Q≤N test. -/
theorem successor_parentWindow {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (hnu : nu ≤ 1)
    (m : Mark) (choice : SuccessorChoice) (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu) :
    parentWindow N ((N : ℝ)^nu) (oldWord t)
      ((advance m choice).history.ceiling (advance m choice).ceiling t) := by
  have hn := advance_boxRows m choice hm
  have hs := (advance m choice).source_scale hN he hn ht
  have hQ : (N : ℝ)^nu ≤ N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hN.le : (1 : ℝ) ≤ N) hnu
  have hc := successor_ceiling_pos hN he m choice hm ht
  unfold parentWindow
  rw [oldWord_product]
  exact ⟨hN,hs.1,hs.2.1,hQ,hc⟩

/-- This parent's exact positive residual exponent and unchanged Q are
obtained from the same tuple, before any W2 row or prime-pair choice. -/
theorem successor_sameQ_positive_level {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (m : Mark) (choice : SuccessorChoice)
    (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu) :
    0 < parentProduct (oldWord t) ∧
      0 < residualExponent N (parentProduct (oldWord t)) nu ∧
      (N : ℝ)^nu = (parentProduct (oldWord t) : ℝ)*
        (N : ℝ)^(residualExponent N (parentProduct (oldWord t)) nu) := by
  have hn := advance_boxRows m choice hm
  have hs := (advance m choice).source_scale hN he hn ht
  have hf := (advance m choice).source_facts hN he hn ht
  have hfloor := floorAt_pos he (horizon+1)
  have h := facts_trueAlpha hN hfloor hf
  have hL : 0 < residualExponent N (Part3.labelledProduct t) nu := by
    linarith only [h.2.1,hfloor]
  rw [oldWord_product]
  exact ⟨hs.1,hL,actual_sameQ hN hs.1 nu⟩

/-- For this actual successor tuple, the parent-window-failure component
of each original pair profile is literally empty. -/
theorem successor_parent_reject_empty {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (hnu : nu ≤ 1)
    (m : Mark) (choice : SuccessorChoice) (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu) (j : Fin 36) (k : Fin 4) :
    (halfCarrier N (residualExponent N (parentProduct (oldWord t)) nu) j k).filter
      (fun p => interior N (residualExponent N (parentProduct (oldWord t)) nu) j k p ∧
        ¬ parentWindow N ((N : ℝ)^nu) (oldWord t)
          ((advance m choice).history.ceiling (advance m choice).ceiling t)) = ∅ := by
  have hp := successor_parentWindow hN he hnu m choice hm ht
  ext p
  simp [hp]

/-- The selected original row keeps the exact H246 Θ-profile, four pair
lane lists and actual child carrier. Only the already-paid product gate
and this successor's parent-window-failure term are removed. -/
theorem successor_h246_tagged_parent_free {N horizon : ℕ} {nu eta : ℝ}
    (hN : 1 < N) (he : 0 < eta) (hnu : nu ≤ 1)
    (m : Mark) (choice : SuccessorChoice) (hm : m.BoxRows nu eta horizon)
    {t : Fin (advance m choice).rank → Fin (N+1)}
    (ht : t ∈ (advance m choice).source N nu)
    {b : Tagged} (hb : b ∈ taggedW2 246) :
    ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧ b.2.pairRows.length = 4 ∧
      (∀ k : Fin 4, encode (lane b.2 k) = weights j k) ∧
      ∀ k : Fin 4,
        let Q := (N : ℝ)^nu
        let old := oldWord t
        let L := residualExponent N (parentProduct old) nu
        let chi := (advance m choice).history.ceiling (advance m choice).ceiling t
        let S := halfCarrier N L j k
        let F := oldPairAtom N Q L (parentProduct old) j k
        pairThetaOldProfile N Q L (parentProduct old) (originalW2At j) k (outputAt 246 true) =
          (∑ p ∈ S.filter (fun p => ¬ interior N L j k p), F p) +
          (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
            ¬ bothCoprime N old p), F p) +
          (∑ p ∈ S.filter (fun p => interior N L j k p ∧ parentWindow N Q old chi ∧
            bothCoprime N old p ∧ ¬ orderedCeiling N chi p), F p) +
          (∑ p ∈ pairChildren j k N Q old chi, F (pairValues p)) := by
  obtain ⟨j,hp,hn,hlanes⟩ := actual_pair_lists 246 hb
  refine ⟨j,hp,hn,hlanes,?_⟩
  intro k
  obtain ⟨hd,hL,hQ⟩ := successor_sameQ_positive_level hN he m choice hm ht
  have h := generation246_pair_profile_without_product_reject hN hd hL hQ j k
    (chi := (advance m choice).history.ceiling (advance m choice).ceiling t)
  rw [successor_parent_reject_empty hN he hnu m choice hm ht j k] at h
  simpa only [Finset.sum_empty,add_zero] using h

end
end ImbalancedChen.P2Historical246SuccessorParentWindow
