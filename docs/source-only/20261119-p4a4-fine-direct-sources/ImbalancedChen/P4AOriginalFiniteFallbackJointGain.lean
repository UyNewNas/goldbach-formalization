import ImbalancedChen.P4AOriginalFiniteFallbackSecondGain
import ImbalancedChen.P4AOriginalFiniteFallbackThirdGain

namespace ImbalancedChen.P4AOriginalFiniteFallbackJointGain
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter
open P4AOriginalFiniteFallbackPolicy (Rule policy dispatch upper)
open P4AOriginalFiniteFallbackOccurrence (onlySecond empty)
open P4AOriginalFiniteFallbackFullTree (withLower actual_two_three)
open P4AOriginalFiniteFallbackOwnCubeRows (secondRow thirdRow)
open P4AOriginalFull87RawChronology (rawRoot)
open P4AOriginalNewFifthUnion (data)
open P5OriginalCommonPositivePresieve (normalize)
open P4AFallbackCanonicalBanks (bank)

theorem lower_even (delta : ℝ) (n : ℕ) (d : P5OriginalCommonRefinedConstructor.OriginalData) (w N : ℝ)
    (p : List ℕ) : P4AOriginalOrderedThirdFullPolicy.policy delta n d w N true p=true := by
  cases hc : P4AOriginalFull87FiniteEighthPolicy.selectedCap delta n N p <;>
    simp [P4AOriginalOrderedThirdFullPolicy.policy,P4AOriginalOrderedThirdFullPolicy.eight,
      P4AOriginalOrderedThirdFullPolicy.six,P4AOriginalOrderedThirdFullPolicy.five,
      P4AOriginalOrderedThirdFullPolicy.common,P4AOriginalOrderedThirdFullPolicy.base,hc,
      firstExitDepthSplicePolicy,frozenParityRosserPolicy,ancestorFrozenPolicy,
      ordinaryParityRosserPolicy,oddFirstExitPolicy,HistoricalThirdCoarse.initialPolicy]

def before (m : ℕ) (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (a w : ℝ) (N : ℕ) :=
  let d := data e q a
  withLower (empty (bank m)) d w N (P4AOriginalOrderedThirdFullPolicy.policy delta n d w N)

theorem gains (eps : ℝ) (heps : 0<eps) :
    ∃ h : ℝ,0<h ∧ ∃ m0 : ℕ,∀ m≥m0,∃ E : ℝ,0<E ∧ ∀ e : ℚ,0<(e:ℝ) → (e:ℝ)<E →
    ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,∀ a w : ℝ,a≤1/800 → w≤a → w≤h →
      ∀ delta : ℝ,∀ n : ℕ, ∀ᶠ N : ℕ in atTop,Even N →
        currentUpperEighteenGains 4+currentUpperEighteenGains 5-eps<
        normalize N (rawRoot (before m delta n e q a w N) N-
          rawRoot (policy (bank m) delta n (data e q a) w N) N) := by
  obtain ⟨h,hh,m2,H2⟩ := P4AOriginalFiniteFallbackSecondGain.gain (eps/2) (half_pos heps)
  obtain ⟨m3,H3⟩ := P4AOriginalFiniteFallbackThirdGain.gain (eps/2) (half_pos heps)
  refine ⟨h,hh,max m2 m3,?_⟩
  intro m hm
  obtain ⟨E2,hE2,H2'⟩ := H2 m (by omega)
  obtain ⟨E3,hE3,H3'⟩ := H3 m (by omega)
  refine ⟨min (1/384) (min E2 E3),lt_min (by norm_num) (lt_min hE2 hE3),?_⟩
  intro e he heE
  obtain ⟨q2,hq2,h2⟩ := H2' e he (heE.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨q3,hq3,h3⟩ := H3' e he (heE.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨M,hM⟩ := eventually_atTop.mp ((tendsto_logPrimeMeshStep 0 (19/96)).eventually
    (gt_mem_nhds (half_pos he)))
  obtain ⟨qm,hqm,_,hq⟩ := P4AActualRefinableArchivePayment.exists_actual_refinement_threshold 1 (by norm_num) 0 M
  refine ⟨max q2 (max q3 qm),by omega,?_⟩
  intro q hq' a w ha hwa hwh delta n
  let D := data e q a
  have hmesh := (hM D.m (hq q (by omega)).1).le
  filter_upwards [h2 q (by omega) a w hwh,h3 q (by omega) a w ha hwa,eventually_ge_atTop 2] with N hs ht hN hEven
  let L := P4AOriginalOrderedThirdFullPolicy.policy delta n D w N
  obtain ⟨c2,c3⟩ := actual_two_three m D he (heE.trans_le (min_le_left _ _)).le hmesh w (by linarith)
    N (by omega) L (lower_even delta n D w N)
  have H := add_lt_add (hs hEven) (ht hEven)
  rw [←c2,←c3] at H
  change _<normalize N (rawRoot (withLower (empty (bank m)) D w N L) N-
      rawRoot (withLower (bank m) D w N L) N)
  dsimp only [normalize] at *
  linarith only [H]

end
end ImbalancedChen.P4AOriginalFiniteFallbackJointGain
