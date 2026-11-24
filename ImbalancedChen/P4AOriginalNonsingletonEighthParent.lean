import ImbalancedChen.P4AOriginalNonsingletonComparison
import ImbalancedChen.P4AOriginalOrderedThirdFullPolicy
import ImbalancedChen.P4AOriginalFull87UnionHistory

/-! Re-establish the R17-enabled sixth parent bound on every original
eight-coordinate source. Only the supported third and actual preceding
odd histories enter. All six-coordinate tent controls come from the
original 87 dictionary, with no upper bound on a sixth parent assumed. -/
namespace ImbalancedChen.P4AOriginalNonsingletonEighthParent
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary (Cell Source comparison)
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)
open P4AOriginalFull87HistoryCore (oldHistory width_pos)
open P4AOriginalFull87UnionHistory (bank oldBank fifth_bounds)
open P4AOriginalOrderedThirdFullPolicy (current prior cap6 root_on_old_owner cap6_prior)
open P5OriginalCommonRefinedConstructor (lambda3 exponent5)
open P1OriginalVariableFourthContinuation (finiteMax_le)

theorem history (e : ℚ) (q : ℕ) (a N : ℝ) (he : 0≤e) (h : List ℕ) (hl : h.length=8)
    (c : Cell) (hs : Source c (primeHistoryLogCoordinates N 8 h))
    (hfirst : HistoricalThirdCoarse.firstStop (e:ℝ) (bank e q a).m N (rosserAncestor 1 h))
    (hsup : P1ThirdFallbackSupport.supported (e:ℝ) (bank e q a).chi (bank e q a).m a N (rosserAncestor 3 h))
    (hodd : ∀ j : Fin 4,oldHistory (primeHistoryLogCoordinates N 8 h) j<lambda3 (oldBank e q a) N (rosserAncestor 4 h)) :
    RealizedHistory e q a N h c := by
  let d := oldBank e q a
  have hlower := P5OriginalCommonRefinedPreservation.lambda3_le_exponent5 d N (rosserAncestor 5 h)
  rw [P5OriginalCommonRefinedPreservation.lambda3_ancestor d N 5 (by decide),
    ← P5OriginalCommonRefinedPreservation.lambda3_ancestor d N 4 (by decide) h] at hlower
  have hstep := P4AOriginalCompleteSixthChronology.fifth_le_current e q a N (rosserAncestor 6 h)
  change exponent5 d N (rosserAncestor 5 (rosserAncestor 6 h))≤_ at hstep
  rw [rosserAncestor_nested 5 6 (by decide)] at hstep
  exact ⟨hfirst,hsup,hodd,hlower.trans hstep,
    P4AOriginalFull87CompleteSixthBound.source_current_le_comparison e q a N he h hl c hs hsup⟩

theorem ordered_cap_bounds (n : ℕ) (e : ℚ) (q : ℕ) (a omega N : ℝ)
    (he : 0≤e) (hN : 1≤N) (hcut : omega≤a) (h : List ℕ) (hl : h.length=8)
    (c : Cell) (hs : Source c (primeHistoryLogCoordinates N 8 h))
    (hfirst : HistoricalThirdCoarse.firstStop (e:ℝ) (bank e q a).m N (rosserAncestor 1 h))
    (hsup : P1ThirdFallbackSupport.supported (e:ℝ) (bank e q a).chi (bank e q a).m a N (rosserAncestor 3 h))
    (hodd : ∀ j : Fin 4,oldHistory (primeHistoryLogCoordinates N 8 h) j<lambda3 (oldBank e q a) N (rosserAncestor 4 h)) :
    let d := bank e q a
    let pre := rosserAncestor 6 h
    let R := current d omega N pre
    let M := if R.lower then cap6 R d N n pre else P4AOriginalOrderedThirdFullPolicy.after R d N pre 8
    lambda3 (oldBank e q a) N (rosserAncestor 4 h)≤M ∧ M≤comparison c (primeHistoryLogCoordinates N 8 h) := by
  let d := bank e q a
  let pre := rosserAncestor 6 h
  have hr := history e q a N he h hl c hs hfirst hsup hodd
  have hf := fifth_bounds n e q a N he h hl c hs hr
  have ha := (P4AOriginalFull87DataPolicy.active_ancestor d N 6 (by decide) h).mpr
    (P4AOriginalFull87UnionHistory.source_active hl hs hr)
  have ho : P1ThirdFallbackSupport.frozenSupported d.e d.chi d.m d.omega N pre := by
    change P1ThirdFallbackSupport.supported _ _ _ _ _ (rosserAncestor 3 (rosserAncestor 6 h))
    rw [rosserAncestor_nested 3 6 (by decide)]
    exact hsup
  have hed : 0≤(d.e:ℝ) := by exact_mod_cast he
  have hrw := root_on_old_owner hed hN hcut ho
  change lambda3 (oldBank e q a) N (rosserAncestor 4 h)≤
      (if (current d omega N pre).lower then cap6 (current d omega N pre) d N n pre
       else P4AOriginalOrderedThirdFullPolicy.after (current d omega N pre) d N pre 8) ∧ _
  rw [hrw,if_pos (show (prior d N pre).lower from ha),cap6_prior]
  have h5 := P4AOriginalFull87DataPolicy.cap5_le_licensed n d N pre
  dsimp only [pre] at h5
  rw [rosserAncestor_nested 5 6 (by decide)] at h5
  refine ⟨hf.1.trans h5,?_⟩
  unfold P4AOriginalFull87DataPolicy.licensedCap
  apply finiteMax_le
  · simpa only [pre,rosserAncestor_nested 5 6 (by decide)] using hf.2
  · intro b _ haccept
    have htent := P4AOriginalFull87CompleteSixthBound.source_ancestor_tent_le_comparison N h hl c hs 6
      (by decide) (P4AOriginalSixthActionBank.selected b)
    have hsmall := haccept.2.2.trans htent
    linarith only [hsmall,width_pos n]

end
end ImbalancedChen.P4AOriginalNonsingletonEighthParent
