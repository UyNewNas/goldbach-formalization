import ImbalancedChen.P4AOriginalOrderedSixthSigned
import ImbalancedChen.P4AOriginalSixthTupleReverse

/-! A whole ordered fifth decision agrees with the earlier d+ decision
on a word with a historical third owner. At ranks one and two both
read the initial policy. All longer ancestors read that same third root. -/
namespace ImbalancedChen.P4AOriginalOrderedFifthOwner
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalOrderedThirdFullPolicy (current prior common base five five_prior root_on_old_owner
  cap5_prior fifth_prior prior_ancestor)
open P4AOriginalOrderedSixthStages (orderedFifth orderedLevel finiteAt rawAt level)
open P4AOriginalSavedSixthSigned (pre old)
open P4AOriginalSavedSixthHistoricalOwner (pre_list)
open P4AOriginalFull87DataPolicy (fifthPolicy level5Exponent active_ancestor)

theorem fifth_on_owner (n : ℕ) (d : OriginalData) {omega N : ℝ}
    (he : 0≤(d.e:ℝ)) (hN : 1≤N) (hwa : omega≤d.omega) {h : List ℕ}
    (hs : P1ThirdFallbackSupport.frozenSupported d.e d.chi d.m d.omega N h) (b : Bool) :
    orderedFifth n d omega N b h=fifthPolicy n d N b h := by
  rw [orderedFifth,root_on_old_owner he hN hwa hs,five_prior]

theorem prior_zero (n : ℕ) (d : OriginalData) (N : ℝ) (h : List ℕ) :
    level 0 n (prior d N h) d N h=old n d N h := by
  simp only [level,finiteAt,rawAt,old,level5Exponent,active_ancestor d N 5 (by decide),
    ←cap5_prior n d N (rosserAncestor 5 h),←fifth_prior d N (rosserAncestor 5 h),
    prior_ancestor d N h 5 (by decide)] <;> rfl

theorem admitted_iff_on_owner (n : ℕ) (d : OriginalData) {omega : ℝ} {N cap : ℕ} {z : ℝ}
    (he : 0≤(d.e:ℝ)) (hN : 1≤(N:ℝ)) (hwa : omega≤d.omega) (p : Fin 6→ℕ)
    (hs : P1ThirdFallbackSupport.frozenSupported d.e d.chi d.m d.omega (N:ℝ) (pre p)) :
    p∈P4AOriginalOrderedSixthSigned.admitted n d omega N cap z ↔
      p∈P4AOriginalSavedSixthSigned.admitted n d N cap z := by
  have h1 : orderedFifth n d omega N false [p 0]=fifthPolicy n d N false [p 0] := by
    rw [←five_prior n d (N:ℝ) false [p 0]]
    simp [orderedFifth,five,common,base,firstExitDepthSplicePolicy]
  have h3 : P1ThirdFallbackSupport.frozenSupported d.e d.chi d.m d.omega (N:ℝ) [p 2,p 1,p 0] := by
    simpa [P1ThirdFallbackSupport.frozenSupported,pre_list,rosserAncestor] using hs
  have h5 : P1ThirdFallbackSupport.frozenSupported d.e d.chi d.m d.omega (N:ℝ) [p 4,p 3,p 2,p 1,p 0] := by
    simpa [P1ThirdFallbackSupport.frozenSupported,pre_list,rosserAncestor] using hs
  have hov3 := fifth_on_owner n d he hN hwa h3 false
  have hov5 := fifth_on_owner n d he hN hwa h5 false
  simp only [P4AOriginalOrderedSixthSigned.admitted,P4AOriginalSavedSixthSigned.admitted,
    mem_firstExitAdmittedTuples_iff]
  apply and_congr_right
  intro _
  rw [show List.ofFn p=[p 0,p 1,p 2,p 3,p 4,p 5] by simp [List.ofFn_succ]]
  simp only [FirstExitValidSelection,Bool.not_true,Bool.not_false,P4AOriginalOrderedSixthSigned.fifth_even,
    P4AOriginalFull87DataPolicy.fifth_even,h1,hov3,hov5]

end
end ImbalancedChen.P4AOriginalOrderedFifthOwner
