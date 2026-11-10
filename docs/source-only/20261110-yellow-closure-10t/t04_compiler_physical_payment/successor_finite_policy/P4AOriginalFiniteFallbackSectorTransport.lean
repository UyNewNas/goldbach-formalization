import ImbalancedChen.P4AOriginalFiniteFallbackJointGain

namespace ImbalancedChen.P4AOriginalFiniteFallbackSectorTransport
noncomputable section
open scoped Classical
open P4AOriginalFiniteFallbackPolicy (Rule dispatch high upper policy)
open P4AOriginalFiniteFallbackOccurrence (empty empty_eq positive)
open P4AOriginalFiniteFallbackJointGain (before lower_even)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P4AOriginalNewFifthUnion (data)
open P4AOrderedThirdArithmeticOccurrence (fresh)
open P4AFallbackCanonicalBanks (bank)

theorem rectangle (N : ℕ) (U V L M : Rule)
    (hU : ∀ p,U true p=true) (hV : ∀ p,V true p=true)
    (hL : ∀ p,L true p=true) (hM : ∀ p,M true p=true) :
    rawRoot (dispatch N U L) N - rawRoot (dispatch N U M) N =
    rawRoot (dispatch N V L) N - rawRoot (dispatch N V M) N := by
  have eqv (A B : Rule) (ha : ∀ p,A true p=true) (hb : ∀ p,B true p=true) :=
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
      (dispatch N A B) (fun p => by simp [dispatch,ha,hb]) N N 0 (cutoff N)
  have H := P4AOriginalFiniteFallbackSignedSectors.signed_split N U V L M
    (fun p : ℕ => 1/((p:ℝ)-1)) (roughPrimeUniverse N N 0 (cutoff N)) true 1
  rw [←eqv U L hU hL,←eqv U M hU hM,←eqv V L hV hL,←eqv V M hV hM]
  linarith only [H]

/-- A genuine original signed stage whose rules agree above mu transfers
unchanged to the tree with any of the finite high banks. -/
theorem local_increment (N : ℕ) (U L M : Rule) (hU : ∀ p,U true p=true)
    (hL : ∀ p,L true p=true) (hM : ∀ p,M true p=true)
    (h : ∀ pos p,high N p → L pos p=M pos p) :
    rawRoot (dispatch N U L) N - rawRoot (dispatch N U M) N = rawRoot L N-rawRoot M N := by
  rw [rectangle N U L L M hU hL hL hM]
  have hl : dispatch N L L=L := by funext pos p; simp [dispatch]
  have hm : dispatch N L M=M := by
    funext pos p
    by_cases hp : high N p <;> simp [dispatch,hp,h pos p]
  rw [hl,hm]

/-- Exact base-to-final decomposition. Every remaining signed lower
stage is measured on the actual empty-bank tree with the full corrected
lower R17 chronology. -/
theorem complete_split (m n : ℕ) (r : ℝ) (e : ℚ) (q : ℕ) (a w : ℝ) (N : ℕ) :
    let d := data e q a
    let old := fresh d w N
    let L := P4AOriginalOrderedThirdFullPolicy.policy r n d w N
    let low := dispatch N old L
    let full := policy (bank m) r n d w N
    rawRoot old N-rawRoot full N =
      (rawRoot old N-rawRoot low N)+(rawRoot (before m r n e q a w N) N-rawRoot full N) := by
  dsimp only
  rw [before,P4AOriginalFiniteFallbackFullTree.withLower,empty_eq]
  ring

end
end ImbalancedChen.P4AOriginalFiniteFallbackSectorTransport
