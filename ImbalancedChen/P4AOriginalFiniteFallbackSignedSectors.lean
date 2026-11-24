import ImbalancedChen.P4AOriginalFiniteFallbackPolicy

namespace ImbalancedChen.P4AOriginalFiniteFallbackSignedSectors
noncomputable section
open scoped Classical
open P4AOriginalFiniteFallbackPolicy
open P4AOriginalFull87RawChronology (rawRoot)

theorem high_cons (N : ℝ) (x : ℕ) {p : List ℕ} (hp : p≠[]) :
    high N (x::p) ↔ high N p := by
  have hl : 1≤p.length := by cases p <;> simp_all
  simp only [high,point,rosserAncestor_cons 1 x p hl]

theorem inside (N : ℝ) (U L : Rule) (h : ℕ → ℝ) (p xs : List ℕ) (pos : Bool)
    (mass : ℝ) (hp : p≠[]) :
    firstExitRetainedPolynomial (dispatch N U L) h p pos mass xs=
      if high N p then firstExitRetainedPolynomial U h p pos mass xs
      else firstExitRetainedPolynomial L h p pos mass xs := by
  induction xs generalizing p pos mass with
  | nil => simp [firstExitRetainedPolynomial]
  | cons x xs ih =>
    simp only [firstExitRetainedPolynomial,ih _ _ _ hp,ih _ _ _ (List.cons_ne_nil _ _),
      dispatch,high_cons N x hp]
    split_ifs <;> rfl

theorem signed_split (N : ℝ) (U V L M : Rule) (h : ℕ → ℝ) (xs : List ℕ) (pos : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial (dispatch N U L) h [] pos mass xs-
      firstExitRetainedPolynomial (dispatch N V L) h [] pos mass xs=
    firstExitRetainedPolynomial (dispatch N U M) h [] pos mass xs-
      firstExitRetainedPolynomial (dispatch N V M) h [] pos mass xs := by
  induction xs with
  | nil => simp [firstExitRetainedPolynomial]
  | cons x xs ih =>
    simp only [firstExitRetainedPolynomial,inside N _ _ h [x] xs _ _ (by simp),dispatch]
    by_cases H : high N [x] <;> simp only [H,if_true,if_false] <;> linarith only [ih]

theorem original_root (B C : P4AOriginalFiniteFallbackBank.Bank)
    (d : P5OriginalCommonRefinedConstructor.OriginalData) (w : ℝ) (N : ℕ)
    (L M : Rule) (hL : ∀ p,L true p=true) (hM : ∀ p,M true p=true) :
    rawRoot (dispatch N (upper B d w N) L) N - rawRoot (dispatch N (upper C d w N) L) N =
    rawRoot (dispatch N (upper B d w N) M) N - rawRoot (dispatch N (upper C d w N) M) N := by
  have pos (A : P4AOriginalFiniteFallbackBank.Bank) (R : Rule) (hR : ∀ p,R true p=true) :
      ∀ p,dispatch N (upper A d w N) R true p=true := by
    intro p
    simp [dispatch,upper,HistoricalThirdCoarse.initialPolicy,ordinaryParityRosserPolicy,oddFirstExitPolicy,hR]
  have eqv (A : P4AOriginalFiniteFallbackBank.Bank) (R : Rule) (hR : ∀ p,R true p=true) :=
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
      (dispatch N (upper A d w N) R) (pos A R hR) N N 0 (P4AOriginalFull87RawChronology.cutoff N)
  change _ - _ = _ - _
  exact (congrArg₂ (·-·) (eqv B L hL).symm (eqv C L hL).symm).trans
    ((signed_split N _ _ L M _ _ true 1).trans
      (congrArg₂ (·-·) (eqv B M hM) (eqv C M hM)))

end
end ImbalancedChen.P4AOriginalFiniteFallbackSignedSectors
