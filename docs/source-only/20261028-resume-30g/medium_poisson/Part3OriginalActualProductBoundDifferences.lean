import ImbalancedChen.Part3OriginalActualRetainedPhaseCost
import Mathlib.Tactic

/-!
Source only; uncompiled; zero formal credit.
Remove only the total rough-product window from the actual independent
factor-choice fibres. All individual windows, both st=d choices, the
original gamma support and smooth trims remain. The two original
lambdaTrim windows then become their four SIGNED upper-bound terms.
These are product-bound branches, not invented uniform phase charts.
-/

noncomputable section
open Classical Finset Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalLambdaTrimPoissonFamily20261028
open ImbalancedChen.Part3.OriginalActualLambdaPairExpansion20261028
open ImbalancedChen.Part3.OriginalSamePsiS1OwnedAtlas
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumOwnedCanonicalReindex20261028
open ImbalancedChen.Part3.MediumCanonicalFixedBlock20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.OriginalMediumDoubleLambdaColorWindows20261028

namespace ImbalancedChen.Part3.OriginalActualProductBoundDifferences20261028

attribute [local instance] Classical.propDecidable

def actualFactorAmbient (atom : MediumAtom) (z : ℝ) (k : Key) (small : ℕ) : Finset Factor :=
  let F := (fixedBlock k small).factorData atom (strictReceiverCutoff z)
  F.smoothS.biUnion fun s => F.smoothT.biUnion fun t =>
    F.roughU.biUnion fun u => F.roughV.image fun v => (⟨s,t,u,v⟩ : Factor)

def choicesWithoutProductWindow (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) : Finset Factor :=
  (actualFactorAmbient atom z k small).filter (fun p =>
    p.s * p.t = small ∧ p.u * p.s ∈ factorCarrier atom.Q2 ∧
      p.v * p.t ∈ factorCarrier atom.Q3 ∧ (p.s : ℝ) ≤ y ∧ (p.t : ℝ) ≤ y)

/-- Exact interface to the ORIGINAL actual trimmedChoices. -/
theorem mem_trimmedChoices_iff_withoutProductWindow
    (atom : MediumAtom) (z y : ℝ) (k : Key) (small w : ℕ) (p : Factor) :
    p ∈ trimmedChoices atom (strictReceiverCutoff z) y k small w ↔
      p ∈ choicesWithoutProductWindow atom z y k small ∧
        p.u * p.v = w ∧ w ∈ dyadicWindow k.w := by
  rw [dyadicWindow_eq_Icc]
  simp only [trimmedChoices, FactorData.choices, choicesWithoutProductWindow,
    Finset.mem_filter]
  change (((p ∈ actualFactorAmbient atom z k small) ∧
    p.s * p.t = small ∧ p.u * p.v = w ∧
      p.u * p.s ∈ factorCarrier atom.Q2 ∧ p.v * p.t ∈ factorCarrier atom.Q3 ∧
        p.u * p.v ∈ Finset.Icc (2 ^ k.w) (2 ^ (k.w + 1) - 1)) ∧
    (p.s : ℝ) ≤ y ∧ (p.t : ℝ) ≤ y) ↔
    (((p ∈ actualFactorAmbient atom z k small) ∧ p.s * p.t = small ∧
      p.u * p.s ∈ factorCarrier atom.Q2 ∧ p.v * p.t ∈ factorCarrier atom.Q3 ∧
        (p.s : ℝ) ≤ y ∧ (p.t : ℝ) ≤ y) ∧ p.u * p.v = w ∧
          w ∈ Finset.Icc (2 ^ k.w) (2 ^ (k.w + 1) - 1))
  constructor
  · rintro ⟨⟨ha, hd, hw, h2, h3, hb⟩, hsy, hty⟩
    exact ⟨⟨ha, hd, h2, h3, hsy, hty⟩, hw, by simpa only [hw] using hb⟩
  · rintro ⟨⟨ha, hd, h2, h3, hsy, hty⟩, hw, hb⟩
    exact ⟨⟨ha, hd, hw, h2, h3, by simpa only [hw] using hb⟩, hsy, hty⟩

/-- This fibre has ONLY the total-product interval removed. -/
def productUnrestrictedLambda (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small w : ℕ) : ℂ :=
  ∑ p ∈ (choicesWithoutProductWindow atom z y k small).filter
      (fun p => p.u * p.v = w), choiceCoefficient atom z k small p

theorem actual_lambdaTrim_eq_product_window
    (atom : MediumAtom) (z y : ℝ) (k : Key) (small w : ℕ) :
    lambdaTrim atom (strictReceiverCutoff z) y k small w =
      if w ∈ dyadicWindow k.w then productUnrestrictedLambda atom z y k small w else 0 := by
  have hs : trimmedChoices atom (strictReceiverCutoff z) y k small w =
      (choicesWithoutProductWindow atom z y k small).filter
        (fun p => p.u * p.v = w ∧ w ∈ dyadicWindow k.w) := by
    ext p
    rw [mem_trimmedChoices_iff_withoutProductWindow]
    simp only [Finset.mem_filter]
  unfold lambdaTrim
  rw [hs]
  by_cases hw : w ∈ dyadicWindow k.w
  · simp only [hw, and_true, if_true]
    rfl
  · simp only [hw, and_false, Finset.filter_false, Finset.sum_empty, if_false]

def lowerProductBound (k : Key) : ℕ := 2 ^ k.w - 1
def upperProductBound (k : Key) : ℕ := 2 ^ (k.w + 1) - 1

theorem productBound_order (k : Key) : lowerProductBound k ≤ upperProductBound k := by
  have hp : 0 < (2 : ℕ) ^ k.w := pow_pos (by norm_num) _
  unfold lowerProductBound upperProductBound
  rw [pow_succ]
  omega

theorem actual_window_iff_productBounds (k : Key) (w : ℕ) :
    w ∈ dyadicWindow k.w ↔ lowerProductBound k < w ∧ w ≤ upperProductBound k := by
  have hp : 0 < (2 : ℕ) ^ k.w := pow_pos (by norm_num) _
  simp only [dyadicWindow, Finset.mem_Ico, lowerProductBound, upperProductBound]
  omega

def productUpperPayload (atom : MediumAtom) (z y : ℝ) (k : Key)
    (small r s Br Bs : ℕ) (Z : ℂ) : ℂ :=
  (if r ≤ Br then productUnrestrictedLambda atom z y k small r *
      star (productUnrestrictedLambda atom z y k small s) * Z else 0) *
    (if s ≤ Bs then (1 : ℂ) else 0)

/-- Every pair of independent original product intervals has all four
signed upper terms. No lower endpoint or st=d copy is discarded. -/
theorem actual_lambda_pair_upper_bound_difference
    (atom : MediumAtom) (z y : ℝ) (k : Key) (small r s : ℕ) (Z : ℂ) :
    lambdaTrim atom (strictReceiverCutoff z) y k small r *
      star (lambdaTrim atom (strictReceiverCutoff z) y k small s) * Z =
      productUpperPayload atom z y k small r s (upperProductBound k) (upperProductBound k) Z -
      productUpperPayload atom z y k small r s (lowerProductBound k) (upperProductBound k) Z -
      productUpperPayload atom z y k small r s (upperProductBound k) (lowerProductBound k) Z +
      productUpperPayload atom z y k small r s (lowerProductBound k) (lowerProductBound k) Z := by
  rw [actual_lambdaTrim_eq_product_window, actual_lambdaTrim_eq_product_window]
  have h := two_product_windows_as_four_upper_terms
    (lowerProductBound k) (upperProductBound k) (lowerProductBound k) (upperProductBound k)
    r s (productBound_order k) (productBound_order k)
    (productUnrestrictedLambda atom z y k small r *
      star (productUnrestrictedLambda atom z y k small s) * Z)
  unfold productUpperPayload
  rw [← h]
  rw [← actual_window_iff_productBounds, ← actual_window_iff_productBounds]
  by_cases hr : r ∈ dyadicWindow k.w <;> by_cases hs : s ∈ dyadicWindow k.w <;>
    simp [hr, hs]

end ImbalancedChen.Part3.OriginalActualProductBoundDifferences20261028
