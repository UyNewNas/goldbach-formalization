import ImbalancedChen.P4AOriginalFull87OwnedEighthSource
import ImbalancedChen.P4AOriginalFull87SignedDeletionLedger
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4: distinguish the genuine arithmetic old-minus-new signedTest from
the finite g_N first-exit correction. They are NOT equal in general:
signedTest uses unit branch weights and the complete sign-dependent,
full-modulus attachedLeafTest. The first-exit correction uses g_N.

We prove the exact identity with its missing arithmetic terminal term.
The latter is explicitly represented on both genuine retained leaf lists,
with their signs and occurrences. No pointwise or asymptotic smallness
of that term is claimed. The rank-nine exits are NOT deleted. The prior
rank>=11 deletion ledger is NOT equated with this arithmetic difference.

All policies, original owner/trim states and beta attachments are the
same as P4AOriginalFull87OwnedEighthSource.
-/

namespace ImbalancedChen.P4AOriginalFull87ArithmeticTerminalBridge
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
  (signedTest signedTest_sub signedTest_eq_leaves attachedLeafTest)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87EighthKernelIntegration (actualParent)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87OwnedEighthSource
  (ordinarySaving ownedSource physical_saving_eq_owned_sources)
open P4AOriginalLicensedSixthSignedLedger (physical)
open P4AOriginalFull87LicensedSixthPolicy (sixthPolicy)
open P4AOriginalFull87LicensedSixthRealization (policy)

/-- Product of physical prime densities at the *actual selected word*.
This is a terminal function, not a new selection policy. -/
def selectedProduct {α : Type*} (g : α → ℝ)
    (_positive : Bool) (word : List α) : ℝ :=
  (word.map g).prod

/-- A unit-weight signedTest carrying the full selected product at each
terminal leaf is exactly the original g-weighted retained polynomial.
The proof recursively accounts for every SELECT and SKIP occurrence. -/
theorem signedTest_terminal_product_eq_retained {α : Type*}
    (R : Bool → List α → Bool) (g : α → ℝ)
    (remaining : List α) :
    ∀ (pre : List α) (positive : Bool) (mass : ℝ),
      signedTest R (fun _ : α => (1 : ℝ)) (selectedProduct g)
          pre positive mass remaining =
        firstExitRetainedPolynomial R g pre positive
          (mass * (pre.map g).prod) remaining := by
  induction remaining with
  | nil =>
      intro pre positive mass
      cases positive <;>
        simp [signedTest, firstExitRetainedPolynomial,
          selectedProduct, signedTreeCoefficient] <;> ring
  | cons p ps ih =>
      intro pre positive mass
      by_cases hp : R (!positive) (p :: pre) = true
      · simp only [signedTest, firstExitRetainedPolynomial, if_pos hp, mul_one]
        rw [ih pre positive mass, ih (p :: pre) (!positive) mass]
        simp only [List.map_cons, List.prod_cons]
        have hm : mass * (g p * (pre.map g).prod) =
            (mass * (pre.map g).prod) * g p := by ring
        rw [hm]
      · simpa only [signedTest, firstExitRetainedPolynomial,
          if_neg hp, add_zero] using ih pre positive mass

/-- The equality that was missing between the original arithmetic test
and the physical first-exit series. It is exact for arbitrary terminal
data T, without assuming the arithmetic term resembles a sieve density.

The common unrestricted Euler product cancels ONLY because the two
policies act on the same incoming word, sign, mass and remaining list.
The residue is the difference of two actual terminal-test mismatches;
it cannot be discarded by cap monotonicity or geometric null measure. -/
theorem signedTest_old_new_exact_bridge {α : Type*}
    (oldPolicy newPolicy : Bool → List α → Bool)
    (g : α → ℝ) (T : Bool → List α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) :
    signedTest oldPolicy (fun _ : α => (1 : ℝ)) T
        pre positive mass remaining -
      signedTest newPolicy (fun _ : α => (1 : ℝ)) T
        pre positive mass remaining =
      (firstExitCorrection oldPolicy g pre positive
          (mass * (pre.map g).prod) remaining -
        firstExitCorrection newPolicy g pre positive
          (mass * (pre.map g).prod) remaining) +
      (signedTest oldPolicy (fun _ : α => (1 : ℝ))
          (fun b xs => T b xs - selectedProduct g b xs)
          pre positive mass remaining -
        signedTest newPolicy (fun _ : α => (1 : ℝ))
          (fun b xs => T b xs - selectedProduct g b xs)
          pre positive mass remaining) := by
  have hOldSub := signedTest_sub oldPolicy (fun _ : α => (1 : ℝ))
    T (selectedProduct g) pre remaining positive mass
  have hNewSub := signedTest_sub newPolicy (fun _ : α => (1 : ℝ))
    T (selectedProduct g) pre remaining positive mass
  have hOldProd :=
    signedTest_terminal_product_eq_retained oldPolicy g remaining pre positive mass
  have hNewProd :=
    signedTest_terminal_product_eq_retained newPolicy g remaining pre positive mass
  have hOldCorr :=
    firstExitRetainedPolynomial_eq_product_add_correction oldPolicy g pre
      remaining positive (mass * (pre.map g).prod)
  have hNewCorr :=
    firstExitRetainedPolynomial_eq_product_add_correction newPolicy g pre
      remaining positive (mass * (pre.map g).prod)
  calc
    _ =
        (signedTest oldPolicy (fun _ : α => (1 : ℝ)) (selectedProduct g)
          pre positive mass remaining -
         signedTest newPolicy (fun _ : α => (1 : ℝ)) (selectedProduct g)
          pre positive mass remaining) +
        (signedTest oldPolicy (fun _ : α => (1 : ℝ))
          (fun b xs => T b xs - selectedProduct g b xs)
          pre positive mass remaining -
         signedTest newPolicy (fun _ : α => (1 : ℝ))
          (fun b xs => T b xs - selectedProduct g b xs)
          pre positive mass remaining) := by
            rw [hOldSub, hNewSub]
            ring
    _ = _ := by
      rw [hOldProd, hNewProd, hOldCorr, hNewCorr]
      ring

/-- Exact original old sixth level at the actual eighth selected word. -/
private def oldAt (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N : ℕ) (s : FirstExitDepthState ℕ) :
    Bool → List ℕ → Bool :=
  ordinaryParityRosserPolicy false
    ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix)

/-- Exact new finite cap at the SAME eighth selected word and owner. -/
private def newAt (n : ℕ) (N : ℕ) (c : Cell)
    (s : FirstExitDepthState ℕ) : Bool → List ℕ → Bool :=
  ordinaryParityRosserPolicy false
    ((N : ℝ) ^ (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ))

/-- This is the genuine full-q attached terminal, MINUS the physical
selected-density product. No arithmetic-smallness premise is inserted. -/
def arithmeticTerminalMismatch (N cap : ℕ) (w L : ℝ)
    (G : ℕ → ℝ) (b : Bool) (pre : List ℕ) : ℝ :=
  attachedLeafTest N cap 1 w L G b pre -
    selectedProduct halfProductDensity b pre

def correctionGapAt (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N : ℕ) (c : Cell) (s : FirstExitDepthState ℕ) : ℝ :=
  firstExitCorrection (oldAt n e q om N s)
      halfProductDensity s.selectedPrefix s.positive
      (s.mass * (s.selectedPrefix.map halfProductDensity).prod) s.remaining -
    firstExitCorrection (newAt n N c s)
      halfProductDensity s.selectedPrefix s.positive
      (s.mass * (s.selectedPrefix.map halfProductDensity).prod) s.remaining

def terminalMismatchGapAt (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (G : ℕ → ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ) : ℝ :=
  signedTest (oldAt n e q om N s) (fun _ : ℕ => (1 : ℝ))
      (arithmeticTerminalMismatch N cap w L G)
      s.selectedPrefix s.positive s.mass s.remaining -
    signedTest (newAt n N c s) (fun _ : ℕ => (1 : ℝ))
      (arithmeticTerminalMismatch N cap w L G)
      s.selectedPrefix s.positive s.mass s.remaining

/-- Precise identity at an actual eighth selected word. It keeps the
original full modulus in attachedLeafTest, the sign-sensitive plus/minus
terminal, and both original parent/finite-cap policies unchanged. -/
theorem ordinarySaving_eq_correctionGap_add_terminalGap
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (G : ℕ → ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ) :
    ordinarySaving n e q om N cap w L G c s =
      correctionGapAt n e q om N c s +
        terminalMismatchGapAt n e q om N cap w L G c s := by
  simpa [ordinarySaving, correctionGapAt, terminalMismatchGapAt,
    oldAt, newAt, arithmeticTerminalMismatch, selectedProduct] using
    (signedTest_old_new_exact_bridge
      (oldAt n e q om N s) (newAt n N c s)
      halfProductDensity (attachedLeafTest N cap 1 w L G)
      s.selectedPrefix s.remaining s.positive s.mass)

/-- Ordinary finite list linearity, retaining each repeated occurrence. -/
private theorem list_sum_map_add {α : Type*} (xs : List α) (f g : α → ℝ) :
    (xs.map (fun x => f x + g x)).sum =
      (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

def ownedCorrectionGap (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (om : ℝ) (N cap : ℕ) (w z : ℝ) (c : Cell) : ℝ :=
  ((states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c).map
    (correctionGapAt n e q om N c)).sum

def ownedTerminalMismatchGap (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (om : ℝ) (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) (c : Cell) : ℝ :=
  ((states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c).map
    (terminalMismatchGapAt n e q om N cap w L G c)).sum

/-- No new mask or matching condition is assumed: the true original
ownedSource is exactly the correction-gap sum PLUS the original full-q
terminal mismatch for every genuine owner/trim occurrence. -/
theorem ownedSource_eq_correction_add_terminalMismatch
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) (c : Cell) :
    ownedSource delta n e q om N cap w z L G c =
      ownedCorrectionGap delta n e q om N cap w z c +
        ownedTerminalMismatchGap delta n e q om N cap w z L G c := by
  unfold ownedSource ownedCorrectionGap ownedTerminalMismatchGap
  rw [← list_sum_map_add
    (states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c)
    (correctionGapAt n e q om N c)
    (terminalMismatchGapAt n e q om N cap w L G c)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  exact ordinarySaving_eq_correctionGap_add_terminalGap
    n e q om N cap w L G c s

/-- The full, original old-minus-new physical arithmetic saving equals
the full87 physical correction difference PLUS the missing full-q
terminal mismatch. This identity does not identify the rank>=11
once-deleted comparison ledger with the actual arithmetic coefficient. -/
theorem physical_saving_eq_correction_plus_terminalMismatch
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    physical (sixthPolicy n e q om (N : ℝ)) N cap w z L G -
      physical (policy delta n e q om (N : ℝ)) N cap w z L G =
        (∑ c : Cell, ownedCorrectionGap delta n e q om N cap w z c) +
        (∑ c : Cell, ownedTerminalMismatchGap delta n e q om N cap w z L G c) := by
  rw [physical_saving_eq_owned_sources]
  calc
    (∑ c : Cell, ownedSource delta n e q om N cap w z L G c) =
      ∑ c : Cell,
        (ownedCorrectionGap delta n e q om N cap w z c +
          ownedTerminalMismatchGap delta n e q om N cap w z L G c) := by
            apply Finset.sum_congr rfl
            intro c hc
            exact ownedSource_eq_correction_add_terminalMismatch
              delta n e q om N cap w z L G c
    _ = _ := Finset.sum_add_distrib

/-- Retain the original signed terminal occurrences in an explicit
nonnegative absolute-error ledger, for each of the TWO original trees. -/
def retainedLeafMismatchCost {α : Type*} (R : Bool → List α → Bool)
    (g : α → ℝ) (T : Bool → List α → ℝ)
    (pre remaining : List α) (positive : Bool) (mass : ℝ) : ℝ :=
  ((firstExitRetainedLeaves R (fun _ : α => (1 : ℝ))
      pre positive mass remaining).map
    (fun leaf => |leaf.value| *
      |T leaf.positive leaf.selected -
        selectedProduct g leaf.positive leaf.selected|)).sum

private theorem list_abs_sum_le {α : Type*} (xs : List α) (f : α → ℝ) :
    |(xs.map f).sum| ≤ (xs.map (fun x => |f x|)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      calc
        |f x + (xs.map f).sum| ≤
          |f x| + |(xs.map f).sum| := abs_add_le _ _
        _ ≤ |f x| + (xs.map (fun y => |f y|)).sum :=
          add_le_add_left ih _

/-- The remaining full-q arithmetic error is NOT zero; its absolute
value is bounded by the literal signed-leaf terminal discrepancies.
No distributional input is used and no reserve is yet spent. -/
theorem signedTest_terminalMismatch_abs_le_retainedCost {α : Type*}
    (R : Bool → List α → Bool) (g : α → ℝ)
    (T : Bool → List α → ℝ) (pre remaining : List α)
    (positive : Bool) (mass : ℝ) :
    |signedTest R (fun _ : α => (1 : ℝ))
      (fun b xs => T b xs - selectedProduct g b xs)
      pre positive mass remaining| ≤
        retainedLeafMismatchCost R g T pre remaining positive mass := by
  rw [signedTest_eq_leaves]
  unfold retainedLeafMismatchCost
  calc
    _ ≤
      ((firstExitRetainedLeaves R (fun _ : α => (1 : ℝ))
        pre positive mass remaining).map
        (fun leaf => |leaf.value *
          (T leaf.positive leaf.selected -
            selectedProduct g leaf.positive leaf.selected)|)).sum :=
        list_abs_sum_le _ _
    _ = _ := by
      congr 1
      apply List.map_congr_left
      intro leaf hleaf
      rw [abs_mul]

end
end ImbalancedChen.P4AOriginalFull87ArithmeticTerminalBridge
