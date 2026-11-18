import ImbalancedChen.P3HBRestoredSixPolynomialD
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-!
P3.6 — directly identify the genuine ordered derivative of the UNSPLIT
six-slot physical grouped HB profile with the previous SIGNED 729-child
restoration. Previously only the latter's own derivative integrals were
estimated; an equality to the direct derivative was missing.

This packet pays the exact finite derivative/signed restoration interchange
under the explicit ORDINARY slice-differentiability condition of the
literal child functions. This condition is not the desired integral
estimate, Fourier decay, nor a statement about the modulus discrepancy.
Its elimination for the actual C-infinity factors remains INTERNAL.
No assertion here covers all frozen U5/hats, growing m(T), or same-rho PP.

Paper UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
§2 original smooth dyadic HB and §4 (F) doubled ordered mixed derivatives.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBUnsplitDirectRestoration
noncomputable section

open MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3HBCanonicalGeometryDerivative
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst
open ImbalancedChen.P3HBSmoothThreeWayRatioTwo
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBOriginalRestoredTensorL1
open ImbalancedChen.P3HBRestoredSixCoordinateD
open ImbalancedChen.P3HBRestoredSixPolynomialD
open ImbalancedChen.P3U5ChartMixedL1Budget

/-- The *unseparated* actual six-position geometry: every original group
factor, the ONE complete physical-product trim, and the six original
dyadic differences, before child labels or differentiating. -/
def originalSixUnsplitWeight {g : ℕ}
    (chi eta : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (u : Fin 6 → ℝ) : ℂ :=
  originalGroupPhysicalTrim chi eta c J s u * unsplitSixLogTensor chi u

/-- Ordinary local regularity of the EXPLICIT actual child derivatives.
No integral bound, rho, or PP conclusion is a premise. The proof that
C-infinity of chi,eta discharges this for every word remains an internal
elaboration task; it cannot be silently replaced by an axiom. -/
def OriginalChildSliceRegular {g : ℕ}
    (chi eta : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (s : ℝ) : Prop :=
  ∀ (word : List (Fin 6)) (child : Fin 6 → Fin 3),
    child ∈ smoothChildren →
      ∀ (u : Fin 6 → ℝ) (i : Fin 6),
        DifferentiableAt ℝ
          (fun t : ℝ =>
            originalOrderedAxisDeriv word
              (fun v => originalGroupPhysicalTrim chi eta c J s v *
                logTensorMixed chi (fun _ => 0) child v)
              (Function.update u i t))
          (u i)

/-- Actual physical geometry equals the signed sum of exactly the
original 3^6 positional smooth children, before derivatives or norms. -/
theorem originalSixUnsplitWeight_eq_children {g : ℕ}
    (chi eta : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) (u : Fin 6 → ℝ) :
    originalSixUnsplitWeight chi eta c J s u =
      ∑ child ∈ smoothChildren,
        originalGroupPhysicalTrim chi eta c J s u *
          logTensorMixed chi (fun _ => 0) child u := by
  unfold originalSixUnsplitWeight
  rw [unsplitSixLogTensor_eq_children chi hchi u]
  rw [Finset.mul_sum]

/-- Finite signed differentiation commutes with the sum of actual
child functions when all corresponding *slices* are differentiable.
The derivative is the genuine originalOrderedAxisDeriv, NOT an abstract
jet family; repetitions and the literal order of axes are preserved. -/
private theorem orderedDerivative_finset_sum {α : Type*}
    (S : Finset α) (F : α → (Fin 6 → ℝ) → ℂ)
    (hregular :
      ∀ (word : List (Fin 6)) (a : α), a ∈ S →
        ∀ (u : Fin 6 → ℝ) (i : Fin 6),
          DifferentiableAt ℝ
            (fun t : ℝ =>
              originalOrderedAxisDeriv word (F a) (Function.update u i t))
            (u i)) :
    ∀ (word : List (Fin 6)) (u : Fin 6 → ℝ),
      originalOrderedAxisDeriv word (fun v => ∑ a ∈ S, F a v) u =
        ∑ a ∈ S, originalOrderedAxisDeriv word (F a) u := by
  classical
  intro word
  induction word with
  | nil =>
      intro u
      rfl
  | cons i rest ih =>
      intro u
      have heq :
          originalOrderedAxisDeriv rest (fun v => ∑ a ∈ S, F a v) =
            (fun v => ∑ a ∈ S, originalOrderedAxisDeriv rest (F a) v) := by
        funext v
        exact ih v
      change actualAxisDeriv
          (originalOrderedAxisDeriv rest (fun v => ∑ a ∈ S, F a v)) i u =
        ∑ a ∈ S, actualAxisDeriv (originalOrderedAxisDeriv rest (F a)) i u
      rw [heq]
      unfold actualAxisDeriv
      exact deriv_fun_sum
        (u := S)
        (A := fun a t =>
          originalOrderedAxisDeriv rest (F a) (Function.update u i t))
        (x := u i)
        (by
          intro a ha
          exact hregular rest a ha u i)

/-- Missing direct-to-signed high-order restoration, on the explicitly
stated local regularity domain. No interchange of mixed derivative
orders and no 729-fold absolute-value loss occur in this equality. -/
theorem originalUnsplitOrdered_eq_restored {g k : ℕ}
    (chi eta : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (hregular : OriginalChildSliceRegular chi eta c J s)
    (axes : Fin k → Fin 6) (u : Fin 6 → ℝ) :
    originalOrderedAxisDeriv (List.ofFn axes)
      (originalSixUnsplitWeight chi eta c J s) u =
    originalRestoredWholeDerivative chi eta c J s
      (fun _ => 0) axes u := by
  have hfun :
      originalSixUnsplitWeight chi eta c J s =
        (fun v => ∑ child ∈ smoothChildren,
          originalGroupPhysicalTrim chi eta c J s v *
            logTensorMixed chi (fun _ => 0) child v) := by
    funext v
    exact originalSixUnsplitWeight_eq_children
      chi eta hchi c J s v
  unfold originalRestoredWholeDerivative
  rw [hfun]
  exact orderedDerivative_finset_sum smoothChildren
    (fun child v =>
      originalGroupPhysicalTrim chi eta c J s v *
        logTensorMixed chi (fun _ => 0) child v)
    hregular (List.ofFn axes) u

/-- The direct 64-word (F) mixed-D ledger of the genuine UNSPLIT
six-dimensional grouped physical profile, as opposed to the previously
defined sum of differentiated children. -/
def sixUnsplitDirectMixedD {g : ℕ}
    (chi eta : ℝ → ℂ) (c : Fin g → ℝ)
    (J : Fin g → Finset (Fin 6)) (s : ℝ) : ℝ :=
  ∑ S : Finset (Fin 6),
    ∫ u : Fin 6 → ℝ,
      ‖originalOrderedAxisDeriv (doubled S)
        (originalSixUnsplitWeight chi eta c J s) u‖

/-- Equality of the actual direct (F) ledger and the restored
729-child ledger. This uses one and the same positive physical trim
scale s for every literal ADJACENT doubled word. -/
theorem sixUnsplitDirectMixedD_eq_restored {g : ℕ}
    (chi eta : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (hregular : OriginalChildSliceRegular chi eta c J s) :
    sixUnsplitDirectMixedD chi eta c J s =
      sixRestoredMixedD chi eta c J s := by
  unfold sixUnsplitDirectMixedD sixRestoredMixedD
  apply Finset.sum_congr rfl
  intro S _
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => by
    have hword :
        List.ofFn (fun i : Fin (doubled S).length => (doubled S)[i]) =
          doubled S := by simp
    rw [← hword]
    exact congrArg norm
      (originalUnsplitOrdered_eq_restored chi eta hchi c J s
        hregular (fun i : Fin (doubled S).length => (doubled S)[i]) u))

end
end ImbalancedChen.P3HBUnsplitDirectRestoration
