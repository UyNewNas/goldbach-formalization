import ImbalancedChen.P3HBUnsplitDirectRestoration
import ImbalancedChen.P3HBOriginalWholeChildAllOrder
import ImbalancedChen.P3HBOriginalWholeDerivativeL1
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-!
P3.6: eliminate the ordinary slice-regularity hypothesis from the
literal UNSPLIT six-slot original HB weight's signed derivative
restoration. The true group product, unique physical complete-product
trim, all 729 positional children and ordered repeated derivatives
are kept. No new geometric jet field or distribution premise is used.

The previously stated OriginalChildSliceRegular was deliberately left
unproved. Here it follows from the existing genuine all-order finite
Leibniz allocation, geometric-jet slice differentiability and the
actual coupled log-tensor derivative. The result is limited to this
specific six-coordinate smooth source, not all U5/hats or physical W_T.

Pinned paper: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
§2 smooth HB and §4 (F) doubled ordered derivatives.
Lean v4.33.0-rc1, Mathlib
e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBUnsplitChildSliceSmooth
noncomputable section

open scoped Classical BigOperators
open ImbalancedChen.P3HBCanonicalGeometryDerivative
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBWeightedAxisLeibniz
open ImbalancedChen.P3HBWeightedTwoAxisLeibniz
open ImbalancedChen.P3HBOriginalGroupLeibnizAllocation
open ImbalancedChen.P3HBOriginalWholeChildAllOrder
open ImbalancedChen.P3HBUnsplitDirectRestoration

/-- The literal owner term is differentiable along every actual
coordinate slice. This is a differentiability theorem, rather than
merely a formula giving the value of an unverified derivative. -/
private theorem wholeChildTerm_slice_differentiable {g k : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (axes : Fin k → Fin 6) (owner : Fin k → Fin 2)
    (u : Fin 6 → ℝ) (i : Fin 6) :
    DifferentiableAt ℝ (fun t : ℝ =>
      wholeChildTerm chi eta c J s orders child axes owner
        (Function.update u i t)) (u i) := by
  have hW := geometryJet_slice_differentiable
    chi eta hchi heta c J s (axesAssigned axes owner 0) u i
  have hW' : HasDerivAt (fun t : ℝ =>
      originalOrderedAxisDeriv (axesAssigned axes owner 0)
        (originalGroupPhysicalTrim chi eta c J s)
        (Function.update u i t))
      (actualAxisDeriv
        (originalOrderedAxisDeriv (axesAssigned axes owner 0)
          (originalGroupPhysicalTrim chi eta c J s)) i u) (u i) := by
    simpa only [actualAxisDeriv] using hW.hasDerivAt
  have hc := coupledAxis_hasDerivAt chi hchi
    (childOrdersAfter orders (axesAssigned axes owner 1)) child u i
    (originalOrderedAxisDeriv (axesAssigned axes owner 0)
      (originalGroupPhysicalTrim chi eta c J s))
    (actualAxisDeriv
      (originalOrderedAxisDeriv (axesAssigned axes owner 0)
        (originalGroupPhysicalTrim chi eta c J s)) i u) hW'
  have heq :
      (fun t : ℝ => wholeChildTerm chi eta c J s orders child axes owner
        (Function.update u i t)) =
      coupledAxis chi (childOrdersAfter orders (axesAssigned axes owner 1))
        child u i
        (originalOrderedAxisDeriv (axesAssigned axes owner 0)
          (originalGroupPhysicalTrim chi eta c J s)) := by
    funext t
    exact (coupledAxis_eq_weighted_slice chi
      (childOrdersAfter orders (axesAssigned axes owner 1))
      child u i _ t).symm
  rw [heq]
  exact hc.differentiableAt

/-- Every literal child slice required by the previous direct/signed
restoration is differentiable, with NO extra regularity hypothesis.
The smoothness premises are exactly the old chi/eta assumptions.
In particular no integration estimate is used to establish smoothness. -/
theorem originalChildSliceRegular_of_smooth {g : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ) :
    OriginalChildSliceRegular chi eta c J s := by
  classical
  unfold OriginalChildSliceRegular
  intro word child _ u i
  let axes : Fin word.length → Fin 6 := fun j => word.get j
  have hword : List.ofFn axes = word := by simp [axes]
  have hpoint (v : Fin 6 → ℝ) :
      originalOrderedAxisDeriv word
        (fun x => originalGroupPhysicalTrim chi eta c J s x *
          logTensorMixed chi (fun _ => 0) child x) v =
      wholeChildSum chi eta c J s (fun _ => 0) child axes v := by
    rw [← hword]
    exact originalWholeChild_ordered_eq_allocation
      chi eta hchi heta c J s (fun _ => 0) child word.length axes v
  have hslice :
      (fun t : ℝ => originalOrderedAxisDeriv word
        (fun v => originalGroupPhysicalTrim chi eta c J s v *
          logTensorMixed chi (fun _ => 0) child v)
        (Function.update u i t)) =
      (fun t : ℝ => wholeChildSum chi eta c J s
        (fun _ => 0) child axes (Function.update u i t)) := by
    funext t
    exact hpoint (Function.update u i t)
  rw [hslice]
  change DifferentiableAt ℝ
    (fun t : ℝ => ∑ owner : Fin word.length → Fin 2,
      wholeChildTerm chi eta c J s (fun _ => 0) child axes owner
        (Function.update u i t)) (u i)
  apply DifferentiableAt.fun_finsetSum
  intro owner _
  exact wholeChildTerm_slice_differentiable
    chi eta hchi heta c J s (fun _ => 0) child axes owner u i

/-- Direct high-order derivative equals the prior signed restoration
using only the source's true C-infinity regularity, not a supplied
OriginalChildSliceRegular premise. Repeated axes and the 729 labels
remain literal. -/
theorem originalUnsplitOrdered_eq_restored_smooth {g k : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (axes : Fin k → Fin 6) (u : Fin 6 → ℝ) :
    originalOrderedAxisDeriv (List.ofFn axes)
      (originalSixUnsplitWeight chi eta c J s) u =
      originalRestoredWholeDerivative chi eta c J s (fun _ => 0)
        axes u := by
  exact originalUnsplitOrdered_eq_restored chi eta hchi c J s
    (originalChildSliceRegular_of_smooth chi eta hchi heta c J s)
    axes u

/-- The true direct mixed physical six-slot D equals the original
restored 729-child D with no independent slice-regularity premise.
The same single physical trim scale s is used on both sides. -/
theorem sixUnsplitDirectMixedD_eq_restored_smooth {g : ℕ}
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ) :
    sixUnsplitDirectMixedD chi eta c J s =
      sixRestoredMixedD chi eta c J s := by
  exact sixUnsplitDirectMixedD_eq_restored chi eta hchi c J s
    (originalChildSliceRegular_of_smooth chi eta hchi heta c J s)

/-- The direct, not merely signed-restored, 64-word (F) ledger inherits
the degree-12 original group polynomial under the genuine smooth
cutoff and trim assumptions. All 64 doubled words are integrable;
the old additional child-slice condition has been discharged. -/
theorem sixUnsplitDirectMixedD_poly12_smooth
    (chi eta : ℝ → ℂ)
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (hpsi : ∀ t : ℝ, ‖chi t - chi (2 * t)‖ ≤ 1)
    (hetaSmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (hetaLarge : ∀ t : ℝ, 2 ≤ t → eta t = 1) :
    ∃ Cpoly : ℝ, 0 ≤ Cpoly ∧
      ∀ (g : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
          (∀ S : Finset (Fin 6),
            Integrable (fun u : Fin 6 → ℝ =>
              ‖originalOrderedAxisDeriv (doubled S)
                (originalSixUnsplitWeight chi eta c J s) u‖)) ∧
          sixUnsplitDirectMixedD chi eta c J s ≤
            Cpoly * (((g : ℝ) + 1) ^ 12) := by
  obtain ⟨Cpoly, hCpoly, hbase⟩ :=
    sixUnsplitDirectMixedD_poly12 chi eta hchi heta
      hsmall hlarge hpsi hetaSmall hetaLarge
  refine ⟨Cpoly, hCpoly, ?_⟩
  intro g c J hc s hs
  exact hbase g c J hc s hs
    (originalChildSliceRegular_of_smooth chi eta hchi heta c J s)

end
end ImbalancedChen.P3HBUnsplitChildSliceSmooth
