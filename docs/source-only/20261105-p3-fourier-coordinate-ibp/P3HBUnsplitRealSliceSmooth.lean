import ImbalancedChen.P3HBUnsplitRealOrderedD
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-!
P3.6 / frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b
prime-product-completion §2 and §4 (F).

Discharge the previous explicit RealUnsplitSliceRegular premise for the
literal chosen smooth real six-slot HB source. This is an actual global
C-infinity statement about the original occurrence-indexed group product,
six dyadic positions and ONE complete-product trim, followed by the
actual real derivative of Function.update coordinate slices.

No Fourier estimate, normalized physical-modulus discrepancy, arbitrary
source-family admission or target-bound premise is introduced.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBUnsplitRealSliceSmooth
noncomputable section

open scoped Classical BigOperators
open MeasureTheory
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBExplicitSmoothCutoffs
open ImbalancedChen.P3HBUnsplitRealProfile
open ImbalancedChen.P3HBUnsplitRealOrderedD
open ImbalancedChen.P3U5ChartMixedL1Budget

/-- The actual finite coordinate sum defining an original HB group is
C-infinity even if a group incidence set is empty. -/
private theorem realGroupSum_contDiff (J : Finset (Fin 6)) :
    ContDiff ℝ ⊤ (originalGroupSum J) := by
  change ContDiff ℝ ⊤ (fun u : Fin 6 → ℝ => ∑ j ∈ J, u j)
  apply ContDiff.sum
  intro j hj
  exact contDiff_apply ℝ ℝ j

private theorem realGroupFactor_contDiff (c : ℝ)
    (J : Finset (Fin 6)) :
    ContDiff ℝ ⊤ (realGroupFactor c J) := by
  have hq : ContDiff ℝ ⊤
      (fun u : Fin 6 → ℝ => c * Real.exp (originalGroupSum J u)) :=
    contDiff_const.mul (Real.contDiff_exp.comp (realGroupSum_contDiff J))
  have h2q : ContDiff ℝ ⊤
      (fun u : Fin 6 → ℝ => (2 : ℝ) *
        (c * Real.exp (originalGroupSum J u))) :=
    contDiff_const.mul hq
  unfold realGroupFactor
  exact (chosenRealChi_smooth.comp hq).sub
    (chosenRealChi_smooth.comp h2q)

private theorem realSlotFactor_contDiff (i : Fin 6) :
    ContDiff ℝ ⊤ (realSlotFactor i) := by
  have hq : ContDiff ℝ ⊤
      (fun u : Fin 6 → ℝ => Real.exp (u i)) :=
    Real.contDiff_exp.comp (contDiff_apply ℝ ℝ i)
  have h2q : ContDiff ℝ ⊤
      (fun u : Fin 6 → ℝ => (2 : ℝ) * Real.exp (u i)) :=
    contDiff_const.mul hq
  unfold realSlotFactor
  exact (chosenRealChi_smooth.comp hq).sub
    (chosenRealChi_smooth.comp h2q)

private theorem realFullTrim_contDiff (s : ℝ) :
    ContDiff ℝ ⊤ (realFullTrim s) := by
  have hq : ContDiff ℝ ⊤
      (fun u : Fin 6 → ℝ =>
        s * Real.exp (originalGroupSum Finset.univ u)) :=
    contDiff_const.mul
      (Real.contDiff_exp.comp (realGroupSum_contDiff Finset.univ))
  unfold realFullTrim
  exact chosenRealEta_smooth.comp hq

/-- This smoothness concerns the precise chosen real HB geometry.
The group index remains Fin g, so equal groups retain multiplicity. -/
theorem realSixUnsplitWeight_contDiff {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) :
    ContDiff ℝ ⊤ (realSixUnsplitWeight c J s) := by
  have hG : ContDiff ℝ ⊤
      (fun u : Fin 6 → ℝ =>
        ∏ j : Fin g, realGroupFactor (c j) (J j) u) := by
    apply contDiff_prod
    intro j hj
    exact realGroupFactor_contDiff (c j) (J j)
  have hH : ContDiff ℝ ⊤
      (fun u : Fin 6 → ℝ =>
        ∏ i : Fin 6, realSlotFactor i u) := by
    apply contDiff_prod
    intro i hi
    exact realSlotFactor_contDiff i
  change ContDiff ℝ ⊤ (fun u : Fin 6 → ℝ =>
    ((∏ j : Fin g, realGroupFactor (c j) (J j) u) *
      realFullTrim s u) *
      (∏ i : Fin 6, realSlotFactor i u))
  exact (hG.mul (realFullTrim_contDiff s)).mul hH

/-- True coordinate deriv is the corresponding application of the
genuine Frechet derivative; the update derivative is the pinned
Mathlib hasDerivAt_update, not a formal jet or proxy. -/
private theorem realAxisDeriv_eq_fderiv
    (w : (Fin 6 → ℝ) → ℝ) (hw : Differentiable ℝ w)
    (i : Fin 6) (u : Fin 6 → ℝ) :
    realAxisDeriv w i u =
      (fderiv ℝ w u) (Pi.single i (1 : ℝ)) := by
  have hu : Function.update u i (u i) = u := by
    ext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  have hwAt : HasFDerivAt w (fderiv ℝ w u)
      (Function.update u i (u i)) := by
    simpa only [hu] using (hw u).hasFDerivAt
  have hchain :=
    hwAt.comp_hasDerivAt (u i) (hasDerivAt_update u i (u i))
  change deriv (fun t : ℝ => w (Function.update u i t)) (u i) =
    (fderiv ℝ w u) (Pi.single i (1 : ℝ))
  simpa only [Function.comp_def] using hchain.deriv

/-- Global smoothness survives one genuine repeated-coordinate real
derivative. No commutation of coordinate derivative orders is used. -/
private theorem realAxisDeriv_contDiff
    (w : (Fin 6 → ℝ) → ℝ) (hw : ContDiff ℝ ⊤ w)
    (i : Fin 6) : ContDiff ℝ ⊤ (realAxisDeriv w i) := by
  have hder : ContDiff ℝ ⊤
      (fun p : (Fin 6 → ℝ) × (Fin 6 → ℝ) =>
        (fderiv ℝ w p.1) p.2) :=
    hw.contDiff_fderiv_apply (m := ⊤) (by simp)
  have hdiag : ContDiff ℝ ⊤
      (fun u : Fin 6 → ℝ => (u, Pi.single i (1 : ℝ))) :=
    (contDiff_id : ContDiff ℝ ⊤ (fun u : Fin 6 → ℝ => u)).prodMk
      contDiff_const
  have happly : ContDiff ℝ ⊤
      (fun u : Fin 6 → ℝ =>
        (fderiv ℝ w u) (Pi.single i (1 : ℝ))) :=
    hder.comp hdiag
  have heq : realAxisDeriv w i =
      (fun u : Fin 6 → ℝ =>
        (fderiv ℝ w u) (Pi.single i (1 : ℝ))) := by
    funext u
    exact realAxisDeriv_eq_fderiv w (hw.differentiable (by simp)) i u
  rw [heq]
  exact happly

/-- Every literal ordered real-coordinate derivative is smooth; in
particular repeated coordinates have not been replaced by a set. -/
theorem realOrderedAxisDeriv_contDiff
    (w : (Fin 6 → ℝ) → ℝ) (hw : ContDiff ℝ ⊤ w) :
    ∀ word : List (Fin 6),
      ContDiff ℝ ⊤ (realOrderedAxisDeriv word w) := by
  intro word
  induction word with
  | nil =>
      simpa [realOrderedAxisDeriv] using hw
  | cons i rest ih =>
      change ContDiff ℝ ⊤
        (realAxisDeriv (realOrderedAxisDeriv rest w) i)
      exact realAxisDeriv_contDiff _ ih i

/-- Pay the previously explicit ordinary RealUnsplitSliceRegular from
the actual C-infinity group factors, six positional factors and unique
complete-product trim. No integrability or PP estimate is assumed. -/
theorem realUnsplitSliceRegular_of_chosen {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) : RealUnsplitSliceRegular c J s := by
  intro word u i
  have hword : ContDiff ℝ ⊤
      (realOrderedAxisDeriv word
        (realSixUnsplitWeight c J s)) :=
    realOrderedAxisDeriv_contDiff _ (realSixUnsplitWeight_contDiff c J s) word
  have hat : DifferentiableAt ℝ
      (realOrderedAxisDeriv word (realSixUnsplitWeight c J s))
      (Function.update u i (u i)) :=
    (hword.differentiable (by simp)).differentiableAt
  exact hat.comp (u i) (hasDerivAt_update u i (u i)).differentiableAt

/-- Remove the ordinary real-slice regularity premise from the actual
64 original doubled-word 2S L1 theorem. This is NOT all-source W_T,
growing-m uniformity or same-rho PP. -/
theorem realSixUnsplitMixedD_poly12_chosen :
    ∃ Cpoly : ℝ, 0 ≤ Cpoly ∧
      ∀ (g : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
          (∀ S : Finset (Fin 6), Integrable
            (fun u : Fin 6 → ℝ =>
              |realOrderedAxisDeriv (doubled S)
                (realSixUnsplitWeight c J s) u|)) ∧
          realSixUnsplitMixedD c J s ≤
            Cpoly * (((g : ℝ) + 1) ^ 12) := by
  obtain ⟨Cpoly, hCpoly, hbase⟩ :=
    realSixUnsplitMixedD_poly12_of_regular
  refine ⟨Cpoly, hCpoly, ?_⟩
  intro g c J hc s hs
  exact hbase g c J hc s hs (realUnsplitSliceRegular_of_chosen c J s)

end
end ImbalancedChen.P3HBUnsplitRealSliceSmooth
