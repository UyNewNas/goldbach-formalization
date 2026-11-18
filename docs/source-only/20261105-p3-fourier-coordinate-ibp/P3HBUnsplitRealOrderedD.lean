import ImbalancedChen.P3HBUnsplitRealProfile
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-!
P3.6 — frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product-completion §4 (F). SOURCE_ONLY / UNCOMPILED.

The preceding packet identified the literal chosen six-slot physical
coefficient as the complex embedding of a real coefficient, only in
order zero. This packet transports ALL actual ordered real-coordinate
`deriv` operators through that embedding. It then identifies the entire
64-word adjacent-doubled mixed L1 ledger, without changing the original
g occurrences, incidences or the one physical complete-product trim.

The transport explicitly assumes ordinary local differentiability of
the REAL intermediate derivatives, not an estimate of their integrals
or a Fourier/discrepancy claim. Discharging this regularity from the
chosen C-infinity factors and compiling all inherited SOURCE_ONLY
parents remain INTERNAL and OPEN. No full W_T or same-rho PP claim.
-/

namespace ImbalancedChen.P3HBUnsplitRealOrderedD
noncomputable section

open MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3HBCanonicalGeometryDerivative
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBUnsplitDirectRestoration
open ImbalancedChen.P3HBUnsplitChildSliceSmooth
open ImbalancedChen.P3HBUnsplitRealProfile
open ImbalancedChen.P3HBExplicitSmoothCutoffs
open ImbalancedChen.P3U5ChartMixedL1Budget

/-- Actual real-axis derivative on exactly the original six log coordinates. -/
def realAxisDeriv (w : (Fin 6 → ℝ) → ℝ)
    (i : Fin 6) (u : Fin 6 → ℝ) : ℝ :=
  deriv (fun t : ℝ => w (Function.update u i t)) (u i)

/-- Ordered axis derivatives; repeated axes are not removed or commuted. -/
def realOrderedAxisDeriv :
    List (Fin 6) → ((Fin 6 → ℝ) → ℝ) → ((Fin 6 → ℝ) → ℝ)
  | [], w => w
  | i :: rest, w => realAxisDeriv (realOrderedAxisDeriv rest w) i

/-- The pinned Mathlib `HasDerivAt.ofReal_comp` transports an ACTUAL
real derivative through the real-linear complex embedding. -/
theorem actualAxisDeriv_ofReal (w : (Fin 6 → ℝ) → ℝ)
    (u : Fin 6 → ℝ) (i : Fin 6)
    (hw : DifferentiableAt ℝ
      (fun t : ℝ => w (Function.update u i t)) (u i)) :
    actualAxisDeriv (fun v => (w v : ℂ)) i u =
      (realAxisDeriv w i u : ℂ) := by
  unfold actualAxisDeriv realAxisDeriv
  exact (hw.hasDerivAt.ofReal_comp).deriv

/-- True ordered derivative transport at EVERY word, conditional only on
ordinary real-slice differentiability of its predecessor word. -/
theorem originalOrderedAxisDeriv_ofReal
    (w : (Fin 6 → ℝ) → ℝ)
    (hregular : ∀ (word : List (Fin 6)) (u : Fin 6 → ℝ)
        (i : Fin 6), DifferentiableAt ℝ
          (fun t : ℝ => realOrderedAxisDeriv word w
            (Function.update u i t)) (u i)) :
    ∀ (word : List (Fin 6)) (u : Fin 6 → ℝ),
      originalOrderedAxisDeriv word (fun v => (w v : ℂ)) u =
        (realOrderedAxisDeriv word w u : ℂ) := by
  intro word
  induction word with
  | nil =>
      intro u
      rfl
  | cons i rest ih =>
      intro u
      have heq :
          originalOrderedAxisDeriv rest (fun v => (w v : ℂ)) =
            (fun v => (realOrderedAxisDeriv rest w v : ℂ)) := by
        funext v
        exact ih v
      change actualAxisDeriv
          (originalOrderedAxisDeriv rest (fun v => (w v : ℂ))) i u =
        (realAxisDeriv (realOrderedAxisDeriv rest w) i u : ℂ)
      rw [heq]
      exact actualAxisDeriv_ofReal
        (realOrderedAxisDeriv rest w) u i (hregular rest u i)

/-- Ordinary slice regularity of the actual REAL unsplit coefficient.
Not an integral/PP/Fourier estimate; its derivation from chosen cutoffs
is the next independent source-internal proof obligation. -/
def RealUnsplitSliceRegular {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ) : Prop :=
  ∀ (word : List (Fin 6)) (u : Fin 6 → ℝ) (i : Fin 6),
    DifferentiableAt ℝ
      (fun t : ℝ => realOrderedAxisDeriv word
        (realSixUnsplitWeight c J s) (Function.update u i t)) (u i)

/-- Transport the literal original physical UNSPLIT profile's *direct*
complex derivative into the genuine real iterated derivative. The same
original six positions, g-labelled occurrences, and scale s survive. -/
theorem chosen_originalOrdered_eq_real {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (hregular : RealUnsplitSliceRegular c J s)
    (word : List (Fin 6)) (u : Fin 6 → ℝ) :
    originalOrderedAxisDeriv word
      (originalSixUnsplitWeight chosenChi chosenEta c J s) u =
      (realOrderedAxisDeriv word (realSixUnsplitWeight c J s) u : ℂ) := by
  have heq :
      originalSixUnsplitWeight chosenChi chosenEta c J s =
        (fun v => (realSixUnsplitWeight c J s v : ℂ)) := by
    funext v
    exact unsplit_chosen_ofReal c J s v
  rw [heq]
  exact originalOrderedAxisDeriv_ofReal
    (realSixUnsplitWeight c J s) hregular word u

/-- The real actual ordered-derivative 2S ledger, not a proxy norm field. -/
def realSixUnsplitMixedD {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ) : ℝ :=
  ∑ S : Finset (Fin 6),
    ∫ u : Fin 6 → ℝ,
      |realOrderedAxisDeriv (doubled S) (realSixUnsplitWeight c J s) u|

/-- Exact equality of real 2S ledger and the prior complex ledger.
The norm identity is pointwise before integration, with no new factor. -/
theorem realSixUnsplitMixedD_eq_complex {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (hregular : RealUnsplitSliceRegular c J s) :
    realSixUnsplitMixedD c J s =
      sixUnsplitDirectMixedD chosenChi chosenEta c J s := by
  unfold realSixUnsplitMixedD sixUnsplitDirectMixedD
  apply Finset.sum_congr rfl
  intro S _
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => by
    rw [chosen_originalOrdered_eq_real c J s hregular (doubled S) u]
    simp only [Complex.norm_real, Real.norm_eq_abs])

/-- Six-slot physical REAL weight: conditional genuine 2S L1 bound
from the old complex original-group budget, NOT from an assumed D bound.
The one additional condition is differentiability of the actual real
intermediate slices, separately exposed rather than hidden as 'admitted'. -/
theorem realSixUnsplitMixedD_poly12_of_regular :
    ∃ Cpoly : ℝ, 0 ≤ Cpoly ∧
      ∀ (g : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s → RealUnsplitSliceRegular c J s →
          (∀ S : Finset (Fin 6), Integrable
            (fun u : Fin 6 → ℝ =>
              |realOrderedAxisDeriv (doubled S)
                (realSixUnsplitWeight c J s) u|)) ∧
          realSixUnsplitMixedD c J s ≤
            Cpoly * (((g : ℝ) + 1) ^ 12) := by
  classical
  obtain ⟨Cpoly, hCpoly, hbase⟩ :=
    sixUnsplitDirectMixedD_poly12_smooth chosenChi chosenEta
      chosenChi_smooth chosenEta_smooth
      chosenChi_left chosenChi_right chosenChi_dyadic_contraction
      chosenEta_left chosenEta_right
  refine ⟨Cpoly, hCpoly, ?_⟩
  intro g c J hc s hs hregular
  obtain ⟨hint, hbound⟩ := hbase g c J hc s hs
  have hnorm (S : Finset (Fin 6)) :
      (fun u : Fin 6 → ℝ =>
        |realOrderedAxisDeriv (doubled S)
          (realSixUnsplitWeight c J s) u|) =
      (fun u : Fin 6 → ℝ =>
        ‖originalOrderedAxisDeriv (doubled S)
          (originalSixUnsplitWeight chosenChi chosenEta c J s) u‖) := by
    funext u
    rw [chosen_originalOrdered_eq_real c J s hregular (doubled S) u]
    simp only [Complex.norm_real, Real.norm_eq_abs]
  refine ⟨?_, ?_⟩
  · intro S
    rw [hnorm S]
    exact hint S
  · rw [realSixUnsplitMixedD_eq_complex c J s hregular]
    exact hbound

end
end ImbalancedChen.P3HBUnsplitRealOrderedD
