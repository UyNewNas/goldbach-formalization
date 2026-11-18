import ImbalancedChen.P3HBUnsplitRealSupport
import ImbalancedChen.P3HBUnsplitRealFourierD
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

/-!
P3.6, frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
distribution-prime-product-completion §2 and §4 (F).

Manuscript-internal source: from the actual chosen six-position dyadic
support and C-infinity of the occurrence-indexed HB product with its
ONE complete physical-product trim, obtain a genuinely compact support
and integrability of EVERY ordered real-coordinate derivative (in
particular the 64 literal adjacent-doubled 2S Fourier derivatives).

The compact closed log box is NOT the previous strict open support
window: closure may meet the endpoints. Neither a target Fourier
estimate nor an integrability hypothesis is introduced.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBUnsplitRealCompactIntegrable
noncomputable section

open Set MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3HBUnsplitRealProfile
open ImbalancedChen.P3HBUnsplitRealOrderedD
open ImbalancedChen.P3HBUnsplitRealSliceSmooth
open ImbalancedChen.P3HBUnsplitRealFourierD
open ImbalancedChen.P3HBUnsplitRealSupport
open ImbalancedChen.P3U5ChartMixedL1Budget

/-- The CLOSED log box containing the topological support.
It is distinct from the strict open positional window. -/
def sixClosedLogBox : Set (Fin 6 → ℝ) :=
  {u | ∀ i : Fin 6,
    u i ∈ Set.Icc (Real.log (1 / 2 : ℝ)) (Real.log (2 : ℝ))}

/-- A genuine compact product of six real compact intervals. -/
theorem sixClosedLogBox_isCompact : IsCompact sixClosedLogBox := by
  change IsCompact
    {u : Fin 6 → ℝ | ∀ i : Fin 6,
      u i ∈ Set.Icc (Real.log (1 / 2 : ℝ)) (Real.log (2 : ℝ))}
  exact isCompact_pi_infinite (fun _ : Fin 6 => isCompact_Icc)

/-- Both strict dyadic endpoints are paid BEFORE closure:
the nonzero original weight lies in the closed log box. -/
theorem realSixUnsplitWeight_support_subset_closedBox {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) :
    Function.support (realSixUnsplitWeight c J s) ⊆
      sixClosedLogBox := by
  intro u hu
  change ∀ i : Fin 6,
    u i ∈ Set.Icc (Real.log (1 / 2 : ℝ)) (Real.log (2 : ℝ))
  intro i
  obtain ⟨hlo, hhi⟩ :=
    realSixUnsplitWeight_nonzero_axis_bounds c J s u hu i
  have helo : (1 / 2 : ℝ) ≤ Real.exp (u i) := by
    linarith
  constructor
  · calc
      Real.log (1 / 2 : ℝ) ≤ Real.log (Real.exp (u i)) :=
        Real.log_le_log (by norm_num) helo
      _ = u i := Real.log_exp _
  · calc
      u i = Real.log (Real.exp (u i)) := (Real.log_exp _).symm
      _ ≤ Real.log (2 : ℝ) :=
        Real.log_le_log (Real.exp_pos _) (le_of_lt hhi)

/-- Topological support may include boundary points, and is compact
because its closed hull is contained in the genuine compact box. -/
theorem realSixUnsplitWeight_hasCompactSupport {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) :
    HasCompactSupport (realSixUnsplitWeight c J s) := by
  change IsCompact (tsupport (realSixUnsplitWeight c J s))
  apply sixClosedLogBox_isCompact.of_isClosed_subset
    (isClosed_tsupport _)
  exact closure_minimal
    (realSixUnsplitWeight_support_subset_closedBox c J s)
    sixClosedLogBox_isCompact.isClosed

/-- Pinned Mathlib's update derivative is the actual Fréchet
derivative applied to the coordinate basis vector. This lemma is
independent of any target integrated estimate. -/
private theorem realAxisDeriv_eq_fderiv_apply
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
  have hchain := hwAt.comp_hasDerivAt (u i)
    (hasDerivAt_update u i (u i))
  change deriv (fun t : ℝ => w (Function.update u i t)) (u i) =
    (fderiv ℝ w u) (Pi.single i (1 : ℝ))
  simpa only [Function.comp_def] using hchain.deriv

/-- Exact ordered derivatives remain compactly supported, including
all repeated coordinates. No derivative-word commutation is used.
The pinned HasCompactSupport.fderiv_apply avoids assuming a derivative
support class or a Fourier-integrability hypothesis. -/
theorem realOrderedAxisDeriv_hasCompactSupport
    (w : (Fin 6 → ℝ) → ℝ)
    (hw : ContDiff ℝ ⊤ w) (hc : HasCompactSupport w) :
    ∀ word : List (Fin 6),
      HasCompactSupport (realOrderedAxisDeriv word w) := by
  intro word
  induction word with
  | nil =>
      simpa [realOrderedAxisDeriv] using hc
  | cons i rest ih =>
      have hdiff : Differentiable ℝ
          (realOrderedAxisDeriv rest w) :=
        (realOrderedAxisDeriv_contDiff w hw rest).differentiable
          (by simp)
      have heq : realAxisDeriv (realOrderedAxisDeriv rest w) i =
          (fun u => (fderiv ℝ (realOrderedAxisDeriv rest w) u)
            (Pi.single i (1 : ℝ))) := by
        funext u
        exact realAxisDeriv_eq_fderiv_apply _ hdiff i u
      change HasCompactSupport
        (realAxisDeriv (realOrderedAxisDeriv rest w) i)
      rw [heq]
      exact ih.fderiv_apply ℝ (Pi.single i (1 : ℝ))

/-- The actual original real source and ALL its finite ordered
axis derivatives are compactly supported, without a new geometric
field or an assumed integral bound. -/
theorem chosen_real_ordered_hasCompactSupport {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) (word : List (Fin 6)) :
    HasCompactSupport
      (realOrderedAxisDeriv word (realSixUnsplitWeight c J s)) := by
  exact realOrderedAxisDeriv_hasCompactSupport _
    (realSixUnsplitWeight_contDiff c J s)
    (realSixUnsplitWeight_hasCompactSupport c J s) word

/-- Real finite-order derivatives: TRUE Lebesgue integrability
from actual continuity and compact support, not a Fourier premise. -/
theorem chosen_real_ordered_integrable {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) (word : List (Fin 6)) :
    Integrable (realOrderedAxisDeriv word
      (realSixUnsplitWeight c J s)) := by
  have hcont : Continuous (realOrderedAxisDeriv word
      (realSixUnsplitWeight c J s)) :=
    (realOrderedAxisDeriv_contDiff _
      (realSixUnsplitWeight_contDiff c J s) word).continuous
  exact hcont.integrable_of_hasCompactSupport
    (chosen_real_ordered_hasCompactSupport c J s word)

/-- All 64 TRUE doubled-coordinate Fourier L1 integrability
obligations for the fixed original six-position smooth source.
This proves integrability, NOT the quantitative polynomial D bound
and NOT admissibility of all actual frozen W_T families. -/
theorem chosen_original_six_doubled_integrable {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6))
    (s : ℝ) :
    ∀ S : Finset (Fin 6),
      Integrable (fun u : Fin 6 → ℝ =>
        |mixed (doubled S) (realSixUnsplitWeight c J s) u|) := by
  intro S
  have hi := (chosen_real_ordered_integrable c J s (doubled S)).norm
  simpa only [chosen_real_mixed_eq_ordered c J s (doubled S),
    Real.norm_eq_abs] using hi

end
end ImbalancedChen.P3HBUnsplitRealCompactIntegrable
