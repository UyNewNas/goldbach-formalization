import ImbalancedChen.P3HBUnsplitRealSliceSmooth
import ImbalancedChen.P3FourierPhysicalMeasureD
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Tactic

/-!
P3.6, manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §4 (F).

The previous actual REAL six-position derivative uses Function.update at
the base coordinate; the frozen Fourier Point chart instead differentiates
a coordinate shift at zero. Prove the two are the SAME derivative using
their actual HasFDerivAt/HasDerivAt identities, then identify the entire
64-word original Fourier derivativeD with the previously budgeted real L1.

No Fourier transform bound or modulus discrepancy is postulated.
This is the fixed-six-position geometric profile only, NOT the entire
frozen W_T family and NOT a same-rho PP conclusion.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBUnsplitRealFourierD
noncomputable section

open MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3AffineTransitionJets
open ImbalancedChen.P3U5ChartMixedL1Budget
open ImbalancedChen.P3FourierDPointwise
open ImbalancedChen.P3FourierPointCoordinateBridge
open ImbalancedChen.P3FourierPhysicalMeasureD
open ImbalancedChen.P3HBUnsplitRealProfile
open ImbalancedChen.P3HBUnsplitRealOrderedD
open ImbalancedChen.P3HBUnsplitRealSliceSmooth

/-- The true derivative at an updated coordinate and the derivative
of the original zero-based Point shift are exactly equal. Neither is
a formal jet: both sides are Mathlib's actual `deriv`. -/
theorem realAxisDeriv_eq_coordinateDeriv
    (w : (Fin 6 → ℝ) → ℝ) (hw : Differentiable ℝ w)
    (i : Fin 6) (u : Fin 6 → ℝ) :
    realAxisDeriv w i u = coordinateDeriv i w u := by
  have hu : Function.update u i (u i) = u := by
    ext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  have hwAt : HasFDerivAt w (fderiv ℝ w u)
      (Function.update u i (u i)) := by
    simpa only [hu] using (hw u).hasFDerivAt
  have hupdate : realAxisDeriv w i u =
      (fderiv ℝ w u) (Pi.single i (1 : ℝ)) := by
    have hcomp := hwAt.comp_hasDerivAt (u i)
      (hasDerivAt_update u i (u i))
    change deriv (fun t : ℝ =>
      w (Function.update u i t)) (u i) =
        (fderiv ℝ w u) (Pi.single i (1 : ℝ))
    simpa only [Function.comp_def] using hcomp.deriv
  have hline :
      (fun t : ℝ => w (shift u i t)) =
        (fun t : ℝ => w (u + t • Pi.single i (1 : ℝ))) := by
    funext t
    rw [shift_eq_add_direction]
    rfl
  have hdir : HasDerivAt
      (fun t : ℝ => u + t • Pi.single i (1 : ℝ))
      (Pi.single i (1 : ℝ)) 0 := by
    simpa using
      ((hasDerivAt_id (0 : ℝ)).smul_const
        (Pi.single i (1 : ℝ))).const_add u
  have hshift : coordinateDeriv i w u =
      (fderiv ℝ w u) (Pi.single i (1 : ℝ)) := by
    unfold coordinateDeriv
    rw [hline]
    exact ((hw u).hasFDerivAt.comp_hasDerivAt 0 hdir).deriv
  exact hupdate.trans hshift.symm

/-- Every ORIGINAL ordered shift derivative equals the chosen real
update derivative. This keeps all repeated coordinate indices and
their literal order, with no permutation and no regularity field. -/
theorem mixed_eq_realOrdered_of_contDiff
    (w : (Fin 6 → ℝ) → ℝ) (hw : ContDiff ℝ ⊤ w) :
    ∀ word : List (Fin 6),
      mixed word w = realOrderedAxisDeriv word w := by
  intro word
  induction word with
  | nil =>
      rfl
  | cons i rest ih =>
      change coordinateDeriv i (mixed rest w) =
        realAxisDeriv (realOrderedAxisDeriv rest w) i
      rw [ih]
      funext u
      exact (realAxisDeriv_eq_coordinateDeriv
        (realOrderedAxisDeriv rest w)
        ((realOrderedAxisDeriv_contDiff w hw rest).differentiable (by simp))
        i u).symm

/-- Apply the exact shift/update bridge to the original six-position
group-product × one full-product trim × six positional factors. -/
theorem chosen_real_mixed_eq_ordered {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (word : List (Fin 6)) :
    mixed word (realSixUnsplitWeight c J s) =
      realOrderedAxisDeriv word (realSixUnsplitWeight c J s) := by
  exact mixed_eq_realOrdered_of_contDiff _
    (realSixUnsplitWeight_contDiff c J s) word

/-- The true original Point 6 D ledger is exactly the previously
proved-in-source 64-word real ordered-derivative ledger. -/
theorem realSixUnsplitMixedD_eq_pointD {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ) :
    realSixUnsplitMixedD c J s =
      ∑ S : Finset (Fin 6),
        ∫ p : Point 6,
          |mixed (doubled S) (realSixUnsplitWeight c J s) p| := by
  unfold realSixUnsplitMixedD
  apply Finset.sum_congr rfl
  intro S _
  rw [chosen_real_mixed_eq_ordered c J s (doubled S)]

/-- The actual Fourier Euclidean derivativeD (with the unchanged
measure-preserving chart) equals that same real six-slot ledger.
This is a numerator equality, NOT a Fourier tail or PP estimate. -/
theorem realSixUnsplitMixedD_eq_actualFourierD {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ) :
    realSixUnsplitMixedD c J s =
      derivativeD 6 (actualMixedFamily (realSixUnsplitWeight c J s)) := by
  calc
    realSixUnsplitMixedD c J s =
        ∑ S : Finset (Fin 6),
          ∫ p : Point 6,
            |mixed (doubled S) (realSixUnsplitWeight c J s) p| :=
      realSixUnsplitMixedD_eq_pointD c J s
    _ = derivativeD 6 (actualMixedFamily (realSixUnsplitWeight c J s)) :=
      (actual_derivativeD_eq_pointD (realSixUnsplitWeight c J s)).symm

/-- The original real six-position geometric source's ACTUAL
Fourier derivativeD has the inherited polynomial budget, while
all 64 actual Point-coordinate L1 norms are integrable.
The complete W_T admission and growing m(T) remain open. -/
theorem exists_chosen_original_six_fourierD_poly12 :
    ∃ Cpoly : ℝ, 0 ≤ Cpoly ∧
      ∀ (g : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
          (∀ S : Finset (Fin 6),
            Integrable (fun p : Point 6 =>
              |mixed (doubled S) (realSixUnsplitWeight c J s) p|)) ∧
          derivativeD 6 (actualMixedFamily
            (realSixUnsplitWeight c J s)) ≤
            Cpoly * (((g : ℝ) + 1) ^ 12) := by
  obtain ⟨Cpoly, hC, hbase⟩ := realSixUnsplitMixedD_poly12_chosen
  refine ⟨Cpoly, hC, ?_⟩
  intro g c J hc s hs
  obtain ⟨hints, hD⟩ := hbase g c J hc s hs
  constructor
  · intro S
    rw [chosen_real_mixed_eq_ordered c J s (doubled S)]
    exact hints S
  · rw [← realSixUnsplitMixedD_eq_actualFourierD c J s]
    exact hD

end
end ImbalancedChen.P3HBUnsplitRealFourierD
