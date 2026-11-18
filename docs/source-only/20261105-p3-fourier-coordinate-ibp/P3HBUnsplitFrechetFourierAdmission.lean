import ImbalancedChen.P3HBUnsplitRealCompactIntegrable
import ImbalancedChen.P3HBUnsplitRealFourierD
import ImbalancedChen.P3FourierCoordinateIBP
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.MeasureTheory.Integral.CompactlySupported

/-!
P3.6, frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§2,4 (F).

From the actual chosen six-position HB weight (all group occurrences,
original dyadic positions and ONE complete-product trim), discharge the
real and complex Fourier chart's C-infinity, compact support and EVERY
iterated Frechet derivative's integrability. No Fourier estimate is an
assumption. The final product numerator is the genuine Fourier transform
at the unchanged physical frequency, not a PP discrepancy conclusion.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBUnsplitFrechetFourierAdmission
noncomputable section

open MeasureTheory
open scoped Classical BigOperators FourierTransform RealInnerProductSpace
open ImbalancedChen.P3FourierDPointwise
open ImbalancedChen.P3FourierSubsetExpansion
open ImbalancedChen.P3FourierPointCoordinateBridge
open ImbalancedChen.P3FourierRealComplex
open ImbalancedChen.P3FourierCoordinateIBP
open ImbalancedChen.P3HBUnsplitRealProfile
open ImbalancedChen.P3HBUnsplitRealSliceSmooth
open ImbalancedChen.P3HBUnsplitRealCompactIntegrable
open ImbalancedChen.P3HBUnsplitRealFourierD

/-- Smoothness survives the ACTUAL Euclidean-to-Point linear equivalence. -/
theorem chosen_chartLift_contDiff {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ) :
    ContDiff ℝ ⊤ (chartLift (realSixUnsplitWeight c J s)) := by
  change ContDiff ℝ ⊤
    (realSixUnsplitWeight c J s ∘ chartEquiv 6)
  exact (realSixUnsplitWeight_contDiff c J s).comp
    (chartEquiv 6).contDiff

/-- Pull back the genuine closed-log-box compact support through the
original Fourier-space homeomorphism, with no guessed Jacobian. -/
theorem chosen_chartLift_hasCompactSupport {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ) :
    HasCompactSupport (chartLift (realSixUnsplitWeight c J s)) := by
  change HasCompactSupport
    (realSixUnsplitWeight c J s ∘ chartEquiv 6)
  exact (realSixUnsplitWeight_hasCompactSupport c J s).comp_homeomorph
    (chartEquiv 6).toHomeomorph

/-- The complexification is real-linear, not holomorphic. -/
theorem chosen_complexChartLift_contDiff {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ) :
    ContDiff ℝ ⊤ (complexChartLift (realSixUnsplitWeight c J s)) := by
  change ContDiff ℝ ⊤
    (Complex.ofRealCLM ∘ chartLift (realSixUnsplitWeight c J s))
  exact Complex.ofRealCLM.contDiff.comp
    (chosen_chartLift_contDiff c J s)

/-- The actual zero-preserving real-to-complex map does not enlarge
the support of the chosen original HB profile. -/
theorem chosen_complexChartLift_hasCompactSupport {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ) :
    HasCompactSupport (complexChartLift (realSixUnsplitWeight c J s)) := by
  change HasCompactSupport
    (Complex.ofRealCLM ∘ chartLift (realSixUnsplitWeight c J s))
  exact (chosen_chartLift_hasCompactSupport c J s).comp_left
    (map_zero Complex.ofRealCLM)

/-- Pay ALL genuine complex-valued iterated Frechet derivative integrals,
including k=0. Uses pinned HasCompactSupport.iteratedFDeriv, not a new
integrability hypothesis or a list of predeclared jet values. -/
theorem chosen_complexChartLift_iterated_integrable {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (k : ℕ) :
    Integrable (iteratedFDeriv ℝ k
      (complexChartLift (realSixUnsplitWeight c J s))) := by
  have hcont : Continuous (iteratedFDeriv ℝ k
      (complexChartLift (realSixUnsplitWeight c J s))) :=
    (chosen_complexChartLift_contDiff c J s).continuous_iteratedFDeriv
      (by simp)
  have hc : HasCompactSupport (iteratedFDeriv ℝ k
      (complexChartLift (realSixUnsplitWeight c J s))) :=
    (chosen_complexChartLift_hasCompactSupport c J s).iteratedFDeriv k
  exact hcont.integrable_of_hasCompactSupport hc

/-- The full 64-word CoordinateFourierIBP premise is now a theorem
candidate for the fixed-six original source, not a postulated interface. -/
theorem chosen_original_six_coordinate_fourierIBP {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (eta : FourierSpace 6) :
    CoordinateFourierIBP 6
      (actualMixedFamily (realSixUnsplitWeight c J s)) eta := by
  exact actual_coordinate_fourierIBP (realSixUnsplitWeight c J s)
    (fun S => (chosen_chartLift_contDiff c J s).of_le (by simp))
    (fun S k hk => chosen_complexChartLift_iterated_integrable c J s k)
    eta

/-- Exact physical Fourier denominator, at the unchanged eta, paid by
the original actual 2S derivatives rather than by a Fourier premise. -/
theorem chosen_original_six_physical_product_bound {g : ℕ}
    (c : Fin g → ℝ) (J : Fin g → Finset (Fin 6)) (s : ℝ)
    (eta : FourierSpace 6) :
    physicalDenom (physicalFrequency (fun i => eta i)) *
      ‖𝓕 (actualMixedFamily (realSixUnsplitWeight c J s) ∅) eta‖ ≤
    derivativeD 6 (actualMixedFamily (realSixUnsplitWeight c J s)) := by
  exact actual_chart_D_pointwise (realSixUnsplitWeight c J s) eta
    (chosen_original_six_coordinate_fourierIBP c J s eta)

/-- Quantifier-order-preserving fixed-six Fourier pointwise budget:
Cpoly is chosen before g, source labels, original physical scales and eta.
NOT a T,m(T)-uniform all-W_T estimate or a same-rho PP estimate. -/
theorem exists_chosen_original_six_physical_fourier_poly12 :
    ∃ Cpoly : ℝ, 0 ≤ Cpoly ∧
      ∀ (g : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
          ∀ eta : FourierSpace 6,
            physicalDenom (physicalFrequency (fun i => eta i)) *
              ‖𝓕 (actualMixedFamily (realSixUnsplitWeight c J s) ∅) eta‖ ≤
                Cpoly * (((g : ℝ) + 1) ^ 12) := by
  obtain ⟨Cpoly, hCpoly, hD⟩ :=
    exists_chosen_original_six_fourierD_poly12
  refine ⟨Cpoly, hCpoly, ?_⟩
  intro g c J hc s hs eta
  obtain ⟨_, hbound⟩ := hD g c J hc s hs
  exact (chosen_original_six_physical_product_bound c J s eta).trans
    hbound

end
end ImbalancedChen.P3HBUnsplitFrechetFourierAdmission
