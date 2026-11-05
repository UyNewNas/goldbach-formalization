import ImbalancedChen.P3FourierSubsetExpansion
import Mathlib.Analysis.Fourier.FourierTransform
import ImbalancedChen.P3U5ChartMixedL1Budget

/-!
P3.6 / MANUSCRIPT INTERNAL / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.

A concrete FOURIER D-ledger bridge using the real Mathlib transform on
EuclideanSpace R (Fin d). All terms in D are genuinely integrals of functions
being Fourier transformed. The only unproved analytic *input* to this
intermediate bridge is the coordinatewise integration-by-parts identity
'hcoord': the signed Fourier transform of the *actual* 2S mixed derivative
equals the corresponding physical frequency monomial times the Fourier
transform of the zeroth derivative. The manuscript itself requires this
identity, and it must be discharged for originalWD's actual mixed functions.

No Fourier product majorant, Fourier L1 bound, asymptotic PP estimate,
arithmetic modulus sum, shifted-divisor moment, or external analytic estimate
is assumed here. The bridge is NOT a proof of the whole formula (F).
-/

namespace ImbalancedChen.P3FourierDPointwise
noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform RealInnerProductSpace
open P3FourierSubsetExpansion

abbrev FourierSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The actual finite sum of L1 norms of the separate doubled-coordinate
 derivative functions. No desired Fourier norm occurs in this definition. -/
def derivativeD (d : ℕ)
    (derivative : Finset (Fin d) → FourierSpace d → ℂ) : ℝ :=
  ∑ S : Finset (Fin d), ∫ x, ‖derivative S x‖

/-- Genuine norm domination of the pinned, multivariate Mathlib Fourier
 transform by the L1 norm of the function itself. -/
theorem fourier_norm_le_L1 {d : ℕ} (f : FourierSpace d → ℂ)
    (eta : FourierSpace d) :
    ‖𝓕 f eta‖ ≤ ∫ x, ‖f x‖ := by
  rw [Real.fourier_eq]
  calc
    ‖∫ x, (𝐞 (-⟪x, eta⟫)) • f x‖
      ≤ ∫ x, ‖(𝐞 (-⟪x, eta⟫)) • f x‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ := by simp_rw [Circle.norm_smul]

/-- The ACTUAL ordered 2S mixed derivative in the older Point d chart,
viewed on the Fourier domain. The coordinatewise double derivative remains
literal: we have not replaced it by an abstract radial or Laplacian bound. -/
def actualMixedFamily {d : ℕ}
    (w : P3AffineTransitionJets.Point d → ℝ)
    (S : Finset (Fin d)) : FourierSpace d → ℂ :=
  fun x => ((P3AffineTransitionJets.mixed
    (P3U5ChartMixedL1Budget.doubled S) w (fun i => x i) : ℝ) : ℂ)

/-- The one remaining analytic identity for THIS finite-algebra bridge.
The equality is not postulated as a new axiom: it is an explicit hypothesis
in the interim theorem. Its proof is a separate manuscript-internal
coordinatewise Fourier integration-by-parts task. In particular this is NOT
an assumed majorant for the whole Fourier transform. -/
def CoordinateFourierIBP (d : ℕ)
    (derivative : Finset (Fin d) → FourierSpace d → ℂ)
    (eta : FourierSpace d) : Prop :=
  ∀ S : Finset (Fin d),
    (-1 : ℂ) ^ S.card * 𝓕 (derivative S) eta =
      complexMonomial S (physicalFrequency (fun i => eta i)) *
        𝓕 (derivative ∅) eta

/-- Real multiple-coordinate algebra: sum every signed derivative Fourier
 transform, with no missing binomial multiplicity, and obtain the FULL
 product denominator. Works for d=0 and repeated coordinates (2S). -/
theorem signed_derivative_fourier_sum (d : ℕ)
    (derivative : Finset (Fin d) → FourierSpace d → ℂ)
    (eta : FourierSpace d)
    (hcoord : CoordinateFourierIBP d derivative eta) :
    complexDenom (physicalFrequency (fun i => eta i)) *
        𝓕 (derivative ∅) eta =
      ∑ S : Finset (Fin d), (-1 : ℂ) ^ S.card *
        𝓕 (derivative S) eta := by
  classical
  let xi : Fin d → ℝ := physicalFrequency (fun i => eta i)
  calc
    complexDenom xi * 𝓕 (derivative ∅) eta =
        (∑ S : Finset (Fin d), complexMonomial S xi) *
          𝓕 (derivative ∅) eta := by
            rw [complexDenom_eq_subset_sum]
    _ = ∑ S : Finset (Fin d),
        complexMonomial S xi * 𝓕 (derivative ∅) eta := by
          rw [Finset.sum_mul]
    _ = ∑ S : Finset (Fin d), (-1 : ℂ) ^ S.card *
        𝓕 (derivative S) eta := by
          apply Finset.sum_congr rfl
          intro S hS
          exact (hcoord S).symm

/-- The true frequency-product numerator D is paid by the integrals of
 the derivatives, not inserted as a Fourier decay premise. -/
theorem physical_product_fourier_bound (d : ℕ)
    (derivative : Finset (Fin d) → FourierSpace d → ℂ)
    (eta : FourierSpace d)
    (hcoord : CoordinateFourierIBP d derivative eta) :
    physicalDenom (physicalFrequency (fun i => eta i)) *
      ‖𝓕 (derivative ∅) eta‖ ≤ derivativeD d derivative := by
  classical
  let xi : Fin d → ℝ := physicalFrequency (fun i => eta i)
  have hsum := signed_derivative_fourier_sum d derivative eta hcoord
  calc
    physicalDenom xi * ‖𝓕 (derivative ∅) eta‖ =
        ‖complexDenom xi * 𝓕 (derivative ∅) eta‖ := by
          rw [norm_mul, norm_complexDenom]
    _ = ‖∑ S : Finset (Fin d), (-1 : ℂ) ^ S.card *
          𝓕 (derivative S) eta‖ := by rw [hsum]
    _ ≤ ∑ S : Finset (Fin d),
        ‖(-1 : ℂ) ^ S.card * 𝓕 (derivative S) eta‖ :=
          norm_sum_le _ _
    _ = ∑ S : Finset (Fin d), ‖𝓕 (derivative S) eta‖ := by
          apply Finset.sum_congr rfl
          intro S hS
          simp [norm_mul]
    _ ≤ ∑ S : Finset (Fin d), ∫ x, ‖derivative S x‖ :=
          Finset.sum_le_sum (fun S hS => fourier_norm_le_L1 (derivative S) eta)
    _ = derivativeD d derivative := rfl

/-- Physical manuscript-frequency version, with the full denominator
 rather than a spurious Euclidean radial decay. The remaining task is
 to realize 'derivative S' as the actual mixed (doubled S) derivative. -/
theorem physical_product_decay (d : ℕ)
    (derivative : Finset (Fin d) → FourierSpace d → ℂ)
    (eta : FourierSpace d)
    (hcoord : CoordinateFourierIBP d derivative eta) :
    ‖𝓕 (derivative ∅) eta‖ ≤
      derivativeD d derivative /
      physicalDenom (physicalFrequency (fun i => eta i)) := by
  apply (le_div_iff₀ (physicalDenom_pos _)).2
  simpa only [mul_comm] using
    physical_product_fourier_bound d derivative eta hcoord

/-- SOURCE-ONLY specialization to the genuine older mixed derivative
expression. The coordinatewise Fourier identity is an OPEN manuscript-internal
obligation, not a theorem proven by this specialization. Additionally the
EuclideanSpace/Pi Haar-measure identification is still needed to identify
this integral ledger with the already defined originalWD. -/
theorem actual_chart_D_pointwise {d : ℕ}
    (w : P3AffineTransitionJets.Point d → ℝ)
    (eta : FourierSpace d)
    (hcoord : CoordinateFourierIBP d (actualMixedFamily w) eta) :
    physicalDenom (physicalFrequency (fun i => eta i)) *
      ‖𝓕 (actualMixedFamily w ∅) eta‖ ≤
      derivativeD d (actualMixedFamily w) := by
  exact physical_product_fourier_bound d (actualMixedFamily w) eta hcoord

end
end ImbalancedChen.P3FourierDPointwise
