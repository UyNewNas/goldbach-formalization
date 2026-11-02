import ImbalancedChen.P5OriginalU9MidpointIntegral
import ImbalancedChen.P5OriginalU9UpperOnlyStrictSlot
import Mathlib.Data.Rat.Cast.Order

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

The closed finite proof below is deliberately UNEVALUATED.  Its proposition
is the actual K midpointUpper, at 64 log-series terms and the original 1024
panels, compared directly with the original savedU9/K0 rational.  No finite
comparison, saved total, containment predicate, integral endpoint or
historical Q80 output identity is an argument.  No arithmetic was run in
writing this file; elaboration, kernel reduction and resource feasibility
remain for the user.  In particular `by decide` is not `native_decide`.

The analytic rule is imported unchanged from K.  It uses the actual signed
curvature, the directed log remainder and the full original ordered domain.
The saved independent Simpson lower slope remains untouched.
-/

namespace ImbalancedChen.P5OriginalU9SavedMidpointEndpoint

noncomputable section
open MeasureTheory
open scoped BigOperators
open P5OriginalCoefficientArithmetic P5OriginalU9MidpointIntegral
open Certificates.P2DirectedLogRounding

/-- Literal original upper COST divided by the original producer's K0. -/
def originalSavedIntegralQ : ℚ :=
  (3937512077512215599969887 / 1208925819614629174706176) / (67619 / 10000)

/-- CLOSED FINITE PROOFTERM, UNEVALUATED.  This exact comparison has no
premises.  Neither successful evaluation nor feasible resources are claimed. -/
theorem midpointUpper64_1024_le_original_saved :
    midpointUpper 64 1024 ≤ originalSavedIntegralQ := by
  -- A single outward rounding AFTER each existing exact K panel keeps
  -- the finite aggregate dyadic.  This is only an arithmetic majorant
  -- inside this proof; the analytic quadrature and theorem target are K's.
  have hround : midpointUpper 64 1024 ≤
      ∑ k ∈ Finset.range 1024,
        roundUp 96 (midpointCellUpper 64
          (P2U9DirectedRationalCover.mesh 1024 k)
          (P2U9DirectedRationalCover.mesh 1024 (k+1))) := by
    unfold midpointUpper
    exact Finset.sum_le_sum (fun k _ => le_roundUp 96 _)
  have hfinite :
      (∑ k ∈ Finset.range 1024,
        roundUp 96 (midpointCellUpper 64
          (P2U9DirectedRationalCover.mesh 1024 k)
          (P2U9DirectedRationalCover.mesh 1024 (k+1)))) ≤
        originalSavedIntegralQ := by
    decide
  exact hround.trans hfinite

/-- Bind the rational comparison to the original named real endpoint. -/
theorem originalSavedIntegralQ_cast :
    (originalSavedIntegralQ : ℝ) = p5z_originalU9UpperIntegralEndpoint := by
  rw [p5z_originalU9UpperIntegralEndpoint_exact]
  simp only [originalSavedIntegralQ, Rat.cast_div, Rat.cast_ofNat]

/-- The original J endpoint; all analytic assumptions are discharged by
K's actual curvature/log construction, not added to this theorem. -/
theorem originalU9_saved_upper_integral :
    currentChenUpsilon9HarmonicIntegral ≤ p5z_originalU9UpperIntegralEndpoint := by
  have hrat : (midpointUpper 64 1024 : ℝ) ≤ (originalSavedIntegralQ : ℝ) :=
    Rat.cast_mono midpointUpper64_1024_le_original_saved
  rw [originalSavedIntegralQ_cast] at hrat
  exact (original_1024_midpoint_enclosure 64).2.trans hrat

/-- The same endpoint on the COMPLETE original ordered three-exponent
domain, with the original squared terminal kernel. -/
theorem originalU9_ordered_domain_saved_upper :
    (∫ x in P5U9RealDomain.domain, P5U9RealDomain.squaredTerminalKernel x) ≤
      p5z_originalU9UpperIntegralEndpoint := by
  rw [P5U9RealDomain.squaredTerminalKernel_integral_eq_originalJ]
  exact originalU9_saved_upper_integral

/-- Consume K's upper-only strict-slot reduction.  The original envelope
and its original independent lower Simpson slope are preserved. -/
theorem originalU9_fixed_density_envelope :
    fixedProductDensityCoefficient * currentChenUpsilon9HarmonicIntegral ≤
      U9Envelope fixedProductDensityCoefficient :=
  originalU9_envelope_of_upper_only originalU9_saved_upper_integral

end
end ImbalancedChen.P5OriginalU9SavedMidpointEndpoint

namespace ImbalancedChen.P5OriginalCoefficientArithmetic

noncomputable section
open Filter P5OriginalU9RepeatedPP P5OriginalU9SavedMidpointEndpoint

/-- The original h9 supplier with its independent upper-integral port
supplied by the closed midpoint proof above.  The SAME nu/r/e, attached
moduli and physical rho occur in scope, density and all THREE strict
coordinate PP estimates.  Those arithmetic hypotheses remain explicit. -/
theorem original_h9_of_saved_midpoint_strict_actual_rho
    (nu r e scopeNu : ℝ) (hnu : 0 < nu) (he : 0 < e) (he8 : e < 1/8)
    (heR : e^2 ≤ r) (hnur : nu*r < 1) (hscopeNu : 0 ≤ scopeNu)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (Licensed : ℕ → Prop)
    (hlicensed : ∀ᶠ N : ℕ in atTop, Even N → Licensed N)
    (hcap : ∀ᶠ N : ℕ in atTop, Even N → Licensed N → (N:ℝ)^(nu*r) ≤ (cap N:ℝ))
    (hscope : ∀ᶠ N : ℕ in atTop, Even N → Licensed N → ∀ d : ℕ,
      d ∈ attachedUpperModuli nu r e retain cap N →
      attachedUpperCoefficient nu r e retain cap N d ≠ 0 → (d:ℝ) ≤ (N:ℝ)^scopeNu)
    (hdensity : ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      physicalDensitySum (attachedUpperModuli nu r e retain cap N)
        (attachedUpperCoefficient nu r e retain cap N) ≤
          fixedProductDensityCoefficient*(singularSeries N/Real.log (N:ℝ)))
    (hstrict : ∀ j : Fin 3, ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      Even N → Licensed N →
        |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e retain cap N)
          (attachedUpperCoefficient nu r e retain cap N) (strictWeight j N)| ≤
            C*(N:ℝ)/Real.log (N:ℝ)^3) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon9 N ≤
        (U9Envelope fixedProductDensityCoefficient+delta)*singularNormalization N := by
  exact original_h9_of_upper_only_strict_actual_rho nu r e scopeNu hnu he he8 heR hnur
    hscopeNu retain cap Licensed originalU9_saved_upper_integral
    hlicensed hcap hscope hdensity hstrict

end
end ImbalancedChen.P5OriginalCoefficientArithmetic
