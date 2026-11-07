import ImbalancedChen.Part3KProfileDerivativePolynomials
import ImbalancedChen.Part3KProfilePolynomialDecay
import ImbalancedChen.Part3ActualKProfileLp
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
SOURCEONLY, 2026-10-24. UNCOMPILED; no acceptance credit.

The actual full-line Laplace profile `exp (-q * cosh u)` is Schwartz for
`q > 0`.  The derivative identity and every polynomially weighted bound
come from the two preceding physical-profile modules.  The final
complex-valued function is exactly `evenLaplaceProfile`, so the Fourier
chain can use its already established L1/L2 and K-integral bridges.
-/

namespace ImbalancedChen.Part3.KProfileSchwartzSourceOnly

noncomputable section

open ImbalancedChen.Part3.KProfileDerivativePolynomialsSourceOnly
open ImbalancedChen.Part3.KProfilePolynomialDecayP3SourceOnly
open ImbalancedChen.Part3.P3ActualKProfileLpSourceOnly

/-- The actual real Laplace profile, as a Schwartz function. -/
def realProfileSchwartz {q : ℝ} (hq : 0 < q) : SchwartzMap ℝ ℝ := by
  refine ⟨profile q, profile_contDiff q, ?_⟩
  intro k n
  obtain ⟨C, _hC, hC⟩ :=
    profile_polynomial_weighted_norm_decay hq (A q n) (B q n) k
  refine ⟨C, ?_⟩
  intro u
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_profile_eq, jetValue, profile] using hC u

@[simp]
theorem realProfileSchwartz_apply {q : ℝ} (hq : 0 < q) (u : ℝ) :
    realProfileSchwartz hq u = Real.exp (-q * Real.cosh u) := by
  rfl

/-- Complexification through the fixed real-linear isometric inclusion. -/
def complexProfileSchwartz {q : ℝ} (hq : 0 < q) : SchwartzMap ℝ ℂ :=
  SchwartzMap.postcompCLM Complex.ofRealCLM (realProfileSchwartz hq)

@[simp]
theorem complexProfileSchwartz_apply {q : ℝ} (hq : 0 < q) (u : ℝ) :
    complexProfileSchwartz hq u = evenLaplaceProfile q u := by
  simp only [complexProfileSchwartz, SchwartzMap.postcompCLM_apply,
    realProfileSchwartz_apply, Complex.ofRealCLM_apply, evenLaplaceProfile]

/-- The Fourier-facing form states literal equality with the existing profile. -/
theorem evenLaplaceProfile_is_schwartz {q : ℝ} (hq : 0 < q) :
    ∃ g : SchwartzMap ℝ ℂ, (g : ℝ → ℂ) = evenLaplaceProfile q := by
  refine ⟨complexProfileSchwartz hq, ?_⟩
  funext u
  exact complexProfileSchwartz_apply hq u

end
end ImbalancedChen.Part3.KProfileSchwartzSourceOnly
