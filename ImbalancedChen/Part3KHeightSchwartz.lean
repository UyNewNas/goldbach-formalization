import ImbalancedChen.Part3KProfileSchwartz
import ImbalancedChen.Part3KFullLineFourierBridge
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Tactic

/-!
PURE NEW CONTINUATION / SOURCE_WRITTEN / UNCOMPILED / CODE_ONLY.
Requires the supplied profile-Schwartz and actual half-Fourier bridge source
bodies, plus Mathlib.Analysis.Distribution.SchwartzSpace.Fourier and
Mathlib.Topology.Algebra.Module.Equiv. The companion standalone bundle
collects the actual imports and preceding source bodies without future imports.
-/

namespace ImbalancedChen.Part3.KHeightSchwartzP3SourceOnly
noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform
open ImaginaryOrderKBesselSourceOnly
open P3ActualKProfileLpSourceOnly
open KProfileSchwartzSourceOnly
open KFullLineFourierBridgeSourceOnly

/-- The exact order-height to Mathlib Fourier-frequency conversion t -> t/pi. -/
def heightFrequencyEquiv : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft
    (Units.mk0 (Real.pi⁻¹) (inv_ne_zero Real.pi_ne_zero))

@[simp]
theorem heightFrequencyEquiv_apply (t : ℝ) :
    heightFrequencyEquiv t = t / Real.pi := by
  change Real.pi⁻¹ * t = t / Real.pi
  rw [div_eq_mul_inv]
  ring

theorem heightFrequencyEquiv_symm_apply (ξ : ℝ) :
    heightFrequencyEquiv.symm ξ = Real.pi * ξ := by
  apply heightFrequencyEquiv.injective
  rw [heightFrequencyEquiv.apply_symm_apply, heightFrequencyEquiv_apply]
  field_simp [Real.pi_ne_zero] <;> ring

/-- The actual K_{2it}(q), using Fourier on Schwartz space and the exact half. -/
def kHeightSchwartz (q : ℝ) (hq : 0 < q) : SchwartzMap ℝ ℂ :=
  (1 / 2 : ℂ) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ heightFrequencyEquiv
      (𝓕 (complexProfileSchwartz hq)))

/-- The construction retains both the literal t/pi scale and scalar 1/2. -/
theorem kHeightSchwartz_half_fourier (q : ℝ) (hq : 0 < q) (t : ℝ) :
    kHeightSchwartz q hq t =
      (1 / 2 : ℂ) * 𝓕 (kEvenProfile q) (t / Real.pi) := by
  have hp : (complexProfileSchwartz hq : ℝ → ℂ) = kEvenProfile q := by
    funext u
    exact complexProfileSchwartz_apply hq u
  have hf : ((𝓕 (complexProfileSchwartz hq) : SchwartzMap ℝ ℂ) : ℝ → ℂ) =
      𝓕 (kEvenProfile q) := by
    rw [SchwartzMap.fourier_coe, hp]
  change (1 / 2 : ℂ) *
      (((𝓕 (complexProfileSchwartz hq) : SchwartzMap ℝ ℂ) : ℝ → ℂ)
        (heightFrequencyEquiv t)) = _
  rw [hf, heightFrequencyEquiv_apply]

/-- Exact pointwise identification with the actual positive-axis K definition. -/
@[simp]
theorem kHeightSchwartz_apply (q : ℝ) (hq : 0 < q) (t : ℝ) :
    kHeightSchwartz q hq t = (imaginaryOrderK t q : ℂ) := by
  rw [kHeightSchwartz_half_fourier]
  exact (imaginaryOrderK_eq_half_fourier t q hq).symm

/-- The callable-function identity is useful under integrals and derivatives. -/
theorem kHeightSchwartz_coe (q : ℝ) (hq : 0 < q) :
    (kHeightSchwartz q hq : ℝ → ℂ) = fun t : ℝ => (imaginaryOrderK t q : ℂ) := by
  funext t
  exact kHeightSchwartz_apply q hq t

theorem kHeightSchwartz_even (q : ℝ) (hq : 0 < q) (t : ℝ) :
    kHeightSchwartz q hq (-t) = kHeightSchwartz q hq t := by
  rw [kHeightSchwartz_apply, kHeightSchwartz_apply, imaginaryOrderK_neg]

theorem kHeightSchwartz_star (q : ℝ) (hq : 0 < q) (t : ℝ) :
    star (kHeightSchwartz q hq t) = kHeightSchwartz q hq t := by
  rw [kHeightSchwartz_apply]
  simp only [Complex.star_def, Complex.conj_ofReal]

/-- Smoothness is obtained from the constructed object, not supplied as a premise. -/
theorem imaginaryOrderK_height_contDiff {q : ℝ} (hq : 0 < q) :
    ContDiff ℝ ∞ (fun t : ℝ => (imaginaryOrderK t q : ℂ)) := by
  rw [← kHeightSchwartz_coe q hq]
  exact (kHeightSchwartz q hq).smooth ⊤

/-- A genuine unweighted full-line height integral is now well-defined. -/
theorem imaginaryOrderK_height_complex_integrable {q : ℝ} (hq : 0 < q) :
    Integrable (fun t : ℝ => (imaginaryOrderK t q : ℂ)) := by
  rw [← kHeightSchwartz_coe q hq]
  exact (kHeightSchwartz q hq).integrable

theorem imaginaryOrderK_height_real_integrable {q : ℝ} (hq : 0 < q) :
    Integrable (fun t : ℝ => imaginaryOrderK t q) := by
  have h := Complex.reCLM.integrable_comp (imaginaryOrderK_height_complex_integrable hq)
  simpa only [Function.comp_apply, Complex.reCLM_apply, Complex.ofReal_re] using h

/-- Every actual weighted derivative is bounded by a genuine Schwartz seminorm. -/
theorem imaginaryOrderK_height_seminorm_bound {q : ℝ} (hq : 0 < q)
    (M n : ℕ) (t : ℝ) :
    |t| ^ M * ‖iteratedDeriv n (fun s : ℝ => (imaginaryOrderK s q : ℂ)) t‖ ≤
      SchwartzMap.seminorm ℂ M n (kHeightSchwartz q hq) := by
  have h := SchwartzMap.le_seminorm' ℂ M n (kHeightSchwartz q hq) t
  simpa only [kHeightSchwartz_coe q hq] using h

/-- All actual height Schwartz bounds follow, for every weight and derivative. -/
theorem imaginaryOrderK_height_all_seminorms_finite {q : ℝ} (hq : 0 < q)
    (M n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      |t| ^ M * ‖iteratedDeriv n (fun s : ℝ => (imaginaryOrderK s q : ℂ)) t‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := (kHeightSchwartz q hq).decay M n
  refine ⟨C, hC, ?_⟩
  intro t
  simpa only [kHeightSchwartz_coe q hq, Real.norm_eq_abs,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hbound t

/-- All polynomially weighted derivative norms are also integrable in height. -/
theorem imaginaryOrderK_height_weighted_derivative_integrable {q : ℝ}
    (hq : 0 < q) (M n : ℕ) :
    Integrable (fun t : ℝ =>
      |t| ^ M * ‖iteratedDeriv n (fun s : ℝ => (imaginaryOrderK s q : ℂ)) t‖) := by
  have h := (kHeightSchwartz q hq).integrable_pow_mul_iteratedFDeriv volume M n
  simpa only [kHeightSchwartz_coe q hq, Real.norm_eq_abs,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv] using h

end
end ImbalancedChen.Part3.KHeightSchwartzP3SourceOnly

/-!
The object is for each fixed positive q and the actual K integral at every
real height t. No extra equality, decay, Schwartz or integrability hypothesis
is accepted. The Fourier profile and bridge are explicitly named preceding
source-only suppliers in the standalone assembly; they are not represented
as independently compiled actual project modules. No q derivative, ODE,
distinguished t^-2 estimate, Kuznetsov normalization, spectral measure,
large-sieve or manuscript endpoint claim is introduced.
-/
