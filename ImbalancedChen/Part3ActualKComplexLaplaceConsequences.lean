import ImbalancedChen.Part3ActualKFullHeightEnergy
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED (2026-10-24).  Genuine consequences of vanishing
of the physical compact-q K transform for an arbitrary complex amplitude.
The Fourier energy forces its continuous even Laplace profile to vanish
pointwise, hence its ordinary Laplace transform vanishes for every s ≥ 1.
A separate finite-atomic Laplace uniqueness lemma records the exact
Vandermonde mechanism.  Full injectivity on continuous q amplitudes still
requires the compact-interval Laplace uniqueness / polynomial-density step.
-/

namespace ImbalancedChen.Part3.ActualKComplexLaplaceConsequences20261024z

noncomputable section

open Classical Set MeasureTheory
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ActualCommonHeightKGramSourceOnly (kTestTransform)
open ActualKTransformFourier20261024z
open ActualKFullHeightEnergy20261024z

variable {ι : Type*}

/-- A vanishing physical K transform has identically zero q-Laplace profile.
This uses actual full-height Fourier energy, the proved L² integrability and
continuity of the compact-q profile, and positive measure of open sets. -/
theorem qLaplaceProfile_eq_zero_of_amplitudeK_eq_zero
    (P : PacketData ι) (a : ℝ → ℂ) (ha : PhysicalAmplitude P a)
    (hK : ∀ t : ℝ, amplitudeK P a t = 0) (u : ℝ) :
    qLaplaceProfile P a u = 0 := by
  let F : ℝ → ℝ := fun v => ‖qLaplaceProfile P a v‖ ^ 2
  have hFcont : Continuous F :=
    (qLaplaceProfile_continuous P a ha).norm.pow 2
  have hFint : Integrable F := qLaplaceProfile_norm_sq_integrable P a ha
  have hFnonneg : 0 ≤ F := by
    intro v
    positivity
  have hEnergy : (∫ v : ℝ, F v) = 0 := by
    have h := amplitudeK_full_height_energy P a ha
    have hzero : (∫ t : ℝ, ‖amplitudeK P a t‖ ^ 2) = 0 := by
      simp [hK]
    rw [hzero] at h
    have hπ : Real.pi / 4 ≠ 0 := ne_of_gt (by positivity)
    exact (mul_eq_zero.mp h.symm).resolve_left hπ
  by_contra hnonzero
  have hFnonzero : F u ≠ 0 := by
    change ‖qLaplaceProfile P a u‖ ^ 2 ≠ 0
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hnonzero)
  have hpos : 0 < ∫ v : ℝ, F v :=
    integral_pos_of_integrable_nonneg_nonzero hFcont hFint hFnonneg hFnonzero
  linarith

/-- The ordinary Laplace transform of the literal compact-q amplitude is
zero on the whole real half-line s ≥ 1.  This is an output, not an assumed
Laplace injectivity premise. -/
theorem compactLaplace_eq_zero_of_amplitudeK_eq_zero
    (P : PacketData ι) (a : ℝ → ℂ) (ha : PhysicalAmplitude P a)
    (hK : ∀ t : ℝ, amplitudeK P a t = 0)
    (s : ℝ) (hs : 1 ≤ s) :
    (∫ q : ℝ, a q * (Real.exp (-q * s) : ℂ)) = 0 := by
  have h := qLaplaceProfile_eq_zero_of_amplitudeK_eq_zero
    P a ha hK (Real.arcosh s)
  simpa only [qLaplaceProfile, Real.cosh_arcosh hs] using h

/-- Every integer exponential moment of the same actual amplitude vanishes.
These are the polynomial moments in x = exp(-q) that a subsequent compact
Stone-Weierstrass argument would have to use. -/
theorem compactExpMoment_eq_zero_of_amplitudeK_eq_zero
    (P : PacketData ι) (a : ℝ → ℂ) (ha : PhysicalAmplitude P a)
    (hK : ∀ t : ℝ, amplitudeK P a t = 0) (n : ℕ) :
    (∫ q : ℝ, a q * (Real.exp (-q) : ℂ) *
      (Real.exp (-q) : ℂ) ^ n) = 0 := by
  have hs : 1 ≤ (n : ℝ) + 1 := by positivity
  have hLap := compactLaplace_eq_zero_of_amplitudeK_eq_zero
    P a ha hK ((n : ℝ) + 1) hs
  have hpoint (q : ℝ) :
      a q * (Real.exp (-q * ((n : ℝ) + 1)) : ℂ) =
        a q * (Real.exp (-q) : ℂ) *
          (Real.exp (-q) : ℂ) ^ n := by
    have harg : -q * ((n : ℝ) + 1) = -q + (n : ℝ) * (-q) := by ring
    rw [harg, Real.exp_add, Real.exp_nat_mul]
    simp only [Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  simpa only [hpoint] using hLap

private theorem compactPolynomialMoment_integrable
    (P : PacketData ι) (a : ℝ → ℂ) (ha : PhysicalAmplitude P a)
    (p : ℂ[X]) :
    Integrable (fun q : ℝ => a q * (Real.exp (-q) : ℂ) *
      p.eval (Real.exp (-q) : ℂ)) := by
  have hc : Continuous (fun q : ℝ => a q * (Real.exp (-q) : ℂ) *
      p.eval (Real.exp (-q) : ℂ)) := by
    have hp : Continuous (fun q : ℝ => p.eval (Real.exp (-q) : ℂ)) :=
      p.continuous.comp (by fun_prop)
    exact (ha.1.mul (by fun_prop)).mul hp
  apply hc.integrable_of_hasCompactSupport
  apply (isCompact_Icc : IsCompact P.region).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isClosed_Icc : IsClosed P.region)
  intro q hq
  by_contra hn
  exact hq (by simp [ha.2 q hn])

/-- All complex polynomial test moments in z = exp(-q) vanish.  This is the
precise algebraic side of the still-missing compact Stone-Weierstrass
density/continuity passage for arbitrary physical amplitudes. -/
theorem compactPolynomialMoment_eq_zero_of_amplitudeK_eq_zero
    (P : PacketData ι) (a : ℝ → ℂ) (ha : PhysicalAmplitude P a)
    (hK : ∀ t : ℝ, amplitudeK P a t = 0) (p : ℂ[X]) :
    (∫ q : ℝ, a q * (Real.exp (-q) : ℂ) *
      p.eval (Real.exp (-q) : ℂ)) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
      have hi₁ := compactPolynomialMoment_integrable P a ha p
      have hi₂ := compactPolynomialMoment_integrable P a ha r
      have hpoint (q : ℝ) :
          a q * (Real.exp (-q) : ℂ) *
              (p + r).eval (Real.exp (-q) : ℂ) =
            (a q * (Real.exp (-q) : ℂ) *
              p.eval (Real.exp (-q) : ℂ)) +
            (a q * (Real.exp (-q) : ℂ) *
              r.eval (Real.exp (-q) : ℂ)) := by
        rw [Polynomial.eval_add]
        ring
      calc
        (∫ q : ℝ, a q * (Real.exp (-q) : ℂ) *
            (p + r).eval (Real.exp (-q) : ℂ)) =
            ∫ q : ℝ, (a q * (Real.exp (-q) : ℂ) *
              p.eval (Real.exp (-q) : ℂ)) +
              (a q * (Real.exp (-q) : ℂ) *
              r.eval (Real.exp (-q) : ℂ)) := by
          congr 1
          funext q
          exact hpoint q
        _ = (∫ q : ℝ, a q * (Real.exp (-q) : ℂ) *
              p.eval (Real.exp (-q) : ℂ)) +
            ∫ q : ℝ, a q * (Real.exp (-q) : ℂ) *
              r.eval (Real.exp (-q) : ℂ) := integral_add hi₁ hi₂
        _ = 0 := by rw [hp, hr, add_zero]
  | monomial n c =>
      have hm := compactExpMoment_eq_zero_of_amplitudeK_eq_zero
        P a ha hK n
      have hpoint (q : ℝ) :
          a q * (Real.exp (-q) : ℂ) *
              (Polynomial.monomial n c).eval (Real.exp (-q) : ℂ) =
            c * (a q * (Real.exp (-q) : ℂ) *
              (Real.exp (-q) : ℂ) ^ n) := by
        rw [Polynomial.eval_monomial]
        ring
      calc
        (∫ q : ℝ, a q * (Real.exp (-q) : ℂ) *
            (Polynomial.monomial n c).eval (Real.exp (-q) : ℂ)) =
          ∫ q : ℝ, c * (a q * (Real.exp (-q) : ℂ) *
            (Real.exp (-q) : ℂ) ^ n) := by
          congr 1
          funext q
          exact hpoint q
        _ = c * ∫ q : ℝ, a q * (Real.exp (-q) : ℂ) *
            (Real.exp (-q) : ℂ) ^ n := integral_const_mul
        _ = 0 := by rw [hm, mul_zero]

/-- The literal spectral-test K transform inherits the pointwise conclusion
without treating its Fourier identification as a supplied field. -/
theorem actualKLaplaceProfile_eq_zero_of_kTestTransform_eq_zero
    (P : PacketData ι) (k : D4 → ℤ)
    (hK : ∀ t : ℝ, kTestTransform P k t = 0) (u : ℝ) :
    actualKLaplaceProfile P k u = 0 := by
  rw [actualKLaplaceProfile_eq_generic]
  apply qLaplaceProfile_eq_zero_of_amplitudeK_eq_zero
    P (actualKAmplitude P k) (actualKAmplitude_physical P k)
  intro t
  rw [← kTestTransform_eq_amplitudeK P k t]
  exact hK t

theorem actualCompactLaplace_eq_zero_of_kTestTransform_eq_zero
    (P : PacketData ι) (k : D4 → ℤ)
    (hK : ∀ t : ℝ, kTestTransform P k t = 0)
    (s : ℝ) (hs : 1 ≤ s) :
    (∫ q : ℝ, actualKAmplitude P k q *
      (Real.exp (-q * s) : ℂ)) = 0 := by
  apply compactLaplace_eq_zero_of_amplitudeK_eq_zero
    P (actualKAmplitude P k) (actualKAmplitude_physical P k)
  · intro t
    rw [← kTestTransform_eq_amplitudeK P k t]
    exact hK t
  · exact hs

/-- A finite family of distinct q atoms has a unique complex Laplace
representation on s ≥ 1.  The proof samples at s = j+1 and applies the
actual Vandermonde determinant theorem to exp(-qᵢ).  Atomic measures are
not the continuous amplitudes of `PhysicalAmplitude`; this lemma does not
by itself settle their injectivity. -/
theorem finite_exp_laplace_unique {n : ℕ}
    (q : Fin n → ℝ) (c : Fin n → ℂ) (hq : Function.Injective q)
    (hLap : ∀ s : ℝ, 1 ≤ s →
      (∑ i : Fin n, c i * (Real.exp (-q i * s) : ℂ)) = 0) :
    c = 0 := by
  let x : Fin n → ℂ := fun i => (Real.exp (-q i) : ℂ)
  let d : Fin n → ℂ := fun i => c i * x i
  have hx : Function.Injective x := by
    intro i j hij
    have hr : Real.exp (-q i) = Real.exp (-q j) :=
      Complex.ofReal_injective hij
    have hneg : -q i = -q j := Real.exp_injective hr
    exact hq (neg_injective hneg)
  have hsample (j : Fin n) :
      (∑ i : Fin n, d i * x i ^ (j : ℕ)) = 0 := by
    have hs : 1 ≤ ((j : ℕ) : ℝ) + 1 := by positivity
    have hj := hLap (((j : ℕ) : ℝ) + 1) hs
    have hfactor (i : Fin n) :
        (Real.exp (-q i * (((j : ℕ) : ℝ) + 1)) : ℂ) =
          x i * x i ^ (j : ℕ) := by
      have harg : -q i * (((j : ℕ) : ℝ) + 1) =
          -q i + ((j : ℕ) : ℝ) * (-q i) := by ring
      rw [harg, Real.exp_add, Real.exp_nat_mul]
      simp only [x, Complex.ofReal_mul, Complex.ofReal_pow]
    simpa only [d, hfactor, mul_assoc] using hj
  have hd : d = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hx hsample
  funext i
  have hdi : d i = 0 := by simpa using congrFun hd i
  have hxi : x i ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  exact (mul_eq_zero.mp hdi).resolve_right hxi

end
end ImbalancedChen.Part3.ActualKComplexLaplaceConsequences20261024z
