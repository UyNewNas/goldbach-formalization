import Mathlib

-- SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
-- Original manuscript internal insertion: finite arithmetic sums commute
-- with absolutely integrable complex separation; only the L1 norm is paid.
namespace ImbalancedChen.PrimeProducts.MellinInsertion20261028

noncomputable section
open MeasureTheory
open scoped BigOperators

variable {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

-- A finite complex functional, with no positivity assumption on its kernel.
def functional (s : Finset ι) (c w : ι → ℂ) : ℂ :=
  ∑ i ∈ s, w i * c i

theorem functional_mul (s : Finset ι) (c w : ι → ℂ) (z : ℂ) :
    functional s c (fun i => z * w i) = z * functional s c w := by
  classical
  simp only [functional, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem functional_integrable (s : Finset ι) (c : ι → ℂ)
    (F : Ω → ι → ℂ) (hF : ∀ i ∈ s, Integrable (fun ξ => F ξ i) μ) :
    Integrable (fun ξ => functional s c (F ξ)) μ := by
  classical
  revert hF
  induction s using Finset.induction_on with
  | empty =>
      intro hF
      simpa only [functional, Finset.sum_empty] using
        (integrable_zero : Integrable (fun _ : Ω => (0 : ℂ)) μ)
  | @insert a s ha ih =>
      intro hF
      have hs := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
      have heq : (fun ξ => functional (insert a s) c (F ξ)) =
          (fun ξ => F ξ a * c a + functional s c (F ξ)) := by
        funext ξ
        simp only [functional, Finset.sum_insert ha]
      rw [heq]
      exact ((hF a (Finset.mem_insert_self a s)).mul_const (c a)).add hs

-- Finite-sum interchange is proved for the actual scalar integrands.
theorem functional_integral (s : Finset ι) (c : ι → ℂ)
    (F : Ω → ι → ℂ) (hF : ∀ i ∈ s, Integrable (fun ξ => F ξ i) μ) :
    functional s c (fun i => ∫ ξ, F ξ i ∂μ) =
      ∫ ξ, functional s c (F ξ) ∂μ := by
  classical
  unfold functional
  rw [integral_finset_sum s (fun i hi => (hF i hi).mul_const (c i))]
  simp only [integral_mul_const]

-- The arithmetic input is a bound for each separated mode. The conclusion
-- charges its integrated coefficient norm, independent of mode-box volume.
theorem norm_functional_of_separation
    (s : Finset ι) (c w : ι → ℂ) (A : Ω → ℂ) (mode : Ω → ι → ℂ)
    (E : ℝ) (hA : Integrable A μ)
    (hAM : ∀ i ∈ s, Integrable (fun ξ => A ξ * mode ξ i) μ)
    (hrep : ∀ i ∈ s, w i = ∫ ξ, A ξ * mode ξ i ∂μ)
    (hmode : ∀ ξ, ‖functional s c (mode ξ)‖ ≤ E) :
    ‖functional s c w‖ ≤ (∫ ξ, ‖A ξ‖ ∂μ) * E := by
  classical
  have hreconstruct : functional s c w =
      functional s c (fun i => ∫ ξ, A ξ * mode ξ i ∂μ) := by
    unfold functional
    apply Finset.sum_congr rfl
    intro i hi
    rw [hrep i hi]
  have hmodeIntegral : Integrable
      (fun ξ => A ξ * functional s c (mode ξ)) μ := by
    have h := functional_integrable s c (fun ξ i => A ξ * mode ξ i) hAM
    simpa only [functional_mul] using h
  rw [hreconstruct, functional_integral s c (fun ξ i => A ξ * mode ξ i) hAM]
  simp_rw [functional_mul]
  calc
    ‖∫ ξ, A ξ * functional s c (mode ξ) ∂μ‖ ≤
        ∫ ξ, ‖A ξ * functional s c (mode ξ)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ξ, ‖A ξ‖ * E ∂μ := by
      apply integral_mono_ae hmodeIntegral.norm (hA.norm.mul_const E)
      exact Filter.Eventually.of_forall (fun ξ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hmode ξ) (norm_nonneg _))
    _ = (∫ ξ, ‖A ξ‖ ∂μ) * E := by rw [integral_mul_const]

-- The residue and coprimality tests refer to the SAME complete integer.
-- No unrestricted mean or modulus-dependent replacement coefficient occurs.
def residueKernel (q a b : ℕ) : ℂ :=
  (if b % q = a % q then 1 else 0) -
    (if Nat.Coprime b q then 1 else 0) / (q.totient : ℂ)

def exactDiscrepancy (s : Finset ι) (Q : Finset ℕ) (rho : ℕ → ℂ)
    (product : ι → ℕ) (a : ℕ) (w : ι → ℂ) : ℂ :=
  functional s (fun i => ∑ q ∈ Q, rho q * residueKernel q a (product i)) w

def residueCount (s : Finset ι) (product : ι → ℕ) (a q : ℕ)
    (w : ι → ℂ) : ℂ :=
  ∑ i ∈ s, w i * (if product i % q = a % q then 1 else 0)

def exactCoprimeMean (s : Finset ι) (product : ι → ℕ) (q : ℕ)
    (w : ι → ℂ) : ℂ :=
  (∑ i ∈ s, w i * (if Nat.Coprime (product i) q then 1 else 0)) /
    (q.totient : ℂ)

-- This equality exposes the exact count/mean pair behind the integrated
-- functional; the same rho and coprimality projector occur on both sides.
theorem exactDiscrepancy_eq_count_sub_mean
    (s : Finset ι) (Q : Finset ℕ) (rho : ℕ → ℂ)
    (product : ι → ℕ) (a : ℕ) (w : ι → ℂ) :
    exactDiscrepancy s Q rho product a w =
      ∑ q ∈ Q, rho q *
        (residueCount s product a q w - exactCoprimeMean s product q w) := by
  classical
  unfold exactDiscrepancy functional
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  calc
    (∑ i ∈ s, w i * (rho q * residueKernel q a (product i))) =
        rho q * (∑ i ∈ s,
          w i * (if product i % q = a % q then 1 else 0) -
          (w i * (if Nat.Coprime (product i) q then 1 else 0)) /
            (q.totient : ℂ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      unfold residueKernel
      ring
    _ = _ := by
      simp only [residueCount, exactCoprimeMean, Finset.sum_sub_distrib, Finset.sum_div]

-- Exact inversion for every retained integer tuple is the classical input.
-- The local arithmetic bound remains uniform in the separated frequency.
theorem norm_exactDiscrepancy_of_separation
    (s : Finset ι) (Q : Finset ℕ) (rho : ℕ → ℂ)
    (product : ι → ℕ) (a : ℕ)
    (w : ι → ℂ) (A : Ω → ℂ) (mode : Ω → ι → ℂ)
    (E : ℝ) (hA : Integrable A μ)
    (hAM : ∀ i ∈ s, Integrable (fun ξ => A ξ * mode ξ i) μ)
    (hrep : ∀ i ∈ s, w i = ∫ ξ, A ξ * mode ξ i ∂μ)
    (hmode : ∀ ξ, ‖exactDiscrepancy s Q rho product a (mode ξ)‖ ≤ E) :
    ‖exactDiscrepancy s Q rho product a w‖ ≤
      (∫ ξ, ‖A ξ‖ ∂μ) * E := by
  exact norm_functional_of_separation s
    (fun i => ∑ q ∈ Q, rho q * residueKernel q a (product i))
    w A mode E hA hAM hrep hmode

end
end ImbalancedChen.PrimeProducts.MellinInsertion20261028
