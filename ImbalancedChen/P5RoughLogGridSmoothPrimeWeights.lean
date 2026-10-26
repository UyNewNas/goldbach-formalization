import ImbalancedChen.P5RoughLogGridSmoothPartition
import ImbalancedChen.FinitePrimeGeometryCore
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual rough-grid labels have a width-explicit all-order scalar and
Frechet budget, uniform in the mesh and label. Their literal original-prime
pullbacks give the nonnegative subpartition required by weighted word
coefficients. Support and carrier error retain exact physical power strips.
There is no assertion about a rho coefficient or progression discrepancy.
-/
namespace ImbalancedChen.P5Z.RoughLogGridSmoothPartition
noncomputable section
open Set Classical
open scoped BigOperators
open P4B

theorem iteratedDeriv_label (k : ℕ) (a b : ℝ) (n : ℕ) (δ : ℝ)
    (j : Fin (n + 1)) (x : ℝ) :
    iteratedDeriv k (label a b n δ j) x =
      iteratedDeriv k (smoothGateUpperStep δ) (x - left a b n j) -
        iteratedDeriv k (smoothGateUpperStep δ) (x - right a b n j) := by
  have hshift (c : ℝ) : iteratedDeriv k (fun t => smoothGateUpperStep δ (t - c)) x =
      iteratedDeriv k (smoothGateUpperStep δ) (x - c) := by
    simpa only [one_pow, one_mul, sub_eq_add_neg, add_comm] using
      iteratedDeriv_comp_real_affine k (smoothGateUpperStep δ)
        (contDiff_smoothGateUpperStep δ) (-c) 1 x
  have hf (c : ℝ) : ContDiffAt ℝ k (fun t => smoothGateUpperStep δ (t - c)) x :=
    ((contDiff_smoothGateUpperStep δ).comp (contDiff_id.sub contDiff_const)).contDiffAt
  change iteratedDeriv k ((fun t => smoothGateUpperStep δ (t - left a b n j)) -
    (fun t => smoothGateUpperStep δ (t - right a b n j))) x = _
  rw [iteratedDeriv_sub (hf _) (hf _), hshift, hshift]

/-- C_k is chosen before every mesh, endpoint, width, label and argument. -/
theorem exists_label_derivative_budget (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (a b : ℝ) (n : ℕ) (δ : ℝ), 0 < δ →
      ∀ (j : Fin (n + 1)) (x : ℝ),
        |iteratedDeriv k (label a b n δ j) x| ≤ C / δ ^ k := by
  obtain ⟨B, hB, hbound⟩ := exists_smoothGateUpperStep_derivative_budget k
  refine ⟨2 * B, by linarith, ?_⟩
  intro a b n δ hδ j x
  rw [iteratedDeriv_label]
  calc
    |_ - _| ≤ |iteratedDeriv k (smoothGateUpperStep δ) (x - left a b n j)| +
        |iteratedDeriv k (smoothGateUpperStep δ) (x - right a b n j)| := abs_sub _ _
    _ ≤ B / δ ^ k + B / δ ^ k := add_le_add (hbound δ hδ _) (hbound δ hδ _)
    _ = (2 * B) / δ ^ k := by ring

theorem exists_label_frechet_budget (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (a b : ℝ) (n : ℕ) (δ : ℝ), 0 < δ →
      ∀ (j : Fin (n + 1)) (x : ℝ),
        ‖iteratedFDeriv ℝ k (label a b n δ j) x‖ ≤ C / δ ^ k := by
  obtain ⟨C, hC, hbound⟩ := exists_label_derivative_budget k
  refine ⟨C, hC, ?_⟩
  intro a b n δ hδ j x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  exact hbound a b n δ hδ j x

def primeLabel (N : ℕ) (a b : ℝ) (n : ℕ) (δ : ℝ) (j : Fin (n + 1)) (p : ℕ) : ℝ :=
  label a b n δ j (Real.log (p : ℝ) / Real.log (N : ℝ))

/-- These are actual functions of the original prime, including all
arithmetic endpoints. No abstract label-weight certificate is assumed. -/
theorem primeLabel_subpartition {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (N n p : ℕ) :
    (∀ j : Fin (n + 1), 0 ≤ primeLabel N a b n δ j p) ∧
      (∑ j : Fin (n + 1), primeLabel N a b n δ j p) ≤ 1 :=
  ⟨fun j => (label_bounds hab hδ n j _).1, (sum_labels_bounds hab hδ n _).2⟩

theorem primeLabel_nonzero_power_support {N p : ℕ} (hN : 1 < N) (hp : 0 < p)
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (n : ℕ) (j : Fin (n + 1))
    (hne : primeLabel N a b n δ j p ≠ 0) :
    (N : ℝ) ^ (left a b n j - δ) < (p : ℝ) ∧
      (p : ℝ) < (N : ℝ) ^ right a b n j := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (Real.log (p : ℝ) / Real.log (N : ℝ)) = (p : ℝ) := by
    simpa only [actualPrimeTupleLog] using
      actualPrimeTupleLog_rpow hN (fun _ : Fin 1 => p) (fun _ => hp) 0
  have hs := label_nonzero_support hab hδ n j hne
  constructor
  · simpa only [hpow] using (Real.rpow_lt_rpow_left_iff hNr).2 hs.1
  · simpa only [hpow] using (Real.rpow_lt_rpow_left_iff hNr).2 hs.2

def physicalEndpointReserve (N : ℕ) (a b δ : ℝ) (p : ℕ) : Prop :=
  ((N : ℝ) ^ (a - δ) < (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ a) ∨
    ((N : ℝ) ^ (b - δ) < (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ b)

theorem prime_partition_error_supported {N p : ℕ} (hN : 1 < N) (hp : 0 < p)
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) (n : ℕ)
    (he : (∑ j : Fin (n + 1), primeLabel N a b n δ j p) -
      literal a b (Real.log (p : ℝ) / Real.log (N : ℝ)) ≠ 0) :
    physicalEndpointReserve N a b δ p := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (Real.log (p : ℝ) / Real.log (N : ℝ)) = (p : ℝ) := by
    simpa only [actualPrimeTupleLog] using
      actualPrimeTupleLog_rpow hN (fun _ : Fin 1 => p) (fun _ => hp) 0
  have hs := partition_error_supported hab hδ n _ he
  rcases hs with hs | hs
  · left
    exact ⟨by simpa only [hpow] using (Real.rpow_lt_rpow_left_iff hNr).2 hs.1,
      by simpa only [hpow] using (Real.rpow_lt_rpow_left_iff hNr).2 hs.2⟩
  · right
    exact ⟨by simpa only [hpow] using (Real.rpow_lt_rpow_left_iff hNr).2 hs.1,
      by simpa only [hpow] using (Real.rpow_lt_rpow_left_iff hNr).2 hs.2⟩

end
end ImbalancedChen.P5Z.RoughLogGridSmoothPartition
