import ImbalancedChen.RectangleDiscrepancyAssembly
import ImbalancedChen.BoundaryLogMesh
import ImbalancedChen.LogCutoffError

/-!
# The actual curved discrepancy reduces to literal rectangle discrepancies

For any fixed logarithmic mesh exponent `k > 4`, the proved geometric
boundary contribution is absorbed into an arbitrary positive multiple of
the genuine singular-series normalization. The remaining term is the
explicit sum of absolute discrepancies of the actual full prime rectangles.

The threshold is uniform over the source cutoff in `[0,N]`, the modulus
cap at most `N`, and every selected family of positive moduli under that
cap. The final statements use the literal cutoff `N / (log N)^10`.

No rectangle-distribution estimate, sieve asymptotic, target discrepancy
bound, or analytic supplier is assumed. In particular, this reduction
does not claim that the remaining rectangle sum is small.
-/

namespace ImbalancedChen

open Filter
open scoped BigOperators

noncomputable section

/-- The actual curved source pays each selected full rectangle once, plus
an arbitrarily small normalized boundary error. All finite choices follow
the eventual threshold, so the bound is uniform in `T`, `D`, and `S`. -/
theorem eventually_sum_abs_halfProductPrimitiveDiscrepancy_le_actualGridRectangles
    {num den k : ℕ} (hden : 0 < den)
    (hb : 0 < (num : ℝ) / (den : ℝ))
    (hb1 : (num : ℝ) / (den : ℝ) < 1) (hk : 4 < k) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ T : ℝ, ∀ D : ℕ, ∀ S : Finset ℕ,
        0 ≤ T → T ≤ (N : ℝ) → D ≤ N → S ⊆ Finset.Icc 1 D →
        (∑ d ∈ S, |halfProductCongruenceMass num den N T d -
          halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)|) ≤
        (∑ ij ∈ actualGridIntersectingIndices num den N T (1 + boundaryLogMesh k N),
          ∑ d ∈ S, |actualGridRectangleDiscrepancy (1 + boundaryLogMesh k N) ij N d|) +
          epsilon * singularNormalization N := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_actualGrid_logMesh_boundary_cost_le_singularNormalization
      hden hb hb1 hk epsilon hepsilon, eventually_boundaryLogMesh_mem k]
    with N hboundary hmesh
  intro T D S hT hTN hD hS
  have hκ : 1 < 1 + boundaryLogMesh k N := by linarith [hmesh.1]
  have hmass : 0 ≤ finiteSourceMass
      (actualGridProductCarrier num den N T (1 + boundaryLogMesh k N))
      (fun m => actualGridUpperWeight num den N T (1 + boundaryLogMesh k N) m -
        actualGridLowerWeight num den N T (1 + boundaryLogMesh k N) m) := by
    rw [actualGrid_boundary_mass_eq_card]
    exact Nat.cast_nonneg _
  have hcost := (mul_le_mul_of_nonneg_left
    (sum_reciprocal_totient_subset_le_log S D hS) hmass).trans
      (hboundary T D hT hTN hD)
  exact (sum_abs_halfProductPrimitiveDiscrepancy_le_actualGridRectangles hden hκ S).trans
    (add_le_add le_rfl hcost)

/-- The reduction at the manuscript's actual logarithmic cutoff. Only the
literal rectangle sum remains; no assumed estimate for it has been inserted. -/
theorem eventually_sum_abs_logCutoff_halfProductDiscrepancy_le_actualGridRectangles
    {num den k : ℕ} (hden : 0 < den)
    (hb : 0 < (num : ℝ) / (den : ℝ))
    (hb1 : (num : ℝ) / (den : ℝ) < 1) (hk : 4 < k) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ D : ℕ, ∀ S : Finset ℕ,
        D ≤ N → S ⊆ Finset.Icc 1 D →
        (∑ d ∈ S, |halfProductCongruenceMass num den N (logCutoff N) d -
          halfProductCoprimeMass num den N (logCutoff N) d / (Nat.totient d : ℝ)|) ≤
        (∑ ij ∈ actualGridIntersectingIndices num den N (logCutoff N)
            (1 + boundaryLogMesh k N),
          ∑ d ∈ S, |actualGridRectangleDiscrepancy (1 + boundaryLogMesh k N) ij N d|) +
          epsilon * singularNormalization N := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_sum_abs_halfProductPrimitiveDiscrepancy_le_actualGridRectangles
      hden hb hb1 hk epsilon hepsilon, eventually_one_le_nat_log]
    with N hreduce hlog
  intro D S hD hS
  have hpow : 1 ≤ (Real.log (N : ℝ)) ^ 10 := one_le_pow₀ hlog
  have hpowpos : 0 < (Real.log (N : ℝ)) ^ 10 := by linarith
  have hcutoff : logCutoff N ≤ (N : ℝ) := by
    unfold logCutoff
    apply (div_le_iff₀ hpowpos).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg N)
  exact hreduce (logCutoff N) D S (logCutoff_nonneg N) hcutoff hD hS

/-- In particular the same reduction holds for the complete positive modulus
interval, including its inclusive upper endpoint and the empty case `D=0`. -/
theorem eventually_sum_abs_logCutoff_halfProductDiscrepancy_Icc_le_actualGridRectangles
    {num den k : ℕ} (hden : 0 < den)
    (hb : 0 < (num : ℝ) / (den : ℝ))
    (hb1 : (num : ℝ) / (den : ℝ) < 1) (hk : 4 < k) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ D : ℕ, D ≤ N →
        (∑ d ∈ Finset.Icc 1 D,
          |halfProductCongruenceMass num den N (logCutoff N) d -
            halfProductCoprimeMass num den N (logCutoff N) d / (Nat.totient d : ℝ)|) ≤
        (∑ ij ∈ actualGridIntersectingIndices num den N (logCutoff N)
            (1 + boundaryLogMesh k N),
          ∑ d ∈ Finset.Icc 1 D,
            |actualGridRectangleDiscrepancy (1 + boundaryLogMesh k N) ij N d|) +
          epsilon * singularNormalization N := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_sum_abs_logCutoff_halfProductDiscrepancy_le_actualGridRectangles
      hden hb hb1 hk epsilon hepsilon] with N hreduce
  intro D hD
  exact hreduce D (Finset.Icc 1 D) hD (fun _ h => h)

end

end ImbalancedChen
