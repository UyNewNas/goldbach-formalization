import ImbalancedChen.P3ActualWeightedFibreInjective
import ImbalancedChen.P3ActualFineLabelThreeGammaTensor

/-!
P3.6 — bounded ORIGINAL group-tuple Fourier multipliers.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

A separated Fourier mode may depend on the ORDERED coordinates inside one
physical group, even when two coordinates share the same fine prime label.
It must not be replaced by a function of the complete group product without
an actual invariance argument.

The literal label factorial M_j is kept. The new normalized weighted fibre
has absolute value at most the EXISTING nonnegative fine-label gamma, hence
at most one on the disjoint prime-label domain. This proves a genuine local
coefficient bound for positional group multipliers, not a PP estimate.

The original complete W_T still has to be represented as a product of THREE
such group multipliers and charged by a uniform Fourier L1 norm.
-/

namespace ImbalancedChen.P3ActualBoundedGroupWeightGamma
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P5Z.ActualNormalizedPrimeLabelCoefficient

/-- The original group normalization M_j = product of per-label factorials.
Unlike gamma itself, the multiplier v may depend on the ordered prime tuple. -/
def weightedLabelGamma (B : ℕ → Finset ℕ) (blocks : List (ℕ × ℕ))
    (v : List ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ ps ∈ (actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)).filter
      (fun ps => ps.prod = n), v ps) /
    (actualPrimeLabelBlocksFactorial blocks : ℝ)

/-- Every bounded positional group weight is dominated by the TRUE
nonnegative unweighted group gamma, at every integer (including diagonals).
No assumption that v is constant on full-product fibres is made. -/
theorem weightedLabelGamma_abs_le_gamma
    (B : ℕ → Finset ℕ) (blocks : List (ℕ × ℕ))
    (v : List ℕ → ℝ)
    (hv : ∀ ps ∈ actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks),
      |v ps| ≤ 1) (n : ℕ) :
    |weightedLabelGamma B blocks v n| ≤ gamma B blocks n := by
  let T := actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)
  let F := T.filter (fun ps => ps.prod = n)
  have hmass : |∑ ps ∈ F, v ps| ≤ (F.card : ℝ) := by
    calc
      _ ≤ ∑ ps ∈ F, |v ps| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ps ∈ F, (1 : ℝ) := Finset.sum_le_sum (by
        intro ps hps
        exact hv ps (Finset.mem_filter.mp hps).1)
      _ = (F.card : ℝ) := by simp
  have hM : (0 : ℝ) < (actualPrimeLabelBlocksFactorial blocks : ℝ) := by
    exact_mod_cast actualPrimeLabelBlocksFactorial_pos blocks
  have hdiv : |∑ ps ∈ F, v ps| /
      (actualPrimeLabelBlocksFactorial blocks : ℝ) ≤
      (F.card : ℝ) / (actualPrimeLabelBlocksFactorial blocks : ℝ) :=
    (div_le_div_iff_of_pos_right hM).2 hmass
  simpa only [weightedLabelGamma, gamma, actualPrimeTupleCoefficient,
    T, F, abs_div, abs_of_pos hM] using hdiv

/-- This is the required genuine one-bound for each of the three groups
whenever its literal fine-label intervals are pairwise disjoint. -/
theorem weightedLabelGamma_abs_le_one
    (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) (hτ : 0 ≤ τ)
    (blocks : List (ℕ × ℕ))
    (hlabels : blocks.Pairwise (fun b d => b.1 ≠ d.1))
    (v : List ℕ → ℝ)
    (hv : ∀ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
      (actualPrimeLabelBlocksWord blocks), |v ps| ≤ 1)
    (n : ℕ) :
    |weightedLabelGamma (actualPrimeFineLabelFinset N τ) blocks v n| ≤ 1 := by
  have hdom := weightedLabelGamma_abs_le_gamma
    (actualPrimeFineLabelFinset N τ) blocks v hv n
  have hgamma := ImbalancedChen.P3ActualFineLabelThreeGammaTensor.fine_gamma_mem_Icc
    N hN τ hτ blocks hlabels n
  exact hdom.trans hgamma.2

/-- Exact fibre transport for arbitrary ordered group multipliers.
No tuple permutation or product-dependent-weight licence is used. -/
theorem weightedLabelGamma_sum_by_product
    (B : ℕ → Finset ℕ) (blocks : List (ℕ × ℕ))
    (v : List ℕ → ℝ) (H : ℕ → ℝ) :
    (∑ ps ∈ actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks),
      v ps * H ps.prod) /
      (actualPrimeLabelBlocksFactorial blocks : ℝ) =
    ∑ n ∈ (actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)).image List.prod,
      weightedLabelGamma B blocks v n * H n := by
  let T := actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)
  change (∑ ps ∈ T, v ps * H ps.prod) /
      (actualPrimeLabelBlocksFactorial blocks : ℝ) =
    ∑ n ∈ T.image List.prod, weightedLabelGamma B blocks v n * H n
  rw [weighted_sum_by_product T v H, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp [weightedLabelGamma]
  ring

/-- A true group-product Fourier twist reduces to the old gamma times its
character. This reduction is NOT allowed for a general positional twist. -/
theorem weightedLabelGamma_of_product_twist
    (B : ℕ → Finset ℕ) (blocks : List (ℕ × ℕ))
    (f : ℕ → ℝ) (n : ℕ) :
    weightedLabelGamma B blocks (fun ps => f ps.prod) n =
      gamma B blocks n * f n := by
  let T := actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)
  let F := T.filter (fun ps => ps.prod = n)
  have hf : (∑ ps ∈ F, f ps.prod) = (F.card : ℝ) * f n := by
    calc
      _ = ∑ ps ∈ F, f n := by
        apply Finset.sum_congr rfl
        intro ps hps
        rw [(Finset.mem_filter.mp hps).2]
      _ = _ := by simp
  change (∑ ps ∈ F, f ps.prod) /
      (actualPrimeLabelBlocksFactorial blocks : ℝ) =
    ((F.card : ℝ) / (actualPrimeLabelBlocksFactorial blocks : ℝ)) * f n
  rw [hf]
  ring

/-- Finite Fourier mode addition is linear BEFORE applying the Fourier
L1 norm. This is not an H^m count of modes. -/
theorem weightedLabelGamma_add
    (B : ℕ → Finset ℕ) (blocks : List (ℕ × ℕ))
    (v w : List ℕ → ℝ) (n : ℕ) :
    weightedLabelGamma B blocks (fun ps => v ps + w ps) n =
      weightedLabelGamma B blocks v n +
        weightedLabelGamma B blocks w n := by
  unfold weightedLabelGamma
  simp only [Finset.sum_add_distrib]
  ring

end
end ImbalancedChen.P3ActualBoundedGroupWeightGamma
