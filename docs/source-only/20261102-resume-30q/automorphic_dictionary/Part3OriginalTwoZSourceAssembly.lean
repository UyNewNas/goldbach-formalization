import ImbalancedChen.Part3OriginalRowPhysicalScalar
import ImbalancedChen.Part3OriginalPoissonPrimaryRows

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The two Z scales are fixed from OriginalData before selecting a level,
quotient, modulus or Poisson frequency.  The actual level family is
partitioned at 2*S^2 with that boundary owned by the upper chart.  This
file assembles P's proved scalar identity over the entire original
z/n/c/p family.  The c-unit filter, signed complete sum and multiplicity
inside blockBeta are retained.  No automorphic identity is asserted.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.CommonSmoothCutoff
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
open ImbalancedChen.Part3.OriginalMaskedOuterEnergy20261102
open ImbalancedChen.Part3.OriginalSimultaneousPrefixCompletion20261102
open ImbalancedChen.Part3.OriginalCompletedReciprocalSource20261102
open ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102
open ImbalancedChen.Part3.OriginalPrimaryPacketRows20261102
open ImbalancedChen.Part3.OriginalPoissonPrimaryRows20261102
open ImbalancedChen.Part3.OriginalRowPhysicalScalar20261102
open ImbalancedChen.Part3.ActualNormalizedSmoothF
open ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly
open ImbalancedChen.P3ZActualPrimaryShortEndpoint
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly

namespace ImbalancedChen.Part3.OriginalTwoZSourceAssembly20261102

attribute [local instance] Classical.propDecidable

/-- Both scales are fixed before all arithmetic summation indices. -/
def fixedZ (D : OriginalData) (upper : Bool) : ℝ :=
  if upper then 2 * (scaleS D.key)^2 else (scaleS D.key)^2

def chartLevels (D : OriginalData) (k : BlockKey) (upper : Bool) : Finset ℕ :=
  (levelCarrier D k).filter (fun z =>
    if upper then 2 * (scaleS D.key)^2 ≤ (z : ℝ)
    else (z : ℝ) < 2 * (scaleS D.key)^2)

theorem fixedZ_pos (D : OriginalData) (upper : Bool) : 0 < fixedZ D upper := by
  have hS := scaleS_pos D.key
  cases upper <;> simp only [fixedZ, Bool.false_eq_true, if_false, if_true] <;>
    positivity

theorem chartLevels_subset (D : OriginalData) (k : BlockKey) (upper : Bool) :
    chartLevels D k upper ⊆ levelCarrier D k := filter_subset _ _

theorem chartLevels_disjoint (D : OriginalData) (k : BlockKey) :
    Disjoint (chartLevels D k false) (chartLevels D k true) := by
  apply disjoint_left.mpr
  intro z hl hu
  have hl' : (z : ℝ) < 2 * (scaleS D.key)^2 := (mem_filter.mp hl).2
  have hu' : 2 * (scaleS D.key)^2 ≤ (z : ℝ) := (mem_filter.mp hu).2
  exact (not_lt_of_ge hu') hl'

/-- Exact finite partition, including empty families and both endpoints. -/
theorem sum_levelCarrier_two_charts (D : OriginalData) (k : BlockKey)
    (F : ℕ → ℂ) :
    (∑ z ∈ levelCarrier D k, F z) =
      (∑ z ∈ chartLevels D k false, F z) +
        ∑ z ∈ chartLevels D k true, F z := by
  simpa only [chartLevels, Bool.false_eq_true, if_false, if_true, not_lt] using
    (sum_filter_add_sum_filter_not (levelCarrier D k)
      (fun z => (z : ℝ) < 2 * (scaleS D.key)^2) F).symm

theorem levelChart_eq_fixedZ (D : OriginalData) (k : BlockKey) (upper : Bool)
    {z : ℕ} (hz : z ∈ chartLevels D k upper) :
    levelChart D z = fixedZ D upper := by
  have hp := (mem_filter.mp hz).2
  cases upper
  · change (z : ℝ) < 2 * (scaleS D.key)^2 at hp
    simp only [levelChart, if_pos hp, fixedZ, Bool.false_eq_true, if_false]
  · change 2 * (scaleS D.key)^2 ≤ (z : ℝ) at hp
    simp only [levelChart, if_neg (not_lt_of_ge hp), fixedZ, if_true]

theorem chartLevels_normalized (D : OriginalData) (k : BlockKey) (upper : Bool)
    {z : ℕ} (hz : z ∈ chartLevels D k upper) :
    (z : ℝ) / fixedZ D upper ∈ Set.Icc (1 : ℝ) 2 := by
  rw [← levelChart_eq_fixedZ D k upper hz]
  exact levelCarrier_normalized D k (chartLevels_subset D k upper hz)

def sourceArgument (D : OriginalData) (k : BlockKey) (z n c p : ℕ) : ℝ :=
  spectralArgument D.block.atom.residue.natAbs p (k.1 * n : ℕ) z c

def chartY0 (D : OriginalData) (k : BlockKey) (upper : Bool) (j : ℕ) (N : ℝ) : ℝ :=
  spectralScale D.block.atom.residue.natAbs (2 ^ j : ℕ)
    (dyadicScale k.2.1) (fixedZ D upper) N

def chartScalar (D : OriginalData) (upper : Bool) (M : ℝ) (z c : ℕ) : ℂ :=
  ((M * Real.sqrt (fixedZ D upper) / ((c : ℝ) * Real.sqrt z) : ℝ) : ℂ)

/-- The original complete sum.  Neither signed index is replaced. -/
def sourceKloosterman (D : OriginalData) (k : BlockKey) (negativeM : Bool)
    (z n c p : ℕ) : ℂ :=
  kloosterman c (signedY negativeM p * inverseResidue c (z : ℤ))
    (D.block.atom.residue * (decode k z n).2)

def normalizedFrequency (D : OriginalData) (k : BlockKey) (upper : Bool)
    (j : ℕ) (negativeM : Bool) (M N : ℝ) (z n c p : ℕ) : ℂ :=
  (chartScalar D upper M z c *
    normalizedF ((2 ^ j : ℕ) * M / N) (if negativeM then -1 else 1)
      (point (sourceArgument D k z n c p / chartY0 D k upper j N)
        ((p : ℝ) / (2 ^ j : ℕ)) (((k.1 * n : ℕ) : ℝ) / dyadicScale k.2.1)
        ((z : ℝ) / fixedZ D upper))) *
    sourceKloosterman D k negativeM z n c p

/-- P's actual row-level theorem, now with a single fixed Z on its whole
chart.  All plateau hypotheses are proved from the original carriers. -/
theorem original_chart_frequency (D : OriginalData) (k : BlockKey)
    (upper : Bool) {z n c p : ℕ} (hz : z ∈ chartLevels D k upper)
    (hn : n ∈ nCarrier D k z) (J j : ℕ) (hp : p ∈ commonMBlock J j)
    (hc : c ∈ Ioc 0 (Nat.floor (10 * D.cScale)))
    (M N : ℝ) (hM : 0 < M) (hN : 0 < N) (negativeM : Bool)
    (ha : D.block.atom.residue ≠ 0) :
    (scaledDyadicCutoff N c : ℂ) *
        frequency M c D.block.atom.residue (decode k z n).2 (z : ℤ)
          (signedY negativeM p) =
      normalizedFrequency D k upper j negativeM M N z n c p := by
  have h := original_row_frequency_physical D k
    ⟨z, chartLevels_subset D k upper hz⟩ hn J j hp hc M N hM hN negativeM ha
  simpa only [normalizedFrequency, chartScalar, sourceArgument, chartY0,
    sourceKloosterman, levelChart_eq_fixedZ D k upper hz] using h

def sourceChartBlock (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) (J j : ℕ) (negativeM : Bool) (M N : ℝ) : ℂ :=
  ∑ z ∈ chartLevels D k upper, ∑ n ∈ nCarrier D k z,
    blockBeta D r k (decode k z n) *
      blockKernel J j negativeM M N D.cScale D.block.atom.residue (decode k z n)

def chartPhysical (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) (J j : ℕ) (negativeM : Bool) (M N : ℝ) : ℂ :=
  ∑ z ∈ chartLevels D k upper, ∑ n ∈ nCarrier D k z,
    ∑ c ∈ Ioc 0 (Nat.floor (10 * D.cScale)),
      if c.Coprime z then
        ∑ p ∈ commonMBlock J j,
          blockBeta D r k (decode k z n) *
            normalizedFrequency D k upper j negativeM M N z n c p
      else 0

/-- Actual whole-family normalized-F identity, with no comparison,
triangle inequality, arbitrary kernel or supplied dictionary premise. -/
theorem sourceChartBlock_eq_physical (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (upper : Bool)
    (J j : ℕ) (negativeM : Bool) (M N : ℝ) (hM : 0 < M) (hN : 0 < N)
    (ha : D.block.atom.residue ≠ 0) :
    sourceChartBlock D r k upper J j negativeM M N =
      chartPhysical D r k upper J j negativeM M N := by
  unfold sourceChartBlock chartPhysical
  apply sum_congr rfl
  intro z hz
  apply sum_congr rfl
  intro n hn
  change blockBeta D r k (decode k z n) *
      (∑ c ∈ Ioc 0 (Nat.floor (10 * D.cScale)),
        if c.Coprime z then (scaledDyadicCutoff N c : ℂ) *
          ∑ p ∈ commonMBlock J j,
            frequency M c D.block.atom.residue (decode k z n).2 (z : ℤ)
              (if negativeM then -(p : ℤ) else (p : ℤ))
        else 0) = _
  rw [mul_sum]
  apply sum_congr rfl
  intro c hc
  by_cases hcz : c.Coprime z
  · simp only [if_pos hcz, mul_sum]
    apply sum_congr rfl
    intro p hp
    exact congrArg (fun v : ℂ => blockBeta D r k (decode k z n) * v)
      (by simpa only [signedY] using
        original_chart_frequency D k upper hz hn J j hp hc M N hM hN negativeM ha)
  · simp only [if_neg hcz, mul_zero]

theorem rowPairing_block_eq_two_chartPhysical (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (J j : ℕ)
    (negativeM : Bool) (M N : ℝ) (hM : 0 < M) (hN : 0 < N)
    (ha : D.block.atom.residue ≠ 0) :
    rowPairing D r k (blockKernel J j negativeM M N D.cScale D.block.atom.residue) =
      chartPhysical D r k false J j negativeM M N +
        chartPhysical D r k true J j negativeM M N := by
  unfold rowPairing
  rw [sum_levelCarrier_two_charts]
  change sourceChartBlock D r k false J j negativeM M N +
    sourceChartBlock D r k true J j negativeM M N = _
  rw [sourceChartBlock_eq_physical D r k false J j negativeM M N hM hN ha,
    sourceChartBlock_eq_physical D r k true J j negativeM M N hM hN ha]

end ImbalancedChen.Part3.OriginalTwoZSourceAssembly20261102
end
