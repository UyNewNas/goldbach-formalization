import ImbalancedChen.Part3OriginalFullModulusSupport

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact replacement of the Q finite-c Fourier representation by a new
whole-positive-modulus Fourier representation. The two representations
agree AFTER the Fourier sum. They are not asserted equal mode by mode.
The existing signed Kloosterman sum, c-unit condition, both fixed Z's,
common completed-variable interval/phase and all three remainder lanes
are unchanged. No spectral trace or energy estimate is assumed.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
open ImbalancedChen.Part3.OriginalSimultaneousPrefixCompletion20261102
open ImbalancedChen.Part3.OriginalCompletedReciprocalSource20261102
open ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102
open ImbalancedChen.Part3.OriginalPrimaryPacketRows20261102
open ImbalancedChen.Part3.OriginalPoissonPrimaryRows20261102
open ImbalancedChen.Part3.OriginalTwoZSourceAssembly20261102
open ImbalancedChen.Part3.OriginalTwoZFourierAssembly20261102
open ImbalancedChen.Part3.OriginalFullModulusSupport20261102
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (actualCoeff)

namespace ImbalancedChen.Part3.OriginalFullModulusAssembly20261102

attribute [local instance] Classical.propDecidable

def enlargedChartPhysical (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) (J j : ℕ) (negativeM : Bool) (M N : ℝ) : ℂ :=
  ∑ z ∈ chartLevels D k upper, ∑ n ∈ nCarrier D k z,
    ∑ c ∈ enlargedModuli D,
      if c.Coprime z then
        ∑ p ∈ commonMBlock J j,
          blockBeta D r k (decode k z n) *
            normalizedFrequency D k upper j negativeM M N z n c p
      else 0

def enlargedChartMode (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) (J j : ℕ) (negativeM : Bool)
    (M N : ℝ) (ell : D4 → ℤ) : ℂ :=
  ∑ z ∈ chartLevels D k upper, ∑ n ∈ nCarrier D k z,
    ∑ c ∈ enlargedModuli D,
      if c.Coprime z then
        ∑ p ∈ commonMBlock J j,
          chartModeAtom D r k upper J j negativeM M N ell z n c p
      else 0

/-- The actual all-positive-modulus arithmetic row. The c=0 term is
excluded explicitly, with the original coprime restriction intact. -/
def fullModulusRow (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) (J j : ℕ) (negativeM : Bool)
    (M N : ℝ) (ell : D4 → ℤ) (z n p : ℕ) : ℂ :=
  ∑' c : ℕ, if 0 < c ∧ c.Coprime z then
    chartModeAtom D r k upper J j negativeM M N ell z n c p else 0

def fullChartMode (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) (J j : ℕ) (negativeM : Bool)
    (M N : ℝ) (ell : D4 → ℤ) : ℂ :=
  ∑ z ∈ chartLevels D k upper, ∑ n ∈ nCarrier D k z,
    ∑ p ∈ commonMBlock J j, fullModulusRow D r k upper J j negativeM M N ell z n p

/-- The full c series is genuinely summable: it has a proved common
finite support. No convergence or trace premise is supplied. -/
theorem fullModulusRow_hasSum (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) (J j : ℕ) (negativeM : Bool) (M : ℝ)
    {N : ℝ} (hN : 0 < N) (hNC : N ≤ 4 * D.cScale)
    (ha : D.block.atom.residue ≠ 0) (ell : D4 → ℤ) {z n p : ℕ}
    (hz : z ∈ chartLevels D k upper) (hn : n ∈ nCarrier D k z)
    (hp : p ∈ commonMBlock J j) :
    HasSum (fun c : ℕ => if 0 < c ∧ c.Coprime z then
      chartModeAtom D r k upper J j negativeM M N ell z n c p else 0)
      (∑ c ∈ enlargedModuli D, if c.Coprime z then
        chartModeAtom D r k upper J j negativeM M N ell z n c p else 0) := by
  have hs : HasSum (fun c : ℕ => if 0 < c ∧ c.Coprime z then
      chartModeAtom D r k upper J j negativeM M N ell z n c p else 0)
      (∑ c ∈ enlargedModuli D, if 0 < c ∧ c.Coprime z then
        chartModeAtom D r k upper J j negativeM M N ell z n c p else 0) := by
    apply hasSum_sum_of_ne_finset_zero
    intro c hout
    by_cases hc : 0 < c ∧ c.Coprime z
    · rw [if_pos hc]
      exact chartModeAtom_zero_outside_enlarged D r k upper J j negativeM M
        hN hNC ha ell hz hn hp hc.1 hout
    · exact if_neg hc
  convert hs using 1
  apply sum_congr rfl
  intro c hc
  have hc0 := (mem_Ioc.mp hc).1
  simp only [hc0, true_and]

theorem fullChartMode_eq_enlarged (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (upper : Bool)
    (J j : ℕ) (negativeM : Bool) (M : ℝ) {N : ℝ}
    (hN : 0 < N) (hNC : N ≤ 4 * D.cScale)
    (ha : D.block.atom.residue ≠ 0) (ell : D4 → ℤ) :
    fullChartMode D r k upper J j negativeM M N ell =
      enlargedChartMode D r k upper J j negativeM M N ell := by
  unfold fullChartMode enlargedChartMode
  apply sum_congr rfl
  intro z hz
  apply sum_congr rfl
  intro n hn
  calc
    _ = ∑ p ∈ commonMBlock J j, ∑ c ∈ enlargedModuli D,
        if c.Coprime z then
          chartModeAtom D r k upper J j negativeM M N ell z n c p else 0 := by
      apply sum_congr rfl
      intro p hp
      exact (fullModulusRow_hasSum D r k upper J j negativeM M hN hNC ha ell hz hn hp).tsum_eq
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro c hc
      by_cases hcz : c.Coprime z
      · simp only [if_pos hcz]
      · simp only [if_neg hcz, sum_const_zero]

/-- Enlarge before separating. Each NEW unseparated summand is zero
because of the original physical cutoff, including the N=4*C endpoint. -/
theorem enlargedChartPhysical_eq_original (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (upper : Bool)
    (J j : ℕ) (negativeM : Bool) (M : ℝ) {N : ℝ}
    (hN : 0 < N) (hNC : N ≤ 4 * D.cScale)
    (ha : D.block.atom.residue ≠ 0) :
    enlargedChartPhysical D r k upper J j negativeM M N =
      chartPhysical D r k upper J j negativeM M N := by
  unfold enlargedChartPhysical chartPhysical
  apply sum_congr rfl
  intro z hz
  apply sum_congr rfl
  intro n hn
  symm
  apply sum_subset (originalModuli_subset D)
  intro c hc hout
  by_cases hcz : c.Coprime z
  · rw [if_pos hcz]
    apply sum_eq_zero
    intro p hp
    rw [normalizedFrequency_zero_outside_original D k upper J j negativeM M
      hN hNC ha hz hn hp (mem_Ioc.mp hc).1 hout, mul_zero]
  · exact if_neg hcz

/-- The entire fixed-Z family has one actualCoeff, the same common
m interval and the same common additive phase. Finite c enlargement
is exchanged with Fourier using Q's actual pointwise HasSum. -/
theorem fullChart_hasSum (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) (J j L : ℕ) (negativeM : Bool) (M : ℝ)
    {N : ℝ} (hN : 0 < N) (hNC : N ≤ 4 * D.cScale)
    (ha : D.block.atom.residue ≠ 0) :
    HasSum (fun ell : D4 → ℤ =>
      actualCoeff ((2 ^ j : ℕ) * M / N) (if negativeM then -1 else 1) ell *
        fullChartMode D r k upper J j negativeM M N ell)
      (chartPhysical D r k upper J j negativeM M N) := by
  rw [← enlargedChartPhysical_eq_original D r k upper J j negativeM M hN hNC ha]
  have hc (z n c : ℕ) (hz : z ∈ chartLevels D k upper)
      (hn : n ∈ nCarrier D k z) :
      HasSum (fun ell : D4 → ℤ => if c.Coprime z then
        ∑ p ∈ commonMBlock J j,
          actualCoeff ((2 ^ j : ℕ) * M / N) (if negativeM then -1 else 1) ell *
            chartModeAtom D r k upper J j negativeM M N ell z n c p else 0)
        (if c.Coprime z then ∑ p ∈ commonMBlock J j,
          blockBeta D r k (decode k z n) *
            normalizedFrequency D k upper j negativeM M N z n c p else 0) := by
    by_cases hcz : c.Coprime z
    · simp only [if_pos hcz]
      exact hasSum_sum (s := commonMBlock J j) (fun p hp =>
        original_chart_atom_hasSum D r k upper J j L negativeM M N hz hn hp)
    · simp only [if_neg hcz]
      exact hasSum_zero
  have hs := hasSum_sum (s := chartLevels D k upper) (fun z hz =>
    hasSum_sum (s := nCarrier D k z) (fun n hn =>
      hasSum_sum (s := enlargedModuli D) (fun c _hc => hc z n c hz hn)))
  apply hs.congr_fun
  intro ell
  rw [fullChartMode_eq_enlarged D r k upper J j negativeM M hN hNC ha ell]
  simp only [enlargedChartMode, mul_sum, mul_ite, mul_zero]

/-- Q's modes and the new full-modulus modes need not agree separately.
Their WHOLE Fourier correction is exactly zero, with no absolute-error
budget and no endpoint subtraction defined from an unknown estimate. -/
theorem full_minus_capped_chart_hasSum_zero (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (upper : Bool)
    (J j L : ℕ) (negativeM : Bool) (M : ℝ) {N : ℝ}
    (hN : 0 < N) (hNC : N ≤ 4 * D.cScale)
    (ha : D.block.atom.residue ≠ 0) :
    HasSum (fun ell : D4 → ℤ =>
      actualCoeff ((2 ^ j : ℕ) * M / N) (if negativeM then -1 else 1) ell *
        (fullChartMode D r k upper J j negativeM M N ell -
          chartMode D r k upper J j negativeM M N ell)) 0 := by
  have h := (fullChart_hasSum D r k upper J j L negativeM M hN hNC ha).sub
    (chart_hasSum D r k upper J j L negativeM M N)
  simp only [sub_self] at h
  apply h.congr_fun
  intro ell
  exact mul_sub _ _ _

def fullBlockMode (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (J j : ℕ) (negativeM : Bool) (M N : ℝ) (ell : D4 → ℤ) : ℂ :=
  actualCoeff ((2 ^ j : ℕ) * M / N) (if negativeM then -1 else 1) ell *
    (fullChartMode D r k false J j negativeM M N ell +
      fullChartMode D r k true J j negativeM M N ell)

theorem fullBlock_hasSum (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (J j L : ℕ) (negativeM : Bool) {M N : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hNC : N ≤ 4 * D.cScale)
    (ha : D.block.atom.residue ≠ 0) :
    HasSum (fullBlockMode D r k J j negativeM M N)
      (rowPairing D r k (blockKernel J j negativeM M N D.cScale D.block.atom.residue)) := by
  rw [rowPairing_block_eq_two_chartPhysical D r k J j negativeM M N hM hN ha]
  have h := (fullChart_hasSum D r k false J j L negativeM M hN hNC ha).add
    (fullChart_hasSum D r k true J j L negativeM M hN hNC ha)
  apply h.congr_fun
  intro ell
  exact mul_add _ _ _

def fullPieceMode (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (J : ℕ) (M N : ℝ) (ell : D4 → ℤ) : ℂ :=
  ∑ k ∈ originalKeys D, ∑ j ∈ blockIndices J,
    (fullBlockMode D r k J j false M N ell + fullBlockMode D r k J j true M N ell)

theorem fullPiece_hasSum (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (J L : ℕ) {M N : ℝ} (hM : 0 < M) (hN : 0 < N)
    (hNC : N ≤ 4 * D.cScale) (ha : D.block.atom.residue ≠ 0) :
    HasSum (fullPieceMode D r J M N) (nonzeroBlocks D r J M N) := by
  exact hasSum_sum (s := originalKeys D) (fun k _hk =>
    hasSum_sum (s := blockIndices J) (fun j _hj =>
      (fullBlock_hasSum D r k J j L false hM hN hNC ha).add
        (fullBlock_hasSum D r k J j L true hM hN hNC ha)))

def fullSixMode (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (J : ℕ) (ell : D4 → ℤ) : ℂ :=
  fullPieceMode D r J D.bScale D.cScale ell +
    fullPieceMode D r J D.bScale (2 * D.cScale) ell +
    fullPieceMode D r J D.bScale (4 * D.cScale) ell +
    fullPieceMode D r J (2 * D.bScale) D.cScale ell +
    fullPieceMode D r J (2 * D.bScale) (2 * D.cScale) ell +
    fullPieceMode D r J (2 * D.bScale) (4 * D.cScale) ell

/-- The actual six-piece source, with its original global J and the
EXACT SAME Q sixRemainder. There is no new zero, tail or endpoint charge.
The existing zero-y/m=0/hard-tail estimates remain separate obligations. -/
theorem original_six_eq_remainder_and_full_modulus (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (x epsilon : ℝ) (L : ℕ)
    (ha : D.block.atom.residue ≠ 0) :
    let J := globalCutoff D x epsilon
    (smoothSix D r : ℂ) = sixRemainder D r J +
      ∑' ell : D4 → ℤ, fullSixMode D r J ell := by
  let J := globalCutoff D x epsilon
  change (smoothSix D r : ℂ) = sixRemainder D r J +
    ∑' ell : D4 → ℤ, fullSixMode D r J ell
  have hB2 : 0 < 2 * D.bScale := mul_pos (by norm_num) D.bScale_pos
  have hC2 : 0 < 2 * D.cScale := mul_pos (by norm_num) D.cScale_pos
  have hC4 : 0 < 4 * D.cScale := mul_pos (by norm_num) D.cScale_pos
  have hC14 : D.cScale ≤ 4 * D.cScale := by linarith [D.cScale_pos]
  have hC24 : 2 * D.cScale ≤ 4 * D.cScale := by linarith [D.cScale_pos]
  have hs := (((((fullPiece_hasSum D r J L D.bScale_pos D.cScale_pos hC14 ha).add
    (fullPiece_hasSum D r J L D.bScale_pos hC2 hC24 ha)).add
    (fullPiece_hasSum D r J L D.bScale_pos hC4 le_rfl ha)).add
    (fullPiece_hasSum D r J L hB2 D.cScale_pos hC14 ha)).add
    (fullPiece_hasSum D r J L hB2 hC2 hC24 ha)).add
    (fullPiece_hasSum D r J L hB2 hC4 le_rfl ha)
  have hsource := original_six_eq_primary_rows D r x epsilon
  dsimp only at hsource
  simp only [primaryRowPiece_eq_remainder_add_nonzero] at hsource
  calc
    (smoothSix D r : ℂ) = sixRemainder D r J +
        (nonzeroBlocks D r J D.bScale D.cScale +
          nonzeroBlocks D r J D.bScale (2 * D.cScale) +
          nonzeroBlocks D r J D.bScale (4 * D.cScale) +
          nonzeroBlocks D r J (2 * D.bScale) D.cScale +
          nonzeroBlocks D r J (2 * D.bScale) (2 * D.cScale) +
          nonzeroBlocks D r J (2 * D.bScale) (4 * D.cScale)) := by
      rw [hsource]
      dsimp only [sixRemainder, J]
      ring
    _ = _ := by
      congr 1
      exact hs.tsum_eq.symm

end ImbalancedChen.Part3.OriginalFullModulusAssembly20261102
end
