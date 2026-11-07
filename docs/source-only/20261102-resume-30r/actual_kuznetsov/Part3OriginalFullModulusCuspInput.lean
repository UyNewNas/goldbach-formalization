import ImbalancedChen.Part3OriginalSignedTraceInput
import ImbalancedChen.Part3OriginalFullModulusAssembly

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

R20's actual whole-modulus row is now the matrix-defined arithmetic side
with the literal trace test.  Its bare c series is proved summable even
when the original beta or m weight vanishes.  No spectral expression or
trace equality is assumed.  All the needed original carriers remain.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalSimultaneousPrefixCompletion20261102
open ImbalancedChen.Part3.OriginalCompletedReciprocalSource20261102
open ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102
open ImbalancedChen.Part3.OriginalPrimaryPacketRows20261102
open ImbalancedChen.Part3.OriginalTwoZSourceAssembly20261102
open ImbalancedChen.Part3.OriginalTwoZFourierAssembly20261102
open ImbalancedChen.Part3.OriginalNonzeroCuspOneSource20261102
open ImbalancedChen.Part3.OriginalSignedTraceInput20261102
open ImbalancedChen.Part3.OriginalFullModulusSupport20261102
open ImbalancedChen.Part3.OriginalFullModulusAssembly20261102
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly (spectralTest)

namespace ImbalancedChen.Part3.OriginalFullModulusCuspInput20261102

attribute [local instance] Classical.propDecidable

/-- Bare normalized arithmetic trace summand, with the actual Gamma0 double
cosets of J, and R20's common admissible test.  c=0 never enters a cusp sum. -/
def bareCuspTerm (D : OriginalData) (k : BlockKey) (upper : Bool) (j : ℕ)
    (negativeM : Bool) (N : ℝ) (ell : D4 → ℤ) (z n p c : ℕ) : ℂ :=
  if hc : 0 < c ∧ c.Coprime z then
    letI : NeZero c := ⟨hc.1.ne'⟩
    cuspOneMatrixSum z c hc.2.symm (p : ℤ) (traceIndex D k negativeM z n) /
      (traceModulus z c : ℂ) *
        spectralTest ell (chartY0 D k upper j N)
          (4 * Real.pi * Real.sqrt ((p : ℝ) *
            ((traceIndex D k negativeM z n).natAbs : ℝ)) / traceModulus z c)
  else 0

/-- A true finite-support proof for the BARE trace side.  It does not divide
by beta, infer convergence from a zero multiplier, or alter the original test. -/
theorem bareCuspTerm_hasSum (D : OriginalData) (k : BlockKey) (upper : Bool)
    (J j : ℕ) (negativeM : Bool) {N : ℝ} (hN : 0 < N)
    (hNC : N ≤ 4 * D.cScale) (ha : D.block.atom.residue ≠ 0)
    (ell : D4 → ℤ) {z n p : ℕ} (hz : z ∈ chartLevels D k upper)
    (hn : n ∈ nCarrier D k z) (hp : p ∈ commonMBlock J j) :
    HasSum (bareCuspTerm D k upper j negativeM N ell z n p)
      (∑ c ∈ enlargedModuli D, bareCuspTerm D k upper j negativeM N ell z n p c) := by
  apply hasSum_sum_of_ne_finset_zero
  intro c hout
  unfold bareCuspTerm
  split_ifs with hc
  · letI : NeZero c := ⟨hc.1.ne'⟩
    have ht : spectralTest ell (chartY0 D k upper j N)
        (sourceArgument D k z n c p) = 0 := by
      by_contra hne
      have hb := spectralTest_modulus_support D k upper J j hN ha ell
        hz hn hp hc.1 hne
      exact hout (mem_Ioc.mpr ⟨hc.1, Nat.le_floor (by linarith)⟩)
    rw [← sourceArgument_eq_traceArgument D k negativeM z n c p, ht, mul_zero]
  · rfl

theorem bareCuspTerm_summable (D : OriginalData) (k : BlockKey) (upper : Bool)
    (J j : ℕ) (negativeM : Bool) {N : ℝ} (hN : 0 < N)
    (hNC : N ≤ 4 * D.cScale) (ha : D.block.atom.residue ≠ 0)
    (ell : D4 → ℤ) {z n p : ℕ} (hz : z ∈ chartLevels D k upper)
    (hn : n ∈ nCarrier D k z) (hp : p ∈ commonMBlock J j) :
    Summable (bareCuspTerm D k upper j negativeM N ell z n p) :=
  (bareCuspTerm_hasSum D k upper J j negativeM hN hNC ha ell hz hn hp).summable

/-- The exact original row, including beta and the common m character, is
the bare normalized trace input times its derived physical outside factor. -/
theorem fullModulusRow_eq_normalized_cusp_sum
    (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) (J j : ℕ) (negativeM : Bool)
    (M N : ℝ) (ell : D4 → ℤ) {z n p : ℕ}
    (hz : z ∈ chartLevels D k upper) :
    fullModulusRow D r k upper J j negativeM M N ell z n p =
      (((M * Real.sqrt (fixedZ D upper) : ℝ) : ℂ) *
        (commonPoissonCompleted J j (ell 1)).weight p *
        traceBeta D r k upper negativeM ell z n) *
          ∑' c : ℕ, bareCuspTerm D k upper j negativeM N ell z n p c := by
  rw [fullModulusRow, ← tsum_mul_left]
  apply tsum_congr
  intro c
  by_cases hc : 0 < c ∧ c.Coprime z
  · letI : NeZero c := ⟨hc.1.ne'⟩
    rw [if_pos hc, bareCuspTerm, dif_pos hc]
    exact original_chartModeAtom_eq_normalized_cuspOne
      D r k upper J j negativeM M N ell z n c p hz hc.2
  · rw [if_neg hc, bareCuspTerm, dif_neg hc, mul_zero]

/-- All original z/n/p indices, including their actual multiplicity, reach
the same normalized cusp test.  No spectral or Fourier sum is interchanged here. -/
theorem fullChartMode_eq_normalized_cusp_sums
    (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper : Bool) (J j : ℕ) (negativeM : Bool)
    (M N : ℝ) (ell : D4 → ℤ) :
    fullChartMode D r k upper J j negativeM M N ell =
      ∑ z ∈ chartLevels D k upper, ∑ n ∈ nCarrier D k z,
        ∑ p ∈ commonMBlock J j,
          (((M * Real.sqrt (fixedZ D upper) : ℝ) : ℂ) *
            (commonPoissonCompleted J j (ell 1)).weight p *
            traceBeta D r k upper negativeM ell z n) *
              ∑' c : ℕ, bareCuspTerm D k upper j negativeM N ell z n p c := by
  unfold fullChartMode
  apply sum_congr rfl
  intro z hz
  apply sum_congr rfl
  intro n hn
  apply sum_congr rfl
  intro p hp
  exact fullModulusRow_eq_normalized_cusp_sum D r k upper J j negativeM M N ell hz

end ImbalancedChen.Part3.OriginalFullModulusCuspInput20261102
end
