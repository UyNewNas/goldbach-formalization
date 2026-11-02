import ImbalancedChen.Part3OriginalTwoZFourierAssembly
import ImbalancedChen.Part3ActualWeightedSpectralBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual chi test is retained. First enlarge the UNSEPARATED source;
only then is its Fourier reconstruction summed on the enlarged carrier.
Every separated test has a common finite modulus support, independent of
the Fourier mode. This supplies the all-positive-modulus association,
without asserting that Q's individual capped modes equal full modes.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.CommonSmoothCutoff
open ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
open ImbalancedChen.Part3.OriginalMaskedOuterEnergy20261102
open ImbalancedChen.Part3.OriginalSimultaneousPrefixCompletion20261102
open ImbalancedChen.Part3.OriginalCompletedReciprocalSource20261102
open ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102
open ImbalancedChen.Part3.OriginalPrimaryPacketRows20261102
open ImbalancedChen.Part3.OriginalPoissonPrimaryRows20261102
open ImbalancedChen.Part3.OriginalRowPhysicalScalar20261102
open ImbalancedChen.Part3.OriginalTwoZSourceAssembly20261102
open ImbalancedChen.Part3.OriginalTwoZFourierAssembly20261102
open ImbalancedChen.Part3.ActualNormalizedSmoothF
open ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly
open P3NativePeriod64SamplingSourceOnly (D4)
open P3Period64NativeReconstructionSourceOnly
  (actualCoeff spectralTest spectralMode chi chi_tsupport_subset
    spectralMode_support_subset spectralTest_contDiff)

namespace ImbalancedChen.Part3.OriginalFullModulusSupport20261102

attribute [local instance] Classical.propDecidable

/-- A common enlargement for ALL six original c scales. It is chosen
before z,n,p,j, either sign, either Z chart, and the Fourier mode. -/
def enlargedModuli (D : OriginalData) : Finset ℕ :=
  Ioc 0 (Nat.floor (128 * D.cScale))

theorem originalModuli_subset (D : OriginalData) :
    Ioc 0 (Nat.floor (10 * D.cScale)) ⊆ enlargedModuli D := by
  intro c hc
  exact mem_Ioc.mpr ⟨(mem_Ioc.mp hc).1,
    (mem_Ioc.mp hc).2.trans (Nat.floor_mono (by linarith [D.cScale_pos]))⟩

/-- The actual upper cutoff 5/2, rather than the older convenient 3,
is essential for the N=4*C member of the six-piece family. -/
theorem cutoff_zero_outside_original (D : OriginalData) {N : ℝ}
    (hN : 0 < N) (hNC : N ≤ 4 * D.cScale) {c : ℕ} (hc : 0 < c)
    (hout : c ∉ Ioc 0 (Nat.floor (10 * D.cScale))) :
    scaledDyadicCutoff N c = 0 := by
  by_contra hn
  have hb := cutoff_nonzero_bounds (show dyadicCutoff ((c : ℝ) / N) ≠ 0 from hn)
  have hupper := (div_le_iff₀ hN).mp hb.2
  exact hout (mem_Ioc.mpr ⟨hc, Nat.le_floor (by linarith)⟩)

theorem original_spectral_scale_pos (D : OriginalData) (k : BlockKey)
    (upper : Bool) (j : ℕ) {N : ℝ} (hN : 0 < N)
    (ha : D.block.atom.residue ≠ 0) : 0 < chartY0 D k upper j N := by
  have hA : (0 : ℝ) < D.block.atom.residue.natAbs := by
    exact_mod_cast Int.natAbs_pos.mpr ha
  have hV : (0 : ℝ) < (2 ^ j : ℕ) := by positivity
  have hU := dyadicScale_pos k.2.1
  have hZ := fixedZ_pos D upper
  unfold chartY0 spectralScale
  positivity

/-- The exact normalized coordinate, now valid at EVERY positive c.
Only P's unnecessary upper-c premise is removed; the scalar identity
itself is reused from the production physical-coordinate theorem. -/
theorem original_spectral_coordinate (D : OriginalData) (k : BlockKey)
    (upper : Bool) (J j : ℕ) {N : ℝ} (hN : 0 < N)
    (ha : D.block.atom.residue ≠ 0) {z n c p : ℕ}
    (hz : z ∈ chartLevels D k upper) (hn : n ∈ nCarrier D k z)
    (hp : p ∈ commonMBlock J j) (hc : 0 < c) :
    sourceArgument D k z n c p / chartY0 D k upper j N =
      chartT ((c : ℝ) / N) ((p : ℝ) / (2 ^ j : ℕ))
        (((k.1 * n : ℕ) : ℝ) / dyadicScale k.2.1)
        ((z : ℝ) / fixedZ D upper) := by
  have hV : (0 : ℝ) < (2 ^ j : ℕ) := by positivity
  have hU := dyadicScale_pos k.2.1
  have hZ := fixedZ_pos D upper
  have hA : (0 : ℝ) < D.block.atom.residue.natAbs := by
    exact_mod_cast Int.natAbs_pos.mpr ha
  have hpR : (0 : ℝ) < p := by
    have hb := (le_div_iff₀ hV).mp (commonMBlock_normalized J j hp).1
    linarith
  have hnData := nCarrier_positive_coprime D k z hn
  have hnR : (0 : ℝ) < ((k.1 * n : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hnData.1 hnData.2.1
  have hzR : (0 : ℝ) < z := by
    exact_mod_cast (levelCarrier_licensed D k (chartLevels_subset D k upper hz)).1
  exact spectral_argument_normalized hA hV hU hZ hN
    (by exact_mod_cast hc) hpR hnR hzR

/-- The unseparated physical source really vanishes on every newly
adjoined modulus. No Fourier mode is individually declared zero here. -/
theorem normalizedFrequency_zero_outside_original (D : OriginalData)
    (k : BlockKey) (upper : Bool) (J j : ℕ) (negativeM : Bool) (M : ℝ)
    {N : ℝ} (hN : 0 < N) (hNC : N ≤ 4 * D.cScale)
    (ha : D.block.atom.residue ≠ 0) {z n c p : ℕ}
    (hz : z ∈ chartLevels D k upper) (hn : n ∈ nCarrier D k z)
    (hp : p ∈ commonMBlock J j) (hc : 0 < c)
    (hout : c ∉ Ioc 0 (Nat.floor (10 * D.cScale))) :
    normalizedFrequency D k upper j negativeM M N z n c p = 0 := by
  have hzero := cutoff_zero_outside_original D hN hNC hc hout
  have hpN := commonMBlock_normalized J j hp
  have hnN := nCarrier_normalized D k z hn
  have hzN := chartLevels_normalized D k upper hz
  have hcoord := original_spectral_coordinate D k upper J j hN ha hz hn hp hc
  have hf : normalizedF ((2 ^ j : ℕ) * M / N) (if negativeM then -1 else 1)
      (point (sourceArgument D k z n c p / chartY0 D k upper j N)
        ((p : ℝ) / (2 ^ j : ℕ)) (((k.1 * n : ℕ) : ℝ) / dyadicScale k.2.1)
        ((z : ℝ) / fixedZ D upper)) = 0 := by
    rw [hcoord]
    change normalizedF _ _ (chart ((c : ℝ) / N) _ _ _) = 0
    rw [normalizedF_chart (div_pos (by exact_mod_cast hc) hN)
      ⟨hpN.1, hpN.2.le⟩ hnN hzN]
    change (((Real.sqrt ((z : ℝ) / fixedZ D upper) *
      scaledDyadicCutoff N c : ℝ) : ℂ) * _) = 0
    simp only [hzero, mul_zero, Complex.ofReal_zero, zero_mul]
  simp only [normalizedFrequency, hf, mul_zero, zero_mul]

private theorem chartT_upper {u v w z : ℝ} (hu : 0 < u)
    (hv : v ∈ Set.Icc (1 : ℝ) 2) (hw : w ∈ Set.Icc (1 : ℝ) 2)
    (hz : z ∈ Set.Icc (1 : ℝ) 2) : chartT u v w z ≤ 2 / u := by
  have hz0 : 0 < z := by linarith [hz.1]
  have hv0 : 0 ≤ v := by linarith [hv.1]
  have hw0 : 0 ≤ w := by linarith [hw.1]
  have hprod : v * w ≤ 4 := by
    have h := mul_le_mul hv.2 hw.2 hw0 (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hquot : v * w / z ≤ 4 := (div_le_iff₀ hz0).mpr (by linarith [hz.1])
  have hroot : Real.sqrt (v * w / z) ≤ 2 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mp
    rw [Real.sq_sqrt (by positivity : 0 ≤ v * w / z)]
    nlinarith
  exact div_le_div_of_nonneg_right hroot hu.le

/-- Each actual separated test has c<32*N, independent of ell,z,n,p,
both signs and both fixed Z charts. This is AFTER common enlargement. -/
theorem spectralTest_modulus_support (D : OriginalData) (k : BlockKey)
    (upper : Bool) (J j : ℕ) {N : ℝ} (hN : 0 < N)
    (ha : D.block.atom.residue ≠ 0) (ell : D4 → ℤ) {z n c p : ℕ}
    (hz : z ∈ chartLevels D k upper) (hn : n ∈ nCarrier D k z)
    (hp : p ∈ commonMBlock J j) (hc : 0 < c)
    (hne : spectralTest ell (chartY0 D k upper j N)
      (sourceArgument D k z n c p) ≠ 0) : (c : ℝ) < 32 * N := by
  have ht := spectralMode_support_subset ell hne
  have hcoord := original_spectral_coordinate D k upper J j hN ha hz hn hp hc
  change (sourceArgument D k z n c p / chartY0 D k upper j N) ∈
    Set.Ioo (1 / 16 : ℝ) 16 at ht
  have hpN := commonMBlock_normalized J j hp
  have hu : 0 < (c : ℝ) / N := div_pos (by exact_mod_cast hc) hN
  have hupper := chartT_upper hu ⟨hpN.1, hpN.2.le⟩
    (nCarrier_normalized D k z hn) (chartLevels_normalized D k upper hz)
  rw [← hcoord] at hupper
  have hratio : (1 / 16 : ℝ) < 2 / ((c : ℝ) / N) := ht.1.trans_le hupper
  have hh := (lt_div_iff₀ hu).mp hratio
  have hdiv : (c : ℝ) / N < 32 := by linarith
  exact (div_lt_iff₀ hN).mp hdiv

theorem chartModeAtom_zero_outside_enlarged (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (upper : Bool)
    (J j : ℕ) (negativeM : Bool) (M : ℝ) {N : ℝ}
    (hN : 0 < N) (hNC : N ≤ 4 * D.cScale)
    (ha : D.block.atom.residue ≠ 0) (ell : D4 → ℤ) {z n c p : ℕ}
    (hz : z ∈ chartLevels D k upper) (hn : n ∈ nCarrier D k z)
    (hp : p ∈ commonMBlock J j) (hc : 0 < c)
    (hout : c ∉ enlargedModuli D) :
    chartModeAtom D r k upper J j negativeM M N ell z n c p = 0 := by
  have ht : spectralTest ell (chartY0 D k upper j N)
      (sourceArgument D k z n c p) = 0 := by
    by_contra hne
    have hb := spectralTest_modulus_support D k upper J j hN ha ell hz hn hp hc hne
    exact hout (mem_Ioc.mpr ⟨hc, Nat.le_floor (by linarith)⟩)
  simp only [chartModeAtom, ht, mul_zero, zero_mul]

/-- Positive compact support and global smooth zero-extension for the
LITERAL test passed to normalized Kuznetsov. -/
theorem spectralTest_support (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) :
    Function.support (spectralTest ell Y) ⊆ Set.Ioo (Y / 16) (16 * Y) := by
  intro q hq
  have ht := spectralMode_support_subset ell hq
  change q / Y ∈ Set.Ioo (1 / 16 : ℝ) 16 at ht
  exact ⟨by have := (lt_div_iff₀ hY).mp ht.1; linarith,
    (div_lt_iff₀ hY).mp ht.2⟩

theorem spectralTest_tsupport (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) :
    tsupport (spectralTest ell Y) ⊆ Set.Icc (Y / 16) (16 * Y) := by
  exact closure_minimal (fun q hq =>
    ⟨(spectralTest_support ell hY hq).1.le, (spectralTest_support ell hY hq).2.le⟩)
    isClosed_Icc

theorem spectralTest_compact (ell : D4 → ℤ) {Y : ℝ} (hY : 0 < Y) :
    HasCompactSupport (spectralTest ell Y) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (spectralTest_tsupport ell hY)

theorem spectralTest_zero_at_ends (ell : D4 → ℤ) {Y q : ℝ} (hY : 0 < Y)
    (hq : q ≤ Y / 16 ∨ 16 * Y ≤ q) : spectralTest ell Y q = 0 := by
  by_contra hne
  have hs := spectralTest_support ell hY hne
  rcases hq with hq | hq <;> linarith [hs.1, hs.2]

theorem original_trace_test_admissible (D : OriginalData) (k : BlockKey)
    (upper : Bool) (j : ℕ) {N : ℝ} (hN : 0 < N)
    (ha : D.block.atom.residue ≠ 0) (ell : D4 → ℤ) :
    ContDiff ℝ ∞ (spectralTest ell (chartY0 D k upper j N)) ∧
    HasCompactSupport (spectralTest ell (chartY0 D k upper j N)) ∧
    tsupport (spectralTest ell (chartY0 D k upper j N)) ⊆
      Set.Icc (chartY0 D k upper j N / 16) (16 * chartY0 D k upper j N) := by
  have hY := original_spectral_scale_pos D k upper j hN ha
  exact ⟨spectralTest_contDiff ell _, spectralTest_compact ell hY,
    spectralTest_tsupport ell hY⟩

/-- All polynomial mode weights are the already paid native Fourier
weights. The common enlargement introduces no new mode or derivative
factor, and this statement does not assert a spectral energy bound. -/
theorem actual_mode_weight_summable (rho sigma : ℝ) (order : ℕ) :
    Summable (fun ell : D4 → ℤ =>
      ‖actualCoeff rho sigma ell‖ * (1 + |(ell 0 : ℝ)|) ^ order) := by
  simpa only [actualCoeff, P3ActualSampledLatticeSourceOnly.testWeight] using
    (P3ActualSampledLatticeSourceOnly.actual_normalizedF_weighted_l1 rho sigma order).1

end ImbalancedChen.Part3.OriginalFullModulusSupport20261102
end
