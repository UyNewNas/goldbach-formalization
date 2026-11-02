import ImbalancedChen.Part3OriginalPrimaryPacketRows
import ImbalancedChen.Part3OriginalCommonPoissonLanes
import ImbalancedChen.Part3ActualPoissonNormalizedFScalar

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The existing exact normalizedF scalar calculation is now applied to the
ACTUAL O/P level/n/m carriers.  The original level range [S^2,4*S^2] uses
two fixed charts; the level does not choose its own m interval.  The
signed Fourier argument, original Kloosterman indices, discrete modulus
c, outside factor M*sqrt(Z), and physical 4*pi argument remain literal.

This is NOT Kuznetsov: there is no replacement of the discrete c-sum by
a q integral, no Bessel kernel insertion and no automorphic coefficient
extraction.  Those are the remaining substantive source interface.
-/

noncomputable section
open Classical Finset
open scoped BigOperators SchwartzMap FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.CommonSmoothCutoff
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
open ImbalancedChen.Part3.OriginalMaskedOuterEnergy20261102
open ImbalancedChen.Part3.OriginalCompletedReciprocalSource20261102
open ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102
open ImbalancedChen.Part3.OriginalPrimaryPacketRows20261102
open ImbalancedChen.Part3.ActualNormalizedSmoothF
open ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly
open ImbalancedChen.P3ZActualPrimaryShortEndpoint
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly

namespace ImbalancedChen.Part3.OriginalRowPhysicalScalar20261102

attribute [local instance] Classical.propDecidable

/-- Exactly two level charts, with their shared boundary owned by the
upper chart.  No coefficient or Poisson frequency enters this choice. -/
def levelChart (D : OriginalData) (z : ℕ) : ℝ :=
  if (z : ℝ) < 2 * (scaleS D.key)^2 then (scaleS D.key)^2
  else 2 * (scaleS D.key)^2

theorem levelChart_pos (D : OriginalData) (z : ℕ) : 0 < levelChart D z := by
  have hS := scaleS_pos D.key
  unfold levelChart
  split_ifs <;> positivity

theorem levelCarrier_original_bounds (D : OriginalData) (k : BlockKey) {z : ℕ}
    (hz : z ∈ levelCarrier D k) :
    (scaleS D.key)^2 ≤ (z : ℝ) ∧ (z : ℝ) ≤ 4 * (scaleS D.key)^2 := by
  obtain ⟨zy, hzy, rfl⟩ := mem_image.mp hz
  obtain ⟨s, hs, rfl⟩ := mem_image.mp hzy
  have hso : s ∈ originalSource D :=
    (mem_filter.mp (block_subset D.block.atom.residue (originalSource D) k hs)).1
  have hb := original_output_bounds D hso
  exact ⟨hb.2.1, hb.2.2.1⟩

theorem levelCarrier_normalized (D : OriginalData) (k : BlockKey) {z : ℕ}
    (hz : z ∈ levelCarrier D k) :
    (z : ℝ) / levelChart D z ∈ Set.Icc (1 : ℝ) 2 := by
  have hb := levelCarrier_original_bounds D k hz
  have hS2 : 0 < (scaleS D.key)^2 := sq_pos_of_pos (scaleS_pos D.key)
  unfold levelChart
  split_ifs with hlow
  · exact ⟨(le_div_iff₀ hS2).mpr (by simpa only [one_mul] using hb.1),
      (div_le_iff₀ hS2).mpr hlow.le⟩
  · have hZ : 0 < 2 * (scaleS D.key)^2 := by positivity
    exact ⟨(le_div_iff₀ hZ).mpr (by simpa only [one_mul] using le_of_not_gt hlow),
      (div_le_iff₀ hZ).mpr (by nlinarith only [hb.2])⟩

theorem signed_m_real (negativeM : Bool) (M : ℝ) (c p : ℕ) :
    (M / (c : ℝ)) * ((signedY negativeM p : ℤ) : ℝ) =
      (if negativeM then (-1 : ℝ) else 1) * (M / (c : ℝ)) * (p : ℝ) := by
  cases negativeM <;> simp only [signedY, Bool.false_eq_true, if_false, if_true,
    Int.cast_natCast, Int.cast_neg] <;> ring

/-- Exact physical scalar identity on original arithmetic rows, with
the original complete sum unmodified.  M,N may be any of the six actual
positive b/c smooth scales.  No normalized-coordinate hypothesis is
supplied: all three are consequences of the actual finite carriers. -/
theorem original_row_frequency_physical (D : OriginalData) (k : BlockKey)
    (z : Row D k) {n p c : ℕ} (hn : n ∈ nCarrier D k z.val)
    (J j : ℕ) (hp : p ∈ commonMBlock J j)
    (hc : c ∈ Ioc 0 (Nat.floor (10 * D.cScale)))
    (M N : ℝ) (hM : 0 < M) (hN : 0 < N) (negativeM : Bool)
    (ha : D.block.atom.residue ≠ 0) :
    let V : ℝ := (2 ^ j : ℕ)
    let U : ℝ := dyadicScale k.2.1
    let Z : ℝ := levelChart D z.val
    let A : ℝ := D.block.atom.residue.natAbs
    let q := spectralArgument A p (k.1 * n : ℕ) z.val c
    let Y0 := spectralScale A V U Z N
    (scaledDyadicCutoff N c : ℂ) *
        frequency M c D.block.atom.residue (decode k z.val n).2 (z.val : ℤ)
          (signedY negativeM p) =
      (((M * Real.sqrt Z / ((c : ℝ) * Real.sqrt z.val) : ℝ) : ℂ) *
        normalizedF (V * M / N) (if negativeM then -1 else 1)
          (point (q / Y0) ((p : ℝ) / V) (((k.1 * n : ℕ) : ℝ) / U)
            ((z.val : ℝ) / Z))) *
        kloosterman c (signedY negativeM p * inverseResidue c (z.val : ℤ))
          (D.block.atom.residue * (decode k z.val n).2) := by
  dsimp only
  have hV : (0 : ℝ) < (2 ^ j : ℕ) := by positivity
  have hU := dyadicScale_pos k.2.1
  have hZ := levelChart_pos D z.val
  have hcR : (0 : ℝ) < c := by exact_mod_cast (mem_Ioc.mp hc).1
  have hpNorm : (p : ℝ) / (2 ^ j : ℕ) ∈ Set.Icc (1 : ℝ) 2 :=
    ⟨(commonMBlock_normalized J j hp).1, (commonMBlock_normalized J j hp).2.le⟩
  have hnNorm := nCarrier_normalized D k z.val hn
  have hzNorm := levelCarrier_normalized D k z.property
  have hA : (0 : ℝ) < D.block.atom.residue.natAbs := by
    exact_mod_cast Int.natAbs_pos.mpr ha
  have hpR : (0 : ℝ) < p := by
    have hh := (le_div_iff₀ hV).mp hpNorm.1
    linarith
  have hnData := nCarrier_positive_coprime D k z.val hn
  have hnR : (0 : ℝ) < ((k.1 * n : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hnData.1 hnData.2.1
  have hzR : (0 : ℝ) < z.val := by
    exact_mod_cast (levelCarrier_licensed D k z.property).1
  have hscalar := poisson_scalar_match hM hN hV hU hZ hcR
    hpNorm hnNorm hzNorm (if negativeM then (-1 : ℝ) else 1)
  rw [chart_eq_spectral_point hA hV hU hZ hN hcR hpR hnR hzR] at hscalar
  calc
    _ = ((((dyadicCutoff ((c : ℝ) / N) * poissonScale M c : ℝ) : ℂ) *
        (𝓕 dyadicCutoffSchwartz)
          ((if negativeM then (-1 : ℝ) else 1) * (M / (c : ℝ)) * (p : ℝ))) *
        kloosterman c (signedY negativeM p * inverseResidue c (z.val : ℤ))
          (D.block.atom.residue * (decode k z.val n).2)) := by
      simp only [frequency, scaledDyadicCutoff, Complex.real_smul,
        signed_m_real, poissonScale, Complex.ofReal_mul]
      ring
    _ = _ := by rw [hscalar]

end ImbalancedChen.Part3.OriginalRowPhysicalScalar20261102
end
