import ImbalancedChen.Part3OriginalTwoZFourierAssembly
import ImbalancedChen.Part3OriginalFrozenReciprocalMask
import ImbalancedChen.Part3ActualSixKernelCommonHardTail
import ImbalancedChen.Part3ActualCompletedHardTailMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual O/Q OriginalData, including its earlier common s frequency,
is connected to the existing six-kernel Schwartz tail.  The Q remainder
is split into its literal y=0, nonzero-y m=0, and nonzero-y outside-J
parts.  Only the last of these is estimated here.  In particular the
all-m y=0 source is not paid twice.

The hard radius is exactly J=ceil((C/B)*x^eps), with R=x^eps/10.
No spectral kernel, trace identity, or automorphic energy is a premise.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.CommonSmoothCutoff
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.HardCompletedSchwartz20261026b
open ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly
open ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
open ImbalancedChen.Part3.ActualCompletedChartSpectralCoefficientSourceOnly
open ImbalancedChen.Part3.ActualSixKernelCommonHardTailSourceOnly
open ImbalancedChen.Part3.ActualCompletedHardTailMass20261026b
open ImbalancedChen.Part3.OriginalFrozenReciprocalMask20261102
open ImbalancedChen.Part3.OriginalReciprocalPrefixDictionary20261102
open ImbalancedChen.Part3.OriginalSimultaneousPrefixCompletion20261102
open ImbalancedChen.Part3.OriginalCompletedReciprocalSource20261102
open ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102
open ImbalancedChen.Part3.OriginalPrimaryPacketRows20261102
open ImbalancedChen.Part3.OriginalPoissonPrimaryRows20261102
open ImbalancedChen.Part3.OriginalTwoZFourierAssembly20261102
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly

namespace ImbalancedChen.Part3.OriginalSixTailBinding20261102

attribute [local instance] Classical.propDecidable

/-- The two untruncated zero contributions in Q's literal remainder. -/
def pieceZeros (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (M N : ℝ) : ℂ :=
  jointMass D r M N (zeroSource (originalSource D)) +
    ∑ k ∈ originalKeys D,
      rowPairing D r k (zeroMKernel M N D.cScale D.block.atom.residue)

/-- Exactly the nonzero-y tail retained by Q, after all primary rows. -/
def pieceTail (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (J : ℕ) (M N : ℝ) : ℂ :=
  ∑ k ∈ originalKeys D,
    rowPairing D r k (tailKernel J M N D.cScale D.block.atom.residue)

def sixZeros (D : OriginalData) (r : ZMod (prefixPeriod D.key)) : ℂ :=
  pieceZeros D r D.bScale D.cScale +
    pieceZeros D r D.bScale (2 * D.cScale) +
    pieceZeros D r D.bScale (4 * D.cScale) +
    pieceZeros D r (2 * D.bScale) D.cScale +
    pieceZeros D r (2 * D.bScale) (2 * D.cScale) +
    pieceZeros D r (2 * D.bScale) (4 * D.cScale)

def sixTail (D : OriginalData) (r : ZMod (prefixPeriod D.key)) (J : ℕ) : ℂ :=
  pieceTail D r J D.bScale D.cScale +
    pieceTail D r J D.bScale (2 * D.cScale) +
    pieceTail D r J D.bScale (4 * D.cScale) +
    pieceTail D r J (2 * D.bScale) D.cScale +
    pieceTail D r J (2 * D.bScale) (2 * D.cScale) +
    pieceTail D r J (2 * D.bScale) (4 * D.cScale)

theorem pieceRemainder_eq_zeros_add_tail (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (J : ℕ) (M N : ℝ) :
    pieceRemainder D r J M N = pieceZeros D r M N + pieceTail D r J M N := by
  simp only [pieceRemainder, pieceZeros, pieceTail, sum_add_distrib]
  ring

theorem sixRemainder_eq_zeros_add_tail (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (J : ℕ) :
    sixRemainder D r J = sixZeros D r + sixTail D r J := by
  simp only [sixRemainder, sixZeros, sixTail, pieceRemainder_eq_zeros_add_tail]
  ring

/-- The already proved actual primary partition removes the apparent
primary/sign/dyadic multiplicity before any norm is taken. -/
theorem pieceTail_eq_original_source (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (J : ℕ) (M N : ℝ) :
    pieceTail D r J M N =
      ∑ s ∈ nonzeroSource (originalSource D), weight (D.lambda r) D.omega s *
        tailKernel J M N D.cScale D.block.atom.residue (output s) := by
  unfold pieceTail
  simp_rw [← original_source_block_eq_rows]
  exact (finite_source_assembly D.block.atom.residue (originalSource D)
    (fun s => weight (D.lambda r) D.omega s *
      tailKernel J M N D.cScale D.block.atom.residue (output s))).symm

/-- Both windows include zero exactly once and have identical endpoints.
This is equality of finite sets, not a comparison of tail estimates. -/
theorem globalCutoff_window_eq_commonHard (D : OriginalData) (x eps : ℝ) :
    mWindow (globalCutoff D x eps) =
      commonHardWindow D.cScale D.bScale (x ^ eps / 10) := by
  have harg : 10 * D.cScale * (x ^ eps / 10) / D.bScale =
      (D.cScale / D.bScale) * x ^ eps := by ring
  ext m
  rw [mem_mWindow_iff, commonHardWindow, mem_Icc, harg]
  change m.natAbs ≤ globalCutoff D x eps ↔
    -(globalCutoff D x eps : ℤ) ≤ m ∧ m ≤ (globalCutoff D x eps : ℤ)
  constructor
  · intro hm
    apply abs_le.mp
    simpa only [Int.natCast_natAbs] using
      (show (m.natAbs : ℤ) ≤ (globalCutoff D x eps : ℤ) by exact_mod_cast hm)
  · intro hm
    have habs := abs_le.mpr hm
    have hcast : (m.natAbs : ℤ) ≤ (globalCutoff D x eps : ℤ) := by
      simpa only [Int.natCast_natAbs] using habs
    exact_mod_cast hcast

private theorem poissonTail_eq_sub {c : ℕ} [NeZero c] {M : ℝ} (hM : 0 < M)
    (J : ℕ) (a y : ℤ) (z : ℕ) (hz : c.Coprime z) :
    poissonTail J M c a y (z : ℤ) =
      (∑' m : ℤ, frequency M c a y (z : ℤ) m) -
        ∑ m ∈ mWindow J, frequency M c a y (z : ℤ) m := by
  have hs : Summable (fun m : ℤ => frequency M c a y (z : ℤ) m) :=
    (completed_summable_norm (c := c) hM a y (z : ℤ)
      ((isUnit_intCast_iff_natAbs_coprime (c := c) (z : ℤ)).mpr
        (by simpa only [Int.natAbs_natCast] using hz.symm))).of_norm
  apply eq_sub_iff_add_eq.mpr
  simpa only [poissonTail, add_comm] using hs.sum_add_tsum_subtype_compl (mWindow J)

theorem original_tailKernel_eq_hard_difference (D : OriginalData) (x eps : ℝ)
    {M : ℝ} (hM : 0 < M) (N : ℝ) (zy : Output) :
    tailKernel (globalCutoff D x eps) M N D.cScale D.block.atom.residue zy =
      completedKernel M N D.cScale D.block.atom.residue zy -
        commonHardKernel M N D.cScale D.bScale (x ^ eps / 10)
          D.block.atom.residue zy := by
  unfold tailKernel weightedC completedKernel commonHardKernel
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro c hc
  by_cases hz : c.Coprime zy.1
  · letI : NeZero c := ⟨(mem_Ioc.mp hc).1.ne'⟩
    simp only [if_pos hz, ← mul_sub]
    rw [poissonTail_eq_sub hM _ _ _ _ hz, globalCutoff_window_eq_commonHard]
  · simp only [if_neg hz, sub_self]

/-- The exact Q tail is a difference of the existing six kernels on the
same signed original source.  All six M/N values remain literal. -/
theorem sixTail_eq_original_hard_difference (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (x eps : ℝ) :
    sixTail D r (globalCutoff D x eps) =
      ∑ s ∈ nonzeroSource (originalSource D), weight (D.lambda r) D.omega s *
        (sixKernel D.bScale D.cScale D.block.atom.residue (output s) -
          commonHardSixKernel D.bScale D.cScale (x ^ eps / 10)
            D.block.atom.residue (output s)) := by
  have hB2 : 0 < 2 * D.bScale := mul_pos (by norm_num) D.bScale_pos
  simp only [sixTail, pieceTail_eq_original_source,
    original_tailKernel_eq_hard_difference D x eps D.bScale_pos,
    original_tailKernel_eq_hard_difference D x eps hB2,
    sixKernel, commonHardSixKernel, mul_sub, mul_add, sum_add_distrib,
    sum_sub_distrib]
  ring

/-- Coefficient bounds are supplied by the original admissible atom,
the original polarization, and the actual common s-frequency character. -/
theorem original_lambda_norm_le_one {b : ℕ} {sigma kappa c0 : ℝ}
    (D : OriginalData) (hA : MediumAdmissible b sigma kappa c0 D.atom)
    (r : ZMod (prefixPeriod D.key)) (s : ℕ) : ‖D.lambda r s‖ ≤ 1 := by
  rw [OriginalData.lambda, completedLambda_norm]
  exact lambdaS_norm_le_one hA D.smoothLeft D.smoothRight D.polarS s

theorem original_sourceAbsMass_le_raw {b : ℕ} {sigma kappa c0 : ℝ}
    (D : OriginalData) (hA : MediumAdmissible b sigma kappa c0 D.atom)
    (r : ZMod (prefixPeriod D.key)) :
    sourceAbsMass (originalSource D) (D.lambda r) D.omega ≤
      rawLabelBudget D.sCarrier D.hBound D.fScale := by
  exact sourceAbsMass_le_rawLabelBudget 1 D.block.atom.residue
    D.sCarrier D.hBound D.fScale (D.lambda r) D.omega
    (fun s _ => original_lambda_norm_le_one D hA r s)
    (fun h _ => originalOmega_norm_le_one D.block D.rectangle h)

theorem original_nonzero_sourceAbsMass_le_raw {b : ℕ} {sigma kappa c0 : ℝ}
    (D : OriginalData) (hA : MediumAdmissible b sigma kappa c0 D.atom)
    (r : ZMod (prefixPeriod D.key)) :
    sourceAbsMass (nonzeroSource (originalSource D)) (D.lambda r) D.omega ≤
      rawLabelBudget D.sCarrier D.hBound D.fScale := by
  apply le_trans _ (original_sourceAbsMass_le_raw D hA r)
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    (fun _ _ _ => norm_nonneg _)

/-- One pre-source constant at every fixed Schwartz order. This consumes
the existing six-kernel theorem, and pays the actual source mass once.
Neither zero contribution is estimated or included on the left. -/
theorem original_sixTail_raw_bound (dord : ℕ) (hdord : 2 ≤ dord) :
    ∃ K : ℝ, 0 < K ∧ ∀ (b : ℕ) (sigma kappa c0 : ℝ)
      (D : OriginalData), MediumAdmissible b sigma kappa c0 D.atom →
      ∀ (r : ZMod (prefixPeriod D.key)) (x eps : ℝ), 0 < x →
      ‖sixTail D r (globalCutoff D x eps)‖ ≤
        K * (D.cScale ^ 2 * rawLabelBudget D.sCarrier D.hBound D.fScale) /
          (x ^ eps) ^ (dord - 1) := by
  obtain ⟨A, hA, hkernel⟩ := sixKernel_common_hard_tail dord hdord
  refine ⟨A * (10 : ℝ) ^ (dord - 1), by positivity, ?_⟩
  intro b sigma kappa c0 D hD r x eps hx
  let R : ℝ := x ^ eps / 10
  have hR : 0 < R := div_pos (Real.rpow_pos_of_pos hx _) (by norm_num)
  have hcap : 0 ≤ A * D.cScale ^ 2 / R ^ (dord - 1) := by positivity
  rw [sixTail_eq_original_hard_difference]
  calc
    _ ≤ ∑ s ∈ nonzeroSource (originalSource D),
        ‖weight (D.lambda r) D.omega s *
          (sixKernel D.bScale D.cScale D.block.atom.residue (output s) -
            commonHardSixKernel D.bScale D.cScale R
              D.block.atom.residue (output s))‖ := norm_sum_le _ _
    _ ≤ ∑ s ∈ nonzeroSource (originalSource D),
        ‖weight (D.lambda r) D.omega s‖ * (A * D.cScale ^ 2 / R ^ (dord - 1)) := by
      apply sum_le_sum
      intro s hs
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (hkernel D.cScale D.bScale R D.cScale_pos D.bScale_pos hR
          D.block.atom.residue (output s)) (norm_nonneg _)
    _ = (A * D.cScale ^ 2 / R ^ (dord - 1)) *
        sourceAbsMass (nonzeroSource (originalSource D)) (D.lambda r) D.omega := by
      unfold sourceAbsMass
      rw [← sum_mul]
      ring
    _ ≤ (A * D.cScale ^ 2 / R ^ (dord - 1)) *
        rawLabelBudget D.sCarrier D.hBound D.fScale :=
      mul_le_mul_of_nonneg_left (original_nonzero_sourceAbsMass_le_raw D hD r) hcap
    _ = _ := by
      dsimp [R]
      rw [div_pow]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hx eps)] <;> ring

end ImbalancedChen.Part3.OriginalSixTailBinding20261102
end
