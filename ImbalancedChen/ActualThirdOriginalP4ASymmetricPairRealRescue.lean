import ImbalancedChen.ActualThirdOriginalP4ASymmetricSafeChordDirection
import ImbalancedChen.ActualThirdOriginalP4ASymmetricBranchPermutation

/-!
SOURCEONLY / UNCOMPILED / HOLD_ELABORATION / OPEN30.
The original selected label, OLD chord, queries, constants and tie order are
preserved. A paired tent is used only as a real cap minorant on the ordered
prism. In particular xz/fall is rescued by the actual yz/fall supplier.
No integral estimate, K allowance or selector change is a hypothesis.
-/
namespace ImbalancedChen.OriginalThirdP4ASymmetricPairRealRescue

noncomputable section
open Set MeasureTheory
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdTriangleMomentsSourceOnly OriginalThirdSymmetricJensenSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdRoundedStoredConsumerSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly
open OriginalThirdP4ASymmetricTentPrerequisites
open OriginalThirdP4ASymmetricSafeChordDirection
open OriginalThirdP4ASymmetricBranchPermutationSourceOnly

theorem swapXY_symmetricLeft (a c : ℝ) :
    swapXY (symmetricLeft a c)=symmetricLeft a c := by
  exact swapXY_symmetric_endpoint a c

theorem swapXY_symmetricRight (b d : ℝ) :
    swapXY (symmetricRight b d)=symmetricRight b d := by
  exact swapXY_symmetric_endpoint b d

theorem symmetric_active_swap_iff (s : TentSum) (k : TentSide) (a b c d : ℝ) :
    sourceActive (swapSum s) k (symmetricLeft a c) (symmetricRight b d) ↔
      sourceActive s k (symmetricLeft a c) (symmetricRight b d) := by
  simpa only [swapXY_symmetricLeft,swapXY_symmetricRight] using
    sourceActive_swap_iff s k (symmetricLeft a c) (symmetricRight b d)

theorem symmetric_root_swap (s : TentSum) (k : TentSide) (a b c d : ℝ) :
    planeUpper (swapSum s) k (symmetricLeft a c) (symmetricRight b d)=
      planeUpper s k (symmetricLeft a c) (symmetricRight b d) := by
  simpa only [swapXY_symmetricLeft,swapXY_symmetricRight] using
    planeUpper_swap s k (symmetricLeft a c) (symmetricRight b d)

theorem symmetric_residual_swap (s : TentSum) (k : TentSide) (b d : ℝ) :
    oldNumerator (swapSum s) k (symmetricRight b d)=
      oldNumerator s k (symmetricRight b d) := by
  simpa only [swapXY_symmetricRight] using oldNumerator_swap s k (symmetricRight b d)

theorem symmetric_low_swap (s : TentSum) (k : TentSide) (b d : ℝ) :
    tentOldLow (swapSum s) k (symmetricRight b d)=
      tentOldLow s k (symmetricRight b d) := by
  simpa only [swapXY_symmetricRight] using tentOldLow_swap s k (symmetricRight b d)

theorem symmetric_high_swap (s : TentSum) (k : TentSide) (a c : ℝ) :
    tentOldHigh (swapSum s) k (symmetricLeft a c)=
      tentOldHigh s k (symmetricLeft a c) := by
  simpa only [swapXY_symmetricLeft] using tentOldHigh_swap s k (symmetricLeft a c)

/-- Producer square mean only: this does not assert equality of the two
ordered-triangle means or symmetry of the actual cap. -/
theorem symmetric_producer_mean_swap (s : TentSum) (k : TentSide) (a b c d : ℝ) :
    tentOldMean (swapSum s) k (symmetricLeft a c) (symmetricRight b d)=
      tentOldMean s k (symmetricLeft a c) (symmetricRight b d) := by
  have hxy : boxEX (symmetricLeft a c) (symmetricRight b d)=
      boxEY (symmetricLeft a c) (symmetricRight b d) := rfl
  simp only [tentOldMean,oldX_swapSum,oldY_swapSum,oldZ_swapSum,←hxy]
  ring

theorem symmetric_producer_chord_swap (s : TentSum) (k : TentSide)
    (a b c d flo fhi : ℝ) :
    tentOldChord (swapSum s) k (symmetricLeft a c) (symmetricRight b d) flo fhi=
      tentOldChord s k (symmetricLeft a c) (symmetricRight b d) flo fhi := by
  simp only [tentOldChord,symmetric_producer_mean_swap,symmetric_low_swap,
    symmetric_high_swap]

/-- The source-selected chord is exactly the paired chord. The latter is
bounded by its genuine ordered mean and then by the actual OLD integral. -/
theorem paired_producer_chord_le_actual_integral
    {s : TentSum} {k : TentSide} (hs : SafeAsymmetricTent (swapSum s) k)
    {a b c d flo fhi : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu)
    (hactive : sourceActive s k (symmetricLeft a c) (symmetricRight b d))
    (hroot : planeUpper s k (symmetricLeft a c) (symmetricRight b d)≤thirdPrefixTheta)
    (hres : 0<oldNumerator s k (symmetricRight b d))
    (hlo : 2≤tentOldLow s k (symmetricRight b d))
    (hfl : flo≤actualExtendedThirdLowerFactor (tentOldLow s k (symmetricRight b d)))
    (hfh : fhi≤actualExtendedThirdLowerFactor (tentOldHigh s k (symmetricLeft a c)))
    (hqueries : flo≤fhi) :
    tentOldChord s k (symmetricLeft a c) (symmetricRight b d) flo fhi≤
      ∫ p, actualExtendedThirdLowerFactor (actualPrismOld p) ∂prismProbability a b c d := by
  rw [←symmetric_producer_chord_swap s k a b c d flo fhi]
  exact safe_asymmetric_producer_chord_le_actual_integral hs hg hmu
    ((symmetric_active_swap_iff s k a b c d).2 hactive)
    (by simpa only [symmetric_root_swap] using hroot)
    (by simpa only [symmetric_residual_swap] using hres)
    (by simpa only [symmetric_low_swap] using hlo)
    (by simpa only [symmetric_low_swap] using hfl)
    (by simpa only [symmetric_high_swap] using hfh) hqueries

/-- Core unsafe selected xz/fall rescue; yz/fall is solely a proof minorant.
The original xz/fall endpoint queries and producer mean remain literal. -/
theorem xz_fall_producer_chord_le_actual_integral
    {a b c d flo fhi : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu)
    (hactive : sourceActive .xz .fall (symmetricLeft a c) (symmetricRight b d))
    (hroot : planeUpper .xz .fall (symmetricLeft a c) (symmetricRight b d)≤thirdPrefixTheta)
    (hres : 0<oldNumerator .xz .fall (symmetricRight b d))
    (hlo : 2≤tentOldLow .xz .fall (symmetricRight b d))
    (hfl : flo≤actualExtendedThirdLowerFactor (tentOldLow .xz .fall (symmetricRight b d)))
    (hfh : fhi≤actualExtendedThirdLowerFactor (tentOldHigh .xz .fall (symmetricLeft a c)))
    (hqueries : flo≤fhi) :
    tentOldChord .xz .fall (symmetricLeft a c) (symmetricRight b d) flo fhi≤
      ∫ p, actualExtendedThirdLowerFactor (actualPrismOld p) ∂prismProbability a b c d := by
  exact paired_producer_chord_le_actual_integral (s := .xz) (k := .fall) .yzFall hg hmu hactive hroot
    hres hlo hfl hfh hqueries

theorem balanced_producer_chord_le_actual_integral
    (s : TentSum) (k : TentSide) (hs : s=.xy ∨ s=.xyz)
    {a b c d flo fhi : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu)
    (hactive : sourceActive s k (symmetricLeft a c) (symmetricRight b d))
    (hroot : planeUpper s k (symmetricLeft a c) (symmetricRight b d)≤thirdPrefixTheta)
    (hres : 0<oldNumerator s k (symmetricRight b d))
    (hlo : 2≤tentOldLow s k (symmetricRight b d))
    (hfl : flo≤actualExtendedThirdLowerFactor (tentOldLow s k (symmetricRight b d)))
    (hfh : fhi≤actualExtendedThirdLowerFactor (tentOldHigh s k (symmetricLeft a c))) :
    tentOldChord s k (symmetricLeft a c) (symmetricRight b d) flo fhi≤
      ∫ p, actualExtendedThirdLowerFactor (actualPrismOld p) ∂prismProbability a b c d := by
  rw [←balanced_tent_chord_eq_producer s k a b c d flo fhi hs]
  exact symmetric_tent_chord_le_actual_integral s k hg hmu hactive hroot hres hlo hfl hfh

/-- Exhausts all six original sums and both source sides. Four safe branches
use their own cap minorant, four use its x/y pair, and four are balanced. -/
theorem all_producer_chord_le_actual_integral
    (s : TentSum) (k : TentSide) {a b c d flo fhi : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu)
    (hactive : sourceActive s k (symmetricLeft a c) (symmetricRight b d))
    (hroot : planeUpper s k (symmetricLeft a c) (symmetricRight b d)≤thirdPrefixTheta)
    (hres : 0<oldNumerator s k (symmetricRight b d))
    (hlo : 2≤tentOldLow s k (symmetricRight b d))
    (hfl : flo≤actualExtendedThirdLowerFactor (tentOldLow s k (symmetricRight b d)))
    (hfh : fhi≤actualExtendedThirdLowerFactor (tentOldHigh s k (symmetricLeft a c)))
    (hqueries : flo≤fhi) :
    tentOldChord s k (symmetricLeft a c) (symmetricRight b d) flo fhi≤
      ∫ p, actualExtendedThirdLowerFactor (actualPrismOld p) ∂prismProbability a b c d := by
  cases s <;> cases k
  · exact safe_asymmetric_producer_chord_le_actual_integral .xRise hg hmu hactive hroot hres hlo hfl hfh hqueries
  · exact paired_producer_chord_le_actual_integral (s := .x) (k := .fall) .yFall hg hmu hactive hroot hres hlo hfl hfh hqueries
  · exact paired_producer_chord_le_actual_integral (s := .y) (k := .rise) .xRise hg hmu hactive hroot hres hlo hfl hfh hqueries
  · exact safe_asymmetric_producer_chord_le_actual_integral .yFall hg hmu hactive hroot hres hlo hfl hfh hqueries
  · exact balanced_producer_chord_le_actual_integral .xy .rise (Or.inl rfl) hg hmu hactive hroot hres hlo hfl hfh
  · exact balanced_producer_chord_le_actual_integral .xy .fall (Or.inl rfl) hg hmu hactive hroot hres hlo hfl hfh
  · exact safe_asymmetric_producer_chord_le_actual_integral .xzRise hg hmu hactive hroot hres hlo hfl hfh hqueries
  · exact paired_producer_chord_le_actual_integral (s := .xz) (k := .fall) .yzFall hg hmu hactive hroot hres hlo hfl hfh hqueries
  · exact paired_producer_chord_le_actual_integral (s := .yz) (k := .rise) .xzRise hg hmu hactive hroot hres hlo hfl hfh hqueries
  · exact safe_asymmetric_producer_chord_le_actual_integral .yzFall hg hmu hactive hroot hres hlo hfl hfh hqueries
  · exact balanced_producer_chord_le_actual_integral .xyz .rise (Or.inr rfl) hg hmu hactive hroot hres hlo hfl hfh
  · exact balanced_producer_chord_le_actual_integral .xyz .fall (Or.inr rfl) hg hmu hactive hroot hres hlo hfl hfh

/-- These are exact rational operands, so .num/.den and reader calls are
identical too. No monotonicity of the stored lower reader is asserted. -/
theorem symmetric_literal_endpoint_swap (s : TentSum) (k : TentSide) (x z D : ℤ) :
    literalTentEndpoint (swapSum s) k ![x,x,z] D=literalTentEndpoint s k ![x,x,z] D := by
  cases s <;> cases k <;>
    simp [literalTentEndpoint,swapSum,literalTentX,literalTentY,literalTentZ] <;>
    push_cast <;> ring

theorem saved_low_swap (s : TentSum) (k : TentSide) (x z : ℤ) :
    savedTentLow (swapSum s) k x z=savedTentLow s k x z := by
  exact symmetric_literal_endpoint_swap s k x z (48000*2^24)

theorem saved_high_swap (s : TentSum) (k : TentSide) (x z : ℤ) :
    savedTentHigh (swapSum s) k x z=savedTentHigh s k x z := by
  exact symmetric_literal_endpoint_swap s k x z (48000*2^24)

theorem saved_query_order_swap_iff (table : CheckedBlockTable) (s : TentSum)
    (k : TentSide) (x0 x1 z0 z1 : ℤ) :
    savedTentQueryOrder table (swapSum s) k x0 x1 z0 z1 ↔
      savedTentQueryOrder table s k x0 x1 z0 z1 := by
  simp only [savedTentQueryOrder,saved_low_swap,saved_high_swap]

/-- Complete SAME-reader OLD integral supplier for every original selected
tent on a symmetric below-mu box. The remaining query-slope premise is the
literal integer-output check, not an estimate of the integral or K. -/
theorem all_saved_producer_chord_le_actual_integral
    (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu)
    (hbranch : literalSymmetricBranch s k x0 x1 z0 z1)
    (hroot : literalSymmetricRoot s k x0 x1 z0 z1)
    (hres : literalSymmetricResidual s k x1)
    (hlow : (2:ℚ)≤savedTentLow s k x1 z1)
    (horder : savedTentQueryOrder table s k x0 x1 z0 z1) :
    tentOldChord s k (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))
      (value (readQueryLo160 (assembledRead table.blocks)
        (savedTentLow s k x1 z1).num ((savedTentLow s k x1 z1).den:ℤ)))
      (value (readQueryLo160 (assembledRead table.blocks)
        (savedTentHigh s k x0 z0).num ((savedTentHigh s k x0 z0).den:ℤ)))≤
      ∫ p, actualExtendedThirdLowerFactor (actualPrismOld p)
        ∂prismProbability (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ) := by
  have hguards := original_selected_tent_guard_bridge s k ![x0,x0,z0] ![x1,x1,z1]
    (48000*2^24) 481573208064
    (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))
    rfl rfl (symmetric_grid_bind x0 z0 a c ha hc) (symmetric_grid_bind x1 z1 b d hb hd)
    (by simpa only [literalSymmetricBranch,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using hbranch)
    (by simpa only [literalSymmetricRoot,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using hroot)
    (by simpa only [literalSymmetricResidual,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using hres)
  have hz0 := positive_grid_binding z0 c hc (symmetric_positive hg).2
  have hz1 := positive_grid_binding z1 d hd ((symmetric_positive hg).2.trans hg.width_z)
  have hloEq : (savedTentLow s k x1 z1:ℝ)=
      tentOldLow s k (symmetricRight (b:ℝ) (d:ℝ)) :=
    saved_tent_endpoint_cast s k x1 z1 b d hb hd hz1
  have hhiEq : (savedTentHigh s k x0 z0:ℝ)=
      tentOldHigh s k (symmetricLeft (a:ℝ) (c:ℝ)) :=
    saved_tent_endpoint_cast s k x0 z0 a c ha hc hz0
  have hloR : (2:ℝ)≤tentOldLow s k (symmetricRight (b:ℝ) (d:ℝ)) := by
    rw [←hloEq]
    exact_mod_cast hlow
  have hqueries := symmetric_saved_tent_three_queries table s k x0 x1 z0 z1
  exact all_producer_chord_le_actual_integral s k hg hmu
    hguards.1 hguards.2.1 hguards.2.2 hloR
    (by rw [←hloEq]; exact hqueries.1)
    (by rw [←hhiEq]; exact hqueries.2.1) (value_mono horder)

/-- The discrepancies of the two real ordered means cancel exactly. This
is an arithmetic identity of computed moments, not a symmetry assumption
about the actual cap or a replacement of the source-selected producer. -/
theorem symmetric_producer_mean_eq_pair_average (s : TentSum) (k : TentSide)
    (a b c d : ℝ) :
    tentOldMean s k (symmetricLeft a c) (symmetricRight b d)=
      (orderedTentMean s k a b c d+orderedTentMean (swapSum s) k a b c d)/2 := by
  have hcancel :
      (orderedTentMean s k a b c d-
        tentOldMean s k (symmetricLeft a c) (symmetricRight b d))+
      (orderedTentMean (swapSum s) k a b c d-
        tentOldMean (swapSum s) k (symmetricLeft a c) (symmetricRight b d))=0 := by
    rw [ordered_mean_sub_producer_mean,ordered_mean_sub_producer_mean,
      oldX_swapSum,oldY_swapSum]
    ring
  rw [symmetric_producer_mean_swap] at hcancel
  linarith only [hcancel]

/-- The two chords have identical endpoints. Affinity transfers the mean
average identity without imposing any sign on fhi-flo. -/
theorem symmetric_producer_chord_eq_pair_average (s : TentSum) (k : TentSide)
    (a b c d flo fhi : ℝ) :
    tentOldChord s k (symmetricLeft a c) (symmetricRight b d) flo fhi=
      (orderedTentChord s k a b c d flo fhi+
        orderedTentChord (swapSum s) k a b c d flo fhi)/2 := by
  unfold tentOldChord orderedTentChord
  rw [symmetric_low_swap,symmetric_high_swap,symmetric_producer_mean_eq_pair_average]
  ring

/-- All twelve original branches, with no query-order condition. The
original producer chord is the average of two genuine real-minorant chord
bounds against the SAME actual OLD integral. No cap symmetry is used. -/
theorem all_producer_chord_le_actual_integral_no_query_order
    (s : TentSum) (k : TentSide) {a b c d flo fhi : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu)
    (hactive : sourceActive s k (symmetricLeft a c) (symmetricRight b d))
    (hroot : planeUpper s k (symmetricLeft a c) (symmetricRight b d)≤thirdPrefixTheta)
    (hres : 0<oldNumerator s k (symmetricRight b d))
    (hlo : 2≤tentOldLow s k (symmetricRight b d))
    (hfl : flo≤actualExtendedThirdLowerFactor (tentOldLow s k (symmetricRight b d)))
    (hfh : fhi≤actualExtendedThirdLowerFactor (tentOldHigh s k (symmetricLeft a c))) :
    tentOldChord s k (symmetricLeft a c) (symmetricRight b d) flo fhi≤
      ∫ p, actualExtendedThirdLowerFactor (actualPrismOld p) ∂prismProbability a b c d := by
  have hfirst := symmetric_tent_chord_le_actual_integral s k hg hmu
    hactive hroot hres hlo hfl hfh
  have hsecond := symmetric_tent_chord_le_actual_integral (swapSum s) k hg hmu
    ((symmetric_active_swap_iff s k a b c d).2 hactive)
    (by simpa only [symmetric_root_swap] using hroot)
    (by simpa only [symmetric_residual_swap] using hres)
    (by simpa only [symmetric_low_swap] using hlo)
    (by simpa only [symmetric_low_swap] using hfl)
    (by simpa only [symmetric_high_swap] using hfh)
  rw [symmetric_producer_chord_eq_pair_average]
  linarith only [hfirst,hsecond]

/-- Exact saved-query binding for the stronger average proof. All original
integer branch/root/residual/low tests are retained. No new query-output
guard is added to the original producer. -/
theorem all_saved_producer_chord_le_actual_integral_no_query_order
    (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu)
    (hbranch : literalSymmetricBranch s k x0 x1 z0 z1)
    (hroot : literalSymmetricRoot s k x0 x1 z0 z1)
    (hres : literalSymmetricResidual s k x1)
    (hlow : (2:ℚ)≤savedTentLow s k x1 z1) :
    tentOldChord s k (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))
      (value (readQueryLo160 (assembledRead table.blocks)
        (savedTentLow s k x1 z1).num ((savedTentLow s k x1 z1).den:ℤ)))
      (value (readQueryLo160 (assembledRead table.blocks)
        (savedTentHigh s k x0 z0).num ((savedTentHigh s k x0 z0).den:ℤ)))≤
      ∫ p, actualExtendedThirdLowerFactor (actualPrismOld p)
        ∂prismProbability (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ) := by
  have hguards := original_selected_tent_guard_bridge s k ![x0,x0,z0] ![x1,x1,z1]
    (48000*2^24) 481573208064
    (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))
    rfl rfl (symmetric_grid_bind x0 z0 a c ha hc) (symmetric_grid_bind x1 z1 b d hb hd)
    (by simpa only [literalSymmetricBranch,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using hbranch)
    (by simpa only [literalSymmetricRoot,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using hroot)
    (by simpa only [literalSymmetricResidual,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using hres)
  have hz0 := positive_grid_binding z0 c hc (symmetric_positive hg).2
  have hz1 := positive_grid_binding z1 d hd ((symmetric_positive hg).2.trans hg.width_z)
  have hloEq : (savedTentLow s k x1 z1:ℝ)=
      tentOldLow s k (symmetricRight (b:ℝ) (d:ℝ)) :=
    saved_tent_endpoint_cast s k x1 z1 b d hb hd hz1
  have hhiEq : (savedTentHigh s k x0 z0:ℝ)=
      tentOldHigh s k (symmetricLeft (a:ℝ) (c:ℝ)) :=
    saved_tent_endpoint_cast s k x0 z0 a c ha hc hz0
  have hloR : (2:ℝ)≤tentOldLow s k (symmetricRight (b:ℝ) (d:ℝ)) := by
    rw [←hloEq]
    exact_mod_cast hlow
  have hqueries := symmetric_saved_tent_three_queries table s k x0 x1 z0 z1
  exact all_producer_chord_le_actual_integral_no_query_order s k hg hmu
    hguards.1 hguards.2.1 hguards.2.2 hloR
    (by rw [←hloEq]; exact hqueries.1)
    (by rw [←hhiEq]; exact hqueries.2.1)

end
end ImbalancedChen.OriginalThirdP4ASymmetricPairRealRescue
