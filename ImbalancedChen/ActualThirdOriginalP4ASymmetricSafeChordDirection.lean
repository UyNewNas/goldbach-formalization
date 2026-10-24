import ImbalancedChen.ActualThirdOriginalP4ASymmetricTentPrerequisites

/-!
SOURCEONLY / UNCOMPILED / HOLD_ELABORATION / OPEN30.
Safe asymmetric six-tent branches of the ORIGINAL symmetric below-mu OLD
chord. Endpoint ordering is an explicit literal query-output comparison;
it is not inferred from two unrelated lower enclosures.
-/
namespace ImbalancedChen.OriginalThirdP4ASymmetricSafeChordDirection

noncomputable section
open Set MeasureTheory
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdTriangleMomentsSourceOnly OriginalThirdSymmetricJensenSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedStoredConsumerSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly
open OriginalThirdP4ASymmetricTentPrerequisites

private theorem triangle_mem_ae (a b : ℝ) :
    ∀ᵐ p ∂triangleProbability a b, p∈xyTriangle a b := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem (measurableSet_xyTriangle a b))

private theorem integrable_triangle_x {a b : ℝ} (ha : 0<a) (hab : a<b) :
    Integrable (fun p : XY => p.1) (triangleProbability a b) := by
  let := triangleProbability_isProbability ha hab
  apply Integrable.of_bound measurable_fst.aestronglyMeasurable (|a|+|b|)
  filter_upwards [triangle_mem_ae a b] with p hp
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le a,abs_nonneg b,hp.1.1.1]
  · linarith [le_abs_self b,abs_nonneg a,hp.1.1.2]

private theorem integrable_triangle_y {a b : ℝ} (ha : 0<a) (hab : a<b) :
    Integrable (fun p : XY => p.2) (triangleProbability a b) := by
  let := triangleProbability_isProbability ha hab
  apply Integrable.of_bound measurable_snd.aestronglyMeasurable (|a|+|b|)
  filter_upwards [triangle_mem_ae a b] with p hp
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le a,abs_nonneg b,hp.1.2.1]
  · linarith [le_abs_self b,abs_nonneg a,hp.1.2.2]

/-- Original reciprocal triangle, with no symmetry or independence guess. -/
theorem triangle_y_mean {a b : ℝ} (ha : 0<a) (hab : a<b) :
    (∫ p : XY, p.2 ∂triangleProbability a b)=minMean a b := by
  rw [integral_triangleProbability ha hab,triangle_y_numerator ha hab.le]
  have hlog := (Real.log_pos ((one_lt_div ha).2 hab)).ne'
  unfold triangleMass minMean sumMean maxMean
  field_simp [hlog] <;> ring

/-- E[y]≤E[x] is supplied by y≤x on the actual triangle and integrability. -/
theorem triangle_minMean_le_maxMean {a b : ℝ} (ha : 0<a) (hab : a<b) :
    minMean a b≤maxMean a b := by
  have hi := integral_mono_ae (integrable_triangle_y ha hab)
    (integrable_triangle_x ha hab)
    ((triangle_mem_ae a b).mono (fun _ hp => hp.2))
  rw [triangle_y_mean ha hab,triangleProbability_x_mean ha hab] at hi
  exact hi

/-- The producer square mean of either coordinate is half the true sum.
It lies below the ordered maximum mean; no logarithmic approximation is used. -/
theorem triangle_squareEx_le_maxMean {a b : ℝ} (ha : 0<a) (hab : a<b) :
    (b-a)/Real.log (b/a)≤maxMean a b := by
  have h := triangle_minMean_le_maxMean ha hab
  unfold minMean sumMean at h
  linarith

/-- Exactly the four asymmetric branches with oldX-oldY positive. The xy
and xyz equal-mean branches already belong to the prerequisite module. -/
inductive SafeAsymmetricTent : TentSum → TentSide → Prop where
  | xRise : SafeAsymmetricTent .x .rise
  | xzRise : SafeAsymmetricTent .xz .rise
  | yFall : SafeAsymmetricTent .y .fall
  | yzFall : SafeAsymmetricTent .yz .fall

theorem safe_asymmetric_coefficient_pos {s : TentSum} {k : TentSide}
    (hs : SafeAsymmetricTent s k) : 0<oldX s k-oldY s k := by
  cases hs <;> norm_num [oldX,oldY,planeSlope,sumX,sumY]

theorem safe_asymmetric_mean_direction {s : TentSum} {k : TentSide}
    (hs : SafeAsymmetricTent s k) {a b c d : ℝ}
    (hg : SymmetricFullBox a b c d) :
    tentOldMean s k (symmetricLeft a c) (symmetricRight b d)≤
      orderedTentMean s k a b c d := by
  have hcoord := sub_nonneg.mpr
    (triangle_squareEx_le_maxMean (symmetric_positive hg).1 hg.width_xy)
  have hc := (symmetric_positive hg).2
  have hd := hc.trans hg.width_z
  have hinv : 0≤invZMean c d := by unfold invZMean; positivity
  apply sub_nonneg.mp
  rw [ordered_mean_sub_producer_mean]
  exact mul_nonneg (mul_nonneg (safe_asymmetric_coefficient_pos hs).le hcoord) hinv

/-- Algebraic chord comparison requires a nonnegative chord slope. Endpoint
factor monotonicity by itself does not order arbitrary lower approximations. -/
theorem safe_asymmetric_producer_chord_le_ordered {s : TentSum} {k : TentSide}
    (hs : SafeAsymmetricTent s k) {a b c d flo fhi : ℝ}
    (hg : SymmetricFullBox a b c d)
    (hres : 0<oldNumerator s k (symmetricRight b d)) (hqueries : flo≤fhi) :
    tentOldChord s k (symmetricLeft a c) (symmetricRight b d) flo fhi≤
      orderedTentChord s k a b c d flo fhi := by
  have hmean := safe_asymmetric_mean_direction hs hg
  have hden := (sub_pos.mpr (symmetric_tent_span s k hg hres)).le
  unfold tentOldChord orderedTentChord
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr hqueries)
  exact div_le_div_of_nonneg_right (sub_le_sub_right hmean _) hden

/-- A genuine original producer-square chord lower bound for all four safe
asymmetric branches, under the literal nonnegative endpoint-query slope. -/
theorem safe_asymmetric_producer_chord_le_actual_integral
    {s : TentSum} {k : TentSide} (hs : SafeAsymmetricTent s k)
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
  exact (safe_asymmetric_producer_chord_le_ordered hs hg hres hqueries).trans
    (symmetric_tent_chord_le_actual_integral s k hg hmu hactive hroot hres hlo hfl hfh)

/-- Flat endpoint queries remove the mean discrepancy for EVERY branch,
including the four asymmetric branches with the reverse mean direction. -/
theorem producer_chord_eq_ordered_of_equal_queries
    (s : TentSum) (k : TentSide) (a b c d flo fhi : ℝ) (heq : flo=fhi) :
    tentOldChord s k (symmetricLeft a c) (symmetricRight b d) flo fhi=
      orderedTentChord s k a b c d flo fhi := by
  rw [heq]
  simp only [tentOldChord,orderedTentChord,sub_self,mul_zero,add_zero]

/-- Both original terminal lower queries literally read Llo(196608)/12.
This is only a branch identity, not a new query-soundness implementation. -/
theorem terminal_lower_query_literal (read : ℕ → OriginalNode) (q : ℚ)
    (htail : 12*(q.den:ℤ)<q.num) :
    readQueryLo160 read q.num (q.den:ℤ)=((read 196608).Llo/12)*2^48 := by
  have hd : (0:ℤ)<(q.den:ℤ) := by exact_mod_cast q.den_pos
  have hclamp : ¬q.num≤2*(q.den:ℤ) := by omega
  simp only [readQueryLo160,if_neg hclamp,if_pos htail]

theorem two_terminal_lower_queries_equal (read : ℕ → OriginalNode) (q0 q1 : ℚ)
    (h0 : 12*(q0.den:ℤ)<q0.num) (h1 : 12*(q1.den:ℤ)<q1.num) :
    readQueryLo160 read q0.num (q0.den:ℤ)=readQueryLo160 read q1.num (q1.den:ℤ) := by
  rw [terminal_lower_query_literal read q0 h0,terminal_lower_query_literal read q1 h1]

theorem flat_producer_chord_le_actual_integral
    (s : TentSum) (k : TentSide) {a b c d flo fhi : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu)
    (hactive : sourceActive s k (symmetricLeft a c) (symmetricRight b d))
    (hroot : planeUpper s k (symmetricLeft a c) (symmetricRight b d)≤thirdPrefixTheta)
    (hres : 0<oldNumerator s k (symmetricRight b d))
    (hlo : 2≤tentOldLow s k (symmetricRight b d))
    (hfl : flo≤actualExtendedThirdLowerFactor (tentOldLow s k (symmetricRight b d)))
    (hfh : fhi≤actualExtendedThirdLowerFactor (tentOldHigh s k (symmetricLeft a c)))
    (heq : flo=fhi) :
    tentOldChord s k (symmetricLeft a c) (symmetricRight b d) flo fhi≤
      ∫ p, actualExtendedThirdLowerFactor (actualPrismOld p) ∂prismProbability a b c d := by
  rw [producer_chord_eq_ordered_of_equal_queries s k a b c d flo fhi heq]
  exact symmetric_tent_chord_le_actual_integral s k hg hmu hactive hroot hres hlo hfl hfh

/-- This is an exact integer-output guard, not a semantic target estimate. -/
def savedTentQueryOrder (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (x0 x1 z0 z1 : ℤ) : Prop :=
  readQueryLo160 (assembledRead table.blocks)
      (savedTentLow s k x1 z1).num ((savedTentLow s k x1 z1).den:ℤ)≤
    readQueryLo160 (assembledRead table.blocks)
      (savedTentHigh s k x0 z0).num ((savedTentHigh s k x0 z0).den:ℤ)

/-- A stronger literal separation check can supply lower-endpoint ordering
without any reader-monotonicity theorem. The low query's own enclosure gives
lo(low)≤hi(low), and this guard gives hi(low)≤lo(high). -/
theorem saved_query_order_of_interval_separation
    (table : CheckedBlockTable) (s : TentSum) (k : TentSide) (x0 x1 z0 z1 : ℤ)
    (hsep : readQueryHi160 (assembledRead table.blocks)
      (savedTentLow s k x1 z1).num ((savedTentLow s k x1 z1).den:ℤ)≤
      readQueryLo160 (assembledRead table.blocks)
        (savedTentHigh s k x0 z0).num ((savedTentHigh s k x0 z0).den:ℤ)) :
    savedTentQueryOrder table s k x0 x1 z0 z1 := by
  have hq := stored_rat_query_encloses table (savedTentLow s k x1 z1)
  have hint : readQueryLo160 (assembledRead table.blocks)
      (savedTentLow s k x1 z1).num ((savedTentLow s k x1 z1).den:ℤ)≤
      readQueryHi160 (assembledRead table.blocks)
        (savedTentLow s k x1 z1).num ((savedTentLow s k x1 z1).den:ℤ) :=
    value_le_iff.mp (hq.1.trans hq.2)
  exact hint.trans hsep

/-- End-to-end OLD subtraction supplier using exact saved query expressions.
Only the original literal branch/root/residual/low-domain guards and the
literal query-output ordering remain; no target integral bound is assumed. -/
theorem safe_asymmetric_saved_producer_chord_le_actual_integral
    (table : CheckedBlockTable) {s : TentSum} {k : TentSide}
    (hs : SafeAsymmetricTent s k) (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
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
  have hcmp := safe_asymmetric_producer_chord_le_ordered hs hg hguards.2.2
    (value_mono horder)
  exact hcmp.trans (symmetric_saved_tent_old_integral table s k x0 x1 z0 z1 a b c d
    ha hb hc hd hg hmu hbranch hroot hres hlow)

end
end ImbalancedChen.OriginalThirdP4ASymmetricSafeChordDirection
