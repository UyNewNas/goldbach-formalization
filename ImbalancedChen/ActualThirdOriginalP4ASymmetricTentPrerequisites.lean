import ImbalancedChen.ActualThirdOriginalSixTentRoundedConsumer
import ImbalancedChen.ActualThirdOriginalRoundedStoredQueryIntegerConsumer

/-!
SOURCEONLY / UNCOMPILED / HOLD_ELABORATION / OPEN30.
The two imports denote the frozen 24u six-tent consumer and the 24x repaired
all-query symmetric consumer, respectively. Exact byte pins are in CP.json.

This module closes the genuine ordered-triangle OLD chord supplier for all
six original tent sums, binds its exact Fraction endpoints and SAME-reader
queries, and exposes the precise producer-square/ordered-triangle mean gap.
It does not assume a leaf integral bound or the original K allowance.
-/
namespace ImbalancedChen.OriginalThirdP4ASymmetricTentPrerequisites

noncomputable section
open Set MeasureTheory
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdTriangleMomentsSourceOnly OriginalThirdSymmetricJensenSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly
open OriginalThirdRoundedStoredConsumerSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

def symmetricLeft (a c : ℝ) : BoxPoint := ![a,a,c]
def symmetricRight (b d : ℝ) : BoxPoint := ![b,b,d]

def orderedTentMean (s : TentSum) (k : TentSide) (a b c d : ℝ) : ℝ :=
  (planeConst k+oldX s k*maxMean a b+oldY s k*minMean a b)*invZMean c d+oldZ s k

def orderedTentChord (s : TentSum) (k : TentSide)
    (a b c d flo fhi : ℝ) : ℝ :=
  flo+(orderedTentMean s k a b c d-tentOldLow s k (symmetricRight b d))/
    (tentOldHigh s k (symmetricLeft a c)-tentOldLow s k (symmetricRight b d))*(fhi-flo)

theorem symmetric_positive {a b c d : ℝ} (hg : SymmetricFullBox a b c d) :
    0<a ∧ 0<c := by
  have hc : 0<c := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/100) hg.cutoff
  exact ⟨hc.trans_le (hg.width_z.le.trans hg.z_below_xy),hc⟩

theorem symmetric_left_positive {a b c d : ℝ} (hg : SymmetricFullBox a b c d) :
    ∀ i, 0<symmetricLeft a c i := by
  intro i
  fin_cases i <;> simp only [symmetricLeft,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  · exact (symmetric_positive hg).1
  · exact (symmetric_positive hg).1
  · exact (symmetric_positive hg).2

theorem symmetric_widths {a b c d : ℝ} (hg : SymmetricFullBox a b c d) :
    ∀ i, symmetricLeft a c i<symmetricRight b d i := by
  intro i
  fin_cases i <;> simp only [symmetricLeft,symmetricRight,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  · exact hg.width_xy
  · exact hg.width_xy
  · exact hg.width_z

theorem prismPoint_mem_symmetric_rectangle {a b c d : ℝ} {p : PrismPoint}
    (hp : p∈prismRegion a b c d) :
    prismPoint p∈Icc (symmetricLeft a c) (symmetricRight b d) := by
  constructor <;> intro i <;> fin_cases i <;>
    simp only [symmetricLeft,symmetricRight,prismPoint,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  · exact hp.1.1.1.1
  · exact hp.1.1.2.1
  · exact hp.2.1
  · exact hp.1.1.1.2
  · exact hp.1.1.2.2
  · exact hp.2.2

/-- Unlike the ordinary supplier, ordering is read from the integration
domain itself. No impossible b≤a condition on the symmetric square is used. -/
theorem symmetric_tent_plane_le_actual_cap
    (s : TentSum) (k : TentSide) {a b c d : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu)
    (hactive : sourceActive s k (symmetricLeft a c) (symmetricRight b d))
    (hroot : planeUpper s k (symmetricLeft a c) (symmetricRight b d)≤thirdPrefixTheta)
    {p : PrismPoint} (hp : p∈prismRegion a b c d) :
    tentPlane s k (prismPoint p)≤actualExtendedThirdBufferedCap 0 p.1.1 p.1.2 p.2 := by
  have ht := prismPoint_mem_symmetric_rectangle hp
  have hc := (symmetric_positive hg).2
  have hz : 0<p.2 := hc.trans_le hp.2.1
  have hordered : VariableEnvelope.Ordered p.1.1 p.1.2 p.2 :=
    ⟨hz.le,hp.2.2.trans (hg.z_below_xy.trans hp.1.1.2.1),
      hp.1.2,hp.1.1.1.2.trans hmu⟩
  unfold actualExtendedThirdBufferedCap thirdPrefixBufferedCap
  simp only [mul_zero,sub_zero]
  apply le_min
  · exact (tent_plane_le_upper s k (symmetricLeft a c) (symmetricRight b d) ht).trans hroot
  · rw [actualExtendedThirdEnvelope_eq_six hordered]
    rw [active_plane_eq_v s k (symmetricLeft a c) (symmetricRight b d) hactive ht]
    exact tent_v_le_six s hordered

/-- All six original selected affine functions are genuine OLD minorants
on the actual half-domain. Its endpoint range is proved from the original
positive low_num residual, not supplied as an analytic hypothesis. -/
theorem symmetric_tent_minorant_range
    (s : TentSum) (k : TentSide) {a b c d : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu)
    (hactive : sourceActive s k (symmetricLeft a c) (symmetricRight b d))
    (hroot : planeUpper s k (symmetricLeft a c) (symmetricRight b d)≤thirdPrefixTheta)
    (hres : 0<oldNumerator s k (symmetricRight b d))
    {p : PrismPoint} (hp : p∈prismRegion a b c d) :
    tentOldArgument s k (prismPoint p)≤actualPrismOld p ∧
      tentOldArgument s k (prismPoint p)∈Icc
        (tentOldLow s k (symmetricRight b d))
        (tentOldHigh s k (symmetricLeft a c)) := by
  have hz : 0<p.2 := (symmetric_positive hg).2.trans_le hp.2.1
  constructor
  · have hc := symmetric_tent_plane_le_actual_cap s k hg hmu hactive hroot hp
    rw [tent_old_argument_identity s k (prismPoint p) (by
      simpa only [prismPoint,Matrix.cons_val_two] using hz.ne')]
    change (tentPlane s k (prismPoint p)-p.1.1-p.1.2-p.2)/p.2≤_
    unfold actualPrismOld
    exact (div_le_div_iff_of_pos_right hz).2 (by linarith)
  · exact original_tent_old_range s k (symmetricLeft a c) (symmetricRight b d)
      (symmetric_left_positive hg) hres (prismPoint_mem_symmetric_rectangle hp)

theorem symmetric_tent_span (s : TentSum) (k : TentSide) {a b c d : ℝ}
    (hg : SymmetricFullBox a b c d)
    (hres : 0<oldNumerator s k (symmetricRight b d)) :
    tentOldLow s k (symmetricRight b d)<tentOldHigh s k (symmetricLeft a c) := by
  exact original_tent_old_span s k (symmetricLeft a c) (symmetricRight b d)
    (symmetric_left_positive hg) (symmetric_widths hg) hres

/-- The existing TRUE prism moments, with original order x=max and y=min. -/
theorem symmetric_tent_exact_ordered_mean (s : TentSum) (k : TentSide)
    {a b c d : ℝ} (hg : SymmetricFullBox a b c d) :
    (∫ p, tentOldArgument s k (prismPoint p) ∂prismProbability a b c d)=
      orderedTentMean s k a b c d := by
  have heq : (fun p => tentOldArgument s k (prismPoint p))=
      prismAffine (planeConst k) (oldX s k) (oldY s k) (oldZ s k) := by
    funext p
    rfl
  rw [heq,prism_affine_mean hg]
  rfl

/-- Exact discrepancy; the producer's square mean is not silently asserted
to be the ordered mean for an asymmetric selected coefficient tuple. -/
theorem ordered_mean_sub_producer_mean (s : TentSum) (k : TentSide)
    (a b c d : ℝ) :
    orderedTentMean s k a b c d-
        tentOldMean s k (symmetricLeft a c) (symmetricRight b d)=
      (oldX s k-oldY s k)*(maxMean a b-(b-a)/Real.log (b/a))*invZMean c d := by
  simp only [orderedTentMean,tentOldMean,symmetricLeft,symmetricRight,
    boxEX,boxEY,boxEZInv,minMean,sumMean,invZMean,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons]
  ring

/-- These are exactly the two enumerated sums whose coefficients agree. -/
theorem symmetric_tent_coefficients (s : TentSum) :
    sumX s=sumY s ↔ s=.xy ∨ s=.xyz := by
  cases s <;> norm_num [sumX,sumY]

theorem balanced_tent_ordered_mean_eq_producer (s : TentSum) (k : TentSide)
    (a b c d : ℝ) (hs : s=.xy ∨ s=.xyz) :
    orderedTentMean s k a b c d=
      tentOldMean s k (symmetricLeft a c) (symmetricRight b d) := by
  have hxy : oldX s k=oldY s k := by
    unfold oldX oldY
    rw [(symmetric_tent_coefficients s).2 hs]
  have h := ordered_mean_sub_producer_mean s k a b c d
  rw [hxy,sub_self,zero_mul,zero_mul] at h
  exact sub_eq_zero.mp h

theorem balanced_tent_chord_eq_producer (s : TentSum) (k : TentSide)
    (a b c d flo fhi : ℝ) (hs : s=.xy ∨ s=.xyz) :
    orderedTentChord s k a b c d flo fhi=
      tentOldChord s k (symmetricLeft a c) (symmetricRight b d) flo fhi := by
  unfold orderedTentChord tentOldChord
  rw [balanced_tent_ordered_mean_eq_producer s k a b c d hs]

theorem ordered_mean_sub_producer_mean_xz_fall (a b c d : ℝ) :
    orderedTentMean .xz .fall a b c d-
        tentOldMean .xz .fall (symmetricLeft a c) (symmetricRight b d)=
      (-(3/2):ℝ)*(maxMean a b-(b-a)/Real.log (b/a))*invZMean c d := by
  rw [ordered_mean_sub_producer_mean]
  norm_num [oldX,oldY,planeSlope,sumX,sumY]

private theorem prism_mem_ae (a b c d : ℝ) :
    ∀ᵐ p ∂prismProbability a b c d, p∈prismRegion a b c d := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem ((measurableSet_xyTriangle a b).prod measurableSet_Icc))

private theorem integrable_tent_argument (s : TentSum) (k : TentSide)
    {a b c d : ℝ} (hg : SymmetricFullBox a b c d)
    (hres : 0<oldNumerator s k (symmetricRight b d)) :
    Integrable (fun p => tentOldArgument s k (prismPoint p))
      (prismProbability a b c d) := by
  let := prismProbability_isProbability (symmetric_positive hg).1 hg.width_xy
    (symmetric_positive hg).2 hg.width_z
  have hm : Measurable (fun p => tentOldArgument s k (prismPoint p)) := by
    change Measurable (prismAffine (planeConst k) (oldX s k) (oldY s k) (oldZ s k))
    unfold prismAffine
    fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable
    (|tentOldLow s k (symmetricRight b d)|+|tentOldHigh s k (symmetricLeft a c)|)
  filter_upwards [prism_mem_ae a b c d] with p hp
  have hr := original_tent_old_range s k (symmetricLeft a c) (symmetricRight b d)
    (symmetric_left_positive hg) hres (prismPoint_mem_symmetric_rectangle hp)
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (tentOldLow s k (symmetricRight b d)),
      abs_nonneg (tentOldHigh s k (symmetricLeft a c)),hr.1]
  · linarith [le_abs_self (tentOldHigh s k (symmetricLeft a c)),
      abs_nonneg (tentOldLow s k (symmetricRight b d)),hr.2]

private theorem integrable_actual_old {a b c d : ℝ} (hg : SymmetricFullBox a b c d) :
    Integrable (fun p => actualExtendedThirdLowerFactor (actualPrismOld p))
      (prismProbability a b c d) := by
  let := prismProbability_isProbability (symmetric_positive hg).1 hg.width_xy
    (symmetric_positive hg).2 hg.width_z
  have hm : Measurable (prismPoint : PrismPoint → BoxPoint) := by
    apply measurable_pi_iff.2
    intro i
    fin_cases i
    · exact measurable_fst.fst
    · exact measurable_fst.snd
    · exact measurable_snd
  have hc := (measurable_actualExtendedThirdBufferedCap 0).comp hm
  have ho : Measurable actualPrismOld :=
    (((hc.sub measurable_fst.fst).sub measurable_fst.snd).sub measurable_snd).div measurable_snd
  apply Integrable.of_bound
    (measurable_actualExtendedThirdLowerFactor.comp ho).aestronglyMeasurable
    (1/(2*Real.exp Real.eulerMascheroniConstant))
  exact Filter.Eventually.of_forall (fun p => by
    change ‖actualExtendedThirdLowerFactor (actualPrismOld p)‖≤_
    rw [Real.norm_eq_abs,abs_of_nonneg (actualExtendedThirdLowerFactor_nonneg _)]
    exact actualExtendedThirdLowerFactor_le_normalization _)

/-- Genuine OLD factor integral lower bound for every original tent sum.
The true ordered mean is a computed expression, never a target hypothesis. -/
theorem symmetric_tent_chord_le_actual_integral
    (s : TentSum) (k : TentSide) {a b c d flo fhi : ℝ}
    (hg : SymmetricFullBox a b c d) (hmu : b≤VariableEnvelope.mu)
    (hactive : sourceActive s k (symmetricLeft a c) (symmetricRight b d))
    (hroot : planeUpper s k (symmetricLeft a c) (symmetricRight b d)≤thirdPrefixTheta)
    (hres : 0<oldNumerator s k (symmetricRight b d))
    (hlo : 2≤tentOldLow s k (symmetricRight b d))
    (hfl : flo≤actualExtendedThirdLowerFactor (tentOldLow s k (symmetricRight b d)))
    (hfh : fhi≤actualExtendedThirdLowerFactor (tentOldHigh s k (symmetricLeft a c))) :
    orderedTentChord s k a b c d flo fhi≤
      ∫ p, actualExtendedThirdLowerFactor (actualPrismOld p) ∂prismProbability a b c d := by
  let := prismProbability_isProbability (symmetric_positive hg).1 hg.width_xy
    (symmetric_positive hg).2 hg.width_z
  have hi := integrable_tent_argument s k hg hres
  have hch := (integrable_const flo).add
    (((hi.sub (integrable_const (tentOldLow s k (symmetricRight b d)))).div_const
      (tentOldHigh s k (symmetricLeft a c)-tentOldLow s k (symmetricRight b d))).mul_const (fhi-flo))
  have hbound := integral_mono_ae hch (integrable_actual_old hg) (show
      (fun p => flo+(tentOldArgument s k (prismPoint p)-tentOldLow s k (symmetricRight b d))/
        (tentOldHigh s k (symmetricLeft a c)-tentOldLow s k (symmetricRight b d))*(fhi-flo))
        ≤ᵐ[prismProbability a b c d]
      (fun p => actualExtendedThirdLowerFactor (actualPrismOld p)) from by
    filter_upwards [prism_mem_ae a b c d] with p hp
    have hr := symmetric_tent_minorant_range s k hg hmu hactive hroot hres hp
    exact (actual_lower_query_endpoint_chord hlo (symmetric_tent_span s k hg hres)
      hr.2 hfl hfh).trans (monotone_actualExtendedThirdLowerFactor hr.1))
  rw [integral_add' (integrable_const flo)
    (((hi.sub (integrable_const (tentOldLow s k (symmetricRight b d)))).div_const
      (tentOldHigh s k (symmetricLeft a c)-tentOldLow s k (symmetricRight b d))).mul_const (fhi-flo)),
    integral_mul_const,integral_div,
    integral_sub' hi (integrable_const (tentOldLow s k (symmetricRight b d)))] at hbound
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] at hbound
  rw [symmetric_tent_exact_ordered_mean s k hg] at hbound
  exact hbound

/-- The exact original Fraction operands, not arbitrary lower/upper queries. -/
def savedTentLow (s : TentSum) (k : TentSide) (x1 z1 : ℤ) : ℚ :=
  literalTentEndpoint s k ![x1,x1,z1] (48000*2^24)

def savedTentHigh (s : TentSum) (k : TentSide) (x0 z0 : ℤ) : ℚ :=
  literalTentEndpoint s k ![x0,x0,z0] (48000*2^24)

theorem saved_tent_endpoint_cast (s : TentSum) (k : TentSide)
    (x z : ℤ) (a c : ℚ)
    (ha : a=(x:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z:ℚ)/((48000*2^24:ℤ):ℚ)) (hz : 0<z) :
    (literalTentEndpoint s k ![x,x,z] (48000*2^24):ℝ)=
      tentOldArgument s k (symmetricLeft (a:ℝ) (c:ℝ)) := by
  apply literalTentEndpoint_cast
  · norm_num
  · have hzR : (0:ℝ)<(z:ℝ) := by exact_mod_cast hz
    simpa only [Matrix.cons_val_two] using hzR.ne'
  · intro i
    fin_cases i <;> simp only [symmetricLeft,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    · rw [ha]
      simp only [Rat.cast_div,Rat.cast_intCast]
    · rw [ha]
      simp only [Rat.cast_div,Rat.cast_intCast]
    · rw [hc]
      simp only [Rat.cast_div,Rat.cast_intCast]

/-- Both OLD endpoint queries and the original UNREDUCED NEW query are
supplied by one immutable checked reader. No factor-query result is input. -/
theorem symmetric_saved_tent_three_queries
    (table : CheckedBlockTable) (s : TentSum) (k : TentSide) (x0 x1 z0 z1 : ℤ) :
    value (readQueryLo160 (assembledRead table.blocks)
      (savedTentLow s k x1 z1).num ((savedTentLow s k x1 z1).den:ℤ))≤
        actualExtendedThirdLowerFactor (savedTentLow s k x1 z1:ℝ) ∧
    value (readQueryLo160 (assembledRead table.blocks)
      (savedTentHigh s k x0 z0).num ((savedTentHigh s k x0 z0).den:ℤ))≤
        actualExtendedThirdLowerFactor (savedTentHigh s k x0 z0:ℝ) ∧
    actualExtendedThirdLowerFactor
      (((storedGridNew x0 x1 z0 z1).hi:ℝ)/(P160:ℝ))≤
        value (readQueryHi160 (assembledRead table.blocks)
          (storedGridNew x0 x1 z0 z1).hi P160) := by
  refine ⟨(stored_rat_query_encloses table (savedTentLow s k x1 z1)).1,
    (stored_rat_query_encloses table (savedTentHigh s k x0 z0)).1,?_⟩
  simpa only [value,P160,Int.cast_pow,Int.cast_ofNat] using
    (CheckedBlockTable.query_encloses_all table (storedGridNew x0 x1 z0 z1).hi
      P160 P160_pos).2

def literalSymmetricBranch (s : TentSum) (k : TentSide)
    (x0 x1 z0 z1 : ℤ) : Prop :=
  match k with
  | .rise => -50*(48000*2^24)+256*
      (literalTentX s*x1+literalTentY s*x1+literalTentZ s*z1)≤0
  | .fall => ¬(-50*(48000*2^24)+256*
      (literalTentX s*x1+literalTentY s*x1+literalTentZ s*z1)≤0) ∧
      0≤-50*(48000*2^24)+256*
        (literalTentX s*x0+literalTentY s*x0+literalTentZ s*z0)

def literalSymmetricRoot (s : TentSum) (k : TentSide) (x0 x1 z0 z1 : ℤ) : Prop :=
  match k with
  | .rise => (48000*2^24)+literalTentX s*x1+literalTentY s*x1+literalTentZ s*z1≤
      2*481573208064
  | .fall => 57*(48000*2^24)-96*
      (literalTentX s*x0+literalTentY s*x0+literalTentZ s*z0)≤64*481573208064

def literalSymmetricResidual (s : TentSum) (k : TentSide) (x1 : ℤ) : Prop :=
  match k with
  | .rise => 0<(48000*2^24)+(literalTentX s-2)*x1+(literalTentY s-2)*x1
  | .fall => 0<57*(48000*2^24)+(-96*literalTentX s-64)*x1+
      (-96*literalTentY s-64)*x1

theorem symmetric_grid_bind (x z : ℤ) (a c : ℚ)
    (ha : a=(x:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z:ℚ)/((48000*2^24:ℤ):ℚ)) :
    ∀ i, symmetricLeft (a:ℝ) (c:ℝ) i=
      (![x,x,z] i:ℝ)/((48000*2^24:ℤ):ℝ) := by
  intro i
  fin_cases i <;> simp only [symmetricLeft,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  · rw [ha]
    simp only [Rat.cast_div,Rat.cast_intCast]
  · rw [ha]
    simp only [Rat.cast_div,Rat.cast_intCast]
  · rw [hc]
    simp only [Rat.cast_div,Rat.cast_intCast]

theorem positive_grid_binding (z : ℤ) (r : ℚ)
    (hr : r=(z:ℚ)/((48000*2^24:ℤ):ℚ)) (hp : (0:ℝ)<(r:ℝ)) : 0<z := by
  have hD : (0:ℝ)<((48000*2^24:ℤ):ℝ) := by norm_num
  have hrR : (r:ℝ)=(z:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [hr]
    simp only [Rat.cast_div,Rat.cast_intCast]
  have h := (lt_div_iff₀ hD).mp (by simpa only [hrR] using hp)
  have hz : (0:ℝ)<(z:ℝ) := by simpa only [zero_mul] using h
  exact_mod_cast hz

/-- Transport the exact original NEW.hi/P160 operand to its physical
interval expression. This bridge also applies below mu: it uses only
coordinate positivity, not the above-mu Jensen conclusion. -/
theorem symmetric_saved_tent_new_query
    (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)) :
    actualExtendedThirdLowerFactor
      (symmetricNewQuery (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)
        (originalLnUnit ((b:ℝ)/(a:ℝ))):ℝ)≤
      value (readQueryHi160 (assembledRead table.blocks)
        (storedGridNew x0 x1 z0 z1).hi P160) := by
  have hx0 := positive_grid_binding x0 a ha (symmetric_positive hg).1
  have hz0 := positive_grid_binding z0 c hc (symmetric_positive hg).2
  have hz1 := positive_grid_binding z1 d hd ((symmetric_positive hg).2.trans hg.width_z)
  have htree := stored_grid_new_eq x0 x1 z0 z1 a b c d ha hb hc hd hx0 hz0 hz1
  have harg :
      (symmetricNewQuery (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)
        (originalLnUnit ((b:ℝ)/(a:ℝ))):ℝ)=
      ((storedGridNew x0 x1 z0 z1).hi:ℝ)/(P160:ℝ) := by
    simp only [symmetricNewQuery,Rat.cast_div,Rat.cast_intCast,htree]
  rw [harg]
  simpa only [value,P160,Int.cast_pow,Int.cast_ofNat] using
    (CheckedBlockTable.query_encloses_all table (storedGridNew x0 x1 z0 z1).hi
      P160 P160_pos).2

/-- Integer producer branch/root/low_num tests, literal Fraction endpoints,
and SAME-reader endpoint queries supply the true symmetric OLD integral.
No cap-minorant, OLD range, mean identity, query result or integral estimate
is a caller premise. The selected s/k and its original max-score choice are
separate data obligations; no max-score conclusion is fabricated here. -/
theorem symmetric_saved_tent_old_integral
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
    orderedTentChord s k (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)
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
    rw [← hloEq]
    exact_mod_cast hlow
  have hqueries := symmetric_saved_tent_three_queries table s k x0 x1 z0 z1
  exact symmetric_tent_chord_le_actual_integral s k hg hmu
    hguards.1 hguards.2.1 hguards.2.2 hloR
    (by rw [← hloEq]; exact hqueries.1)
    (by rw [← hhiEq]; exact hqueries.2.1)

end
end ImbalancedChen.OriginalThirdP4ASymmetricTentPrerequisites
