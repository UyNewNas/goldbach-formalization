import ImbalancedChen.P5OldFifthFirstFConcavity
import ImbalancedChen.P5OldFifthChildQJensen
import ImbalancedChen.P1FifthUnitBoxLiteralGainLower
import Mathlib.Analysis.Convex.Integral

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual grid1600 child, its original frozen parent picks, the same
strict-gate positive kernel, and the exact 32-vertex gap are used throughout.
The closed-child ratio guard is a geometric payload obligation. The Q range,
normalized Jensen range, and the target integral inequality are proved here.
No whole-owner integral, saved floor, or current K is claimed.
-/

namespace ImbalancedChen.P5OldFifthActualChildJensenIntegral
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthRawBoxSelectorEquivalence
open P1LiteralVariableFifthCompactSupplier
open P1FifthUnitBoxLiteralGainLower
open P5OldFifthExact64ChildTiling
open P5OldFifthFrozenUpperSurrogate
open P5OldFifthFrozenGapConcavity
open P5OldFifthOneCoordinateVertexChord
open P5OldFifthFiveCoordinateBarycentric
open P5OldFifthChildGapIntegral
open P5OldFifthPointwiseQ
open P5OldFifthFirstFConcavity
open P5OldFifthChildQJensen

abbrev Point := Fin 5 → ℝ

def childClosed (raw : FifthWireRow) (c : ChildIndex) : Set Point :=
  Icc (childLeft raw c) (childRight raw c)

theorem childBox_subset_closed (raw : FifthWireRow) (c : ChildIndex) :
    childBox raw c ⊆ childClosed raw c := by
  intro t ht
  exact ⟨fun i => (ht i).1, fun i => (ht i).2.le⟩

theorem childRight_pos (raw : FifthWireRow) (c : ChildIndex)
    (hleft : ∀ i : Fin 5, 0 < childLeft raw c i) (i : Fin 5) :
    0 < childRight raw c i := by
  linarith [hleft i, child_span_pos raw c i]

theorem child_point_pos (raw : FifthWireRow) (c : ChildIndex)
    (hleft : ∀ i : Fin 5, 0 < childLeft raw c i)
    {t : Point} (ht : t ∈ childClosed raw c) : ∀ i : Fin 5, 0 < t i := by
  intro i
  exact (hleft i).trans_le (ht.1 i)

/-- A geometric ratio bound, not an integral premise, bounds the actual
positive frozen gap. Both the full own-cube wall and the same old parent
remain inside frozenCeiling. -/
theorem positive_gap_le_ratio_times_last
    (picks : ParentPicks) (raw : FifthWireRow) (t : Point)
    (ht4 : 0 < t 4) {b : ℝ} (hb2 : 2 ≤ b)
    (hnew : residual (rawCandidate 0 raw t) t ≤ b) :
    max 0 (frozenGap picks raw t) ≤ (b - 2) * t 4 := by
  have hnew' : rawCandidate 0 raw t - sum5 t ≤ b * t 4 :=
    (div_le_iff₀ ht4).mp hnew
  have hwall : ownCubeThreshold t ≤ frozenCeiling picks t :=
    le_max_right _ _
  apply max_le (mul_nonneg (sub_nonneg.mpr hb2) ht4.le)
  dsimp [frozenGap]
  dsimp [ownCubeThreshold, sum5] at hwall hnew'
  linarith

/-- The actual variable t5 and its child upper endpoint T are kept distinct.
This proves every range guard used by the normalized Jensen application. -/
theorem childX_and_localRatio_bounds
    (picks : ParentPicks) (raw : FifthWireRow) (c : ChildIndex)
    (hleft : ∀ i : Fin 5, 0 < childLeft raw c i)
    {b : ℝ} (hb2 : 2 ≤ b)
    (hnew : ∀ t ∈ childClosed raw c,
      residual (rawCandidate 0 raw t) t ≤ b)
    {t : Point} (ht : t ∈ childClosed raw c) :
    childX picks raw c t ∈ Icc (0 : ℝ) (b - 2) ∧
      max 0 (frozenGap picks raw t) / t 4 ∈ Icc (0 : ℝ) (b - 2) ∧
      childX picks raw c t ≤ max 0 (frozenGap picks raw t) / t 4 := by
  have ht4 := child_point_pos raw c hleft ht 4
  have hT := childRight_pos raw c hleft 4
  have hrange := positive_gap_le_ratio_times_last picks raw t ht4 hb2 (hnew t ht)
  have hupper : t 4 ≤ childRight raw c 4 := ht.2 4
  have hgap0 : 0 ≤ max 0 (frozenGap picks raw t) := le_max_left _ _
  have hr0 : 0 ≤ max 0 (frozenGap picks raw t) / t 4 := div_nonneg hgap0 ht4.le
  have hrb : max 0 (frozenGap picks raw t) / t 4 ≤ b - 2 :=
    (div_le_iff₀ ht4).mpr hrange
  have hXr : childX picks raw c t ≤ max 0 (frozenGap picks raw t) / t 4 :=
    div_le_div_of_nonneg_left hgap0 ht4 hupper
  exact ⟨⟨div_nonneg hgap0 hT.le, hXr.trans hrb⟩, ⟨hr0, hrb⟩, hXr⟩

/-- The vertex gap lower bound and the actual geometric ratio guard already
force the saved Jensen input into the legal interval. No saved e-range
check, Q average, or desired integral is assumed. -/
theorem saved_e_mem_ratio_interval
    (picks : ParentPicks) (raw : FifthWireRow) (c : ChildIndex)
    (hleft : ∀ i : Fin 5, 0 < childLeft raw c i)
    {b : ℝ} (hb2 : 2 ≤ b)
    (hnew : ∀ t ∈ childClosed raw c,
      residual (rawCandidate 0 raw t) t ≤ b)
    (d : ℤ) (hd0 : 0 ≤ d) (hd : (d : ℝ) = vertexD picks raw c) :
    (d : ℝ) / (1024 * 1600 * childRight raw c 4) ∈ Icc (0 : ℝ) (b - 2) := by
  let T := childRight raw c 4
  let V := childVolume raw c
  have hT : 0 < T := childRight_pos raw c hleft 4
  have hV : 0 < V := childVolume_pos raw c
  have hdc : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd0
  refine ⟨div_nonneg hdc (by positivity), ?_⟩
  have hconst : IntegrableOn (fun _ : Point => (b - 2) * T) (childBox raw c) :=
    (continuous_const : Continuous (fun _ : Point => (b - 2) * T)).integrableOn_Icc.mono_set
      (childBox_subset_closed raw c)
  have hupper : (∫ t in childBox raw c, frozenGap picks raw t) ≤ V * ((b - 2) * T) := by
    have hi := setIntegral_mono_on (integrableOn_frozenGap picks raw c)
      hconst (childBox_measurable raw c) (fun t ht => by
        have hc := childBox_subset_closed raw c ht
        have hb := (childX_and_localRatio_bounds picks raw c hleft hb2 hnew hc).1.2
        have hb' := (div_le_iff₀ hT).mp hb
        exact (le_max_right 0 (frozenGap picks raw t)).trans hb')
    simpa only [setIntegral_const, smul_eq_mul,
      childVolume_eq_measureReal, V] using hi
  have hlower := integral_frozenGap_ge_saved_integer_d picks raw c d hd
  have hscaled : V * ((d : ℝ) / (1024 * 1600)) ≤ V * ((b - 2) * T) := by
    convert hlower.trans hupper using 1 <;> ring
  have hcancel := (mul_le_mul_left hV).mp hscaled
  have hnum := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1024 * 1600)).mp hcancel
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1024 * 1600 * T)).mpr
  nlinarith

/-- The actual normalized uniform-child Jensen inequality, with all Q
range guards derived from the source geometry and the 32-vertex gap. -/
theorem actual_child_Q_average_lower
    (picks : ParentPicks) (raw : FifthWireRow) (c : ChildIndex)
    (hleft : ∀ i : Fin 5, 0 < childLeft raw c i)
    {b : ℝ} (hb2 : 2 < b) (hb4 : b ≤ 4)
    (hnew : ∀ t ∈ childClosed raw c,
      residual (rawCandidate 0 raw t) t ≤ b)
    (d : ℤ) (hd0 : 0 ≤ d) (hd : (d : ℝ) = vertexD picks raw c) :
    Q b ((d : ℝ) / (1024 * 1600 * childRight raw c 4)) ≤
      ⨍ t in childBox raw c, Q b (childX picks raw c t) := by
  exact child_Q_average_ge_saved_e picks raw c b hb2 hb4
    (childRight_pos raw c hleft 4)
    (fun t ht => (childX_and_localRatio_bounds picks raw c hleft hb2.le hnew ht).1)
    d hd (saved_e_mem_ratio_interval picks raw c hleft hb2.le hnew d hd0 hd)

/-- Continuity of the same literal moving strict-gate profile on the actual
closed rectangular child. The true zero extension resolves the own-cube
wall; no cutoff discontinuity or assumed integrability is introduced. -/
theorem continuousOn_moving_gatedProfile_child
    (raw : FifthWireRow) (c : ChildIndex)
    (hleft : ∀ i : Fin 5, 0 < childLeft raw c i)
    (level : Point → ℝ) (hlevel : Continuous level) :
    ContinuousOn (fun t => primeOwnCubeGatedProfile (level t) t) (childClosed raw c) := by
  have ht : ∀ t ∈ childClosed raw c, 0 < t (Fin.last 4) :=
    fun t ht => child_point_pos raw c hleft ht (Fin.last 4)
  have hlast : ContinuousOn (fun t : Point => t (Fin.last 4)) (childClosed raw c) :=
    (continuous_apply _).continuousOn
  have hsum : Continuous (fun t : Point => ∑ i, t i) := by fun_prop
  have harg : ContinuousOn (fun t => (level t - ∑ i, t i) / t (Fin.last 4))
      (childClosed raw c) :=
    (hlevel.continuousOn.sub hsum.continuousOn).div hlast (fun t ht' => (ht t ht').ne')
  have hfactor := continuous_actualExtendedThirdLowerFactor.comp_continuousOn harg
  have hc : ContinuousOn (fun t => 4 * actualExtendedThirdLowerFactor
      ((level t - ∑ i, t i) / t (Fin.last 4)) / t (Fin.last 4))
      (childClosed raw c) :=
    (continuousOn_const.mul hfactor).div hlast (fun t ht' => (ht t ht').ne')
  apply hc.congr
  intro t ht'
  rw [p1PrimeOwnCubeGatedProfile_eq_profile _ t (ht t ht'),
    p1PrimeTupleMinusProfile_eq_lowerFactor _ t (ht t ht')]

theorem integrableOn_frozenUpperPositiveKernel_child
    (picks : ParentPicks) (raw : FifthWireRow) (c : ChildIndex)
    (hleft : ∀ i : Fin 5, 0 < childLeft raw c i) :
    IntegrableOn (frozenUpperPositiveKernel picks raw) (childBox raw c) := by
  have hp : ContinuousOn (fun t : Point => ∏ i, 1 / t i) (childClosed raw c) := by
    apply continuousOn_finsetProd Finset.univ
    intro i _
    exact continuousOn_const.div (continuous_apply i).continuousOn
      (fun t ht => (child_point_pos raw c hleft ht i).ne')
  have hnew := continuousOn_moving_gatedProfile_child raw c hleft _
    (continuous_rawCandidate 0 raw)
  have hold := continuousOn_moving_gatedProfile_child raw c hleft _
    (continuous_frozenParentUpper picks)
  have hc : ContinuousOn (frozenUpperPositiveKernel picks raw) (childClosed raw c) :=
    continuousOn_const.sup ((hnew.sub hold).mul hp)
  exact (hc.integrableOn_compact isCompact_Icc).mono_set (childBox_subset_closed raw c)

/-- The precise child endpoint reciprocal amplitude, before rewriting the
five grid1600 numerators into the producer's integer formula. -/
def childPrefactor (raw : FifthWireRow) (c : ChildIndex) : ℝ :=
  (4 / childRight raw c 4) * ∏ i : Fin 5, 1 / childRight raw c i

theorem childPrefactor_nonneg (raw : FifthWireRow) (c : ChildIndex)
    (hleft : ∀ i : Fin 5, 0 < childLeft raw c i) : 0 ≤ childPrefactor raw c := by
  unfold childPrefactor
  exact mul_nonneg (div_nonneg (by norm_num) (childRight_pos raw c hleft 4).le)
    (Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (childRight_pos raw c hleft i).le))

theorem childPrefactor_le_local (raw : FifthWireRow) (c : ChildIndex)
    (hleft : ∀ i : Fin 5, 0 < childLeft raw c i)
    {t : Point} (ht : t ∈ childClosed raw c) :
    childPrefactor raw c ≤ (4 / t 4) * ∏ i : Fin 5, 1 / t i := by
  have htp := child_point_pos raw c hleft ht
  have h4 : 4 / childRight raw c 4 ≤ 4 / t 4 :=
    div_le_div_of_nonneg_left (by norm_num) (htp 4) (ht.2 4)
  have hp : (∏ i : Fin 5, 1 / childRight raw c i) ≤ ∏ i : Fin 5, 1 / t i := by
    apply Finset.prod_le_prod
    · intro i _
      exact one_div_nonneg.mpr (childRight_pos raw c hleft i).le
    · intro i _
      exact div_le_div_of_nonneg_left (by norm_num) (htp i) (ht.2 i)
  exact mul_le_mul h4 hp
    (Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (childRight_pos raw c hleft i).le))
    (div_nonneg (by norm_num) (htp 4).le)

/-- Pointwise minorant with a constant child amplitude and the actual
normalized gap X=g_+/T. The comparison never replaces U_P by a constant. -/
theorem frozenUpperPositiveKernel_ge_childPrefactor_Q
    (picks : ParentPicks) (raw : FifthWireRow) (c : ChildIndex)
    (hleft : ∀ i : Fin 5, 0 < childLeft raw c i)
    {b : ℝ} (hb2 : 2 < b) (hb4 : b ≤ 4)
    (hnew : ∀ t ∈ childClosed raw c,
      residual (rawCandidate 0 raw t) t ≤ b)
    {t : Point} (ht : t ∈ childClosed raw c) :
    childPrefactor raw c * Q b (childX picks raw c t) ≤
      frozenUpperPositiveKernel picks raw t := by
  obtain ⟨hX, hr, hXr⟩ := childX_and_localRatio_bounds picks raw c hleft hb2.le hnew ht
  have hq := Q_monotoneOn_no_calculus_input hb2.le hb4 hX hr hXr
  have hq0 := Q_nonneg hb2.le hb4 hX
  have htp := child_point_pos raw c hleft ht
  have ha0 : 0 ≤ (4 / t 4) * ∏ i : Fin 5, 1 / t i :=
    mul_nonneg (div_nonneg (by norm_num) (htp 4).le)
      (Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (htp i).le))
  calc
    childPrefactor raw c * Q b (childX picks raw c t) ≤
        ((4 / t 4) * ∏ i : Fin 5, 1 / t i) * Q b (childX picks raw c t) :=
      mul_le_mul_of_nonneg_right (childPrefactor_le_local raw c hleft ht) hq0
    _ ≤ ((4 / t 4) * ∏ i : Fin 5, 1 / t i) *
        Q b (max 0 (frozenGap picks raw t) / t 4) :=
      mul_le_mul_of_nonneg_left hq ha0
    _ ≤ frozenUpperPositiveKernel picks raw t :=
      frozenUpperPositiveKernel_ge_Q_no_calculus_input picks raw t htp b hb2 hb4 (hnew t ht)

/-- The original whole-child Jensen lower bound (J), before the separate
archived integer logarithm floor and selected-owner clipping steps.
All analytical premises in the former ChildQJensen call are discharged
from literal geometry, actual profiles and the 32 actual gap vertices. -/
theorem integral_frozenUpperPositiveKernel_ge_child_Jensen
    (picks : ParentPicks) (raw : FifthWireRow) (c : ChildIndex)
    (hleft : ∀ i : Fin 5, 0 < childLeft raw c i)
    {b : ℝ} (hb2 : 2 < b) (hb4 : b ≤ 4)
    (hnew : ∀ t ∈ childClosed raw c,
      residual (rawCandidate 0 raw t) t ≤ b)
    (d : ℤ) (hd0 : 0 ≤ d) (hd : (d : ℝ) = vertexD picks raw c) :
    childVolume raw c * childPrefactor raw c *
        Q b ((d : ℝ) / (1024 * 1600 * childRight raw c 4)) ≤
      ∫ t in childBox raw c, frozenUpperPositiveKernel picks raw t := by
  let C := childBox raw c
  let V := childVolume raw c
  let A := childPrefactor raw c
  let e := (d : ℝ) / (1024 * 1600 * childRight raw c 4)
  have hV : 0 < V := childVolume_pos raw c
  have hA : 0 ≤ A := childPrefactor_nonneg raw c hleft
  have hXrange : ∀ t ∈ childClosed raw c, childX picks raw c t ∈ Icc (0 : ℝ) (b - 2) :=
    fun t ht => (childX_and_localRatio_bounds picks raw c hleft hb2.le hnew ht).1
  have hQint : IntegrableOn (fun t => Q b (childX picks raw c t)) C := by
    have hc : ContinuousOn (fun t => Q b (childX picks raw c t)) (childClosed raw c) :=
      (Q_continuousOn b hb2).comp (childX_continuous picks raw c).continuousOn hXrange
    exact (hc.integrableOn_compact isCompact_Icc).mono_set (childBox_subset_closed raw c)
  have hkernel := integrableOn_frozenUpperPositiveKernel_child picks raw c hleft
  have hint : A * (∫ t in C, Q b (childX picks raw c t)) ≤
      ∫ t in C, frozenUpperPositiveKernel picks raw t := by
    have hi := setIntegral_mono_on (hQint.const_mul A) hkernel (childBox_measurable raw c)
      (fun t ht => frozenUpperPositiveKernel_ge_childPrefactor_Q picks raw c hleft
        hb2 hb4 hnew (childBox_subset_closed raw c ht))
    simpa only [integral_const_mul] using hi
  have hj := actual_child_Q_average_lower picks raw c hleft hb2 hb4 hnew d hd0 hd
  have hscaled := mul_le_mul_of_nonneg_left hj (mul_nonneg hV.le hA)
  have hmass : volume.real C = V := childVolume_eq_measureReal raw c
  rw [setAverage_eq, hmass] at hscaled
  simp only [smul_eq_mul] at hscaled
  have hid : V * A * (V⁻¹ * (∫ t in C, Q b (childX picks raw c t))) =
      A * (∫ t in C, Q b (childX picks raw c t)) := by
    field_simp [hV.ne']
    <;> ring
  rw [hid] at hscaled
  exact hscaled.trans hint

/-- The grid1600 scale cancels exactly in the saved input e=d/(1024*h5).
This equality is arithmetic and does not authenticate any archived d. -/
theorem child_e_eq_integer_scale (raw : FifthWireRow) (c : ChildIndex) (d : ℤ) :
    (d : ℝ) / (1024 * 1600 * childRight raw c 4) =
      (d : ℝ) / (1024 * (childRightNumer raw c 4 : ℝ)) := by
  simp only [childRight]
  congr 1
  ring

/-- The real child amplitude is exactly the original integer width/right
numerator prefactor 4*n*prod(width)/(h5*prod(h_i)), with n=1600. -/
theorem child_volume_mul_prefactor_integerScale
    (raw : FifthWireRow) (c : ChildIndex)
    (hleft : ∀ i : Fin 5, 0 < childLeft raw c i) :
    childVolume raw c * childPrefactor raw c =
      (4 * 1600 * ∏ i : Fin 5, (width i : ℝ)) /
        ((childRightNumer raw c 4 : ℝ) * ∏ i : Fin 5, (childRightNumer raw c i : ℝ)) := by
  have hH : ∀ i : Fin 5, (childRightNumer raw c i : ℝ) ≠ 0 := by
    intro i hi
    have hpos := childRight_pos raw c hleft i
    simp only [childRight, hi, zero_div] at hpos
    exact lt_irrefl _ hpos
  simp only [childVolume, childPrefactor, child_span, childRight, Fin.prod_univ_succ]
  field_simp [hH]
  <;> ring

end
end ImbalancedChen.P5OldFifthActualChildJensenIntegral
