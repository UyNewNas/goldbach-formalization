import ImbalancedChen.Part3OriginalCompletedReciprocalSource
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact signed Poisson-frequency bookkeeping for the actual original
completed reciprocal source.  One global cutoff gives one family of
common dyadic positive-m intervals.  Negative m is reflected with its
negative Fourier argument intact.  The infinite tail is RETAINED.
No assertion that this tail is small, or that a spectral PacketData has
been constructed, appears in this file.
-/

noncomputable section
open Classical Finset
open scoped BigOperators SchwartzMap FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.CommonSmoothCutoff
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical
open ImbalancedChen.Part3.ActualReciprocalSquarePoissonSourceOnly
open ImbalancedChen.Part3.ActualCompletedSquarePushforwardSourceOnly
open ImbalancedChen.Part3.OriginalSimultaneousPrefixCompletion20261102
open ImbalancedChen.Part3.OriginalCompletedReciprocalSource20261102

namespace ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102

attribute [local instance] Classical.propDecidable

def positiveM (J : ℕ) : Finset ℕ := Ico 1 (J + 1)
def mWindow (J : ℕ) : Finset ℤ :=
  insert 0 ((positiveM J).image (fun p => (p : ℤ)) ∪
    (positiveM J).image (fun p => -(p : ℤ)))

theorem zero_mem_mWindow (J : ℕ) : (0 : ℤ) ∈ mWindow J := mem_insert_self _ _

theorem mem_mWindow_iff (J : ℕ) (m : ℤ) : m ∈ mWindow J ↔ m.natAbs ≤ J := by
  constructor
  · intro hm
    rcases mem_insert.mp hm with hm | hm
    · subst m
      simp
    · rcases mem_union.mp hm with hm | hm
      · obtain ⟨p, hp, rfl⟩ := mem_image.mp hm
        have hh := (mem_Ico.mp hp).2
        simpa only [Int.natAbs_natCast] using (show p ≤ J by omega)
      · obtain ⟨p, hp, rfl⟩ := mem_image.mp hm
        have hh := (mem_Ico.mp hp).2
        simpa only [Int.natAbs_neg, Int.natAbs_natCast] using (show p ≤ J by omega)
  · intro hm
    by_cases hz : m = 0
    · subst m
      exact zero_mem_mWindow J
    · have hp : m.natAbs ∈ positiveM J := by
        apply mem_Ico.mpr
        have hn : m.natAbs ≠ 0 := fun h => hz (Int.natAbs_eq_zero.mp h)
        omega
      apply mem_insert_of_mem
      by_cases hs : 0 ≤ m
      · exact mem_union_left _ (mem_image.mpr ⟨m.natAbs, hp,
          by simp only [Int.natCast_natAbs, abs_of_nonneg hs]⟩)
      · exact mem_union_right _ (mem_image.mpr ⟨m.natAbs, hp,
          by simp only [Int.natCast_natAbs, abs_of_nonpos (le_of_not_ge hs), neg_neg]⟩)

/-- The signed finite interval includes m=0 exactly once. -/
theorem sum_mWindow (J : ℕ) (g : ℤ → ℂ) :
    (∑ m ∈ mWindow J, g m) =
      g 0 + (∑ p ∈ positiveM J, g (p : ℤ)) +
        ∑ p ∈ positiveM J, g (-(p : ℤ)) := by
  have hzero : (0 : ℤ) ∉
      (positiveM J).image (fun p => (p : ℤ)) ∪
        (positiveM J).image (fun p => -(p : ℤ)) := by
    intro hm
    rcases mem_union.mp hm with hm | hm
    · obtain ⟨p, hp, he⟩ := mem_image.mp hm
      have hh := (mem_Ico.mp hp).1
      have hp0 : p = 0 := by exact_mod_cast he
      omega
    · obtain ⟨p, hp, he⟩ := mem_image.mp hm
      have hh := (mem_Ico.mp hp).1
      have hp0 : (p : ℤ) = 0 := by omega
      have : p = 0 := by exact_mod_cast hp0
      omega
  have hdisj : Disjoint ((positiveM J).image (fun p => (p : ℤ)))
      ((positiveM J).image (fun p => -(p : ℤ))) := by
    apply disjoint_left.mpr
    intro m hm hn
    obtain ⟨p, hp, he⟩ := mem_image.mp hm
    obtain ⟨q, hq, he'⟩ := mem_image.mp hn
    have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast (mem_Ico.mp hp).1
    have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast (mem_Ico.mp hq).1
    omega
  have hplus :
      (∑ m ∈ (positiveM J).image (fun p => (p : ℤ)), g m) =
        ∑ p ∈ positiveM J, g (p : ℤ) := by
    rw [sum_image]
    intro p hp q hq he
    exact_mod_cast he
  have hminus :
      (∑ m ∈ (positiveM J).image (fun p => -(p : ℤ)), g m) =
        ∑ p ∈ positiveM J, g (-(p : ℤ)) := by
    rw [sum_image]
    intro p hp q hq he
    have h : (p : ℤ) = q := neg_injective he
    exact_mod_cast h
  rw [mWindow, sum_insert hzero, sum_union hdisj, hplus, hminus]
  ring

/-- Half-open dyadic intervals are chosen once from J, before any c,z,y
or oldform label is examined.  The last interval is clipped at J+1. -/
def blockIndices (J : ℕ) : Finset ℕ := range (Nat.log 2 J + 1)
def commonMBlock (J j : ℕ) : Finset ℕ := Ico (2 ^ j) (min (2 ^ (j + 1)) (J + 1))

theorem commonMBlock_eq_fibre (J j : ℕ) :
    commonMBlock J j = (positiveM J).filter (fun p => Nat.log 2 p = j) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hlo, hhi⟩ := mem_Ico.mp hp
    have hupper := lt_min_iff.mp hhi
    have hpow : 0 < (2 : ℕ) ^ j := pow_pos (by omega) _
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, hupper.2⟩,
      Nat.log_eq_of_pow_le_of_lt_pow hlo hupper.1⟩
  · intro hp
    obtain ⟨hp, he⟩ := mem_filter.mp hp
    obtain ⟨hpos, hcut⟩ := mem_Ico.mp hp
    have hne : p ≠ 0 := by omega
    have hlo := Nat.pow_log_le_self 2 hne
    have hhi := Nat.lt_pow_succ_log_self (by omega : 1 < (2 : ℕ)) p
    rw [he] at hlo hhi
    exact mem_Ico.mpr ⟨hlo, lt_min_iff.mpr ⟨hhi, hcut⟩⟩

theorem commonMBlock_owner {J p j : ℕ} (hp : p ∈ commonMBlock J j) :
    Nat.log 2 p = j := (mem_filter.mp (commonMBlock_eq_fibre J j ▸ hp)).2

theorem commonMBlock_unique {J p i j : ℕ}
    (hi : p ∈ commonMBlock J i) (hj : p ∈ commonMBlock J j) : i = j :=
  (commonMBlock_owner hi).symm.trans (commonMBlock_owner hj)

theorem sum_positiveM_eq_common_blocks (J : ℕ) (g : ℕ → ℂ) :
    (∑ p ∈ positiveM J, g p) =
      ∑ j ∈ blockIndices J, ∑ p ∈ commonMBlock J j, g p := by
  have hf := sum_fiberwise_of_maps_to (s := positiveM J) (t := blockIndices J)
    (g := Nat.log 2)
    (fun p hp => mem_range.mpr (by
      have hpJ : p ≤ J := by have := (mem_Ico.mp hp).2; omega
      have hlog := Nat.log_mono_right (b := 2) hpJ
      omega)) g
  simpa only [commonMBlock_eq_fibre] using hf.symm

theorem commonMBlock_normalized (J j : ℕ) {p : ℕ} (hp : p ∈ commonMBlock J j) :
    1 ≤ (p : ℝ) / (2 ^ j : ℕ) ∧ (p : ℝ) / (2 ^ j : ℕ) < 2 := by
  have hV : (0 : ℝ) < (2 ^ j : ℕ) := by positivity
  obtain ⟨hlo, hhi⟩ := mem_Ico.mp hp
  have hupper := (lt_min_iff.mp hhi).1
  have hloR : ((2 ^ j : ℕ) : ℝ) ≤ p := by exact_mod_cast hlo
  have hhiR : (p : ℝ) < 2 * (2 ^ j : ℕ) := by
    rw [pow_succ, mul_comm] at hupper
    exact_mod_cast hupper
  exact ⟨(le_div_iff₀ hV).mpr (by simpa only [one_mul] using hloR),
    (div_lt_iff₀ hV).mpr hhiR⟩

def commonPoissonCompleted (J j : ℕ) (k1 : ℤ) : CommonCompletedVariable where
  intervalLo := 2 ^ j
  intervalHi := min (2 ^ (j + 1)) (J + 1)
  additivePhase := (k1 : ℝ) / (64 * (2 ^ j : ℕ))

/-- The only completed-variable phase has the physical dyadic denominator.
It has no level argument and no dependence on the earlier s-frequency r. -/
theorem commonPoissonCompleted_weight (J j : ℕ) (k1 : ℤ) (p : ℕ)
    (hp : p ∈ commonMBlock J j) :
    (commonPoissonCompleted J j k1).weight p =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        ((k1 : ℝ) / (64 * (2 ^ j : ℕ)) : ℝ) * (p : ℂ)) := by
  exact if_pos hp

def globalCutoff (D : OriginalData) (x epsilon : ℝ) : ℕ :=
  Nat.ceil ((D.cScale / D.bScale) * x ^ epsilon)

theorem globalCutoff_covers (D : OriginalData) (x epsilon : ℝ) :
    (D.cScale / D.bScale) * x ^ epsilon ≤ globalCutoff D x epsilon := Nat.le_ceil _

def poissonTail (J : ℕ) (M : ℝ) (c : ℕ) (a y z : ℤ) : ℂ :=
  ∑' m : {m : ℤ // m ∉ mWindow J}, frequency M c a y z m

theorem tail_frequency_outside (J : ℕ) (m : {m : ℤ // m ∉ mWindow J}) :
    J < m.val.natAbs ∧ m.val ≠ 0 := by
  have hgt : J < m.val.natAbs :=
    Nat.lt_of_not_ge (fun h => m.property ((mem_mWindow_iff J m.val).mpr h))
  refine ⟨hgt, ?_⟩
  intro h
  apply m.property
  simpa only [h] using zero_mem_mWindow J

/-- Exact finite/infinite split, using the actual Poisson summability.
The tail is an explicit absolutely convergent subseries, not a remainder
defined by subtracting the asserted identity. -/
theorem poisson_series_eq_lanes {c : ℕ} [NeZero c] {M : ℝ} (hM : 0 < M)
    (J : ℕ) (a y : ℤ) (z : ℕ) (hz : c.Coprime z) :
    (∑' m : ℤ, frequency M c a y (z : ℤ) m) =
      frequency M c a y (z : ℤ) 0 +
      (∑ j ∈ blockIndices J,
        ((∑ p ∈ commonMBlock J j, frequency M c a y (z : ℤ) (p : ℤ)) +
         ∑ p ∈ commonMBlock J j, frequency M c a y (z : ℤ) (-(p : ℤ)))) +
      poissonTail J M c a y (z : ℤ) := by
  have hs : Summable (fun m : ℤ => frequency M c a y (z : ℤ) m) :=
    (completed_summable_norm (c := c) hM a y (z : ℤ)
      ((isUnit_intCast_iff_natAbs_coprime (c := c) (z : ℤ)).mpr
        (by simpa only [Int.natAbs_natCast] using hz.symm))).of_norm
  rw [← hs.sum_add_tsum_subtype_compl (mWindow J), sum_mWindow,
    sum_positiveM_eq_common_blocks J (fun p => frequency M c a y (z : ℤ) (p : ℤ)),
    sum_positiveM_eq_common_blocks J (fun p => frequency M c a y (z : ℤ) (-(p : ℤ)))]
  rw [sum_add_distrib]
  ring

/-- Negative original m keeps the Fourier transform evaluated at -pM/c.
Only the Kloosterman sign chart is changed; beta is not conjugated. -/
theorem negative_block_literal {c : ℕ} [NeZero c] (J j : ℕ)
    (M : ℝ) (a y : ℤ) (z : ℕ) :
    (∑ p ∈ commonMBlock J j, frequency M c a y (z : ℤ) (-(p : ℤ))) =
      ∑ p ∈ commonMBlock J j,
        (M / (c : ℝ)) • (𝓕 dyadicCutoffSchwartz) (-(M / (c : ℝ)) * (p : ℝ)) *
          kloosterman c ((p : ℤ) * inverseResidue c (z : ℤ)) (-(a * y)) := by
  apply sum_congr rfl
  intro p hp
  simpa only [Int.cast_natCast] using frequency_negative (c := c) M a y (z : ℤ) (p : ℤ)

def weightedC (N C : ℝ) (z : ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ c ∈ Ioc 0 (Nat.floor (10 * C)),
    if c.Coprime z then (scaledDyadicCutoff N c : ℂ) * f c else 0

theorem weightedC_add (N C : ℝ) (z : ℕ) (f g : ℕ → ℂ) :
    weightedC N C z (fun c => f c + g c) = weightedC N C z f + weightedC N C z g := by
  unfold weightedC
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro c hc
  by_cases hz : c.Coprime z <;> simp only [hz, if_true, if_false, mul_add, zero_add]

theorem weightedC_sum {ι : Type*} (N C : ℝ) (z : ℕ) (I : Finset ι) (f : ι → ℕ → ℂ) :
    weightedC N C z (fun c => ∑ i ∈ I, f i c) = ∑ i ∈ I, weightedC N C z (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [weightedC]
  | @insert i I hi ih => simp only [sum_insert hi, weightedC_add, ih]

def zeroMKernel (M N C : ℝ) (a : ℤ) (zy : Output) : ℂ :=
  weightedC N C zy.1 (fun c => frequency M c a zy.2 (zy.1 : ℤ) 0)
def blockKernel (J j : ℕ) (negativeM : Bool) (M N C : ℝ) (a : ℤ) (zy : Output) : ℂ :=
  weightedC N C zy.1 (fun c => ∑ p ∈ commonMBlock J j,
    frequency M c a zy.2 (zy.1 : ℤ) (if negativeM then -(p : ℤ) else (p : ℤ)))
def tailKernel (J : ℕ) (M N C : ℝ) (a : ℤ) (zy : Output) : ℂ :=
  weightedC N C zy.1 (fun c => poissonTail J M c a zy.2 (zy.1 : ℤ))

/-- The true physical Kloosterman kernel, with its c-unit filter, has
separate zero-m, common positive/reflected-negative blocks, and tail. -/
theorem completedKernel_eq_m_lanes {M : ℝ} (hM : 0 < M)
    (J : ℕ) (N C : ℝ) (a : ℤ) (zy : Output) :
    completedKernel M N C a zy = zeroMKernel M N C a zy +
      (∑ j ∈ blockIndices J,
        (blockKernel J j false M N C a zy + blockKernel J j true M N C a zy)) +
      tailKernel J M N C a zy := by
  have hpoint : completedKernel M N C a zy = weightedC N C zy.1 (fun c =>
      frequency M c a zy.2 (zy.1 : ℤ) 0 +
      (∑ j ∈ blockIndices J,
        ((∑ p ∈ commonMBlock J j, frequency M c a zy.2 (zy.1 : ℤ) (p : ℤ)) +
         ∑ p ∈ commonMBlock J j, frequency M c a zy.2 (zy.1 : ℤ) (-(p : ℤ)))) +
      poissonTail J M c a zy.2 (zy.1 : ℤ)) := by
    unfold completedKernel weightedC
    apply sum_congr rfl
    intro c hc
    by_cases hcz : c.Coprime zy.1
    · let : NeZero c := ⟨(mem_Ioc.mp hc).1.ne'⟩
      simp only [if_pos hcz]
      rw [poisson_series_eq_lanes hM J a zy.2 zy.1 hcz]
    · simp only [if_neg hcz]
  rw [hpoint, weightedC_add, weightedC_add, weightedC_sum]
  simp only [weightedC_add, zeroMKernel, blockKernel, tailKernel, Bool.false_eq_true,
    if_false, if_true]

def jointZeroM (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (M N : ℝ) (U : Finset Source) : ℂ :=
  ∑ zy ∈ U.image output, jointBeta D r U zy * zeroMKernel M N D.cScale D.block.atom.residue zy
def jointBlock (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (J j : ℕ) (negativeM : Bool) (M N : ℝ) (U : Finset Source) : ℂ :=
  ∑ zy ∈ U.image output,
    jointBeta D r U zy * blockKernel J j negativeM M N D.cScale D.block.atom.residue zy
def jointTail (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (J : ℕ) (M N : ℝ) (U : Finset Source) : ℂ :=
  ∑ zy ∈ U.image output,
    jointBeta D r U zy * tailKernel J M N D.cScale D.block.atom.residue zy
def resolvedJointMass (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (J : ℕ) (M N : ℝ) (U : Finset Source) : ℂ :=
  jointZeroM D r M N U +
    (∑ j ∈ blockIndices J, jointBlock D r J j false M N U + jointBlock D r J j true M N U) +
    jointTail D r J M N U

theorem jointMass_eq_resolved (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    {M : ℝ} (hM : 0 < M) (J : ℕ) (N : ℝ) (U : Finset Source) :
    jointMass D r M N U = resolvedJointMass D r J M N U := by
  unfold jointMass resolvedJointMass jointZeroM jointBlock jointTail
  simp_rw [completedKernel_eq_m_lanes hM J N D.cScale D.block.atom.residue]
  simp only [mul_add, mul_sum, sum_add_distrib]
  rw [sum_comm (s := U.image output) (t := blockIndices J),
    sum_comm (s := U.image output) (t := blockIndices J)]

/-- No double payment: y=0 retains ALL m; only y>0 and y<0 are split
into their separate m=0, common dyadic nonzero-m blocks and explicit tails. -/
def resolvedThreeLanes (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (J : ℕ) (M N : ℝ) : ℂ :=
  jointMass D r M N (zeroSource (originalSource D)) +
    resolvedJointMass D r J M N (positiveSource (originalSource D)) +
    resolvedJointMass D r J M N (negativeSource (originalSource D))

theorem threeLanes_eq_resolved (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    {M : ℝ} (hM : 0 < M) (J : ℕ) (N : ℝ) :
    threeLanes D r M N = resolvedThreeLanes D r J M N := by
  unfold threeLanes resolvedThreeLanes
  rw [jointMass_eq_resolved D r hM J N (positiveSource (originalSource D)),
    jointMass_eq_resolved D r hM J N (negativeSource (originalSource D))]

/-- Full original six-piece source with ONE global J.  Its coefficient
contains only the original common s-frequency and original f/h masks;
its completed nonzero variable is separately the Poisson m. -/
theorem original_six_global_m_dictionary (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (x epsilon : ℝ) :
    let J := globalCutoff D x epsilon
    (smoothSix D r : ℂ) =
      resolvedThreeLanes D r J D.bScale D.cScale +
      resolvedThreeLanes D r J D.bScale (2 * D.cScale) +
      resolvedThreeLanes D r J D.bScale (4 * D.cScale) +
      resolvedThreeLanes D r J (2 * D.bScale) D.cScale +
      resolvedThreeLanes D r J (2 * D.bScale) (2 * D.cScale) +
      resolvedThreeLanes D r J (2 * D.bScale) (4 * D.cScale) := by
  dsimp only
  rw [original_six_eq_signed_joint_source]
  have hB2 : 0 < 2 * D.bScale := mul_pos (by norm_num) D.bScale_pos
  simp only [threeLanes_eq_resolved D r D.bScale_pos (globalCutoff D x epsilon),
    threeLanes_eq_resolved D r hB2 (globalCutoff D x epsilon)]

end ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102
end
