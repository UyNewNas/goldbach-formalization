import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Recovered original common Poisson-frequency core

Source-preserving intake from the frozen original CommonPoissonLanes file,
Git blob 00a797ac77cb444479ce097f4b44c56930489e32, source SHA256
1c15c03a6fa6a1c188e8f5f2498aaee5f14da01b05e48676b263f9f3df1919e4.
The original namespace and mathematical statements are retained. The first
compile exposed three local elaboration issues: natural-number image domains,
filter-conjunction inference, and unfolding the existing tail before ring.
The repairs are recorded in EXPRESSION_REPAIR.json beside SOURCE_INTAKE.json;
current proof bodies are no longer byte-identical to the archived segments.

The exact signed window, dyadic ownership and common phase are followed by
the full absolutely-convergent Poisson series identity. Zero occurs once;
negative frequencies and the complementary tail remain literal.

The accepted Physical Poisson supplier has the same mathematical declarations
as the original dependency (only its prose header differs). OriginalData,
the original global cutoff and full-family coupling are not imported or
replaced. This file does not construct a spectral PacketData or assert the
smallness of its retained tail. A later full original source must import this
core instead of redeclaring the same constants.
-/

noncomputable section
open Classical Finset
open scoped BigOperators SchwartzMap FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.CommonSmoothCutoff
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical

namespace ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102

attribute [local instance] Classical.propDecidable

-- BEGIN recovered finite_core
def positiveM (J : ℕ) : Finset ℕ := Ico 1 (J + 1)
def mWindow (J : ℕ) : Finset ℤ :=
  insert 0 ((positiveM J).image (fun p : ℕ => (p : ℤ)) ∪
    (positiveM J).image (fun p : ℕ => -(p : ℤ)))

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
      (positiveM J).image (fun p : ℕ => (p : ℤ)) ∪
        (positiveM J).image (fun p : ℕ => -(p : ℤ)) := by
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
  have hdisj : Disjoint ((positiveM J).image (fun p : ℕ => (p : ℤ)))
      ((positiveM J).image (fun p : ℕ => -(p : ℤ))) := by
    apply disjoint_left.mpr
    intro m hm hn
    obtain ⟨p, hp, he⟩ := mem_image.mp hm
    obtain ⟨q, hq, he'⟩ := mem_image.mp hn
    have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast (mem_Ico.mp hp).1
    have hq1 : (1 : ℤ) ≤ q := by exact_mod_cast (mem_Ico.mp hq).1
    omega
  have hplus :
      (∑ m ∈ (positiveM J).image (fun p : ℕ => (p : ℤ)), g m) =
        ∑ p ∈ positiveM J, g (p : ℤ) := by
    rw [sum_image]
    intro p hp q hq he
    exact_mod_cast he
  have hminus :
      (∑ m ∈ (positiveM J).image (fun p : ℕ => -(p : ℤ)), g m) =
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
    Nat.log 2 p = j := by
  have hmem : p ∈ positiveM J ∧ Nat.log 2 p = j := by
    simpa only [commonMBlock_eq_fibre, mem_filter] using hp
  exact hmem.2

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
-- END recovered finite_core

-- BEGIN recovered poisson_series
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
  dsimp only [poissonTail]
  ring
-- END recovered poisson_series

end ImbalancedChen.Part3.OriginalCommonPoissonLanes20261102
end
