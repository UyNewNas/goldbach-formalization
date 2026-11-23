import ImbalancedChen.P4BSupportedRampStripUnion
import ImbalancedChen.P4BNormalizedImbalanceStripMass
import ImbalancedChen.P4BLowerProductStripMass

/-!
# P4B: unconditional mass reserve for the jointly supported badness strip

YELLOW / SOURCE ONLY / UNCOMPILED.

The carrier is the actual jointly supported physical strip at wall 1.
At width at most log 2 its product cap is at most 2N. Reindexing by the
literal tuple-pair map lands in either the existing normalized collar at
2N or the full low-product prime-pair set there. The first reserve comes
from the proved exponent-source band theorem, the second from the proved
two-orientations ceiling bound and cutoff absorption. No reserve or source
mass conclusion is introduced as a hypothesis.
-/

namespace ImbalancedChen.P4BSupportedBadnessStripMass

noncomputable section
open scoped Classical BigOperators
open Filter Topology
open ImbalancedChen.Part3 ImbalancedChen.P4B
open ImbalancedChen.P4BLabelledPairDictionary
open ImbalancedChen.P4BLabelledLogGeometry
open ImbalancedChen.P4BNormalizedImbalanceStripMass
open ImbalancedChen.P4BLowerProductStripMass

/-- All prime pairs below the new lower cutoff, without a width or ordering
condition. Its unconditional crude count pays every low-product branch. -/
def lowPrimePairs (kappa : ℝ) (M : ℕ) : Finset (ℕ × ℕ) :=
  (ordinaryPrimePairs M).filter (fun p =>
    (p.1 * p.2 : ℕ) < manuscriptHalfProductCutoff kappa M)

theorem lowPrimePairs_card_le_two_ceil (kappa : ℝ) (M : ℕ) :
    (lowPrimePairs kappa M).card ≤ 2 * Nat.ceil (manuscriptHalfProductCutoff kappa M) := by
  apply prime_pairs_card_le_two_ceil (lowPrimePairs kappa M)
    (manuscriptHalfProductCutoff kappa M)
  · intro p hp
    have hcarrier := (Finset.mem_filter.mp hp).1
    exact ⟨(mem_ordinaryPrimePairs.mp hcarrier).2.2.1,
      (mem_ordinaryPrimePairs.mp hcarrier).2.2.2⟩
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.le

/-- Both exact logarithmic comparison bounds for changing N to 2N. -/
theorem log_double_bounds {N : ℕ} (hN : 2 ≤ N) :
    Real.log (N : ℝ) ≤ Real.log ((2 * N : ℕ) : ℝ) ∧
      Real.log ((2 * N : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h2N : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog2N : Real.log (2 : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) h2N
  have heq : Real.log ((2 * N : ℕ) : ℝ) =
      Real.log (2 : ℝ) + Real.log (N : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNpos.ne')
  rw [heq]
  constructor <;> linarith

/-- The original mass scale at the doubled cap costs at most a factor two. -/
theorem massScale_double_le {N : ℕ} (hN : 2 ≤ N) :
    (((2 * N : ℕ) : ℝ) / Real.log ((2 * N : ℕ) : ℝ)) ≤
      2 * ((N : ℝ) / Real.log (N : ℝ)) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hlogLe := (log_double_bounds hN).1
  have hlogM : 0 < Real.log ((2 * N : ℕ) : ℝ) := hlogN.trans_le hlogLe
  calc
    (((2 * N : ℕ) : ℝ) / Real.log ((2 * N : ℕ) : ℝ)) ≤
        ((2 * N : ℕ) : ℝ) / Real.log (N : ℝ) := by
      apply (div_le_div_iff₀ hlogM hlogN).mpr
      exact mul_le_mul_of_nonneg_left hlogLe (Nat.cast_nonneg (2 * N))
    _ = 2 * ((N : ℝ) / Real.log (N : ℝ)) := by
      rw [Nat.cast_mul, Nat.cast_ofNat]
      ring

/-- The actual first physical margin is exactly the normalized badness wall. -/
theorem physical_badness_margin_eq_normalizedWall
    (b T : ℝ) (N : ℕ) (t : Fin 2 → Fin (N + 1)) :
    physicalPairMargins b N T t 1 =
      normalizedWall b N (tuplePair t).1 (tuplePair t).2 := by
  change (Real.log ((t 0).val : ℝ) / Real.log (N : ℝ) -
      b * (Real.log ((t 1).val : ℝ) / Real.log (N : ℝ))) =
    (Real.log ((t 0).val : ℝ) - b * Real.log ((t 1).val : ℝ)) / Real.log (N : ℝ)
  ring

/-- A nonpositive normalized numerator stays in the same one-sided collar
when the positive denominator increases from log N to log(2N). -/
theorem normalizedWall_double_mem_interval {b width : ℝ} {N r q : ℕ}
    (hN : 2 ≤ N)
    (hwall : -width < normalizedWall b N r q ∧ normalizedWall b N r q ≤ 0) :
    -width < normalizedWall b (2 * N) r q ∧ normalizedWall b (2 * N) r q ≤ 0 := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hlogLe := (log_double_bounds hN).1
  have hlogM : 0 < Real.log ((2 * N : ℕ) : ℝ) := hlogN.trans_le hlogLe
  have hnum : Real.log (r : ℝ) - b * Real.log (q : ℝ) ≤ 0 := by
    have hh := (div_le_iff₀ hlogN).mp hwall.2
    simpa only [zero_mul] using hh
  have hratio : normalizedWall b N r q ≤ normalizedWall b (2 * N) r q := by
    apply (div_le_div_iff₀ hlogN hlogM).mpr
    exact mul_le_mul_of_nonpos_left hlogLe hnum
  exact ⟨hwall.1.trans_le hratio, div_nonpos_of_nonpos_of_nonneg hnum hlogM.le⟩

/-- On the badness-side strip, b<1 and prime q>1 force the original order. -/
theorem pair_order_of_nonpositive_badness_margin {b T : ℝ} {N : ℕ}
    (hb1 : b < 1) (hN : 2 ≤ N) {t : Fin 2 → Fin (N + 1)}
    (ht : t ∈ labelledPrimeTuples 2 N) (hbad : physicalPairMargins b N T t 1 ≤ 0) :
    (tuplePair t).1 ≤ (tuplePair t).2 := by
  have hp : ∀ i : Fin 2, Nat.Prime (t i).val := (Finset.mem_filter.mp ht).2
  obtain ⟨hrR, hqR⟩ := labelled_prime_pair_pos ht
  have hq1 : (1 : ℝ) < (tuplePair t).2 := by
    change (1 : ℝ) < ((t 1).val : ℝ)
    exact_mod_cast (show 1 < (t 1).val by have hh := (hp 1).two_le; omega)
  have hlogq : 0 < Real.log ((tuplePair t).2 : ℝ) := Real.log_pos hq1
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  rw [physical_badness_margin_eq_normalizedWall] at hbad
  have hnum := (div_le_iff₀ (Real.log_pos hN1)).mp hbad
  have hbq : b * Real.log ((tuplePair t).2 : ℝ) ≤ Real.log ((tuplePair t).2 : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hb1.le hlogq.le
  have hlogs : Real.log ((tuplePair t).1 : ℝ) ≤ Real.log ((tuplePair t).2 : ℝ) := by
    linarith only [hnum, hbq]
  have hreal := (Real.log_le_log_iff hrR hqR).mp hlogs
  exact_mod_cast hreal

/-- Complete physical upper support gives a cap 2N for width<=log 2.
No nonzero-product hypothesis is substituted for the actual joint support. -/
theorem pair_product_le_double_of_upper_support
    {b T width : ℝ} {N : ℕ} (hN : 2 ≤ N) (hwidth : width ≤ Real.log (2 : ℝ))
    {t : Fin 2 → Fin (N + 1)} (ht : t ∈ labelledPrimeTuples 2 N)
    (hsoft : -width < physicalPairMargins b N T t 3) :
    (tuplePair t).1 * (tuplePair t).2 ≤ 2 * N := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN1
  obtain ⟨hr, hq⟩ := labelled_prime_pair_pos ht
  rw [physicalPairMargins_upper_eq_log_gap b T hN1 t] at hsoft
  have hlt : (((tuplePair t).1 * (tuplePair t).2 : ℕ) : ℝ) <
      Real.exp width * (N : ℝ) := by
    rw [Nat.cast_mul]
    apply (Real.log_lt_log_iff (mul_pos hr hq) (mul_pos (Real.exp_pos width) hNpos)).mp
    rw [Real.log_mul hr.ne' hq.ne',
      Real.log_mul (Real.exp_pos width).ne' hNpos.ne', Real.log_exp]
    linarith only [hsoft]
  have hexp : Real.exp width ≤ (2 : ℝ) := by
    calc
      Real.exp width ≤ Real.exp (Real.log (2 : ℝ)) := Real.exp_le_exp.mpr hwidth
      _ = 2 := Real.exp_log (by norm_num)
  have hle : (((tuplePair t).1 * (tuplePair t).2 : ℕ) : ℝ) ≤ (2 : ℝ) * N :=
    hlt.le.trans (mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg N))
  exact_mod_cast hle

/-- The normalized collar increases monotonically with its width. -/
theorem normalizedPrimePairStrip_mono_width {b kappa width widthMax : ℝ} {M : ℕ}
    (hwidth : width ≤ widthMax) :
    normalizedPrimePairStrip b kappa width M ⊆ normalizedPrimePairStrip b kappa widthMax M := by
  rintro ⟨r, q⟩ hp
  rcases mem_normalizedPrimePairStrip.mp hp with ⟨hr, hq, hord, hcut, hprod, hlo, hhi⟩
  exact mem_normalizedPrimePairStrip.mpr
    ⟨hr, hq, hord, hcut, hprod, by linarith, hhi⟩

/-- Exact finite containment at cap M=2N. Every jointly supported badness
point maps into the normalized collar at M or the full low-product set. -/
theorem supported_badness_pair_mem_union
    {b kappa T width : ℝ} {N : ℕ} (hb1 : b < 1) (hN : 2 ≤ N)
    (hwidth : width ≤ Real.log (2 : ℝ)) {t : Fin 2 → Fin (N + 1)}
    (ht : t ∈ physicalSupportedStrip width b N T 1) :
    tuplePair t ∈ normalizedPrimePairStrip b kappa width (2 * N) ∪ lowPrimePairs kappa (2 * N) := by
  obtain ⟨htprime, hwall, hsoft⟩ := Finset.mem_filter.mp ht
  have hp : ∀ i : Fin 2, Nat.Prime (t i).val := (Finset.mem_filter.mp htprime).2
  have horder := pair_order_of_nonpositive_badness_margin hb1 hN htprime hwall.2
  have hprod := pair_product_le_double_of_upper_support hN hwidth htprime (hsoft 3)
  rw [physical_badness_margin_eq_normalizedWall] at hwall
  have hwallM := normalizedWall_double_mem_interval hN hwall
  by_cases hcut : manuscriptHalfProductCutoff kappa (2 * N) ≤
      ((tuplePair t).1 * (tuplePair t).2 : ℕ)
  · exact Finset.mem_union_left _ (mem_normalizedPrimePairStrip.mpr
      ⟨hp 0, hp 1, horder, hcut, hprod, hwallM.1, hwallM.2⟩)
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨mem_ordinaryPrimePairs.mpr ⟨?_, ?_, hp 0, hp 1⟩, lt_of_not_ge hcut⟩
    · have hcoord := Nat.lt_succ_iff.mp (t 0).isLt
      change (t 0).val ≤ 2 * N
      omega
    · have hcoord := Nat.lt_succ_iff.mp (t 1).isLt
      change (t 1).val ≤ 2 * N
      omega

/-- The genuine tuple-pair map is injective; no factor-witness multiplicity
or factor two is introduced in passing to the two actual pair sets. -/
theorem supported_badness_card_le_strip_add_low
    {b kappa T width : ℝ} {N : ℕ} (hb1 : b < 1) (hN : 2 ≤ N)
    (hwidth : width ≤ Real.log (2 : ℝ)) :
    (physicalSupportedStrip width b N T 1).card ≤
      (normalizedPrimePairStrip b kappa width (2 * N)).card + (lowPrimePairs kappa (2 * N)).card := by
  have hcard : (physicalSupportedStrip width b N T 1).card ≤
      (normalizedPrimePairStrip b kappa width (2 * N) ∪ lowPrimePairs kappa (2 * N)).card := by
    apply Finset.card_le_card_of_injOn (@tuplePair N)
    · intro t ht
      exact supported_badness_pair_mem_union hb1 hN hwidth ht
    · intro t ht u hu heq
      exact tuplePair_injective N heq
  exact hcard.trans (Finset.card_union_le _ _)

/-- Unconditional actual jointly supported badness reserve. Width is chosen
below any prescribed positive maximum, then one threshold works for every N.
No boundary reserve, mass limit or equivalent conclusion is a premise. -/
theorem exists_supported_badness_strip_mass_reserve
    {b kappa eta widthMax : ℝ}
    (hbHalf : (1 / 2 : ℝ) < b) (hb1 : b < 1)
    (hkappa : 0 < kappa) (hkappa1 : kappa < 1)
    (heta : 0 < eta) (hwidthMax : 0 < widthMax) :
    ∃ width : ℝ, 0 < width ∧ width ≤ widthMax ∧ width ≤ Real.log (2 : ℝ) ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
        ((physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 1).card : ℝ) ≤
          eta * ((N : ℝ) / Real.log (N : ℝ)) := by
  have heta4 : 0 < eta / 4 := by linarith
  obtain ⟨bandWidth, hbandWidth, NB, hNB, hband⟩ :=
    exists_normalized_strip_mass_reserve hbHalf hb1 hkappa hkappa1 heta4
  obtain ⟨NL, hNL, hlow⟩ := prime_pairs_below_cutoff_uniform_mass_reserve hkappa heta4
  let width : ℝ := min widthMax (min (Real.log (2 : ℝ)) bandWidth)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hwidth : 0 < width := lt_min hwidthMax (lt_min hlog2 hbandWidth)
  have hwidthMaxLe : width ≤ widthMax := min_le_left _ _
  have hwidthLog : width ≤ Real.log (2 : ℝ) := (min_le_right _ _).trans (min_le_left _ _)
  have hwidthBand : width ≤ bandWidth := (min_le_right _ _).trans (min_le_right _ _)
  let N0 : ℕ := max 2 (max NB NL)
  refine ⟨width, hwidth, hwidthMaxLe, hwidthLog, N0, le_max_left _ _, ?_⟩
  intro N hN0
  have hN : 2 ≤ N := (le_max_left 2 (max NB NL)).trans hN0
  have hNBM : NB ≤ 2 * N := by
    have hh := (le_max_left NB NL).trans ((le_max_right 2 (max NB NL)).trans hN0)
    omega
  have hNLM : NL ≤ 2 * N := by
    have hh := (le_max_right NB NL).trans ((le_max_right 2 (max NB NL)).trans hN0)
    omega
  have hfinite :
      ((physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 1).card : ℝ) ≤
        ((normalizedPrimePairStrip b kappa width (2 * N)).card : ℝ) +
          ((lowPrimePairs kappa (2 * N)).card : ℝ) := by
    exact_mod_cast supported_badness_card_le_strip_add_low hb1 hN hwidthLog
  have hbandN : ((normalizedPrimePairStrip b kappa width (2 * N)).card : ℝ) ≤
      (eta / 4) * (((2 * N : ℕ) : ℝ) / Real.log ((2 * N : ℕ) : ℝ)) := by
    have hmono : ((normalizedPrimePairStrip b kappa width (2 * N)).card : ℝ) ≤
        ((normalizedPrimePairStrip b kappa bandWidth (2 * N)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (normalizedPrimePairStrip_mono_width hwidthBand)
    exact hmono.trans (hband (2 * N) hNBM)
  have hlowN : ((lowPrimePairs kappa (2 * N)).card : ℝ) ≤
      (eta / 4) * (((2 * N : ℕ) : ℝ) / Real.log ((2 * N : ℕ) : ℝ)) := by
    apply hlow (2 * N) hNLM (lowPrimePairs kappa (2 * N))
    · intro p hp
      have hcarrier := (Finset.mem_filter.mp hp).1
      exact ⟨(mem_ordinaryPrimePairs.mp hcarrier).2.2.1,
        (mem_ordinaryPrimePairs.mp hcarrier).2.2.2⟩
    · intro p hp
      exact (Finset.mem_filter.mp hp).2.le
  have hscale := massScale_double_le hN
  calc
    ((physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 1).card : ℝ) ≤
        ((normalizedPrimePairStrip b kappa width (2 * N)).card : ℝ) +
          ((lowPrimePairs kappa (2 * N)).card : ℝ) := hfinite
    _ ≤ (eta / 4) * (((2 * N : ℕ) : ℝ) / Real.log ((2 * N : ℕ) : ℝ)) +
          (eta / 4) * (((2 * N : ℕ) : ℝ) / Real.log ((2 * N : ℕ) : ℝ)) :=
      add_le_add hbandN hlowN
    _ = (eta / 2) * (((2 * N : ℕ) : ℝ) / Real.log ((2 * N : ℕ) : ℝ)) := by ring
    _ ≤ (eta / 2) * (2 * ((N : ℝ) / Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hscale (half_pos heta).le
    _ = eta * ((N : ℝ) / Real.log (N : ℝ)) := by ring

end
end ImbalancedChen.P4BSupportedBadnessStripMass