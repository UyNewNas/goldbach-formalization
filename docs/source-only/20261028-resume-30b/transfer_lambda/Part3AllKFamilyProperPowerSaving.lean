import ImbalancedChen.Part3AllKFamilyLambdaCorrectionBound

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
The scale hypotheses of the older Cartesian proper-power count are now
derived from a nonzero ORIGINAL chart word of the SAME all-rank Family.
An empty active bad-word set is handled before enlarging to a whole box.
This is needed: a box attached to an inactive chart has no physical scale.
-/
namespace ImbalancedChen.Part3.AllKFamilyProperPowerSaving

noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.P5Z.ExactOriginalSmoothDyadicPartition
open ImbalancedChen.P5Z.ActualLabelledPrimeSmoothCharts
open ImbalancedChen.P5Z.AdmissibleAllRankIntegerGeometricFamily
open ImbalancedChen.Part3.OriginalProperPowerActualChart
open ImbalancedChen.Part3.OriginalProperPowerChartCount
open ImbalancedChen.Part3.AllKLambdaChartCorrection
open ImbalancedChen.Part3.AllKFamilyLambdaCorrectionBound

-- No asymptotic or analytic logarithm estimate is input: the actual bank
-- bounds the exponent j, and U_j is exactly the natural number 2^(j+1).
theorem log2_chartUpper {k : ℕ} (js : List ℕ) (i : Fin k) :
    Nat.log2 (chartUpper k js i) = js.getD i.val 0 + 1 := by
  let j := js.getD i.val 0 + 1
  change Nat.log2 (2 ^ j) = j
  have hne : (2 ^ j : ℕ) ≠ 0 := by positivity
  have hlo : j ≤ Nat.log2 (2 ^ j) := (Nat.le_log2 hne).mpr le_rfl
  have hhi : Nat.log2 (2 ^ j) ≤ j := by
    by_contra h
    have hexp : j + 1 ≤ Nat.log2 (2 ^ j) := by omega
    have hh : (2 ^ (j + 1) : ℕ) ≤ 2 ^ j := (Nat.le_log2 hne).mp hexp
    rw [pow_succ] at hh
    have hpos : (0 : ℕ) < 2 ^ j := by positivity
    omega
  exact Nat.le_antisymm hhi hlo

theorem chart_log_bound {cap k : ℕ} {js : List ℕ}
    (hjs : js ∈ chartBank cap k) (i : Fin k) :
    Nat.log2 (chartUpper k js i) + 1 ≤ cutoffIndex cap + 2 := by
  obtain ⟨hlen, hmem⟩ :=
    words_spec (Finset.range (cutoffIndex cap + 1)) k js hjs
  have hi : i.val < js.length := by omega
  have hm : js.getD i.val 0 ∈ js := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hj := Finset.mem_range.mp (hmem _ hm)
  rw [log2_chartUpper]
  omega

-- The padded COMPLETE chart box, not just the chosen point, has product
-- O(T). Its chosen bad slot also has the physical lower scale T^aStar.
theorem actual_bad_chart_scales {kStar : ℕ} (A : Family kStar)
    (T : ℕ) (k : Fin (kStar + 1)) (chi eta : ℝ → ℝ)
    (hone : ∀ t, t ≤ 1 → chi t = 1)
    (hzero : ∀ t, 2 ≤ t → chi t = 0)
    (cap : ℕ) (kappa0 : ℝ) {js : List ℕ}
    (hjs : js ∈ chartBank cap k.val) (bad : Fin k.val) {ps : List ℕ}
    (hps : ps ∈ badChartWords chi eta (bankWeight A T k)
      (T : ℝ) kappa0 cap k.val js bad) :
    (∏ i : Fin k.val, ((chartUpper k.val js i + 1 : ℕ) : ℝ)) ≤
        ((5 : ℝ)^k.val * A.upper) * (T : ℝ) ∧
      A.lower * (T : ℝ)^A.aStar ≤ (chartUpper k.val js bad : ℝ) := by
  obtain ⟨hlen, hpositive, hactive, hpower⟩ := badChartWords_spec hps
  have hW : bankWeight A T k ps ≠ 0 := by
    intro hz
    exact hactive (by simp [chartTerm, trimmedWeight, hz])
  have hs := bankWeight_support A T k hlen hW
  constructor
  · have hbox := padded_chart_product_le_five_pow_word chi eta
      (bankWeight A T k) hone hzero cap k.val (T : ℝ) kappa0 bad hjs hps
    calc
      _ ≤ (5 : ℝ)^k.val * (ps.prod : ℝ) := hbox
      _ ≤ (5 : ℝ)^k.val * (A.upper * (T : ℝ)) :=
        mul_le_mul_of_nonneg_left hs.2 (by positivity)
      _ = _ := by ring
  · have hb := active_bad_word_in_chart_box chi eta (bankWeight A T k)
      hone hzero cap k.val (T : ℝ) kappa0 bad hjs hps
    have hm : wordVector k.val ps bad ∈ properPowers (chartUpper k.val js bad) := by
      have hh := (Finset.mem_piFinset.mp hb) bad
      simpa only [if_pos rfl] using hh
    have hu := (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2
    have hi : bad.val < ps.length := by omega
    have hmem : wordVector k.val ps bad ∈ ps := by
      simp only [wordVector, List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    exact (hs.1 _ hmem).trans (by exact_mod_cast hu)

-- Keeping the active bad sets here is essential for the empty-chart case.
-- The previous batch's box bound had already enlarged those sets.
theorem correction_le_actual_bad_mass
    (chi eta : ℝ → ℝ) (W : List ℕ → ℂ)
    (cap k : ℕ) (T kappa0 : ℝ) (js : List ℕ) (K : ℕ → ℂ) :
    ‖∑ ps ∈ properChartWords cap k,
      lambdaWord ps * chartTerm chi eta W T kappa0 js ps * K ps.prod‖ ≤
      ∑ bad : Fin k, ∑ ps ∈ badChartWords chi eta W T kappa0 cap k js bad,
        ‖chartTerm chi eta W T kappa0 js ps * K ps.prod‖ := by
  let f : List ℕ → ℝ := fun ps =>
    ‖chartTerm chi eta W T kappa0 js ps * K ps.prod‖
  calc
    _ ≤ ∑ ps ∈ properChartWords cap k,
        ‖lambdaWord ps * chartTerm chi eta W T kappa0 js ps * K ps.prod‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ps ∈ properChartWords cap k, f ps := by
      apply Finset.sum_le_sum
      intro ps hps
      rw [mul_assoc, norm_mul]
      exact (mul_le_mul_of_nonneg_right (lambdaWord_norm_le_one ps)
        (norm_nonneg _)).trans_eq (one_mul _)
    _ ≤ _ := by
      apply covered_nonnegative_sum_le _ Finset.univ _ f (fun _ => norm_nonneg _)
      intro ps hps hf
      have hactive : chartTerm chi eta W T kappa0 js ps ≠ 0 := by
        intro hz
        exact hf (by simp [f, hz])
      obtain ⟨bad, hb⟩ :=
        active_proper_chart_in_bad_words chi eta W T kappa0 js hps hactive
      exact ⟨bad, Finset.mem_univ _, hb⟩

theorem actual_bad_chart_power_budget {kStar : ℕ} (A : Family kStar)
    (T : ℕ) (hT : 0 < T) (k : Fin (kStar + 1))
    (chi eta : ℝ → ℝ)
    (hone : ∀ t, t ≤ 1 → chi t = 1)
    (hzero : ∀ t, 2 ≤ t → chi t = 0)
    (hchi : ∀ t, 0 ≤ chi t ∧ chi t ≤ 1)
    (heta : ∀ t, |eta t| ≤ 1)
    (cap : ℕ) (kappa0 : ℝ) {js : List ℕ}
    (hjs : js ∈ chartBank cap k.val) (bad : Fin k.val)
    (K : ℕ → ℂ) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hamp : ∀ ps, ps.length = k.val → ‖bankWeight A T k ps‖ ≤ M)
    (hK : ∀ n, ‖K n‖ ≤ H) :
    (∑ ps ∈ badChartWords chi eta (bankWeight A T k)
      (T : ℝ) kappa0 cap k.val js bad,
        ‖chartTerm chi eta (bankWeight A T k) (T : ℝ) kappa0 js ps * K ps.prod‖) ≤
      2 * (M * H) * ((5 : ℝ)^k.val * A.upper) * (T : ℝ) *
        ((cutoffIndex cap + 2 : ℕ) : ℝ) /
          Real.sqrt (A.lower * (T : ℝ)^A.aStar) := by
  have hTReal : 0 < (T : ℝ) := by exact_mod_cast hT
  have hlower := A.lower_pos
  have hupper := A.upper_pos
  let S := badChartWords chi eta (bankWeight A T k)
    (T : ℝ) kappa0 cap k.val js bad
  by_cases hS : S.Nonempty
  · obtain ⟨ps, hps⟩ := hS
    have hs := actual_bad_chart_scales A T k chi eta hone hzero cap kappa0
      hjs bad hps
    calc
      _ ≤ ∑ v ∈ oneBadSlotBox (chartUpper k.val js) bad,
          ‖chartTerm chi eta (bankWeight A T k) (T : ℝ) kappa0 js
            (List.ofFn v) * K (List.ofFn v).prod‖ :=
        signed_kernel_bad_chart_absolute_box chi eta (bankWeight A T k) K
          hone hzero cap k.val (T : ℝ) kappa0 bad hjs
      _ ≤ _ := by
        apply oneBadSlotBox_absolute_mass_scale (chartUpper k.val js) bad
          (fun i => by unfold chartUpper; positivity)
          (fun v => chartTerm chi eta (bankWeight A T k) (T : ℝ) kappa0 js
            (List.ofFn v) * K (List.ofFn v).prod)
          (M * H) ((5 : ℝ)^k.val * A.upper) (T : ℝ)
          (A.lower * (T : ℝ)^A.aStar) ((cutoffIndex cap + 2 : ℕ) : ℝ)
          (mul_nonneg hM hH) (by positivity)
          (Nat.cast_nonneg _) (by positivity) (by positivity)
        · intro v hv
          rw [norm_mul]
          exact mul_le_mul
            (bank_chart_amplitude A T k chi eta hchi heta M hM hamp
              kappa0 js (List.ofFn v) (by simp))
            (hK _) (norm_nonneg _) hM
        · exact hs.1
        · exact hs.2
        · exact_mod_cast chart_log_bound hjs bad
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change (∑ ps ∈ S, _) ≤ _
    rw [hempty]
    simp only [Finset.sum_empty]
    positivity

-- The complete proper-power correction has a genuine square-root reserve
-- in the physical lower scale; no product-volume hypothesis remains.
theorem family_all_k_power_budget {kStar : ℕ} (A : Family kStar)
    (T : ℕ) (hT : 0 < T) (k : Fin (kStar + 1))
    (chi eta : ℝ → ℝ)
    (hone : ∀ t, t ≤ 1 → chi t = 1)
    (hzero : ∀ t, 2 ≤ t → chi t = 0)
    (hchi : ∀ t, 0 ≤ chi t ∧ chi t ≤ 1)
    (heta : ∀ t, |eta t| ≤ 1)
    (cap : ℕ) (kappa0 : ℝ) {js : List ℕ}
    (hjs : js ∈ chartBank cap k.val)
    (K : ℕ → ℂ) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hamp : ∀ ps, ps.length = k.val → ‖bankWeight A T k ps‖ ≤ M)
    (hK : ∀ n, ‖K n‖ ≤ H) :
    ‖∑ ps ∈ properChartWords cap k.val,
      lambdaWord ps *
        chartTerm chi eta (bankWeight A T k) (T : ℝ) kappa0 js ps * K ps.prod‖ ≤
      (k.val : ℝ) *
        (2 * (M * H) * ((5 : ℝ)^k.val * A.upper) * (T : ℝ) *
          ((cutoffIndex cap + 2 : ℕ) : ℝ) /
            Real.sqrt (A.lower * (T : ℝ)^A.aStar)) := by
  apply (correction_le_actual_bad_mass chi eta (bankWeight A T k) cap
    k.val (T : ℝ) kappa0 js K).trans
  calc
    _ ≤ ∑ bad : Fin k.val,
        2 * (M * H) * ((5 : ℝ)^k.val * A.upper) * (T : ℝ) *
          ((cutoffIndex cap + 2 : ℕ) : ℝ) /
            Real.sqrt (A.lower * (T : ℝ)^A.aStar) := by
      apply Finset.sum_le_sum
      intro bad hb
      exact actual_bad_chart_power_budget A T hT k chi eta hone hzero
        hchi heta cap kappa0 hjs bad K M H hM hH hamp hK
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]

-- This identity exposes the actual exponent 1-aStar/2, rather than merely
-- describing the preceding finite Cartesian count as power-small.
theorem physical_scale_power_identity {T lower a : ℝ}
    (hT : 0 < T) (hlower : 0 < lower) :
    T / Real.sqrt (lower * T^a) =
      (1 / Real.sqrt lower) * T^(1 - a/2) := by
  have hs : Real.sqrt (T^a) = T^(a/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT.le]
    congr 1
    ring
  rw [Real.sqrt_mul hlower.le, hs, Real.rpow_sub hT, Real.rpow_one]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

def powerSavingBudget {kStar : ℕ} (A : Family kStar) (T : ℕ)
    (k : Fin (kStar + 1)) (cap : ℕ) (M H : ℝ) : ℝ :=
  (2 * (k.val : ℝ) * (M * H) * ((5 : ℝ)^k.val * A.upper) *
    ((cutoffIndex cap + 2 : ℕ) : ℝ) / Real.sqrt A.lower) *
      (T : ℝ)^(1 - A.aStar/2)

theorem family_all_k_power_saving {kStar : ℕ} (A : Family kStar)
    (T : ℕ) (hT : 0 < T) (k : Fin (kStar + 1))
    (chi eta : ℝ → ℝ)
    (hone : ∀ t, t ≤ 1 → chi t = 1)
    (hzero : ∀ t, 2 ≤ t → chi t = 0)
    (hchi : ∀ t, 0 ≤ chi t ∧ chi t ≤ 1)
    (heta : ∀ t, |eta t| ≤ 1)
    (cap : ℕ) (kappa0 : ℝ) {js : List ℕ}
    (hjs : js ∈ chartBank cap k.val)
    (K : ℕ → ℂ) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hamp : ∀ ps, ps.length = k.val → ‖bankWeight A T k ps‖ ≤ M)
    (hK : ∀ n, ‖K n‖ ≤ H) :
    ‖∑ ps ∈ properChartWords cap k.val,
      lambdaWord ps *
        chartTerm chi eta (bankWeight A T k) (T : ℝ) kappa0 js ps * K ps.prod‖ ≤
      powerSavingBudget A T k cap M H := by
  apply (family_all_k_power_budget A T hT k chi eta hone hzero hchi heta cap
    kappa0 hjs K M H hM hH hamp hK).trans_eq
  have hTReal : 0 < (T : ℝ) := by exact_mod_cast hT
  calc
    _ = (2 * (k.val : ℝ) * (M * H) * ((5 : ℝ)^k.val * A.upper) *
        ((cutoffIndex cap + 2 : ℕ) : ℝ)) *
          ((T : ℝ) / Real.sqrt (A.lower * (T : ℝ)^A.aStar)) := by ring
    _ = _ := by
      rw [physical_scale_power_identity hTReal A.lower_pos]
      unfold powerSavingBudget
      ring

-- C and B come from m=0 of the original all-rank family and are fixed
-- before T, rank, chart, and signed test kernel. Thus M is not a new
-- unproved physical amplitude hypothesis in this final interface.
theorem uniform_family_power_saving {kStar : ℕ} (A : Family kStar) :
    ∃ C B : ℕ, 0 < C ∧
      ∀ (T : ℕ), 0 < T → ∀ (k : Fin (kStar + 1)) (chi eta : ℝ → ℝ),
        (∀ t, t ≤ 1 → chi t = 1) →
        (∀ t, 2 ≤ t → chi t = 0) →
        (∀ t, 0 ≤ chi t ∧ chi t ≤ 1) →
        (∀ t, |eta t| ≤ 1) →
        ∀ (cap : ℕ) (kappa0 : ℝ) (js : List ℕ),
          js ∈ chartBank cap k.val →
          ∀ (K : ℕ → ℂ) (H : ℝ), 0 ≤ H → (∀ n, ‖K n‖ ≤ H) →
          ‖∑ ps ∈ properChartWords cap k.val,
            lambdaWord ps *
              chartTerm chi eta (bankWeight A T k) (T : ℝ) kappa0 js ps *
                K ps.prod‖ ≤
            powerSavingBudget A T k cap
              ((C : ℝ) * (Real.log ((T : ℝ) + 2))^B) H := by
  obtain ⟨C, B, hC, hamp⟩ := all_rank_bank_amplitude A
  refine ⟨C, B, hC, ?_⟩
  intro T hT k chi eta hone hzero hchi heta cap kappa0 js hjs K H hH hK
  have hlog : 0 ≤ Real.log ((T : ℝ) + 2) :=
    Real.log_nonneg (by positivity : (1 : ℝ) ≤ (T : ℝ) + 2)
  exact family_all_k_power_saving A T hT k chi eta hone hzero hchi heta cap
    kappa0 hjs K _ H (by positivity) hH (hamp T k) hK

theorem family_atlas_power_saving {kStar : ℕ} (A : Family kStar)
    (T : ℕ) (hT : 0 < T) (k : Fin (kStar + 1)) (cap : ℕ)
    (chi eta : ℝ → ℝ)
    (hone : ∀ t, t ≤ 1 → chi t = 1)
    (hzero : ∀ t, 2 ≤ t → chi t = 0)
    (hchi : ∀ t, 0 ≤ chi t ∧ chi t ≤ 1)
    (heta : ∀ t, |eta t| ≤ 1)
    (z kappa0 : ℝ) (hz : 0 ≤ z)
    (hfloor : z < A.lower * (T : ℝ)^A.aStar)
    {js : List ℕ} (hjs : js ∈ chartBank cap k.val)
    (K : ℕ → ℂ) (M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hamp : ∀ ps, ps.length = k.val → ‖bankWeight A T k ps‖ ≤ M)
    (hK : ∀ n, ‖K n‖ ≤ H) :
    ‖familyAtlasSum A T k cap chi eta z kappa0 js K -
      familyPrimeSum A T k cap chi eta kappa0 js K‖ ≤
        powerSavingBudget A T k cap M H := by
  rw [family_atlas_sub_primes_exact A T k cap chi eta hone hzero z kappa0 hz
    hfloor js K]
  apply family_all_k_power_saving A T hT k chi eta hone hzero hchi heta cap
    kappa0 hjs (fun n => roughOneSlot z n * K n) M H hM hH hamp
  intro n
  rw [norm_mul]
  exact (mul_le_mul (roughOneSlot_norm_le z n) (hK n)
    (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

end
end ImbalancedChen.Part3.AllKFamilyProperPowerSaving
