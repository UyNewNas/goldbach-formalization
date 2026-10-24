import ImbalancedChen.P5ZU11LoweredCutoffFiniteRosser
import ImbalancedChen.CurrentChenUpsilon1011JointPolicyCentreBudget
import Mathlib.Tactic.GCongr

/-!
Centre payment for the actual lowered-cutoff selected ordinary source.

The old joint centre and signed-pushforward APIs fix the original p2
coefficient. They cannot be substituted for the lowered coefficient.
Here only the coefficient-independent joint harmonic tensor is reused;
the short active-divisor bound is proved for the actual lowered weight.
The remaining signed AP sum is literal, before any absolute value.

The physical level cap follows from actual four-slot upper endpoints,
the selected-largest parent gate and delta>=0. No cap or centre estimate
is left as a supplier in the final selected-parent statement.
Remaining CP: averaged signed-PP distribution, H248 count semantics and
the ordinary endpoint limit. Status: source_written / uncompiled.
-/

namespace ImbalancedChen.P5Z.U11SelectedCentre

open Filter Topology
open scoped BigOperators
open U11Adaptive U11LoweredRosser
open Classical

noncomputable section

theorem prefix_product_le_power (N : ℕ) (hN : 0 < (N : ℝ))
    (t : Four) (upper : U11Integral.LogFour)
    (hu : (t.2.2 : ℝ) ≤ (N : ℝ) ^ upper 0 ∧
      (t.2.1 : ℝ) ≤ (N : ℝ) ^ upper 1 ∧
      (t.1.2 : ℝ) ≤ (N : ℝ) ^ upper 2 ∧
      (t.1.1 : ℝ) ≤ (N : ℝ) ^ upper 3) :
    (multiplier t : ℝ) ≤ (N : ℝ) ^ U11SelectedLargest.prefixSum upper := by
  obtain ⟨h0, h1, h2, h3⟩ := hu
  calc
    _ = (t.2.2 : ℝ) * (t.2.1 : ℝ) * (t.1.2 : ℝ) * (t.1.1 : ℝ) := by
      simp only [multiplier, Nat.cast_mul]
      ring
    _ ≤ (N : ℝ) ^ upper 0 * (N : ℝ) ^ upper 1 *
        (N : ℝ) ^ upper 2 * (N : ℝ) ^ upper 3 := by gcongr <;> assumption
    _ = _ := by
      rw [U11SelectedLargest.prefixSum, Real.rpow_add hN, Real.rpow_add hN, Real.rpow_add hN]

theorem reduced_level_cap (N : ℕ) (hN : 1 < (N : ℝ)) (b : ℕ) (hb : 0 < b)
    (Tplus nu delta : ℝ) (hnu : nu ≤ (153 / 256 : ℝ)) (hdelta : 0 ≤ delta)
    (hproduct : (b : ℝ) ≤ (N : ℝ) ^ Tplus) :
    (N : ℝ) ^ (nu - Tplus - 20 * delta) ≤ (N : ℝ) ^ (153 / 256 : ℝ) / (b : ℝ) := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr hb : (0 : ℝ) < b)).2
  calc
    _ ≤ (N : ℝ) ^ (nu - Tplus - 20 * delta) * (N : ℝ) ^ Tplus :=
      mul_le_mul_of_nonneg_left hproduct (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = (N : ℝ) ^ (nu - 20 * delta) := by
      rw [← Real.rpow_add (zero_lt_one.trans hN)]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)

/-- This active-divisor argument uses Z itself in every coefficient and
support; it never replaces the lowered coefficient by the p2 coefficient. -/
theorem row_abs_centre_le_level {N : ℕ} (hN : 0 < N)
    (t : Four) (Z R : ℝ) (hR : 0 ≤ R) :
    |signedCentre N t Z R| ≤ R * (N.primeFactors.card : ℝ) := by
  let S := (actualSmallRosserSupport N (Nat.ceil Z) Z).filter
    (fun d => actualSmallRosserPlus N (Nat.ceil Z) Z R d ≠ 0)
  have hsub : S ⊆ Finset.Icc 1 (Nat.floor R) := by
    intro d hd
    have ha := actualSmallRosserPlus_active (Finset.mem_filter.mp hd).2
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha.1,
      (Nat.le_floor_iff hR).mpr ha.2.1.le⟩
  have hc : (S.card : ℝ) ≤ R := by
    have hh : S.card ≤ Nat.floor R := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub
    exact (Nat.cast_le.mpr hh).trans (Nat.floor_le hR)
  have heq : signedCentre N t Z R = ∑ d ∈ S,
      actualSmallRosserPlus N (Nat.ceil Z) Z R d * chenCentrePrimeAPCount N N (multiplier t * d) := by
    unfold signedCentre
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : actualSmallRosserPlus N (Nat.ceil Z) Z R d = 0 <;> simp [hd]
  rw [heq]
  calc
    _ ≤ ∑ d ∈ S, |actualSmallRosserPlus N (Nat.ceil Z) Z R d *
        chenCentrePrimeAPCount N N (multiplier t * d)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ S, (N.primeFactors.card : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      rw [abs_mul, abs_of_nonneg (chenCentrePrimeAPCount_nonneg _ _ _)]
      have hh := mul_le_mul_of_nonneg_right
        (actualSmallRosserPlus_abs_le_one N (Nat.ceil Z) Z R d)
        (chenCentrePrimeAPCount_nonneg N N (multiplier t * d))
      exact hh.trans (by simpa only [one_mul] using
        (chenCentrePrimeAPCount_le_divisorCount N N (multiplier t * d)).trans
          (chenPrimeDivisorCount_le_primeFactors_card N hN))
    _ = (S.card : ℝ) * (N.primeFactors.card : ℝ) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)

def centreCost (N : ℕ) (T : Finset Four) (Z R : Four → ℝ) : ℝ :=
  ∑ t ∈ T, |signedCentre N t (Z t) (R t)|

theorem centreCost_le_harmonic {N : ℕ} (hN : 1 ≤ N) (E : ℕ × ℕ → Prop)
    (T : Finset Four) (hT : T ⊆ source N E) (Z R : Four → ℝ)
    (hR : ∀ t ∈ T, 0 ≤ R t)
    (hcap : ∀ t ∈ T, R t ≤ (N : ℝ) ^ (153 / 256 : ℝ) / (multiplier t : ℝ)) :
    centreCost N T Z R ≤ (N : ℝ) ^ (153 / 256 : ℝ) *
      (1 + Real.log (N : ℝ)) ^ 4 * (N.primeFactors.card : ℝ) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsub : T ⊆ P5U1011JointOverlap.jointSelector N E :=
    fun t ht => P5U1011JointOverlap.originalU11_mem_joint hNr (hT ht)
  have hmass : (∑ t ∈ T, 1 / (multiplier t : ℝ)) ≤ (1 + Real.log (N : ℝ)) ^ 4 := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _))).trans
        (P5U1011JointPolicyCentre.joint_reciprocal_multiplier_sum_le N E)
  have hpow := Real.rpow_nonneg (Nat.cast_nonneg N) (153 / 256 : ℝ)
  calc
    _ ≤ ∑ t ∈ T, ((N : ℝ) ^ (153 / 256 : ℝ) / (multiplier t : ℝ)) *
        (N.primeFactors.card : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact (row_abs_centre_le_level (by omega) t (Z t) (R t) (hR t ht)).trans
        (mul_le_mul_of_nonneg_right (hcap t ht) (Nat.cast_nonneg _))
    _ = ((N : ℝ) ^ (153 / 256 : ℝ) * (N.primeFactors.card : ℝ)) *
        (∑ t ∈ T, 1 / (multiplier t : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ ((N : ℝ) ^ (153 / 256 : ℝ) * (N.primeFactors.card : ℝ)) *
        (1 + Real.log (N : ℝ)) ^ 4 :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg hpow (Nat.cast_nonneg _))
    _ = _ := by ring

theorem eventually_centreCost_paid (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ E : ℕ × ℕ → Prop, ∀ T : Finset Four,
      T ⊆ source N E → ∀ Z R : Four → ℝ,
      (∀ t ∈ T, 0 ≤ R t) →
      (∀ t ∈ T, R t ≤ (N : ℝ) ^ (153 / 256 : ℝ) / (multiplier t : ℝ)) →
      centreCost N T Z R ≤ epsilon * singularNormalization N := by
  have hp := eventually_powerLog_le_singularNormalization (16 / Real.log 2)
    (153 / 256) 5 (by norm_num) epsilon hepsilon
  have hl : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hp, hl, eventually_ge_atTop (1 : ℕ)] with N hp hl hN
  intro E T hT Z R hR hcap
  have hh := centreCost_le_harmonic hN E T hT Z R hR hcap
  have hlogs : (1 + Real.log (N : ℝ)) ^ 4 ≤ 16 * Real.log (N : ℝ) ^ 4 := by
    calc
      _ ≤ (2 * Real.log (N : ℝ)) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
      _ = _ := by ring
  have hfactor := chen_primeFactors_card_le_log (show 0 < N by omega)
  have hbound : centreCost N T Z R ≤
      (16 / Real.log 2) * (N : ℝ) ^ (153 / 256 : ℝ) * Real.log (N : ℝ) ^ 5 := by
    calc
      _ ≤ (N : ℝ) ^ (153 / 256 : ℝ) * (16 * Real.log (N : ℝ) ^ 4) *
          (Real.log (N : ℝ) / Real.log 2) := by
        apply hh.trans
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hlogs (Real.rpow_nonneg (Nat.cast_nonneg N) _)
        · exact hfactor
        · exact Nat.cast_nonneg _
        · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
            (mul_nonneg (by norm_num) (pow_nonneg (by linarith) _))
      _ = _ := by ring
  exact hbound.trans hp

/-- One threshold handles every original masked selected parent and its
winner subselector. The genuine parent/full-square tests imply the
physical exponent cap; only the actual signed AP supplier remains. -/
theorem eventually_reduced_parent_upper_centre_paid (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ E : ℕ × ℕ → Prop, ∀ T : Finset Four,
      T ⊆ source N E → ∀ lower upper : U11Integral.LogFour, ∀ nu delta xi rho : ℝ,
      U11SelectedLargest.parentGate lower upper nu → lower ≤ upper →
      0 ≤ delta → 0 ≤ xi → 0 < lower 3 - xi →
      20 * delta < nu - U11SelectedLargest.prefixSum upper → 0 < rho →
      (∀ t ∈ T, (N : ℝ) ^ lower 3 ≤ (t.1.1 : ℝ)) →
      (∀ t ∈ T, (t.2.2 : ℝ) ≤ (N : ℝ) ^ upper 0 ∧
        (t.2.1 : ℝ) ≤ (N : ℝ) ^ upper 1 ∧
        (t.1.2 : ℝ) ≤ (N : ℝ) ^ upper 2 ∧ (t.1.1 : ℝ) ≤ (N : ℝ) ^ upper 3) →
      let Z := (N : ℝ) ^ U11SelectedLargest.reducedCutoff lower upper nu delta xi rho
      let R := (N : ℝ) ^ (nu - U11SelectedLargest.prefixSum upper - 20 * delta)
      (∑ t ∈ T, weight N t) ≤ (∑ t ∈ T, mainTerm N t Z R) +
        (∑ t ∈ T, signedAP N t Z R) + epsilon * singularNormalization N := by
  filter_upwards [eventually_centreCost_paid epsilon hepsilon, eventually_ge_atTop (2 : ℕ)]
    with N hpaid hN
  intro E T hT lower upper nu delta xi rho hg hlu hdelta hxi hsmall hmargin hrho hfirst hupper
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hnu : nu ≤ (153 / 256 : ℝ) :=
    (U11SelectedLargest.parentGate_point hg hlu le_rfl).2.2.2.le.trans
      (U11SelectedLargest.cap_le_Lambda upper)
  have hleg := reduced_physical_level_legal N hNr lower upper nu delta xi rho hsmall hmargin hrho
  have hcap : ∀ t ∈ T, (N : ℝ) ^ (nu - U11SelectedLargest.prefixSum upper - 20 * delta) ≤
      (N : ℝ) ^ (153 / 256 : ℝ) / (multiplier t : ℝ) := by
    intro t ht
    have hj := P5U1011JointOverlap.originalU11_mem_joint hNr.le (hT ht)
    exact reduced_level_cap N hNr _ (P5U1011JointOverlap.joint_multiplier_pos hj)
      _ nu delta hnu hdelta (prefix_product_le_power N (zero_lt_one.trans hNr) t upper (hupper t ht))
  have hc := hpaid E T hT _ _ (fun _ _ => (zero_lt_one.trans hleg.1).le) hcap
  have hf := reduced_parent_family_upper N E hNr T hT lower upper nu delta xi rho
    hxi hsmall hmargin hrho hfirst
  have habs := Finset.abs_sum_le_sum_abs
    (fun t => signedCentre N t
      ((N : ℝ) ^ U11SelectedLargest.reducedCutoff lower upper nu delta xi rho)
      ((N : ℝ) ^ (nu - U11SelectedLargest.prefixSum upper - 20 * delta))) T
  have hneg := neg_le_abs (∑ t ∈ T, signedCentre N t
    ((N : ℝ) ^ U11SelectedLargest.reducedCutoff lower upper nu delta xi rho)
    ((N : ℝ) ^ (nu - U11SelectedLargest.prefixSum upper - 20 * delta)))
  dsimp only at hf ⊢
  dsimp only [centreCost] at hc
  linarith only [hf, hc, habs, hneg]

end

end ImbalancedChen.P5Z.U11SelectedCentre
