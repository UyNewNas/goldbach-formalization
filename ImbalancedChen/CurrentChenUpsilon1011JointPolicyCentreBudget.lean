import ImbalancedChen.CurrentChenUpsilon1011JointOverlapFiniteMean
import ImbalancedChen.ChenInitialCorrectionBudget
import ImbalancedChen.PowerErrorBudget
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Centre payment at the original licensed per-prefix levels

Every original Rosser row retains its own real level L(t). If
0<=L(t)<=N^nu/b(t), nu<1, the active positive divisors d<L(t) cost at
most L(t)*omega(N). The literal four-label reciprocal multiplier mass
is at most (1+log N)^4. Hence the total centre cost is bounded by

  N^nu*(1+log N)^4*omega(N) = o(singularNormalization N).

The main term and signed AP error keep the same L(t). No enlargement
of the physical level and no centre-cost hypothesis is used.
SOURCE-WRITTEN, UNCOMPILED. Earlier candidates remain frozen.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open P5U10OriginalMean P5U1011JointOverlap

namespace P5U1011JointPolicyCentre

/-- Arbitrary original levels keep their exact coefficient-zero tests. -/
theorem signedCentre_eq_active (N : ℕ) (t : Label) (L : ℝ) :
    signedCentre N t L = ∑ d ∈ (support N t).filter
      (fun d => coefficient N t L d ≠ 0),
        coefficient N t L d * chenCentrePrimeAPCount N N (multiplier t * d) := by
  unfold signedCentre
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hz : coefficient N t L d = 0 <;> simp only [hz, ne_eq,
    not_true_eq_false, not_false_eq_true, if_false, if_true, zero_mul]

/-- Counting positive active divisors below the REAL level costs at
most L, with no ceiling loss and no dependence on the number of tuples. -/
theorem row_abs_centre_le_level {N : ℕ} (hN : 0 < N) (t : Label)
    (L : ℝ) (hL : 0 ≤ L) :
    |signedCentre N t L| ≤ L * (N.primeFactors.card : ℝ) := by
  let S := (support N t).filter (fun d => coefficient N t L d ≠ 0)
  have hsub : S ⊆ Finset.Icc 1 (Nat.floor L) := by
    intro d hd
    have hactive := actualSmallRosserPlus_active (Finset.mem_filter.mp hd).2
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hactive.1
    exact Finset.mem_Icc.mpr ⟨hdpos,
      (Nat.le_floor_iff hL).mpr hactive.2.1.le⟩
  have hcount : (S.card : ℝ) ≤ L := by
    have hnat : S.card ≤ Nat.floor L := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub
    exact (Nat.cast_le.mpr hnat).trans (Nat.floor_le hL)
  rw [signedCentre_eq_active]
  change |∑ d ∈ S, coefficient N t L d *
    chenCentrePrimeAPCount N N (multiplier t * d)| ≤ _
  calc
    _ ≤ ∑ d ∈ S, |coefficient N t L d *
        chenCentrePrimeAPCount N N (multiplier t * d)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ S, (N.primeFactors.card : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      rw [abs_mul, abs_of_nonneg (chenCentrePrimeAPCount_nonneg _ _ _)]
      calc
        _ ≤ 1 * chenCentrePrimeAPCount N N (multiplier t * d) :=
          mul_le_mul_of_nonneg_right (coefficient_abs_le_one N t L d)
            (chenCentrePrimeAPCount_nonneg _ _ _)
        _ ≤ _ := by
          rw [one_mul]
          exact (chenCentrePrimeAPCount_le_divisorCount _ _ _).trans
            (chenPrimeDivisorCount_le_primeFactors_card N hN)
    _ = (S.card : ℝ) * (N.primeFactors.card : ℝ) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg _)

/-- The literal joint labels are a subset of four positive integer
coordinates through N. This cover leaves every original mask untouched. -/
theorem joint_subset_four_integer_carrier (N : ℕ) (E : ℕ × ℕ → Prop) :
    jointSelector N E ⊆
      ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N)) := by
  intro t ht
  obtain ⟨h1, h2, h3, h4, _⟩ := joint_carrier_order ht
  have hmem : ∀ {p : ℕ}, p ∈ chenAdditivePrimeCarrier N → p ∈ Finset.Icc 1 N := by
    intro p hp
    obtain ⟨hpN, hpprime, _⟩ := mem_chenAdditivePrimeCarrier.mp hp
    exact Finset.mem_Icc.mpr ⟨hpprime.pos, hpN.le⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hmem h1, hmem h2⟩,
    Finset.mem_product.mpr ⟨hmem h3, hmem h4⟩⟩

/-- Exact four-label harmonic tensor. No product image erases labels. -/
theorem four_integer_reciprocal_multiplier_sum (N : ℕ) :
    (∑ t ∈ ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N) ×ˢ
        (Finset.Icc 1 N ×ˢ Finset.Icc 1 N)), 1 / (multiplier t : ℝ)) =
      (∑ p ∈ Finset.Icc 1 N, 1 / (p : ℝ)) ^ 4 := by
  let A := Finset.Icc 1 N
  let g : ℕ × ℕ → ℝ := fun u => 1 / (u.1 : ℝ) * (1 / (u.2 : ℝ))
  have hterm : ∀ t : Label, 1 / (multiplier t : ℝ) = g t.1 * g t.2 := by
    intro t
    dsimp [g, multiplier]
    simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  have hpair : (∑ u ∈ A ×ˢ A, g u) = (∑ p ∈ A, 1 / (p : ℝ)) ^ 2 := by
    dsimp [g]
    rw [Finset.sum_product, ← Finset.sum_mul_sum, pow_two]
  simp_rw [hterm]
  change (∑ t ∈ (A ×ˢ A) ×ˢ (A ×ˢ A), g t.1 * g t.2) = _
  rw [Finset.sum_product, ← Finset.sum_mul_sum]
  simp only [hpair]
  change ((∑ p ∈ A, 1 / (p : ℝ)) ^ 2) *
    ((∑ p ∈ A, 1 / (p : ℝ)) ^ 2) = (∑ p ∈ A, 1 / (p : ℝ)) ^ 4
  ring

/-- The required reciprocal prefix mass is proved by the elementary
integer harmonic bound, uniformly in the original joint mask. -/
theorem joint_reciprocal_multiplier_sum_le (N : ℕ) (E : ℕ × ℕ → Prop) :
    (∑ t ∈ jointSelector N E, 1 / (multiplier t : ℝ)) ≤
      (1 + Real.log (N : ℝ)) ^ 4 := by
  have hH : (∑ p ∈ Finset.Icc 1 N, 1 / (p : ℝ)) ≤ 1 + Real.log (N : ℝ) := by
    have heq : (∑ p ∈ Finset.Icc 1 N, 1 / (p : ℝ)) = (harmonic N : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    rw [heq]
    exact harmonic_le_one_add_log N
  calc
    _ ≤ ∑ t ∈ ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N) ×ˢ
        (Finset.Icc 1 N ×ˢ Finset.Icc 1 N)), 1 / (multiplier t : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (joint_subset_four_integer_carrier N E)
        (fun _ _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _))
    _ = (∑ p ∈ Finset.Icc 1 N, 1 / (p : ℝ)) ^ 4 := four_integer_reciprocal_multiplier_sum N
    _ ≤ _ := pow_le_pow_left₀
      (Finset.sum_nonneg (fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _))) hH 4

/-- The actual rowwise absolute centre error at the supplied original levels. -/
def policyCentreCost (N : ℕ) (E : ℕ × ℕ → Prop) (L : Label → ℝ) : ℝ :=
  ∑ t ∈ jointSelector N E, |signedCentre N t (L t)|

theorem policyCentreCost_nonneg (N : ℕ) (E : ℕ × ℕ → Prop) (L : Label → ℝ) :
    0 ≤ policyCentreCost N E L := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- Original physical caps are paid by reciprocal multiplier mass.
nu may exceed one half; the only analytic decay requirement later is nu<1. -/
theorem policyCentreCost_le_harmonic {N : ℕ} (hN : 1 ≤ N)
    (E : ℕ × ℕ → Prop) (L : Label → ℝ) (nu : ℝ)
    (hL : ∀ t ∈ jointSelector N E, 0 ≤ L t)
    (hcap : ∀ t ∈ jointSelector N E, L t ≤ (N : ℝ) ^ nu / (multiplier t : ℝ)) :
    policyCentreCost N E L ≤
      (N : ℝ) ^ nu * (1 + Real.log (N : ℝ)) ^ 4 * (N.primeFactors.card : ℝ) := by
  have hNnat : 0 < N := by omega
  have hpow : 0 ≤ (N : ℝ) ^ nu := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc
    _ ≤ ∑ t ∈ jointSelector N E,
        ((N : ℝ) ^ nu / (multiplier t : ℝ)) * (N.primeFactors.card : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact (row_abs_centre_le_level hNnat t (L t) (hL t ht)).trans
        (mul_le_mul_of_nonneg_right (hcap t ht) (Nat.cast_nonneg _))
    _ = ((N : ℝ) ^ nu * (N.primeFactors.card : ℝ)) *
        (∑ t ∈ jointSelector N E, 1 / (multiplier t : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ ((N : ℝ) ^ nu * (N.primeFactors.card : ℝ)) *
        (1 + Real.log (N : ℝ)) ^ 4 :=
      mul_le_mul_of_nonneg_left (joint_reciprocal_multiplier_sum_le N E)
        (mul_nonneg hpow (Nat.cast_nonneg _))
    _ = _ := by ring

/-- An explicit fixed power-log majorant at the original levels. -/
theorem policyCentreCost_le_power_log {N : ℕ} (hN : 1 ≤ N)
    (hlog : 1 ≤ Real.log (N : ℝ)) (E : ℕ × ℕ → Prop)
    (L : Label → ℝ) (nu : ℝ)
    (hL : ∀ t ∈ jointSelector N E, 0 ≤ L t)
    (hcap : ∀ t ∈ jointSelector N E, L t ≤ (N : ℝ) ^ nu / (multiplier t : ℝ)) :
    policyCentreCost N E L ≤
      (16 / Real.log 2) * (N : ℝ) ^ nu * Real.log (N : ℝ) ^ 5 := by
  have hNnat : 0 < N := by omega
  have hlog0 : 0 ≤ Real.log (N : ℝ) := by linarith
  have hpow : 0 ≤ (N : ℝ) ^ nu := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hlogs : (1 + Real.log (N : ℝ)) ^ 4 ≤ 16 * Real.log (N : ℝ) ^ 4 := by
    calc
      _ ≤ (2 * Real.log (N : ℝ)) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
      _ = _ := by ring
  calc
    _ ≤ (N : ℝ) ^ nu * (1 + Real.log (N : ℝ)) ^ 4 * (N.primeFactors.card : ℝ) :=
      policyCentreCost_le_harmonic hN E L nu hL hcap
    _ ≤ (N : ℝ) ^ nu * (16 * Real.log (N : ℝ) ^ 4) *
        (Real.log (N : ℝ) / Real.log 2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hlogs hpow
      · exact chen_primeFactors_card_le_log hNnat
      · exact Nat.cast_nonneg _
      · exact mul_nonneg hpow (mul_nonneg (by norm_num) (pow_nonneg hlog0 _))
    _ = _ := by ring

/-- One threshold precedes every mask and every licensed original level
family. The physical exponent has only the strict requirement nu<1. -/
theorem eventually_policyCentreCost_le_singularNormalization
    (nu : ℝ) (hnu : nu < 1) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ E : ℕ × ℕ → Prop, ∀ L : Label → ℝ,
      (∀ t ∈ jointSelector N E, 0 ≤ L t) →
      (∀ t ∈ jointSelector N E, L t ≤ (N : ℝ) ^ nu / (multiplier t : ℝ)) →
      policyCentreCost N E L ≤ epsilon * singularNormalization N := by
  have hpower := eventually_powerLog_le_singularNormalization
    (16 / Real.log 2) nu 5 hnu epsilon hepsilon
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hpower, hlog, eventually_ge_atTop (1 : ℕ)] with N hp hl hN
  intro E L hL hcap
  exact (policyCentreCost_le_power_log hN hl E L nu hL hcap).trans hp

theorem abs_joint_signedCentre_le_policyCost (N : ℕ) (E : ℕ × ℕ → Prop) (L : Label → ℝ) :
    |∑ t ∈ jointSelector N E, signedCentre N t (L t)| ≤ policyCentreCost N E L :=
  Finset.abs_sum_le_sum_abs _ _

/-- Genuine little normalized centre cost for target-dependent masks
and original levels, assuming only their eventual structural cap. -/
theorem tendsto_policyCentreCost_normalized (nu : ℝ) (hnu : nu < 1)
    (E : ℕ → ℕ × ℕ → Prop) (L : ℕ → Label → ℝ)
    (hlevels : ∀ᶠ N : ℕ in atTop, ∀ t ∈ jointSelector N (E N),
      0 ≤ L N t ∧ L N t ≤ (N : ℝ) ^ nu / (multiplier t : ℝ)) :
    Tendsto (fun N : ℕ => policyCentreCost N (E N) (L N) / singularNormalization N)
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [eventually_singularNormalization_pos] with N hpos
    exact ha.trans_le (div_nonneg (policyCentreCost_nonneg N (E N) (L N)) hpos.le)
  · intro b hb
    filter_upwards [eventually_policyCentreCost_le_singularNormalization nu hnu
      (b / 2) (half_pos hb), hlevels, eventually_singularNormalization_pos]
      with N hbound hlevel hpos
    have hpaid := hbound (E N) (L N)
      (fun t ht => (hlevel t ht).1) (fun t ht => (hlevel t ht).2)
    have hquot : policyCentreCost N (E N) (L N) / singularNormalization N ≤ b / 2 :=
      (div_le_iff₀ hpos).mpr hpaid
    exact hquot.trans_lt (by linarith)

/-- The actual joint finite mean keeps the ORIGINAL supplied levels in
both density and signed AP distribution; only the centre cost is paid. -/
theorem eventually_joint_upper_originalLevels_centre_paid
    (nu : ℝ) (hnu : nu < 1) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ E : ℕ × ℕ → Prop, ∀ L : Label → ℝ, ∀ M : ℝ,
      (∀ t ∈ jointSelector N E, 1 < L t) →
      (∀ t ∈ jointSelector N E, (t.1.2 : ℝ) ≤ L t) →
      (∀ t ∈ jointSelector N E, L t ≤ (N : ℝ) ^ nu / (multiplier t : ℝ)) →
      currentChenUpsilon10 N + currentChenUpsilon11 N E ≤
        M * (∑ t ∈ jointSelector N E, 1 / (Nat.totient (multiplier t) : ℝ) *
          ∑ e ∈ (residualProduct N t).divisors,
            effectiveCoefficient N t (L t) e / (Nat.totient e : ℝ)) +
          (∑ t ∈ jointSelector N E, signedAPError N M t (L t)) +
          epsilon * singularNormalization N := by
  filter_upwards [eventually_policyCentreCost_le_singularNormalization nu hnu epsilon hepsilon,
    eventually_ge_atTop (1 : ℕ)] with N hcost hN
  intro E L M hL hpL hcap
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hfinite := currentChenUpsilon1011_joint_upper_effective N E hNr M L hL hpL
  have hpaid := hcost E L (fun t ht => (zero_lt_one.trans (hL t ht)).le) hcap
  have habs := (abs_joint_signedCentre_le_policyCost N E L).trans hpaid
  have hneg := neg_le_abs (∑ t ∈ jointSelector N E, signedCentre N t (L t))
  linarith only [hfinite, habs, hneg]

end P5U1011JointPolicyCentre

end

end ImbalancedChen
