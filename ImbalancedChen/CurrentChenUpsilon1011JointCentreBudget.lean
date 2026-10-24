import ImbalancedChen.CurrentChenUpsilon1011JointOverlapFiniteMean
import ImbalancedChen.ChenInitialCorrectionBudget
import ImbalancedChen.PowerErrorBudget

/-!
# Paying the original joint centre correction at the actual second-prime level

The level max(2,p₂) equals p₂ at every actual tuple. Only nonzero original
Rosser coefficients enter the centre error, and each has d<p₂. There are
at most N^(3h+d) original joint labels and p₂<N^h, where h=19/125 and
d=59/250. Thus the full centre cost is at most

  N^(211/250) * card(primeFactors N)
    <= (1/log 2)*N^(211/250)*log N = o(singularNormalization N).

The signed AP distribution error remains explicit. No freely chosen
physical level or centre-cost estimate is a hypothesis.
SOURCE-WRITTEN, UNCOMPILED.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open P5U10OriginalMean P5U1011JointOverlap

namespace P5U1011JointCentre

/-- The original three low primes and full high fourth-prime endpoint
give a literal Cartesian cover. Label multiplicity is retained. -/
theorem joint_card_le_power {N : ℕ} (hN : 1 ≤ N) (E : ℕ × ℕ → Prop) :
    ((jointSelector N E).card : ℝ) ≤ (N : ℝ) ^ (173 / 250 : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let H : ℝ := (N : ℝ) ^ (19 / 125 : ℝ)
  let D : ℝ := (N : ℝ) ^ (59 / 250 : ℝ)
  have hH : 0 ≤ H := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hD : 0 ≤ D := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hsub : jointSelector N E ⊆
      ((Finset.Ioc 0 (Nat.floor H) ×ˢ Finset.Ioc 0 (Nat.floor H)) ×ˢ
        (Finset.Ioc 0 (Nat.floor H) ×ˢ Finset.Ioc 0 (Nat.floor D))) := by
    intro t ht
    obtain ⟨h1, h2, h3, h4, h12, h23, _⟩ := joint_carrier_order ht
    obtain ⟨_, h3H, h4D, _⟩ := joint_band_and_mask ht
    have h2H : (t.1.2 : ℝ) < H :=
      (show (t.1.2 : ℝ) < (t.2.1 : ℝ) by exact_mod_cast h23).trans h3H
    have h1H : (t.1.1 : ℝ) < H :=
      (show (t.1.1 : ℝ) < (t.1.2 : ℝ) by exact_mod_cast h12).trans h2H
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Ioc.mpr ⟨(mem_chenAdditivePrimeCarrier.mp h1).2.1.pos,
          (Nat.le_floor_iff hH).mpr h1H.le⟩,
        Finset.mem_Ioc.mpr ⟨(mem_chenAdditivePrimeCarrier.mp h2).2.1.pos,
          (Nat.le_floor_iff hH).mpr h2H.le⟩⟩,
      Finset.mem_product.mpr
        ⟨Finset.mem_Ioc.mpr ⟨(mem_chenAdditivePrimeCarrier.mp h3).2.1.pos,
            (Nat.le_floor_iff hH).mpr h3H.le⟩,
          Finset.mem_Ioc.mpr ⟨(mem_chenAdditivePrimeCarrier.mp h4).2.1.pos,
            (Nat.le_floor_iff hD).mpr h4D.le⟩⟩⟩
  have hcard : ((jointSelector N E).card : ℝ) ≤
      ((Nat.floor H : ℕ) : ℝ) * ((Nat.floor H : ℕ) : ℝ) *
        (((Nat.floor H : ℕ) : ℝ) * ((Nat.floor D : ℕ) : ℝ)) := by
    exact_mod_cast (show (jointSelector N E).card ≤
      (Nat.floor H * Nat.floor H) * (Nat.floor H * Nat.floor D) by
        simpa only [Finset.card_product, Nat.card_Ioc, Nat.sub_zero] using
          Finset.card_le_card hsub)
  have hHH : ((Nat.floor H : ℕ) : ℝ) * ((Nat.floor H : ℕ) : ℝ) ≤ H * H :=
    mul_le_mul (Nat.floor_le hH) (Nat.floor_le hH) (Nat.cast_nonneg _) hH
  have hHD : ((Nat.floor H : ℕ) : ℝ) * ((Nat.floor D : ℕ) : ℝ) ≤ H * D :=
    mul_le_mul (Nat.floor_le hH) (Nat.floor_le hD) (Nat.cast_nonneg _) hH
  calc
    _ ≤ (H * H) * (H * D) := hcard.trans
      (mul_le_mul hHH hHD (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (mul_nonneg hH hH))
    _ = _ := by
      dsimp [H, D]
      rw [← Real.rpow_add hNp, ← Real.rpow_add hNp, ← Real.rpow_add hNp]
      norm_num

theorem joint_second_prime_lt_power {N : ℕ} {E : ℕ × ℕ → Prop} {t : Label}
    (ht : t ∈ jointSelector N E) :
    (t.1.2 : ℝ) < (N : ℝ) ^ (19 / 125 : ℝ) := by
  have h23 := (joint_carrier_order ht).2.2.2.2.2.1
  exact (show (t.1.2 : ℝ) < (t.2.1 : ℝ) by exact_mod_cast h23).trans
    (joint_band_and_mask ht).2.1

/-- Zero Rosser coefficients are removed exactly before the centre
correction is counted. This is a coefficient identity, not an estimate. -/
theorem signedCentre_eq_active_sum (N : ℕ) (t : Label) :
    signedCentre N t (t.1.2 : ℝ) =
      ∑ d ∈ (support N t).filter
        (fun d => coefficient N t (t.1.2 : ℝ) d ≠ 0),
          coefficient N t (t.1.2 : ℝ) d * chenCentrePrimeAPCount N N (multiplier t * d) := by
  unfold signedCentre
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hz : coefficient N t (t.1.2 : ℝ) d = 0 <;> simp only [hz, ne_eq,
    not_true_eq_false, not_false_eq_true, if_false, if_true, zero_mul]

/-- The concrete level p₂ permits at most p₂ original nonzero divisor
coefficients; every literal centre AP count is a subset of primeFactors N. -/
theorem row_abs_centre_le {N : ℕ} (hN : 0 < N) (t : Label) :
    |signedCentre N t (t.1.2 : ℝ)| ≤
      (t.1.2 : ℝ) * (N.primeFactors.card : ℝ) := by
  let S := (support N t).filter (fun d => coefficient N t (t.1.2 : ℝ) d ≠ 0)
  have hsub : S ⊆ Finset.range t.1.2 := by
    intro d hd
    have hactive := (actualSmallRosserPlus_active (Finset.mem_filter.mp hd).2).2.1
    exact Finset.mem_range.mpr (by exact_mod_cast hactive)
  have hcount : (S.card : ℝ) ≤ (t.1.2 : ℝ) := by
    exact_mod_cast (show S.card ≤ t.1.2 by
      simpa only [Finset.card_range] using Finset.card_le_card hsub)
  rw [signedCentre_eq_active_sum]
  change |∑ d ∈ S, coefficient N t (t.1.2 : ℝ) d *
    chenCentrePrimeAPCount N N (multiplier t * d)| ≤ _
  calc
    _ ≤ ∑ d ∈ S, |coefficient N t (t.1.2 : ℝ) d *
        chenCentrePrimeAPCount N N (multiplier t * d)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ S, (N.primeFactors.card : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      rw [abs_mul, abs_of_nonneg (chenCentrePrimeAPCount_nonneg _ _ _)]
      calc
        _ ≤ 1 * chenCentrePrimeAPCount N N (multiplier t * d) :=
          mul_le_mul_of_nonneg_right (coefficient_abs_le_one N t (t.1.2 : ℝ) d)
            (chenCentrePrimeAPCount_nonneg _ _ _)
        _ ≤ _ := by
          rw [one_mul]
          exact (chenCentrePrimeAPCount_le_divisorCount _ _ _).trans
            (chenPrimeDivisorCount_le_primeFactors_card N hN)
    _ = (S.card : ℝ) * (N.primeFactors.card : ℝ) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg _)

theorem joint_maxLevel_eq_second {N : ℕ} {E : ℕ × ℕ → Prop} {t : Label}
    (ht : t ∈ jointSelector N E) : max 2 (t.1.2 : ℝ) = (t.1.2 : ℝ) := by
  have h2 := (joint_carrier_order ht).2.1
  exact max_eq_right (by exact_mod_cast (mem_chenAdditivePrimeCarrier.mp h2).2.1.two_le)

/-- The literal sum of absolute rowwise signed centre corrections. -/
def centreCost (N : ℕ) (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ t ∈ jointSelector N E, |signedCentre N t (max 2 (t.1.2 : ℝ))|

theorem centreCost_nonneg (N : ℕ) (E : ℕ × ℕ → Prop) : 0 ≤ centreCost N E :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- Exactly 4h+d=211/250 is paid. The first three factors remain below
N^h and the fourth below the full original N^d. -/
theorem centreCost_le_power_primeFactors {N : ℕ} (hN : 1 ≤ N) (E : ℕ × ℕ → Prop) :
    centreCost N E ≤ (N : ℝ) ^ (211 / 250 : ℝ) * (N.primeFactors.card : ℝ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNnat : 0 < N := by omega
  have hH : 0 ≤ (N : ℝ) ^ (19 / 125 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  calc
    _ ≤ ∑ _t ∈ jointSelector N E,
        (N : ℝ) ^ (19 / 125 : ℝ) * (N.primeFactors.card : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      rw [joint_maxLevel_eq_second ht]
      exact (row_abs_centre_le hNnat t).trans
        (mul_le_mul_of_nonneg_right (joint_second_prime_lt_power ht).le (Nat.cast_nonneg _))
    _ = ((jointSelector N E).card : ℝ) *
        ((N : ℝ) ^ (19 / 125 : ℝ) * (N.primeFactors.card : ℝ)) := by simp
    _ ≤ (N : ℝ) ^ (173 / 250 : ℝ) *
        ((N : ℝ) ^ (19 / 125 : ℝ) * (N.primeFactors.card : ℝ)) :=
      mul_le_mul_of_nonneg_right (joint_card_le_power hN E)
        (mul_nonneg hH (Nat.cast_nonneg _))
    _ = _ := by
      rw [← mul_assoc, ← Real.rpow_add hNp]
      norm_num

theorem centreCost_le_power_log {N : ℕ} (hN : 1 ≤ N) (E : ℕ × ℕ → Prop) :
    centreCost N E ≤ (1 / Real.log 2) * (N : ℝ) ^ (211 / 250 : ℝ) * Real.log (N : ℝ) := by
  have hNnat : 0 < N := by omega
  calc
    _ ≤ (N : ℝ) ^ (211 / 250 : ℝ) * (N.primeFactors.card : ℝ) :=
      centreCost_le_power_primeFactors hN E
    _ ≤ (N : ℝ) ^ (211 / 250 : ℝ) * (Real.log (N : ℝ) / Real.log 2) :=
      mul_le_mul_of_nonneg_left (chen_primeFactors_card_le_log hNnat)
        (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = _ := by ring

/-- The centre payment is uniform in the original mask E. The threshold
is chosen before the mask, and no evenness or distribution input is used. -/
theorem eventually_centreCost_le_singularNormalization (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ E : ℕ × ℕ → Prop,
      centreCost N E ≤ epsilon * singularNormalization N := by
  have hpower := eventually_powerLog_le_singularNormalization
    (1 / Real.log 2) (211 / 250) 1 (by norm_num) epsilon hepsilon
  filter_upwards [hpower, eventually_ge_atTop (1 : ℕ)] with N hp hN
  intro E
  exact (centreCost_le_power_log hN E).trans (by simpa only [pow_one] using hp)

/-- A genuine normalized zero limit, even for a target-dependent mask. -/
theorem tendsto_centreCost_normalized (E : ℕ → ℕ × ℕ → Prop) :
    Tendsto (fun N : ℕ => centreCost N (E N) / singularNormalization N) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [eventually_singularNormalization_pos] with N hpos
    exact ha.trans_le (div_nonneg (centreCost_nonneg N (E N)) hpos.le)
  · intro b hb
    filter_upwards [eventually_centreCost_le_singularNormalization (b / 2) (half_pos hb),
      eventually_singularNormalization_pos] with N hbound hpos
    have hquot : centreCost N (E N) / singularNormalization N ≤ b / 2 :=
      (div_le_iff₀ hpos).mpr (hbound (E N))
    exact hquot.trans_lt (by linarith)

theorem abs_joint_signedCentre_le_cost (N : ℕ) (E : ℕ × ℕ → Prop) :
    |∑ t ∈ jointSelector N E, signedCentre N t (max 2 (t.1.2 : ℝ))| ≤ centreCost N E :=
  Finset.abs_sum_le_sum_abs _ _

/-- The actual joint finite mean now has a paid centre reserve. The
same signed AP distribution error is deliberately still explicit. -/
theorem eventually_joint_upper_centre_paid (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ E : ℕ × ℕ → Prop, ∀ M : ℝ,
      currentChenUpsilon10 N + currentChenUpsilon11 N E ≤
        M * (∑ t ∈ jointSelector N E, 1 / (Nat.totient (multiplier t) : ℝ) *
          ∑ e ∈ (residualProduct N t).divisors,
            effectiveCoefficient N t (max 2 (t.1.2 : ℝ)) e / (Nat.totient e : ℝ)) +
          (∑ t ∈ jointSelector N E, signedAPError N M t (max 2 (t.1.2 : ℝ))) +
          epsilon * singularNormalization N := by
  filter_upwards [eventually_centreCost_le_singularNormalization epsilon hepsilon,
    eventually_ge_atTop (1 : ℕ)] with N hcost hN
  intro E M
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hfinite := currentChenUpsilon1011_joint_upper_maxLevel N E hNr M
  have habs := (abs_joint_signedCentre_le_cost N E).trans (hcost E)
  have hneg := neg_le_abs (∑ t ∈ jointSelector N E,
    signedCentre N t (max 2 (t.1.2 : ℝ)))
  linarith only [hfinite, habs, hneg]

end P5U1011JointCentre

end

end ImbalancedChen
