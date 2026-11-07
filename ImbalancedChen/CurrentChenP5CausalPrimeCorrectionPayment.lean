import ImbalancedChen.CurrentChenP5OriginalU5CausalFinite
import ImbalancedChen.CurrentChenP5U6CausalLevelGeometry
import ImbalancedChen.ChenInitialCorrectionBudget
import ImbalancedChen.PowerErrorBudget
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Payment of genuine causal quotient prime corrections at licensed caps

Inactive rho atoms are removed BEFORE charging positive costs. This is
essential: a physical cap on nonzero coefficients cannot bound the full
displayed small/rough support's unweighted positive cost. The signed AP
discrepancy remains signed throughout; no rowwise absolute BV is used.

The modulus-prime correction is evaluated at b*d, including primes of b.
A genuine physical cap b*d<=N^nu gives at most N^nu/b active atoms and
two log(N)/log(2) costs per atom. Integer pair harmonics pay the aggregate
uniformly in policies and masks. Original U5/U6 V<=153/256 removes the
exponent choice; the total-active-support licensing itself remains a
separate structural input, not an inferred distribution theorem.

SOURCE ONLY: uncompiled; earlier draft sources are unchanged.
-/

namespace ImbalancedChen.P5CausalPrimeCorrectionPayment

open scoped BigOperators
open Classical Filter Topology

noncomputable section

abbrev Active (policy : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) : Finset ℕ :=
  P5CausalRhoQuotientBridge.active policy N cap w z L

def atomCost (N b k : ℕ) : ℝ :=
  chenPrimeDivisorCount N (b * k) / (Nat.totient (b * k) : ℝ) +
    chenCentrePrimeAPCount N N (b * k)

def correctionCost (policy : List ℕ → Bool) (N cap b : ℕ) (w z L : ℝ) : ℝ :=
  ∑ k ∈ Active policy N cap w z L, atomCost N b k

theorem atomCost_nonneg (N b k : ℕ) : 0 ≤ atomCost N b k :=
  add_nonneg (div_nonneg (chenPrimeDivisorCount_nonneg N _) (Nat.cast_nonneg _))
    (chenCentrePrimeAPCount_nonneg N N _)

theorem signed_corrections_le_cost (policy : List ℕ → Bool)
    (N cap b : ℕ) (w z L : ℝ) :
    (∑ k ∈ Active policy N cap w z L,
      actualLowerSmallRoughRho policy N cap w z L k *
        (chenPrimeDivisorCount N (b * k) / (Nat.totient (b * k) : ℝ))) +
    (∑ k ∈ Active policy N cap w z L,
      actualLowerSmallRoughRho policy N cap w z L k * chenCentrePrimeAPCount N N (b * k)) ≤
      correctionCost policy N cap b w z L := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  have hrho := (le_abs_self (actualLowerSmallRoughRho policy N cap w z L k)).trans
    (actualLowerSmallRoughRho_abs_le_one policy N cap w z L k)
  have hmul := mul_le_mul_of_nonneg_right hrho (atomCost_nonneg N b k)
  simpa only [atomCost, mul_add, one_mul] using hmul

/-- The actual lower-count entrance uses only ACTIVE prime correction
costs. The primitive AP error remains the signed same-rho sum. -/
theorem quotient_primitive_lower_sub_active_cost
    (policy : List ℕ → Bool) (N cap b : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ))
    (hb : ChenPrimeRough z b) :
    ((chenPrimePrefix N).card : ℝ) / (Nat.totient b : ℝ) *
        physicalDensitySum (actualLowerSmallRoughModuli policy N cap w z)
          (actualLowerSmallRoughRho policy N cap w z L) +
      (∑ k ∈ Active policy N cap w z L,
        actualLowerSmallRoughRho policy N cap w z L k *
          finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N (b * k)) -
      correctionCost policy N cap b w z L ≤
      ((chenSiftedQuotientPrimeSource N b z).card : ℝ) := by
  have h := P5CausalRhoQuotientBridge.quotient_signed_sum_le_sifted
    policy N b cap w z L hL hwL hwz hzcap
  rw [P5CausalRhoQuotientBridge.quotient_main_primitive_and_prime_corrections
    policy N cap b w z L hwz hb] at h
  rw [P5CausalRhoQuotientBridge.sum_eq_active,
    P5CausalRhoQuotientBridge.sum_eq_active,
    P5CausalRhoQuotientBridge.sum_eq_active] at h
  have hcost := signed_corrections_le_cost policy N cap b w z L
  linarith only [h, hcost]

/-- This includes the primes of b: the numerator is the divisor count
of the full physical modulus b*k, rather than just that of k. -/
theorem atomCost_le_log {N b k : ℕ} (hN : 1 ≤ N)
    (hb : 0 < b) (hk : 0 < k) (hphysical : b * k ≤ N) :
    atomCost N b k ≤ 2 * (Real.log (N : ℝ) / Real.log 2) := by
  have hphyspos := Nat.mul_pos hb hk
  have hphi : (1 : ℝ) ≤ Nat.totient (b * k) := by
    exact_mod_cast (show 1 ≤ Nat.totient (b * k) from Nat.totient_pos.mpr hphyspos)
  have hprime := chenPrimeDivisorCount_le_log_center hphyspos hphysical
  have hprimeDiv : chenPrimeDivisorCount N (b * k) / (Nat.totient (b * k) : ℝ) ≤
      Real.log (N : ℝ) / Real.log 2 :=
    (div_le_self (chenPrimeDivisorCount_nonneg N _) hphi).trans hprime
  have hcentre := (chenCentrePrimeAPCount_le_divisorCount N N (b * k)).trans
    (chenPrimeDivisorCount_le_log N (by omega : 0 < N))
  unfold atomCost
  linarith only [hprimeDiv, hcentre]

theorem active_card_le_physical_div_prefix (policy : List ℕ → Bool)
    (N cap b : ℕ) (w z L X : ℝ) (hb : 0 < b) (hX : 0 ≤ X)
    (hcap : ∀ k ∈ Active policy N cap w z L, ((b * k : ℕ) : ℝ) ≤ X) :
    ((Active policy N cap w z L).card : ℝ) ≤ X / (b : ℝ) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hdiv : 0 ≤ X / (b : ℝ) := div_nonneg hX hbR.le
  have hsub : Active policy N cap w z L ⊆ Finset.Icc 1 (Nat.floor (X / (b : ℝ))) := by
    intro k hk
    have hsf := actualLowerSmallRoughModuli_squarefree policy N cap w z
      (Finset.mem_filter.mp hk).1
    have hkR : (k : ℝ) ≤ X / (b : ℝ) := by
      apply (le_div_iff₀ hbR).mpr
      simpa only [Nat.cast_mul, mul_comm] using hcap k hk
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hsf.ne_zero,
      (Nat.le_floor_iff hdiv).mpr hkR⟩
  have hnat : (Active policy N cap w z L).card ≤ Nat.floor (X / (b : ℝ)) := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub
  exact (Nat.cast_le.mpr hnat).trans (Nat.floor_le hdiv)

theorem correctionCost_le_physical_cap (policy : List ℕ → Bool)
    (N cap b : ℕ) (w z L nu : ℝ) (hN : 1 ≤ N) (hb : 0 < b) (hnu : nu ≤ 1)
    (hcap : ∀ k ∈ Active policy N cap w z L, ((b * k : ℕ) : ℝ) ≤ (N : ℝ) ^ nu) :
    correctionCost policy N cap b w z L ≤
      (2 / Real.log 2) * ((N : ℝ) ^ nu / (b : ℝ)) * Real.log (N : ℝ) := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hXle : (N : ℝ) ^ nu ≤ N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNR hnu
  have hB : 0 ≤ Real.log (N : ℝ) / Real.log 2 :=
    div_nonneg (Real.log_nonneg hNR) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hcount := active_card_le_physical_div_prefix policy N cap b w z L ((N : ℝ) ^ nu)
    hb (Real.rpow_nonneg (Nat.cast_nonneg N) _) hcap
  calc
    _ ≤ ∑ _k ∈ Active policy N cap w z L, 2 * (Real.log (N : ℝ) / Real.log 2) := by
      apply Finset.sum_le_sum
      intro k hk
      have hsf := actualLowerSmallRoughModuli_squarefree policy N cap w z
        (Finset.mem_filter.mp hk).1
      have hphysical : b * k ≤ N := by exact_mod_cast (hcap k hk).trans hXle
      exact atomCost_le_log hN hb (Nat.pos_of_ne_zero hsf.ne_zero) hphysical
    _ = ((Active policy N cap w z L).card : ℝ) *
        (2 * (Real.log (N : ℝ) / Real.log 2)) := by simp
    _ ≤ ((N : ℝ) ^ nu / (b : ℝ)) * (2 * (Real.log (N : ℝ) / Real.log 2)) :=
      mul_le_mul_of_nonneg_right hcount (mul_nonneg (by norm_num) hB)
    _ = _ := by ring

theorem two_integer_reciprocal_sum (N : ℕ) :
    (∑ t ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, 1 / ((t.1 * t.2 : ℕ) : ℝ)) =
      (∑ p ∈ Finset.Icc 1 N, 1 / (p : ℝ)) ^ 2 := by
  have hterm (t : ℕ × ℕ) : 1 / ((t.1 * t.2 : ℕ) : ℝ) =
      (1 / (t.1 : ℝ)) * (1 / (t.2 : ℝ)) := by
    simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  simp_rw [hterm]
  rw [Finset.sum_product, ← Finset.sum_mul_sum, pow_two]

theorem pair_reciprocal_sum_le (N : ℕ) (T : Finset (ℕ × ℕ))
    (hT : T ⊆ Finset.Icc 1 N ×ˢ Finset.Icc 1 N) :
    (∑ t ∈ T, 1 / ((t.1 * t.2 : ℕ) : ℝ)) ≤ (1 + Real.log (N : ℝ)) ^ 2 := by
  have hH : (∑ p ∈ Finset.Icc 1 N, 1 / (p : ℝ)) ≤ 1 + Real.log (N : ℝ) := by
    have heq : (∑ p ∈ Finset.Icc 1 N, 1 / (p : ℝ)) = (harmonic N : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    rw [heq]
    exact harmonic_le_one_add_log N
  calc
    _ ≤ ∑ t ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, 1 / ((t.1 * t.2 : ℕ) : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hT (fun _ _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _))
    _ = (∑ p ∈ Finset.Icc 1 N, 1 / (p : ℝ)) ^ 2 := two_integer_reciprocal_sum N
    _ ≤ _ := pow_le_pow_left₀
      (Finset.sum_nonneg (fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _))) hH 2

abbrev cutoff (N : ℕ) : ℝ := (N : ℝ) ^ (417 / 5000 : ℝ)

def pairCorrectionCost (N : ℕ) (T : Finset (ℕ × ℕ))
    (policy : (ℕ × ℕ) → List ℕ → Bool) (w L : (ℕ × ℕ) → ℝ) : ℝ :=
  ∑ t ∈ T, correctionCost (policy t) N (Nat.ceil (cutoff N)) (t.1 * t.2) (w t) (cutoff N) (L t)

theorem pairCorrectionCost_le_harmonic (N : ℕ) (T : Finset (ℕ × ℕ))
    (policy : (ℕ × ℕ) → List ℕ → Bool) (w L : (ℕ × ℕ) → ℝ)
    (nu : ℝ) (hN : 1 ≤ N) (hnu : nu ≤ 1)
    (hT : T ⊆ Finset.Icc 1 N ×ˢ Finset.Icc 1 N)
    (hcap : ∀ t ∈ T, ∀ k ∈ Active (policy t) N (Nat.ceil (cutoff N)) (w t) (cutoff N) (L t),
      (((t.1 * t.2) * k : ℕ) : ℝ) ≤ (N : ℝ) ^ nu) :
    pairCorrectionCost N T policy w L ≤
      (2 / Real.log 2) * (N : ℝ) ^ nu * Real.log (N : ℝ) * (1 + Real.log (N : ℝ)) ^ 2 := by
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hfactor : 0 ≤ (2 / Real.log 2) * (N : ℝ) ^ nu * Real.log (N : ℝ) :=
    mul_nonneg (mul_nonneg (div_nonneg (by norm_num)
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)) hlog
  calc
    _ ≤ ∑ t ∈ T, (2 / Real.log 2) * ((N : ℝ) ^ nu / ((t.1 * t.2 : ℕ) : ℝ)) * Real.log (N : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp (hT ht)
      exact correctionCost_le_physical_cap (policy t) N (Nat.ceil (cutoff N))
        (t.1 * t.2) (w t) (cutoff N) (L t) nu hN
        (Nat.mul_pos (Finset.mem_Icc.mp hp).1 (Finset.mem_Icc.mp hq).1) hnu (hcap t ht)
    _ = ((2 / Real.log 2) * (N : ℝ) ^ nu * Real.log (N : ℝ)) *
        (∑ t ∈ T, 1 / ((t.1 * t.2 : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pair_reciprocal_sum_le N T hT) hfactor

theorem pairCorrectionCost_le_power_log (N : ℕ) (T : Finset (ℕ × ℕ))
    (policy : (ℕ × ℕ) → List ℕ → Bool) (w L : (ℕ × ℕ) → ℝ)
    (nu : ℝ) (hN : 1 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ)) (hnu : nu ≤ 1)
    (hT : T ⊆ Finset.Icc 1 N ×ˢ Finset.Icc 1 N)
    (hcap : ∀ t ∈ T, ∀ k ∈ Active (policy t) N (Nat.ceil (cutoff N)) (w t) (cutoff N) (L t),
      (((t.1 * t.2) * k : ℕ) : ℝ) ≤ (N : ℝ) ^ nu) :
    pairCorrectionCost N T policy w L ≤
      (8 / Real.log 2) * (N : ℝ) ^ nu * Real.log (N : ℝ) ^ 3 := by
  have hlogs : (1 + Real.log (N : ℝ)) ^ 2 ≤ 4 * Real.log (N : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + Real.log (N : ℝ))
      (by linarith : 1 + Real.log (N : ℝ) ≤ 2 * Real.log (N : ℝ)) 2
    nlinarith only [h]
  have hlog0 : 0 ≤ Real.log (N : ℝ) := zero_le_one.trans hlog
  have hfactor : 0 ≤ (2 / Real.log 2) * (N : ℝ) ^ nu * Real.log (N : ℝ) :=
    mul_nonneg (mul_nonneg (div_nonneg (by norm_num)
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)) hlog0
  exact (pairCorrectionCost_le_harmonic N T policy w L nu hN hnu hT hcap).trans
    (by convert mul_le_mul_of_nonneg_left hlogs hfactor using 1 <;> ring)

theorem eventually_uniform_pairCorrectionCost (nu : ℝ) (hnu : nu < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ T : Finset (ℕ × ℕ),
      ∀ policy : (ℕ × ℕ) → List ℕ → Bool, ∀ w L : (ℕ × ℕ) → ℝ,
        T ⊆ Finset.Icc 1 N ×ˢ Finset.Icc 1 N →
        (∀ t ∈ T, ∀ k ∈ Active (policy t) N (Nat.ceil (cutoff N)) (w t) (cutoff N) (L t),
          (((t.1 * t.2) * k : ℕ) : ℝ) ≤ (N : ℝ) ^ nu) →
        pairCorrectionCost N T policy w L ≤ epsilon * singularNormalization N := by
  filter_upwards [eventually_powerLog_le_singularNormalization (8 / Real.log 2) nu 3 hnu epsilon hepsilon,
    eventually_one_le_nat_log, eventually_ge_atTop (1 : ℕ)] with N hp hlog hN
  intro T policy w L hT hcap
  exact (pairCorrectionCost_le_power_log N T policy w L nu hN hlog hnu.le hT hcap).trans hp

/-- This is the actual source envelope; it does not license the total
signed physical support by itself. -/
theorem original_U5_level_le_cap (x : Fin 2 → ℝ) :
    Part5OriginalUpsilon5CausalDictionary.level (x 0) (x 1) ≤ (153 / 256 : ℝ) := by
  unfold Part5OriginalUpsilon5CausalDictionary.level
  apply max_le (VariableEnvelope.v_le_cap _)
  apply max_le (VariableEnvelope.v_le_cap _)
  norm_num [VariableEnvelope.B, VariableEnvelope.cap, Part5OriginalUpsilon5CausalDictionary.a]

theorem original_U6_level_le_cap (x : Fin 2 → ℝ) :
    P5U6CausalLevelGeometry.physicalLevel (x 0) (x 1) ≤ (153 / 256 : ℝ) := by
  unfold P5U6CausalLevelGeometry.physicalLevel
  split_ifs
  · apply max_le (VariableEnvelope.v_le_cap _)
    apply max_le (VariableEnvelope.v_le_cap _)
    norm_num [VariableEnvelope.B, VariableEnvelope.cap, P5U6CausalLevelGeometry.a]
  · exact VariableEnvelope.v_le_cap _

theorem original_pair_carrier_subset_integer (N : ℕ) :
    chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N ⊆
      Finset.Icc 1 N ×ˢ Finset.Icc 1 N := by
  intro t ht
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp ht
  have hmem : ∀ {p : ℕ}, p ∈ chenAdditivePrimeCarrier N → p ∈ Finset.Icc 1 N := by
    intro p hp
    obtain ⟨hpN, hprime, _⟩ := mem_chenAdditivePrimeCarrier.mp hp
    exact Finset.mem_Icc.mpr ⟨hprime.pos, hpN.le⟩
  exact Finset.mem_product.mpr ⟨hmem hp, hmem hq⟩

theorem eventually_original_U5_correction_payment (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ policy : (ℕ × ℕ) → List ℕ → Bool,
      ∀ w L : (ℕ × ℕ) → ℝ,
      (∀ t ∈ P5OriginalU5CausalFinite.pairSupport N,
        ∀ k ∈ Active (policy t) N (Nat.ceil (cutoff N)) (w t) (cutoff N) (L t),
          (((t.1 * t.2) * k : ℕ) : ℝ) ≤ (N : ℝ) ^
            Part5OriginalUpsilon5CausalDictionary.level
              (P5OriginalU5CausalFinite.coordinates N t 0) (P5OriginalU5CausalFinite.coordinates N t 1)) →
      pairCorrectionCost N (P5OriginalU5CausalFinite.pairSupport N) policy w L ≤
        epsilon * singularNormalization N := by
  filter_upwards [eventually_uniform_pairCorrectionCost (153 / 256) (by norm_num) epsilon hepsilon,
    eventually_ge_atTop (1 : ℕ)] with N hpaid hN
  intro policy w L hlicense
  apply hpaid _ policy w L
  · exact (Finset.filter_subset _ _).trans (original_pair_carrier_subset_integer N)
  · intro t ht k hk
    exact (hlicense t ht k hk).trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hN) (original_U5_level_le_cap _))

theorem eventually_original_U6_correction_payment (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ eta : ℝ, ∀ E : ℕ × ℕ → Prop,
      ∀ policy : (ℕ × ℕ) → List ℕ → Bool, ∀ w L : (ℕ × ℕ) → ℝ,
      (∀ t ∈ currentChenUpsilon6RetainedSelector N E eta,
        ∀ k ∈ Active (policy t) N (Nat.ceil (cutoff N)) (w t) (cutoff N) (L t),
          (((t.1 * t.2) * k : ℕ) : ℝ) ≤ (N : ℝ) ^
            P5U6CausalLevelGeometry.physicalLevel
              (currentChenUpsilon6LogCoordinates N t 0) (currentChenUpsilon6LogCoordinates N t 1)) →
      pairCorrectionCost N (currentChenUpsilon6RetainedSelector N E eta) policy w L ≤
        epsilon * singularNormalization N := by
  filter_upwards [eventually_uniform_pairCorrectionCost (153 / 256) (by norm_num) epsilon hepsilon,
    eventually_ge_atTop (1 : ℕ)] with N hpaid hN
  intro eta E policy w L hlicense
  apply hpaid _ policy w L
  · intro t ht
    have hsource := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1).1
    exact original_pair_carrier_subset_integer N hsource
  · intro t ht k hk
    exact (hlicense t ht k hk).trans (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hN) (original_U6_level_le_cap _))

/-- This strengthens the earlier U5 finite entrance by deleting inactive
atoms before charging costs. It does not attempt to bound that earlier
module's larger full-display unweighted positive costs. -/
theorem original_U5_lower_with_active_cost {N : ℕ} (hN : 2 ≤ N)
    {precision : ℝ} (hprecision : 0 < precision) (hprecision8 : precision < 1 / 8)
    (policy : (ℕ × ℕ) → List ℕ → Bool) :
    P5OriginalU5CausalFinite.mainSum N precision policy +
      P5OriginalU5CausalFinite.signedPrimitiveSum N precision policy -
      pairCorrectionCost N (P5OriginalU5CausalFinite.pairSupport N) policy
        (fun _ => P5OriginalU5CausalFinite.smallCutoff N precision)
        (fun _ => P5OriginalU5CausalFinite.smallLevel N precision) ≤ currentChenUpsilon5 N := by
  have hg := P5OriginalU5CausalFinite.attachment_gates hN hprecision hprecision8
  have hrow (t : ℕ × ℕ) (ht : t ∈ P5OriginalU5CausalFinite.pairSupport N) :=
    quotient_primitive_lower_sub_active_cost (policy t) N (Nat.ceil (cutoff N)) (t.1 * t.2)
      (P5OriginalU5CausalFinite.smallCutoff N precision) (cutoff N)
      (P5OriginalU5CausalFinite.smallLevel N precision) hg.1 hg.2.1 hg.2.2 (Nat.le_ceil _)
      (P5OriginalU5CausalFinite.row_multiplier_rough ht)
  have hrowFull (t : ℕ × ℕ) (ht : t ∈ P5OriginalU5CausalFinite.pairSupport N) :
      P5OriginalU5CausalFinite.rowMain N precision (policy t) t +
        P5OriginalU5CausalFinite.rowSignedPrimitive N precision (policy t) t -
        correctionCost (policy t) N (Nat.ceil (cutoff N)) (t.1 * t.2)
          (P5OriginalU5CausalFinite.smallCutoff N precision) (cutoff N)
          (P5OriginalU5CausalFinite.smallLevel N precision) ≤
        ((chenSiftedQuotientPrimeSource N (t.1 * t.2) (cutoff N)).card : ℝ) := by
    have h := hrow t ht
    rw [← P5CausalRhoQuotientBridge.sum_eq_active] at h
    exact h
  rw [currentChenUpsilon5_eq_siftedQuotientPrimeSource]
  have hsum := Finset.sum_le_sum hrowFull
  simpa only [P5OriginalU5CausalFinite.mainSum, P5OriginalU5CausalFinite.signedPrimitiveSum,
    pairCorrectionCost, Finset.sum_add_distrib, Finset.sum_sub_distrib] using hsum

/-- Actual original U5 causal main plus its SIGNED primitive remainder
now has only the prescribed normalized prime-correction loss, conditional
solely on the separately supplied structural physical-support license. -/
theorem eventually_original_U5_lower_prime_corrections_paid
    (precision epsilon : ℝ) (hprecision : 0 < precision) (hprecision8 : precision < 1 / 8)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ policy : (ℕ × ℕ) → List ℕ → Bool,
      (∀ t ∈ P5OriginalU5CausalFinite.pairSupport N,
        ∀ k ∈ Active (policy t) N (Nat.ceil (cutoff N))
          (P5OriginalU5CausalFinite.smallCutoff N precision) (cutoff N)
          (P5OriginalU5CausalFinite.smallLevel N precision),
          (((t.1 * t.2) * k : ℕ) : ℝ) ≤ (N : ℝ) ^
            Part5OriginalUpsilon5CausalDictionary.level
              (P5OriginalU5CausalFinite.coordinates N t 0) (P5OriginalU5CausalFinite.coordinates N t 1)) →
      P5OriginalU5CausalFinite.mainSum N precision policy +
        P5OriginalU5CausalFinite.signedPrimitiveSum N precision policy -
        epsilon * singularNormalization N ≤ currentChenUpsilon5 N := by
  filter_upwards [eventually_original_U5_correction_payment epsilon hepsilon,
    eventually_ge_atTop (2 : ℕ)] with N hpaid hN
  intro policy hlicense
  have hcost := hpaid policy
    (fun _ => P5OriginalU5CausalFinite.smallCutoff N precision)
    (fun _ => P5OriginalU5CausalFinite.smallLevel N precision) hlicense
  have hfinite := original_U5_lower_with_active_cost hN hprecision hprecision8 policy
  linarith only [hcost, hfinite]

def pairMainAndSigned (N : ℕ) (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ) (t : ℕ × ℕ) : ℝ :=
  ((chenPrimePrefix N).card : ℝ) / (Nat.totient (t.1 * t.2) : ℝ) *
    physicalDensitySum
      (actualLowerSmallRoughModuli (policy t) N (Nat.ceil (cutoff N)) (w t) (cutoff N))
      (actualLowerSmallRoughRho (policy t) N (Nat.ceil (cutoff N)) (w t) (cutoff N) (L t)) +
  ∑ k ∈ Active (policy t) N (Nat.ceil (cutoff N)) (w t) (cutoff N) (L t),
    actualLowerSmallRoughRho (policy t) N (Nat.ceil (cutoff N)) (w t) (cutoff N) (L t) k *
      finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N ((t.1 * t.2) * k)

def retainedU6MainAndSigned (N : ℕ) (eta : ℝ) (E : ℕ × ℕ → Prop)
    (policy : (ℕ × ℕ) → List ℕ → Bool) (precision : ℝ) : ℝ :=
  ∑ t ∈ currentChenUpsilon6RetainedSelector N E eta,
    pairMainAndSigned N policy (P5U6CausalLevelGeometry.attachedSmallCutoff N precision)
      (P5U6CausalLevelGeometry.attachedSmallLevel N precision) t

theorem retained_U6_lower_with_active_cost {N : ℕ} (hN : (1 : ℝ) < N)
    {eta precision : ℝ} (heta : 0 ≤ eta) (hprecision : 0 < precision)
    (hprecision8 : precision < 1 / 8) (E : ℕ × ℕ → Prop)
    (policy : (ℕ × ℕ) → List ℕ → Bool) :
    retainedU6MainAndSigned N eta E policy precision -
      pairCorrectionCost N (currentChenUpsilon6RetainedSelector N E eta) policy
        (P5U6CausalLevelGeometry.attachedSmallCutoff N precision)
        (P5U6CausalLevelGeometry.attachedSmallLevel N precision) ≤
      currentChenUpsilon6Retained N E eta := by
  unfold retainedU6MainAndSigned pairCorrectionCost currentChenUpsilon6Retained
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro t ht
  have hg := P5U6CausalLevelGeometry.attachment_gates hN heta hprecision hprecision8 E ht
  have hselector := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  exact quotient_primitive_lower_sub_active_cost (policy t) N (Nat.ceil (cutoff N)) (t.1 * t.2)
    (P5U6CausalLevelGeometry.attachedSmallCutoff N precision t) (cutoff N)
    (P5U6CausalLevelGeometry.attachedSmallLevel N precision t)
    hg.1 hg.2.1 hg.2.2 (Nat.le_ceil _)
    (P5CausalRhoQuotientBridge.row_multiplier_rough hselector)

theorem eventually_original_U6_lower_prime_corrections_paid
    (precision epsilon : ℝ) (hprecision : 0 < precision) (hprecision8 : precision < 1 / 8)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ eta : ℝ, 0 ≤ eta → ∀ E : ℕ × ℕ → Prop,
      ∀ policy : (ℕ × ℕ) → List ℕ → Bool,
      (∀ t ∈ currentChenUpsilon6RetainedSelector N E eta,
        ∀ k ∈ Active (policy t) N (Nat.ceil (cutoff N))
          (P5U6CausalLevelGeometry.attachedSmallCutoff N precision t) (cutoff N)
          (P5U6CausalLevelGeometry.attachedSmallLevel N precision t),
          (((t.1 * t.2) * k : ℕ) : ℝ) ≤ (N : ℝ) ^
            P5U6CausalLevelGeometry.physicalLevel
              (currentChenUpsilon6LogCoordinates N t 0) (currentChenUpsilon6LogCoordinates N t 1)) →
      retainedU6MainAndSigned N eta E policy precision - epsilon * singularNormalization N ≤
        currentChenUpsilon6Retained N E eta := by
  filter_upwards [eventually_original_U6_correction_payment epsilon hepsilon,
    eventually_ge_atTop (2 : ℕ)] with N hpaid hN
  intro eta heta E policy hlicense
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hcost := hpaid eta E policy (P5U6CausalLevelGeometry.attachedSmallCutoff N precision)
    (P5U6CausalLevelGeometry.attachedSmallLevel N precision) hlicense
  have hfinite := retained_U6_lower_with_active_cost hNr heta hprecision hprecision8 E policy
  linarith only [hcost, hfinite]

end

end ImbalancedChen.P5CausalPrimeCorrectionPayment
