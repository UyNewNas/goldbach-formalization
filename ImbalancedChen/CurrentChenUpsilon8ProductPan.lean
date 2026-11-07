import ImbalancedChen.CurrentChenUpsilon8PrimeSource
import ImbalancedChen.CurrentChenUpsilon9PanAggregate

/-!
# The actual eighth product coefficient and bounded Pan majorant

The eighth and ninth selector predicates have the same generic form, so
the proved product injection is reused at the eighth endpoints.  The
literal eighth image gives its own modulus-independent zero-one source
coefficient.  Its true upper endpoint is N^(2/3), which is allowed
inclusively by the fixed bounded-coefficient Pan theorem.

The original p2 roughness is dropped only after primality in the finite
count upper bound.  The actual additive-prime carrier remains.  This leaf
pays the actual source window and coefficient bounds, then applies the
genuine Pan aggregate.  The subsequent coprime main-term gate and signed
Rosser error payment are not assumed or asserted here.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory.LiuWeight

theorem chenY8PrimeSelector_multiplier_injOn (N : ℕ) (A C : ℝ) :
    Set.InjOn (fun t : ℕ × ℕ => t.1 * t.2)
      (chenY8PrimeSelector N A C : Set (ℕ × ℕ)) := by
  exact chenY9PrimeSelector_multiplier_injOn N A C

def currentChenUpsilon8PrefixProducts (N : ℕ) : Finset ℕ :=
  (chenY8PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
    ((N : ℝ) ^ (1 / 3 : ℝ))).image (fun t => t.1 * t.2)

def currentChenUpsilon8ProductCoefficient (N a : ℕ) : ℝ :=
  if a ∈ currentChenUpsilon8PrefixProducts N then 1 else 0

theorem abs_currentChenUpsilon8ProductCoefficient_le_one (N a : ℕ) :
    |currentChenUpsilon8ProductCoefficient N a| ≤ 1 := by
  by_cases ha : a ∈ currentChenUpsilon8PrefixProducts N <;>
    simp only [currentChenUpsilon8ProductCoefficient, ha, if_true, if_false,
      abs_one, abs_zero, zero_le_one, le_refl]

theorem currentChenUpsilon8PrefixProducts_data {N a : ℕ}
    (ha : a ∈ currentChenUpsilon8PrefixProducts N) :
    0 < a ∧ Nat.Coprime a N := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hc, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc₁, hc₂⟩ := Finset.mem_product.mp hc
  have hp₁ := mem_chenAdditivePrimeCarrier.mp hc₁
  have hp₂ := mem_chenAdditivePrimeCarrier.mp hc₂
  exact ⟨mul_pos hp₁.2.1.pos hp₂.2.1.pos, hp₁.2.2.mul_left hp₂.2.2⟩

/-- The original square-root wall and strict first cap pay the endpoint
2/3 itself, rather than an assumed smaller ninth-source exponent. -/
theorem currentChenUpsilon8_multiplier_power_bounds {N : ℕ} {t : ℕ × ℕ}
    (hN : (1 : ℝ) ≤ N)
    (ht : t ∈ chenY8PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) :
    (N : ℝ) ^ (6251 / 15000 : ℝ) ≤ ((t.1 * t.2 : ℕ) : ℝ) ∧
      ((t.1 * t.2 : ℕ) : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ) := by
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN
  obtain ⟨hc, hA, hfirst, hsecond, hcap⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc₁, _⟩ := Finset.mem_product.mp hc
  have hp₁ : (0 : ℝ) < t.1 := by
    exact_mod_cast (mem_chenAdditivePrimeCarrier.mp hc₁).2.1.pos
  have hlo : (N : ℝ) ^ (417 / 5000 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) ≤
      ((t.1 * t.2 : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    exact mul_le_mul hA hsecond (Real.rpow_nonneg hNp.le _) (Nat.cast_nonneg _)
  have hcapsq : (t.2 : ℝ) ^ 2 < (N : ℝ) / (t.1 : ℝ) := by
    have h := (sq_lt_sq₀ (Nat.cast_nonneg t.2) (Real.sqrt_nonneg _)).mpr hcap
    rwa [Real.sq_sqrt (div_nonneg hNp.le hp₁.le)] at h
  have hcapmul : (t.2 : ℝ) ^ 2 * (t.1 : ℝ) < (N : ℝ) :=
    (lt_div_iff₀ hp₁).mp hcapsq
  have hprodsq : ((t.1 : ℝ) * (t.2 : ℝ)) ^ 2 < (N : ℝ) * (t.1 : ℝ) := by
    have h := mul_lt_mul_of_pos_right hcapmul hp₁
    nlinarith only [h]
  have hfirstmul : (N : ℝ) * (t.1 : ℝ) <
      (N : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) := mul_lt_mul_of_pos_left hfirst hNp
  have hpowersq : ((N : ℝ) ^ (2 / 3 : ℝ)) ^ 2 =
      (N : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_mul_natCast hNp.le (2 / 3 : ℝ) 2,
      show (2 / 3 : ℝ) * ((2 : ℕ) : ℝ) = 1 + 1 / 3 by norm_num,
      Real.rpow_add hNp, Real.rpow_one]
  constructor
  · rw [← Real.rpow_add hNp] at hlo
    convert hlo using 1
    norm_num
  · rw [Nat.cast_mul]
    apply (sq_lt_sq₀ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Real.rpow_nonneg hNp.le _)).mp
    rw [hpowersq]
    exact hprodsq.trans hfirstmul

theorem currentChenUpsilon8PrefixProducts_power_bounds {N a : ℕ}
    (hN : (1 : ℝ) ≤ N) (ha : a ∈ currentChenUpsilon8PrefixProducts N) :
    (N : ℝ) ^ (6251 / 15000 : ℝ) ≤ (a : ℝ) ∧
      (a : ℝ) < (N : ℝ) ^ (2 / 3 : ℝ) := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
  exact currentChenUpsilon8_multiplier_power_bounds hN ht

def currentChenUpsilon8PanLower (N : ℕ) : ℕ :=
  Nat.ceil ((N : ℝ) ^ (6251 / 15000 : ℝ)) - 1

def currentChenUpsilon8PanUpper (N : ℕ) : ℕ :=
  Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) - 1

theorem currentChenUpsilon8PrefixProducts_subset_pan_interval {N : ℕ}
    (hN : (1 : ℝ) ≤ N) :
    currentChenUpsilon8PrefixProducts N ⊆
      Finset.Ioc (currentChenUpsilon8PanLower N) (currentChenUpsilon8PanUpper N) := by
  intro a ha
  obtain ⟨hlo, hhi⟩ := currentChenUpsilon8PrefixProducts_power_bounds hN ha
  have hceil : Nat.ceil ((N : ℝ) ^ (6251 / 15000 : ℝ)) ≤ a := Nat.ceil_le.mpr hlo
  have hceilpos : 1 ≤ Nat.ceil ((N : ℝ) ^ (6251 / 15000 : ℝ)) :=
    Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos (zero_lt_one.trans_le hN) _)
  have hceilhi : a < Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) := Nat.lt_ceil.mpr hhi
  apply Finset.mem_Ioc.mpr
  dsimp [currentChenUpsilon8PanLower, currentChenUpsilon8PanUpper]
  omega

/-- Exact source-coefficient identity on the actual Pan window. -/
theorem currentChenUpsilon8ProductCoefficient_sum {N : ℕ}
    (hN : (1 : ℝ) ≤ N) (G : ℕ → ℝ) :
    (∑ a ∈ Finset.Ioc (currentChenUpsilon8PanLower N) (currentChenUpsilon8PanUpper N),
      currentChenUpsilon8ProductCoefficient N a * G a) =
        ∑ a ∈ currentChenUpsilon8PrefixProducts N, G a := by
  have hfilter :
      (Finset.Ioc (currentChenUpsilon8PanLower N) (currentChenUpsilon8PanUpper N)).filter
        (fun a => a ∈ currentChenUpsilon8PrefixProducts N) =
          currentChenUpsilon8PrefixProducts N := by
    ext a
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,
      fun ha => ⟨currentChenUpsilon8PrefixProducts_subset_pan_interval hN ha, ha⟩⟩
  rw [← hfilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ currentChenUpsilon8PrefixProducts N <;>
    simp only [currentChenUpsilon8ProductCoefficient, ha, if_true, if_false, one_mul, zero_mul]

/-- This uses the already defined generic switched prime fibre in the
ninth module.  Only its arbitrary N,a parameters occur in that definition. -/
theorem currentChenUpsilon8_le_switched_prime_fibres_add_unitFibres (N : ℕ) :
    currentChenUpsilon8 N ≤
      (∑ a ∈ currentChenUpsilon8PrefixProducts N,
        ((currentChenUpsilon9SwitchedPrimeFibre N a).card : ℝ)) +
          ((currentChenUpsilon8UnitFibres N).card : ℝ) := by
  rw [currentChenUpsilon8_eq_primeTriples_add_unitFibres,
    currentChenUpsilon8PrimeTriples, Finset.card_sigma, Nat.cast_sum,
    currentChenUpsilon8PrefixProducts,
    Finset.sum_image (chenY8PrimeSelector_multiplier_injOn N
      ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)))]
  refine add_le_add ?_ (le_refl _)
  apply Finset.sum_le_sum
  intro t ht
  have hp := chenY9PrimeSelector_ordered_prime_data
    (N := N) (H := (N : ℝ) ^ (417 / 5000 : ℝ)) (D := (N : ℝ) ^ (1 / 3 : ℝ)) ht
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro q hq
  obtain ⟨hqsource, hprime⟩ := Finset.mem_filter.mp hq
  obtain ⟨hlt, hP, _⟩ :=
    (currentChenUpsilon9_prime_mem_iff (mul_pos hp.1.pos hp.2.1.pos) hprime _).mp hqsource
  have hqN := (chenQuotientPrimeSource_data (Finset.mem_filter.mp hqsource).1).2.1
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hqN), hprime, hlt, hP⟩

theorem currentChenUpsilon8_le_same_coefficient_switched_count {N : ℕ}
    (hN : (1 : ℝ) ≤ N) :
    currentChenUpsilon8 N ≤
      (∑ a ∈ Finset.Ioc (currentChenUpsilon8PanLower N) (currentChenUpsilon8PanUpper N),
        currentChenUpsilon8ProductCoefficient N a *
          ((currentChenUpsilon9SwitchedPrimeFibre N a).card : ℝ)) +
            ((currentChenUpsilon8UnitFibres N).card : ℝ) := by
  rw [currentChenUpsilon8ProductCoefficient_sum hN]
  exact currentChenUpsilon8_le_switched_prime_fibres_add_unitFibres N

theorem currentChenUpsilon8_panUpper_le_two_thirds {N : ℕ} (hN : (1 : ℝ) ≤ N) :
    (currentChenUpsilon8PanUpper N : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
  have hu : 0 < (N : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hN) _
  have hceil : 1 ≤ Nat.ceil ((N : ℝ) ^ (2 / 3 : ℝ)) := Nat.one_le_ceil_iff.mpr hu
  unfold currentChenUpsilon8PanUpper
  rw [Nat.cast_sub hceil, Nat.cast_one]
  have h := Nat.ceil_lt_add_one hu.le
  linarith only [h]

theorem eventually_currentChenUpsilon8_panLower_log_gate (B : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ (2 * B) ≤ (currentChenUpsilon8PanLower N : ℝ) := by
  have hreal : ∀ᶠ x : ℝ in atTop,
      Real.log x ^ (2 * B) ≤ (1 / 2 : ℝ) * x ^ (6251 / 15000 : ℝ) := by
    have hb := (isLittleO_log_rpow_rpow_atTop (2 * B)
      (by norm_num : (0 : ℝ) < 6251 / 15000)).bound (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx1) _)] at hx
    exact hx
  have hlarge : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (6251 / 15000 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 6251 / 15000)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hreal, hlarge] with N hlog hlarge
  have hceil : 1 ≤ Nat.ceil ((N : ℝ) ^ (6251 / 15000 : ℝ)) :=
    Nat.one_le_ceil_iff.mpr (by linarith only [hlarge])
  have hbound : (1 / 2 : ℝ) * (N : ℝ) ^ (6251 / 15000 : ℝ) ≤
      (currentChenUpsilon8PanLower N : ℝ) := by
    unfold currentChenUpsilon8PanLower
    rw [Nat.cast_sub hceil, Nat.cast_one]
    have h := Nat.le_ceil ((N : ℝ) ^ (6251 / 15000 : ℝ))
    linarith only [h, hlarge]
  exact hlog.trans hbound

theorem currentChenUpsilon8_li_argument_power_lower {N a : ℕ}
    (hN : (1 : ℝ) ≤ N) (ha : a ∈ currentChenUpsilon8PrefixProducts N) :
    (N : ℝ) ^ (1 / 3 : ℝ) ≤ (N : ℝ) / (a : ℝ) := by
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN
  have hap : (0 : ℝ) < a := by exact_mod_cast (currentChenUpsilon8PrefixProducts_data ha).1
  apply (le_div_iff₀ hap).mpr
  calc
    _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left (currentChenUpsilon8PrefixProducts_power_bounds hN ha).2.le
        (Real.rpow_nonneg hNp.le _)
    _ = _ := by
      rw [← Real.rpow_add hNp, show (1 / 3 : ℝ) + 2 / 3 = 1 by norm_num, Real.rpow_one]

theorem currentChenUpsilon8_log_gap_lower {N a : ℕ} (hN : 2 ≤ N)
    (ha : a ∈ currentChenUpsilon8PrefixProducts N) :
    (1 / 3 : ℝ) ≤ 1 - Real.log (a : ℝ) / Real.log (N : ℝ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hap : (0 : ℝ) < a := by exact_mod_cast (currentChenUpsilon8PrefixProducts_data ha).1
  have hlog := Real.log_pos hNr
  have hupper := Real.log_le_log hap
    (currentChenUpsilon8PrefixProducts_power_bounds hNr.le ha).2.le
  rw [Real.log_rpow (zero_lt_one.trans hNr)] at hupper
  have hquot : Real.log (a : ℝ) / Real.log (N : ℝ) ≤ (2 / 3 : ℝ) :=
    (div_le_iff₀ hlog).mpr (by nlinarith only [hupper])
  linarith only [hquot]

/-- The fixed true-li Pan theorem is applied to the actual eighth zero-one
coefficient, after both source-window gates have been proved. -/
theorem exists_currentChenUpsilon8_sameCoefficient_pan_majorant
    (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (∑ d ∈ Finset.Icc 1 (panModulusCutoff N B),
        liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
          N (currentChenUpsilon8PanLower N) (currentChenUpsilon8PanUpper N) d
            (currentChenUpsilon8ProductCoefficient N)) ≤
        C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨C, hC, B, hB, N₀, hPan⟩ :=
    liuMainPanCoprimeIntervalMaxL_boundedAggregate_log_saving U hU
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (eventually_currentChenUpsilon8_panLower_log_gate B)
  refine ⟨C, hC, B, hB, max N₀ (max N₁ 1), ?_⟩
  intro N hN
  have h0 : N₀ ≤ N := by omega
  have h1 : N₁ ≤ N := by omega
  have hNp : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  exact hPan N h0 _ _ _ (currentChenUpsilon8_panUpper_le_two_thirds hNp)
    (hN₁ N h1) (abs_currentChenUpsilon8ProductCoefficient_le_one N)

end

end ImbalancedChen
