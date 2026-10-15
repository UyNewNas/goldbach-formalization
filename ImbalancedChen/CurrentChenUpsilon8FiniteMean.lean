import ImbalancedChen.CurrentChenUpsilon8CoprimeGateBudget
import ImbalancedChen.CurrentChenUpsilon8SourceErrorBudget
import ImbalancedChen.CurrentChenUpsilon9FiniteMean

/-!
# The actual eighth count and its paid switched density main term

The original eighth product image, its modulus-independent zero-one
coefficient and its literal unit fibres are retained. The public generic
prime-fibre sieve and finite Fubini bridge are reused on each actual eighth
multiplier. Their native prime carrier has the closed endpoint a*q<=N,
including receiver zero; the strict original count is enlarged only by
the already proved nonnegativity of the complete divisor sum.

The AP identity below keeps the true multiplier coprimality gate and the
actual signed upper Rosser coefficient. The strict level Q+1 makes the
fullsupport-to-active restriction exact. The owned actual eighth Pan
majorant, its paid coprime gate and the literal finite source errors give
one B before every epsilon, and one threshold before every cap.

Only this finite main-and-error statement is proved. The density is the
same source-independent explicit sum already defined in the ninth finite
bridge. No density bound, true-li mean, harmonic mean or adopted constant
is assumed or asserted here.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.LiuWeight

/-- The native closed AP count on the literal eighth product image. -/
def currentChenUpsilon8PrefixAPCount (N d : ℕ) : ℝ :=
  ∑ a ∈ currentChenUpsilon8PrefixProducts N, (primesInAPBelow N a d N : ℝ)

/-- The actual eighth same-coefficient Pan error at the original target residue. -/
def currentChenUpsilon8PanError (N d : ℕ) : ℝ :=
  liuMainPanCoprimeIntervalSum (liuLogarithmicIntegral (2 / Real.log 2))
    N (currentChenUpsilon8PanLower N) (currentChenUpsilon8PanUpper N)
    d (N % d) (currentChenUpsilon8ProductCoefficient N)

private theorem currentChenUpsilon8_primesInAPBelow_target_mod (N a d : ℕ) :
    primesInAPBelow N a d (N % d) = primesInAPBelow N a d N := by
  simp only [primesInAPBelow, Nat.ModEq, Nat.mod_mod]
  rfl

/-- Exact li main mass, genuine coprime defect and same-coefficient Pan error. -/
theorem currentChenUpsilon8_prefixAPCount_eq_main_sub_defect_add_error
    {N d : ℕ} (hN : (1 : ℝ) ≤ N) (hNd : Nat.Coprime N d) :
    currentChenUpsilon8PrefixAPCount N d =
      (currentChenUpsilon8LiMainMass N - currentChenUpsilon8CoprimeMainDefect N d) /
        (Nat.totient d : ℝ) + currentChenUpsilon8PanError N d := by
  have herror : currentChenUpsilon8PanError N d =
      ∑ a ∈ currentChenUpsilon8PrefixProducts N,
        if Nat.Coprime a d then
          liuScaledAPError (liuLogarithmicIntegral (2 / Real.log 2)) N a d (N % d)
        else 0 := by
    unfold currentChenUpsilon8PanError liuMainPanCoprimeIntervalSum
    calc
      _ = ∑ a ∈ Finset.Ioc (currentChenUpsilon8PanLower N) (currentChenUpsilon8PanUpper N),
          currentChenUpsilon8ProductCoefficient N a *
            (if Nat.Coprime a d then
              liuScaledAPError (liuLogarithmicIntegral (2 / Real.log 2)) N a d (N % d)
            else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        split_ifs <;> ring
      _ = _ := currentChenUpsilon8ProductCoefficient_sum hN _
  have hpoint : ∀ a ∈ currentChenUpsilon8PrefixProducts N,
      (if Nat.Coprime a d then
        liuScaledAPError (liuLogarithmicIntegral (2 / Real.log 2)) N a d (N % d)
      else 0) = (primesInAPBelow N a d N : ℝ) -
        (liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (a : ℝ)) -
          (if Nat.Coprime a d then 0 else
            liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (a : ℝ)))) /
              (Nat.totient d : ℝ) := by
    intro a _
    by_cases hc : Nat.Coprime a d
    · rw [if_pos hc, if_pos hc, sub_zero, liuScaledAPError,
        currentChenUpsilon8_primesInAPBelow_target_mod]
    · simp only [hc, if_false, sub_self, zero_div, sub_zero]
      exact (currentChenUpsilon9_primesInAPBelow_eq_zero_of_not_coprime hNd hc).symm
  have hidentity : currentChenUpsilon8PanError N d =
      currentChenUpsilon8PrefixAPCount N d -
        (currentChenUpsilon8LiMainMass N - currentChenUpsilon8CoprimeMainDefect N d) /
          (Nat.totient d : ℝ) := by
    rw [herror]
    calc
      _ = ∑ a ∈ currentChenUpsilon8PrefixProducts N,
          ((primesInAPBelow N a d N : ℝ) -
            (liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (a : ℝ)) -
              (if Nat.Coprime a d then 0 else
                liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (a : ℝ)))) /
                  (Nat.totient d : ℝ)) := Finset.sum_congr rfl hpoint
      _ = _ := by
        simp only [currentChenUpsilon8PrefixAPCount, currentChenUpsilon8LiMainMass,
          currentChenUpsilon8CoprimeMainDefect, Finset.sum_sub_distrib, Finset.sum_div, sub_div]
  linarith only [hidentity]

private theorem currentChenUpsilon8_upper_sum_eq_active
    (B : ℝ) (N cap : ℕ) (z : ℝ) (G : ℕ → ℝ) :
    (∑ d ∈ actualSmallRosserSupport N cap z,
      actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d * G d) =
      ∑ d ∈ currentChenUpsilon9PanActive B N cap z,
        actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d * G d := by
  rw [currentChenUpsilon9PanActive, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d ≤ panModulusCutoff N B
  · simp only [hd, if_true]
  · have hz : actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d = 0 := by
      by_contra hn
      have hactive := (actualSmallRosserPlus_active hn).2.1
      have hdlt : d < panModulusCutoff N B + 1 := by exact_mod_cast hactive
      omega
    simp only [hd, if_false, hz, zero_mul]

/-- The same complete signed upper Rosser weight applied to the actual eighth error. -/
def currentChenUpsilon8PanRosserError (B : ℝ) (N cap : ℕ) (z : ℝ) : ℝ :=
  ∑ d ∈ actualSmallRosserSupport N cap z,
    actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d *
      currentChenUpsilon8PanError N d

/-- The strict level Q+1 pays every omitted modulus exactly. -/
theorem currentChenUpsilon8PanRosserError_eq_active (B : ℝ) (N cap : ℕ) (z : ℝ) :
    currentChenUpsilon8PanRosserError B N cap z =
      ∑ d ∈ currentChenUpsilon9PanActive B N cap z,
        actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d *
          currentChenUpsilon8PanError N d := by
  exact currentChenUpsilon8_upper_sum_eq_active B N cap z _

private theorem currentChenUpsilon8_abs_panError_le_MaxL {N d : ℕ}
    (hd : 0 < d) (hNd : Nat.Coprime N d) :
    |currentChenUpsilon8PanError N d| ≤
      liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
        N (currentChenUpsilon8PanLower N) (currentChenUpsilon8PanUpper N) d
        (currentChenUpsilon8ProductCoefficient N) := by
  have hres : N % d ∈ unitResidues d := by
    change N % d ∈ finiteReducedResidues d
    exact (mod_mem_finiteReducedResidues_iff N d hd).mpr hNd
  have hnonempty : (unitResidues d).Nonempty := ⟨N % d, hres⟩
  unfold liuMainPanCoprimeIntervalMaxL
  dsimp only
  rw [dif_pos hnonempty]
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨N % d, hres, rfl⟩

/-- No factor for the number of source labels or active moduli is inserted. -/
theorem currentChenUpsilon8_abs_panRosserError_le_MaxL_sum
    (B : ℝ) (N cap : ℕ) (z : ℝ) :
    |currentChenUpsilon8PanRosserError B N cap z| ≤
      ∑ d ∈ Finset.Icc 1 (panModulusCutoff N B),
        liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
          N (currentChenUpsilon8PanLower N) (currentChenUpsilon8PanUpper N) d
          (currentChenUpsilon8ProductCoefficient N) := by
  have hpoint : |currentChenUpsilon8PanRosserError B N cap z| ≤
      ∑ d ∈ currentChenUpsilon9PanActive B N cap z,
        liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
          N (currentChenUpsilon8PanLower N) (currentChenUpsilon8PanUpper N) d
          (currentChenUpsilon8ProductCoefficient N) := by
    rw [currentChenUpsilon8PanRosserError_eq_active]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro d hd
    have hds := (Finset.mem_filter.mp hd).1
    have hdp := Nat.pos_of_mem_divisors hds
    have hNd := (actualSmallRosserSupport_coprime_target N cap z hds).symm
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _)
      (actualSmallRosserPlus_abs_le_one N cap z _ d)).trans
        (currentChenUpsilon8_abs_panError_le_MaxL hdp hNd)
  apply hpoint.trans
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (currentChenUpsilon9PanActive_subset B N cap z)
    (fun d _ _ => liuMainPanCoprimeIntervalMaxL_nonneg _ _ _ _ _ _)

/-- The actual eighth majorant chooses B before epsilon, N, cap and z. -/
theorem exists_currentChenUpsilon8_panRosserError_budget :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ cap : ℕ, ∀ z : ℝ,
        |currentChenUpsilon8PanRosserError B N cap z| ≤
          ε * singularNormalization N := by
  obtain ⟨C, _hC, B, hB, N₀, hagg⟩ :=
    exists_currentChenUpsilon8_sameCoefficient_pan_majorant 3 (by norm_num)
  refine ⟨B, hB, ?_⟩
  intro ε hε
  have hlarge : ∀ᶠ N : ℕ in atTop,
      C / (ε * twinPrimeConstant) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  have hlog : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop N₀, hlarge, hlog]
    with N hN₀ hlarge hlog
  intro cap z
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hdist := hagg N hN₀
  rw [Real.rpow_ofNat] at hdist
  have hcoeff : C / Real.log (N : ℝ) ≤ ε * twinPrimeConstant := by
    apply (div_le_iff₀ hlogpos).mpr
    have h := (div_le_iff₀ (mul_pos hε twinPrimeConstant_pos)).mp hlarge
    nlinarith only [h]
  have hpaid : C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℕ) ≤
      ε * singularNormalization N := by
    calc
      _ = (C / Real.log (N : ℝ)) *
          ((N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ)) := by
        field_simp [hlogpos.ne']
      _ ≤ (ε * twinPrimeConstant) * ((N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = ε * (twinPrimeConstant * (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (singularNormalization_lower N) hε.le
  exact ((currentChenUpsilon8_abs_panRosserError_le_MaxL_sum B N cap z).trans hdist).trans hpaid

/-- Generic finite Fubini, reindexed over the original eighth products. -/
theorem currentChenUpsilon8_product_sum_upperDivisorSum
    (N cap : ℕ) (z L : ℝ) :
    (∑ a ∈ currentChenUpsilon8PrefixProducts N,
      ∑ q ∈ currentChenUpsilon9PrefixPrimeFibre N a,
        supportedDivisorSum (actualSmallRosserSupport N cap z)
          (actualSmallRosserPlus N cap z L) (N - a * q)) =
      ∑ d ∈ actualSmallRosserSupport N cap z,
        actualSmallRosserPlus N cap z L d * currentChenUpsilon8PrefixAPCount N d := by
  simp_rw [currentChenUpsilon9_prefix_sum_upperDivisorSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [currentChenUpsilon8PrefixAPCount, Finset.mul_sum]

/-- The same full actual coefficient supplies all three terms of this exact identity. -/
theorem currentChenUpsilon8_upper_AP_sum_eq_main_errors
    (B : ℝ) {N : ℕ} (hN : (1 : ℝ) ≤ N) (cap : ℕ) (z : ℝ) :
    (∑ d ∈ actualSmallRosserSupport N cap z,
      actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d *
        currentChenUpsilon8PrefixAPCount N d) =
      currentChenUpsilon8LiMainMass N * currentChenUpsilon9SwitchedUpperDensity B N cap z -
        currentChenUpsilon8CoprimeGateError N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ)
          (currentChenUpsilon9PanActive B N cap z) +
        currentChenUpsilon8PanRosserError B N cap z := by
  have hgate : currentChenUpsilon8CoprimeGateError N cap z
      ((panModulusCutoff N B + 1 : ℕ) : ℝ) (actualSmallRosserSupport N cap z) =
      currentChenUpsilon8CoprimeGateError N cap z
        ((panModulusCutoff N B + 1 : ℕ) : ℝ) (currentChenUpsilon9PanActive B N cap z) :=
    currentChenUpsilon8_upper_sum_eq_active B N cap z _
  rw [← hgate]
  calc
    _ = ∑ d ∈ actualSmallRosserSupport N cap z,
        ((currentChenUpsilon8LiMainMass N *
          (actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d /
            (Nat.totient d : ℝ)) -
          actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d *
            (currentChenUpsilon8CoprimeMainDefect N d / (Nat.totient d : ℝ))) +
          actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d *
            currentChenUpsilon8PanError N d) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [currentChenUpsilon8_prefixAPCount_eq_main_sub_defect_add_error hN
        (actualSmallRosserSupport_coprime_target N cap z hd).symm]
      ring
    _ = _ := by
      simp only [currentChenUpsilon9SwitchedUpperDensity, currentChenUpsilon8CoprimeGateError,
        currentChenUpsilon8PanRosserError, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum]

/-- The literal eighth count, including its actual unit fibres and generic small-P loss. -/
theorem currentChenUpsilon8_le_upper_density_main_add_errors
    (B : ℝ) {N : ℕ} (hN : (1 : ℝ) ≤ N) (cap : ℕ) (z : ℝ)
    (hL : 1 < ((panModulusCutoff N B + 1 : ℕ) : ℝ))
    (hzL : z ≤ ((panModulusCutoff N B + 1 : ℕ) : ℝ)) :
    currentChenUpsilon8 N ≤
      currentChenUpsilon8LiMainMass N * currentChenUpsilon9SwitchedUpperDensity B N cap z -
        currentChenUpsilon8CoprimeGateError N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ)
          (currentChenUpsilon9PanActive B N cap z) +
        currentChenUpsilon8PanRosserError B N cap z +
        ((currentChenUpsilon8PrefixProducts N).card : ℝ) * (Nat.ceil z : ℝ) +
        ((currentChenUpsilon8UnitFibres N).card : ℝ) := by
  have hsource := currentChenUpsilon8_le_switched_prime_fibres_add_unitFibres N
  have hrows : (∑ a ∈ currentChenUpsilon8PrefixProducts N,
      ((currentChenUpsilon9SwitchedPrimeFibre N a).card : ℝ)) ≤
      (∑ a ∈ currentChenUpsilon8PrefixProducts N,
        ∑ q ∈ currentChenUpsilon9PrefixPrimeFibre N a,
          supportedDivisorSum (actualSmallRosserSupport N cap z)
            (actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ)) (N - a * q)) +
        ((currentChenUpsilon8PrefixProducts N).card : ℝ) * (Nat.ceil z : ℝ) := by
    have h := Finset.sum_le_sum (s := currentChenUpsilon8PrefixProducts N)
      (fun a ha => currentChenUpsilon9_switchedPrimeFibre_card_le_upperDivisorSum_add_cap
        N a cap (currentChenUpsilon8PrefixProducts_data ha).1 z
          ((panModulusCutoff N B + 1 : ℕ) : ℝ) hL hzL)
    simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] using h
  rw [currentChenUpsilon8_product_sum_upperDivisorSum,
    currentChenUpsilon8_upper_AP_sum_eq_main_errors B hN cap z] at hrows
  linarith only [hsource, hrows]

/-- The exact actual eighth product cardinal and the single receiver ceiling
have cost at most 2*N^(13/15). -/
theorem currentChenUpsilon8_small_prime_cost_le_power {N : ℕ} (hN : (1 : ℝ) ≤ N) :
    ((currentChenUpsilon8PrefixProducts N).card : ℝ) *
      (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)) : ℝ) ≤
        2 * (N : ℝ) ^ (13 / 15 : ℝ) := by
  have hNnat : 1 ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN
  have hcard : ((currentChenUpsilon8PrefixProducts N).card : ℝ) ≤
      (N : ℝ) ^ (2 / 3 : ℝ) :=
    (Nat.cast_le.mpr (currentChenUpsilon8_prefixProducts_card_le_panUpper hNnat)).trans
      (currentChenUpsilon8_panUpper_le_two_thirds hN)
  have hsmallOne : 1 ≤ (N : ℝ) ^ (1 / 5 : ℝ) := Real.one_le_rpow hN (by norm_num)
  have hsmallCeil : (Nat.ceil ((N : ℝ) ^ (1 / 5 : ℝ)) : ℝ) ≤
      2 * (N : ℝ) ^ (1 / 5 : ℝ) := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hNp.le (1 / 5 : ℝ))
    linarith only [h, hsmallOne]
  calc
    _ ≤ (N : ℝ) ^ (2 / 3 : ℝ) * (2 * (N : ℝ) ^ (1 / 5 : ℝ)) :=
      mul_le_mul hcard hsmallCeil (Nat.cast_nonneg _) (Real.rpow_nonneg hNp.le _)
    _ = _ := by
      rw [show (13 / 15 : ℝ) = 2 / 3 + 1 / 5 by norm_num, Real.rpow_add hNp]
      ring

private theorem eventually_currentChenUpsilon8_panLevel_sieveCutoff
    (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in atTop,
      1 < ((panModulusCutoff N B + 1 : ℕ) : ℝ) ∧
      (N : ℝ) ^ (1 / 5 : ℝ) ≤ ((panModulusCutoff N B + 1 : ℕ) : ℝ) ∧
      panModulusCutoff N B ≤ N := by
  filter_upwards [eventually_pan_conductor_bounds B hB,
    eventually_pan_log_rpow_le_rpow B (3 / 10) (by norm_num),
    eventually_ge_atTop (1 : ℕ)] with N hb hlogPower hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hNr
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hb.1
  have hden : 0 < Real.log (N : ℝ) ^ B := Real.rpow_pos_of_pos hlogpos _
  have hQ : 1 ≤ panModulusCutoff N B := hb.2.1.trans hb.2.2.1
  have hlevel : 1 < ((panModulusCutoff N B + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < panModulusCutoff N B + 1 by omega)
  have hcut : (N : ℝ) ^ (1 / 5 : ℝ) ≤
      (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ B := by
    apply (le_div_iff₀ hden).mpr
    calc
      _ ≤ (N : ℝ) ^ (1 / 5 : ℝ) * (N : ℝ) ^ (3 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hlogPower (Real.rpow_nonneg hNp.le _)
      _ = _ := by
        rw [← Real.rpow_add hNp, show (1 / 5 : ℝ) + 3 / 10 = 1 / 2 by norm_num]
  have hfloor : (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ B <
      ((panModulusCutoff N B + 1 : ℕ) : ℝ) := by
    simpa only [panModulusCutoff, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one ((N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ B)
  exact ⟨hlevel, hcut.trans hfloor.le, hb.2.2.2.2⟩

/-- Every actual error is paid before the cap is chosen; no main-term or distribution premise. -/
theorem exists_currentChenUpsilon8_le_switched_density_main :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ cap : ℕ,
        currentChenUpsilon8 N ≤
          currentChenUpsilon8LiMainMass N *
            currentChenUpsilon9SwitchedUpperDensity B N cap ((N : ℝ) ^ (1 / 5 : ℝ)) +
              ε * singularNormalization N := by
  obtain ⟨B, hB, hPan⟩ := exists_currentChenUpsilon8_panRosserError_budget
  refine ⟨B, hB, ?_⟩
  intro ε hε
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  filter_upwards [hPan δ hδ,
    eventually_currentChenUpsilon8_abs_coprimeGateError_le_singularNormalization δ hδ,
    eventually_powerLog_le_singularNormalization 2 (13 / 15) 0 (by norm_num) δ hδ,
    eventually_currentChenUpsilon8_sourceErrors_le_singularNormalization δ hδ,
    eventually_currentChenUpsilon8_panLevel_sieveCutoff B hB,
    eventually_ge_atTop (1 : ℕ)] with N hPanN hGateN hSmallN hSourceN hlevel hN
  intro cap
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let z : ℝ := (N : ℝ) ^ (1 / 5 : ℝ)
  let L : ℝ := ((panModulusCutoff N B + 1 : ℕ) : ℝ)
  let S := currentChenUpsilon9PanActive B N cap z
  have hS : S ⊆ Finset.Icc 1 N := by
    intro d hd
    have h := Finset.mem_Icc.mp (currentChenUpsilon9PanActive_subset B N cap z hd)
    exact Finset.mem_Icc.mpr ⟨h.1, h.2.trans hlevel.2.2⟩
  have hGate := hGateN cap z L S hS
  dsimp only [L, S] at hGate
  have hPanCost := hPanN cap z
  have hSmall : ((currentChenUpsilon8PrefixProducts N).card : ℝ) * (Nat.ceil z : ℝ) ≤
      δ * singularNormalization N := by
    apply (currentChenUpsilon8_small_prime_cost_le_power hNr).trans
    simpa only [pow_zero, mul_one] using hSmallN
  have hUnit : ((currentChenUpsilon8UnitFibres N).card : ℝ) ≤
      δ * singularNormalization N := by
    have hSmallNonneg : (0 : ℝ) ≤
        ((currentChenUpsilon8SmallGoldbachPrimeTriples N).card : ℝ) := Nat.cast_nonneg _
    linarith only [hSourceN, hSmallNonneg]
  have hfinite := currentChenUpsilon8_le_upper_density_main_add_errors B hNr cap z
    hlevel.1 hlevel.2.1
  have hPanHi := (abs_le.mp hPanCost).2
  have hGateLo := (abs_le.mp hGate).1
  have htotal : 4 * (δ * singularNormalization N) = ε * singularNormalization N := by
    dsimp [δ]
    ring
  change currentChenUpsilon8 N ≤
    currentChenUpsilon8LiMainMass N * currentChenUpsilon9SwitchedUpperDensity B N cap z +
      ε * singularNormalization N
  nlinarith only [hfinite, hPanHi, hGateLo, hSmall, hUnit, htotal]

end

end ImbalancedChen
