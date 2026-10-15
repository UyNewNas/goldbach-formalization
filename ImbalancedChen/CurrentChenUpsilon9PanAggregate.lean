import ImbalancedChen.CurrentChenUpsilon9CoprimeGateBudget
import MathlibNt.SieveTheory.LiLiuPanBoundedAggregate
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanActualErrorEnvelope

/-!
# The bounded Pan aggregate on the actual ninth product coefficient

The AP count below is the literal sum of prime q with a*q <= N and
a*q congruent to the original N.  Its coefficient is the proved zero-one
image of the ninth selector.  The exact finite decomposition retains the
non-coprime li defect from `CurrentChenUpsilon9CoprimeGateBudget`.

The original product band proves both source-window hypotheses of the
pinned unconditional bounded-coefficient Pan theorem.  Its B is chosen
before N and before every enumeration cap and sieve cutoff.  The same
signed actual upper Rosser coefficient then receives an arbitrarily small
singular-normalization error budget.  No distribution premise is supplied
by the caller, and no adopted constant or ordinary factor eight is changed.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.LiuWeight

/-- The literal physical AP count on all prime quotients of the same
actual prefix-product image.  The product endpoint is closed. -/
def currentChenUpsilon9PrefixAPCount (N d : ℕ) : ℝ :=
  ∑ a ∈ currentChenUpsilon9PrefixProducts N, (primesInAPBelow N a d N : ℝ)

/-- The actual bounded-coefficient Pan error at the canonical residue of
the unchanged target.  The source coefficient has no modulus argument. -/
def currentChenUpsilon9PanError (N d : ℕ) : ℝ :=
  liuMainPanCoprimeIntervalSum (liuLogarithmicIntegral (2 / Real.log 2))
    N (currentChenUpsilon9PanLower N) (currentChenUpsilon9PanUpper N)
    d (N % d) (currentChenUpsilon9ProductCoefficient N)

private theorem currentChenUpsilon9_primesInAPBelow_target_mod (N a d : ℕ) :
    primesInAPBelow N a d (N % d) = primesInAPBelow N a d N := by
  unfold primesInAPBelow
  congr 1
  ext q
  simp only [Finset.mem_filter, Nat.ModEq, Nat.mod_mod]

/-- A non-coprime multiplier has no physical AP witness at a primitive
target residue.  This proves the gate rather than dropping it. -/
theorem currentChenUpsilon9_primesInAPBelow_eq_zero_of_not_coprime
    {N a d : ℕ} (hNd : Nat.Coprime N d) (had : ¬ Nat.Coprime a d) :
    (primesInAPBelow N a d N : ℝ) = 0 := by
  unfold primesInAPBelow
  rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q _ hq
  have hAP := hq.2.2
  have hprod : Nat.Coprime (a * q) d := by
    rw [Nat.Coprime, hAP.gcd_eq]
    exact hNd
  exact had (Nat.coprime_mul_iff_left.mp hprod).1

/-- This is the exact AP count, the full actual li main mass, its genuine
coprimality defect, and the actual Pan error with the same coefficient. -/
theorem currentChenUpsilon9_prefixAPCount_eq_main_sub_defect_add_error
    {N d : ℕ} (hN : (1 : ℝ) ≤ N) (hNd : Nat.Coprime N d) :
    currentChenUpsilon9PrefixAPCount N d =
      (currentChenUpsilon9LiMainMass N - currentChenUpsilon9CoprimeMainDefect N d) /
        (Nat.totient d : ℝ) + currentChenUpsilon9PanError N d := by
  have herror : currentChenUpsilon9PanError N d =
      ∑ a ∈ currentChenUpsilon9PrefixProducts N,
        if Nat.Coprime a d then
          liuScaledAPError (liuLogarithmicIntegral (2 / Real.log 2)) N a d (N % d)
        else 0 := by
    unfold currentChenUpsilon9PanError liuMainPanCoprimeIntervalSum
    calc
      _ = ∑ a ∈ Finset.Ioc (currentChenUpsilon9PanLower N) (currentChenUpsilon9PanUpper N),
          currentChenUpsilon9ProductCoefficient N a *
            (if Nat.Coprime a d then
              liuScaledAPError (liuLogarithmicIntegral (2 / Real.log 2)) N a d (N % d)
            else 0) := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases hc : Nat.Coprime a d <;> simp only [hc, if_true, if_false, mul_zero]
      _ = _ := currentChenUpsilon9ProductCoefficient_sum hN _
  have hpoint : ∀ a ∈ currentChenUpsilon9PrefixProducts N,
      (if Nat.Coprime a d then
        liuScaledAPError (liuLogarithmicIntegral (2 / Real.log 2)) N a d (N % d)
      else 0) = (primesInAPBelow N a d N : ℝ) -
        (liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (a : ℝ)) -
          (if Nat.Coprime a d then 0 else
            liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (a : ℝ)))) /
              (Nat.totient d : ℝ) := by
    intro a _
    by_cases hc : Nat.Coprime a d
    · simp only [hc, if_true, sub_zero, liuScaledAPError,
        currentChenUpsilon9_primesInAPBelow_target_mod]
    · simp only [hc, if_false, sub_self, zero_div, sub_zero]
      exact (currentChenUpsilon9_primesInAPBelow_eq_zero_of_not_coprime hNd hc).symm
  have hidentity : currentChenUpsilon9PanError N d =
      currentChenUpsilon9PrefixAPCount N d -
        (currentChenUpsilon9LiMainMass N - currentChenUpsilon9CoprimeMainDefect N d) /
          (Nat.totient d : ℝ) := by
    rw [herror]
    calc
      _ = ∑ a ∈ currentChenUpsilon9PrefixProducts N,
          (primesInAPBelow N a d N : ℝ) -
            (liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (a : ℝ)) -
              (if Nat.Coprime a d then 0 else
                liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (a : ℝ)))) /
                  (Nat.totient d : ℝ) := Finset.sum_congr rfl hpoint
      _ = _ := by
        simp only [currentChenUpsilon9PrefixAPCount, currentChenUpsilon9LiMainMass,
          currentChenUpsilon9CoprimeMainDefect, Finset.sum_sub_distrib, Finset.sum_div, sub_div]
  linarith only [hidentity]

/-- The upper end of the actual product window lies below N^(2/3), as
required by the bounded aggregate; no historical 9/19 band is used. -/
theorem currentChenUpsilon9_panUpper_le_two_thirds {N : ℕ} (hN : (1 : ℝ) ≤ N) :
    (currentChenUpsilon9PanUpper N : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN
  have hu : 0 < (N : ℝ) ^ (309 / 500 : ℝ) := Real.rpow_pos_of_pos hNp _
  have hceil : 1 ≤ Nat.ceil ((N : ℝ) ^ (309 / 500 : ℝ)) := Nat.one_le_ceil_iff.mpr hu
  have hupper : (currentChenUpsilon9PanUpper N : ℝ) < (N : ℝ) ^ (309 / 500 : ℝ) := by
    unfold currentChenUpsilon9PanUpper
    rw [Nat.cast_sub hceil, Nat.cast_one]
    have h := Nat.ceil_lt_add_one hu.le
    linarith
  exact hupper.le.trans (Real.rpow_le_rpow_of_exponent_le hN (by norm_num))

/-- Every fixed B precedes the actual source interval.  Power growth of
the actual lower product endpoint pays its logarithmic lower gate. -/
theorem eventually_currentChenUpsilon9_panLower_log_gate (B : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ (2 * B) ≤ (currentChenUpsilon9PanLower N : ℝ) := by
  have hreal : ∀ᶠ x : ℝ in atTop,
      Real.log x ^ (2 * B) ≤ (1 / 2 : ℝ) * x ^ (97 / 250 : ℝ) := by
    have hb := (isLittleO_log_rpow_rpow_atTop (2 * B)
      (by norm_num : (0 : ℝ) < 97 / 250)).bound (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx1) _)] at hx
    exact hx
  have hlarge : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (97 / 250 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 97 / 250)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hreal, hlarge] with N hlog hlarge
  have hceil : 1 ≤ Nat.ceil ((N : ℝ) ^ (97 / 250 : ℝ)) :=
    Nat.one_le_ceil_iff.mpr (by linarith)
  have hbound : (1 / 2 : ℝ) * (N : ℝ) ^ (97 / 250 : ℝ) ≤
      (currentChenUpsilon9PanLower N : ℝ) := by
    unfold currentChenUpsilon9PanLower
    rw [Nat.cast_sub hceil, Nat.cast_one]
    have h := Nat.le_ceil ((N : ℝ) ^ (97 / 250 : ℝ))
    linarith
  exact hlog.trans hbound

/-- The actual divisor set retained by the strict upper Rosser level
Q+1, where Q is the single bounded-Pan modulus cutoff. -/
def currentChenUpsilon9PanActive (B : ℝ) (N cap : ℕ) (z : ℝ) : Finset ℕ :=
  (actualSmallRosserSupport N cap z).filter (fun d => d ≤ panModulusCutoff N B)

def currentChenUpsilon9PanRosserError (B : ℝ) (N cap : ℕ) (z : ℝ) : ℝ :=
  ∑ d ∈ actualSmallRosserSupport N cap z,
    actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d *
      currentChenUpsilon9PanError N d

/-- The actual strict level Q+1 pays the entire omitted support.  The
modulus truncation in the aggregate is therefore an exact equality. -/
theorem currentChenUpsilon9PanRosserError_eq_active (B : ℝ) (N cap : ℕ) (z : ℝ) :
    currentChenUpsilon9PanRosserError B N cap z =
      ∑ d ∈ currentChenUpsilon9PanActive B N cap z,
        actualSmallRosserPlus N cap z ((panModulusCutoff N B + 1 : ℕ) : ℝ) d *
          currentChenUpsilon9PanError N d := by
  unfold currentChenUpsilon9PanRosserError currentChenUpsilon9PanActive
  rw [Finset.sum_filter]
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

theorem currentChenUpsilon9PanActive_subset (B : ℝ) (N cap : ℕ) (z : ℝ) :
    currentChenUpsilon9PanActive B N cap z ⊆ Finset.Icc 1 (panModulusCutoff N B) := by
  intro d hd
  obtain ⟨hds, hcap⟩ := Finset.mem_filter.mp hd
  exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hds, hcap⟩

private theorem currentChenUpsilon9_abs_panError_le_MaxL {N d : ℕ}
    (hd : 0 < d) (hNd : Nat.Coprime N d) :
    |currentChenUpsilon9PanError N d| ≤
      liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
        N (currentChenUpsilon9PanLower N) (currentChenUpsilon9PanUpper N) d
        (currentChenUpsilon9ProductCoefficient N) := by
  have hres : N % d ∈ unitResidues d := by
    change N % d ∈ finiteReducedResidues d
    exact (mod_mem_finiteReducedResidues_iff N d hd).mpr hNd
  have hnonempty : (unitResidues d).Nonempty := ⟨N % d, hres⟩
  unfold liuMainPanCoprimeIntervalMaxL
  dsimp only
  rw [dif_pos hnonempty]
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨N % d, hres, rfl⟩)

/-- The actual signed error is bounded by the full residue-maximum sum
without multiplying by the number of selected moduli or factor labels. -/
theorem currentChenUpsilon9_abs_panRosserError_le_MaxL_sum
    (B : ℝ) (N cap : ℕ) (z : ℝ) :
    |currentChenUpsilon9PanRosserError B N cap z| ≤
      ∑ d ∈ Finset.Icc 1 (panModulusCutoff N B),
        liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
          N (currentChenUpsilon9PanLower N) (currentChenUpsilon9PanUpper N) d
          (currentChenUpsilon9ProductCoefficient N) := by
  have hpoint : |currentChenUpsilon9PanRosserError B N cap z| ≤
      ∑ d ∈ currentChenUpsilon9PanActive B N cap z,
        liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
          N (currentChenUpsilon9PanLower N) (currentChenUpsilon9PanUpper N) d
          (currentChenUpsilon9ProductCoefficient N) := by
    rw [currentChenUpsilon9PanRosserError_eq_active]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro d hd
    have hds := (Finset.mem_filter.mp hd).1
    have hdp := Nat.pos_of_mem_divisors hds
    have hNd := (actualSmallRosserSupport_coprime_target N cap z hds).symm
    rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _)
      (actualSmallRosserPlus_abs_le_one N cap z _ d)).trans
        (currentChenUpsilon9_abs_panError_le_MaxL hdp hNd)
  apply hpoint.trans
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (currentChenUpsilon9PanActive_subset B N cap z)
    (fun d _ _ => liuMainPanCoprimeIntervalMaxL_nonneg _ _ _ _ _ _)

/-- A proved Pan exponent B, chosen before epsilon, N, the actual
coefficient and every sieve cap, pays this literal signed source error. -/
theorem exists_currentChenUpsilon9_panRosserError_budget :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, ∀ cap : ℕ, ∀ z : ℝ,
        |currentChenUpsilon9PanRosserError B N cap z| ≤
          ε * singularNormalization N := by
  obtain ⟨C, _hC, B, hB, N₀, hagg⟩ :=
    liuMainPanCoprimeIntervalMaxL_boundedAggregate_log_saving 3 (by norm_num)
  refine ⟨B, hB, ?_⟩
  intro ε hε
  have hlarge : ∀ᶠ N : ℕ in atTop,
      C / (ε * twinPrimeConstant) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop _)
  have hlog : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_currentChenUpsilon9_panLower_log_gate B,
    eventually_ge_atTop N₀, eventually_ge_atTop (1 : ℕ), hlarge, hlog]
    with N hlower hN₀ hN hlarge hlog
  intro cap z
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hdist := hagg N hN₀ (currentChenUpsilon9PanLower N) (currentChenUpsilon9PanUpper N)
    (currentChenUpsilon9ProductCoefficient N)
    (currentChenUpsilon9_panUpper_le_two_thirds hNr) hlower
    (abs_currentChenUpsilon9ProductCoefficient_le_one N)
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
  exact ((currentChenUpsilon9_abs_panRosserError_le_MaxL_sum B N cap z).trans hdist).trans hpaid

end

end ImbalancedChen
