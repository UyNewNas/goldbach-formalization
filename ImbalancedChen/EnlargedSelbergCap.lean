import ImbalancedChen.ActualSieveGate

/-!
# An enlarged Selberg level and its geometric cap

For a fixed real `theta` in `(2/5, 1/2)`, put
`L(N) = floor(N^(theta/2))` and use the strict sieve cap `z(N) = L(N) + 1`.
The square of the exact natural level is at most `floor(N^theta)`.
The literal logarithmic cutoff clears this cap eventually for every fixed
`b > 1/2`, including every rational exponent in the manuscript's interval.

The positive power gap between `theta/2` and `1/4` pays for the extra unit.
The existing three-quarter-power lower bound for `logCutoff` then supplies
the roughness gate. Both finite localization losses are negligible relative
to the genuine `singularNormalization`, so the original bad count is at
most the enlarged-cap sifted count plus any positive normalized error.

No prime-distribution estimate, Selberg-G asymptotic, replacement source,
or unproved growth hypothesis occurs in these results.
-/

namespace ImbalancedChen

open Filter Topology

noncomputable section

/-- Exact natural Selberg level at exponent `theta/2`. -/
def enlargedSelbergLevel (theta : ℝ) (N : ℕ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (theta / 2))

/-- The strict sieve cap immediately above the exact Selberg level. -/
def enlargedSelbergCap (theta : ℝ) (N : ℕ) : ℕ :=
  enlargedSelbergLevel theta N + 1

/-- The cap is strictly above the level, including at small arguments. -/
theorem enlargedSelbergLevel_lt_cap (theta : ℝ) (N : ℕ) :
    enlargedSelbergLevel theta N < enlargedSelbergCap theta N := by
  unfold enlargedSelbergCap
  omega

/-- Nonnegative exponents give a positive natural level as soon as `N ≥ 1`. -/
theorem one_le_enlargedSelbergLevel {theta : ℝ} (htheta : 0 ≤ theta)
    {N : ℕ} (hN : 1 ≤ N) : 1 ≤ enlargedSelbergLevel theta N := by
  unfold enlargedSelbergLevel
  apply (Nat.one_le_floor_iff _).mpr
  exact Real.one_le_rpow (by exact_mod_cast hN) (by linarith)

/-- Eventual positivity of the exact floor level. -/
theorem eventually_one_le_enlargedSelbergLevel {theta : ℝ} (htheta : 0 ≤ theta) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ enlargedSelbergLevel theta N := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact one_le_enlargedSelbergLevel htheta hN

/-- Squaring the floor cannot exceed the floor of the exact full power.
This finite statement holds for every real exponent and every natural `N`. -/
theorem enlargedSelbergLevel_sq_le_floor (theta : ℝ) (N : ℕ) :
    enlargedSelbergLevel theta N ^ 2 ≤ Nat.floor ((N : ℝ) ^ theta) := by
  have hroot : ((N : ℝ) ^ (theta / 2)) ^ (2 : ℕ) = (N : ℝ) ^ theta := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    norm_num <;> ring
  have hfloor : (enlargedSelbergLevel theta N : ℝ) ≤ (N : ℝ) ^ (theta / 2) :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) (theta / 2))
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (enlargedSelbergLevel theta N))
    hfloor 2
  rw [hroot] at hsq
  apply Nat.le_floor
  simpa only [Nat.cast_pow] using hsq

/-- Multiplicative form for the existing lambda-square truncation API. -/
theorem enlargedSelbergLevel_mul_self_le_floor (theta : ℝ) (N : ℕ) :
    enlargedSelbergLevel theta N * enlargedSelbergLevel theta N ≤
      Nat.floor ((N : ℝ) ^ theta) := by
  simpa only [pow_two] using enlargedSelbergLevel_sq_le_floor theta N

/-- A positive real-power gap absorbs the full floor-plus-one rounding cost. -/
theorem eventually_floor_rpow_add_one_le_rpow {alpha beta : ℝ}
    (halpha : 0 ≤ alpha) (hgap : alpha < beta) :
    ∀ᶠ N : ℕ in atTop,
      (Nat.floor ((N : ℝ) ^ alpha) : ℝ) + 1 ≤ (N : ℝ) ^ beta := by
  have hdecay : Tendsto (fun N : ℕ => 1 / (N : ℝ) ^ (beta - alpha))
      atTop (𝓝 0) := by
    simpa only [pow_zero] using
      tendsto_nat_log_pow_div_rpow 0 (sub_pos.mpr hgap)
  have hsmall : ∀ᶠ N : ℕ in atTop,
      1 / (N : ℝ) ^ (beta - alpha) < 1 / 2 :=
    hdecay.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with N hsmallN hN
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hNreal
  have htwo : (2 : ℝ) ≤ (N : ℝ) ^ (beta - alpha) := by
    have h := (div_lt_iff₀ (Real.rpow_pos_of_pos hNpos (beta - alpha))).mp hsmallN
    linarith
  have hone : (1 : ℝ) ≤ (N : ℝ) ^ alpha := Real.one_le_rpow hNreal halpha
  have hnonneg : (0 : ℝ) ≤ (N : ℝ) ^ alpha :=
    Real.rpow_nonneg (Nat.cast_nonneg N) alpha
  calc
    (Nat.floor ((N : ℝ) ^ alpha) : ℝ) + 1 ≤ (N : ℝ) ^ alpha + 1 :=
      add_le_add_right (Nat.floor_le hnonneg) 1
    _ ≤ (N : ℝ) ^ alpha * 2 := by linarith
    _ ≤ (N : ℝ) ^ alpha * (N : ℝ) ^ (beta - alpha) :=
      mul_le_mul_of_nonneg_left htwo hnonneg
    _ = (N : ℝ) ^ beta := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring

/-- The enlarged cap eventually lies below the quarter power. -/
theorem eventually_enlargedSelbergCap_le_quarterPower {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta : theta < 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      (enlargedSelbergCap theta N : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
  simpa only [enlargedSelbergCap, enlargedSelbergLevel, Nat.cast_add, Nat.cast_one]
    using eventually_floor_rpow_add_one_le_rpow
      (by linarith : 0 ≤ theta / 2) (by linarith : theta / 2 < (1 / 4 : ℝ))

/-- The logarithmic roughness gate for the enlarged cap. The upper restriction
`b < 1` is not needed for this geometric result. -/
theorem eventually_enlargedSelbergCap_sieve_gate {b theta : ℝ}
    (hb : 1 / 2 < b) (htheta0 : 0 ≤ theta) (htheta : theta < 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      0 < logCutoff N ∧
        (enlargedSelbergCap theta N : ℝ) ≤ (logCutoff N) ^ (b / (1 + b)) := by
  have hden : 0 < 1 + b := by linarith
  have halpha : (1 / 3 : ℝ) < b / (1 + b) := by
    apply (lt_div_iff₀ hden).mpr
    linarith
  have halphaNonneg : 0 ≤ b / (1 + b) := by linarith
  have hexponent : (1 / 4 : ℝ) ≤ (3 / 4 : ℝ) * (b / (1 + b)) := by
    linarith
  filter_upwards [eventually_threeQuarterPower_le_logCutoff,
    eventually_enlargedSelbergCap_le_quarterPower htheta0 htheta,
    eventually_ge_atTop (1 : ℕ)] with N hcut hcap hN
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  refine ⟨hcut.1, ?_⟩
  calc
    (enlargedSelbergCap theta N : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := hcap
    _ ≤ (N : ℝ) ^ ((3 / 4 : ℝ) * (b / (1 + b))) :=
      Real.rpow_le_rpow_of_exponent_le hNreal hexponent
    _ = ((N : ℝ) ^ (3 / 4 : ℝ)) ^ (b / (1 + b)) :=
      Real.rpow_mul (Nat.cast_nonneg N) (3 / 4 : ℝ) (b / (1 + b))
    _ ≤ (logCutoff N) ^ (b / (1 + b)) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) (3 / 4 : ℝ))
        hcut.2 halphaNonneg

/-- Rational-exponent version, with the exact integer strict half-threshold. -/
theorem eventually_enlargedSelbergCap_sieve_gate_rational (num den : ℕ)
    (hden : 0 < den) (hhalf : den < 2 * num) {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta : theta < 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      0 < logCutoff N ∧
        (enlargedSelbergCap theta N : ℝ) ≤
          (logCutoff N) ^ (((num : ℝ) / (den : ℝ)) /
            (1 + (num : ℝ) / (den : ℝ))) := by
  apply eventually_enlargedSelbergCap_sieve_gate _ htheta0 htheta
  have hdenR : (0 : ℝ) < (den : ℝ) := Nat.cast_pos.mpr hden
  have hhalfR : (den : ℝ) < 2 * (num : ℝ) := by exact_mod_cast hhalf
  apply (lt_div_iff₀ hdenR).mpr
  linarith

/-- The exact floor-plus-one cap has arbitrarily small normalized cost.
Only `theta < 2` is needed for this analytic error estimate. -/
theorem eventually_enlargedSelbergCap_le_singularNormalization
    {theta : ℝ} (htheta : theta < 2) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        (enlargedSelbergCap theta N : ℝ) ≤ epsilon * singularNormalization N := by
  simpa only [enlargedSelbergCap, enlargedSelbergLevel, Nat.cast_add, Nat.cast_one,
    one_mul, pow_zero, mul_one] using
    eventually_floor_powerLog_add_one_le_singularNormalization 1 (theta / 2) 0
      (by norm_num) (by linarith : theta / 2 < 1)

/-- Both explicit finite losses are negligible in the genuine normalization. -/
theorem eventually_enlargedSelbergCap_add_logCutoff_add_one_le
    {theta : ℝ} (htheta : theta < 2) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        (enlargedSelbergCap theta N : ℝ) + logCutoff N + 1 ≤
          epsilon * singularNormalization N := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_enlargedSelbergCap_le_singularNormalization htheta
      (epsilon / 2) (half_pos hepsilon),
      eventually_logCutoff_add_one_le_singularNormalization
        (epsilon / 2) (half_pos hepsilon)] with N hcap hcut
  linarith

/-- The actual prime-indexed bad count is bounded by the genuine sifted
source at the enlarged cap, with arbitrarily small normalized loss. -/
theorem eventually_B_cast_le_enlargedSelberg_sifted_add_error
    (num den : ℕ) {theta : ℝ} (htheta : theta < 2) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        (B num den N : ℝ) ≤
          (siftedHalfProductSource num den N (logCutoff N)
            (enlargedSelbergCap theta N)).card + epsilon * singularNormalization N := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_enlargedSelbergCap_add_logCutoff_add_one_le htheta epsilon hepsilon]
    with N herror
  have hfinite := B_cast_le_siftedHalfProductSource_card_add_cap_cutoff
    num den N (enlargedSelbergCap theta N) (logCutoff_nonneg N)
  linarith

/-- All geometric level and cap gates, together with the actual bad-count
comparison, in the requested fixed parameter range. Each error budget has
its own eventual threshold; neither distribution nor a `G` estimate is assumed. -/
theorem eventually_enlargedSelbergCap_data (num den : ℕ)
    (hden : 0 < den) (hhalf : den < 2 * num) (_hnumden : num < den)
    {theta : ℝ} (hthetaLower : 2 / 5 < theta) (hthetaUpper : theta < 1 / 2)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ enlargedSelbergLevel theta N ∧
      enlargedSelbergLevel theta N ^ 2 ≤ Nat.floor ((N : ℝ) ^ theta) ∧
      0 < logCutoff N ∧
      (enlargedSelbergCap theta N : ℝ) ≤
        (logCutoff N) ^ (((num : ℝ) / (den : ℝ)) /
          (1 + (num : ℝ) / (den : ℝ))) ∧
      (enlargedSelbergCap theta N : ℝ) + logCutoff N + 1 ≤
        epsilon * singularNormalization N ∧
      (B num den N : ℝ) ≤
        (siftedHalfProductSource num den N (logCutoff N)
          (enlargedSelbergCap theta N)).card + epsilon * singularNormalization N := by
  have htheta0 : 0 ≤ theta := by linarith
  have htheta2 : theta < 2 := by linarith
  filter_upwards [eventually_one_le_enlargedSelbergLevel htheta0,
    eventually_enlargedSelbergCap_sieve_gate_rational num den hden hhalf
      htheta0 hthetaUpper,
    eventually_enlargedSelbergCap_add_logCutoff_add_one_le htheta2 epsilon hepsilon,
    eventually_B_cast_le_enlargedSelberg_sifted_add_error num den htheta2 epsilon hepsilon]
    with N hlevel hgate herror hB
  exact ⟨hlevel, enlargedSelbergLevel_sq_le_floor theta N, hgate.1, hgate.2, herror, hB⟩

end

end ImbalancedChen
