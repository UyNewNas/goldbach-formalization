import ImbalancedChen.ChenLogLevelGeometry
import ImbalancedChen.ChenQuotientSieveRemainders

/-!
# Literal quotient-row levels and uniform logarithmic geometry

The strict row level is Q / b + 1, using natural division. Its positive
inner divisors are exactly those with full product b*d <= Q. Uniformly
for positive b <= N^beta with beta < 1/2, the logarithmic parameter is
(1/2 - log b / log N)/a + o(1). All four original selectors lie in one
such fixed power range. No analytic distribution or lower-sieve estimate
is assumed. In particular the full sixth selector is not restricted to
the lower-positive region s >= 2.

Held source candidate: no Lean/Lake execution or verification is claimed.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open Classical

/-- Literal strict level for a row with full product cap Q. -/
def chenQuotientRowLevel (Q b : ℕ) : ℕ := Q / b + 1

/-- The strict row level at the actual logarithmic distribution cap. -/
def chenQuotientRosserD (B : ℝ) (N b : ℕ) : ℕ :=
  chenQuotientRowLevel (chenInitialLevelCap B N) b

/-- The actual row parameter at the original power sieve cutoff. -/
def chenQuotientRosserT (B a : ℝ) (N b : ℕ) : ℝ :=
  Real.log (chenQuotientRosserD B N b : ℝ) / Real.log ((N : ℝ) ^ a)

@[simp] theorem chenQuotientRowLevel_sub_one (Q b : ℕ) :
    chenQuotientRowLevel Q b - 1 = Q / b := by
  simp [chenQuotientRowLevel]

@[simp] theorem chenQuotientRowLevel_one (Q : ℕ) :
    chenQuotientRowLevel Q 1 = Q + 1 := by
  simp [chenQuotientRowLevel]

@[simp] theorem chenQuotientRowLevel_zero_cap (b : ℕ) :
    chenQuotientRowLevel 0 b = 1 := by
  simp [chenQuotientRowLevel]

/-- This exact equivalence needs positive b; b=0 is not silently admitted. -/
theorem lt_chenQuotientRowLevel_iff {Q b d : ℕ} (hb : 0 < b) :
    d < chenQuotientRowLevel Q b ↔ b * d ≤ Q := by
  unfold chenQuotientRowLevel
  rw [Nat.lt_succ_iff]
  simpa only [Nat.mul_comm] using
    (Nat.le_div_iff_mul_le hb : d ≤ Q / b ↔ d * b ≤ Q)

/-- Modulus one is in the strict row range exactly when b is within Q. -/
theorem one_lt_chenQuotientRowLevel_iff {Q b : ℕ} (hb : 0 < b) :
    1 < chenQuotientRowLevel Q b ↔ b ≤ Q := by
  simpa only [mul_one] using (lt_chenQuotientRowLevel_iff (Q := Q) (d := 1) hb)

/-- Divisor membership keeps the natural zero-modulus convention unchanged. -/
theorem chenQuotientRowLevel_divisor_filter (P Q b : ℕ) (hb : 0 < b) :
    P.divisors.filter (fun d => d < chenQuotientRowLevel Q b) =
      P.divisors.filter (fun d => b * d ≤ Q) := by
  ext d
  simp only [Finset.mem_filter, lt_chenQuotientRowLevel_iff hb]

/-- Integer rounding gives a uniform multiplicative factor-two sandwich. -/
theorem chenQuotientRowLevel_mul_bounds {Q b : ℕ}
    (hb : 0 < b) (hbQ : b ≤ Q + 1) :
    Q + 1 ≤ b * chenQuotientRowLevel Q b ∧
      b * chenQuotientRowLevel Q b ≤ 2 * (Q + 1) := by
  have hrem := Nat.mod_lt Q hb
  have hsplit := Nat.mod_add_div Q b
  have hpart := Nat.div_mul_le_self Q b
  unfold chenQuotientRowLevel
  constructor <;> nlinarith

/-- Exact logarithmic rounding control before any asymptotic statement. -/
theorem chenQuotientRowLevel_log_bounds {Q b : ℕ}
    (hb : 0 < b) (hbQ : b ≤ Q + 1) :
    Real.log ((Q + 1 : ℕ) : ℝ) ≤
        Real.log (b : ℝ) + Real.log (chenQuotientRowLevel Q b : ℝ) ∧
      Real.log (b : ℝ) + Real.log (chenQuotientRowLevel Q b : ℝ) ≤
        Real.log 2 + Real.log ((Q + 1 : ℕ) : ℝ) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hD : 0 < chenQuotientRowLevel Q b := by
    change 0 < Nat.succ (Q / b)
    exact Nat.succ_pos (Q / b)
  have hDR : (0 : ℝ) < chenQuotientRowLevel Q b := by exact_mod_cast hD
  have hQR : (0 : ℝ) < ((Q + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨hlo, hhi⟩ := chenQuotientRowLevel_mul_bounds hb hbQ
  have hloR : ((Q + 1 : ℕ) : ℝ) ≤
      (b : ℝ) * (chenQuotientRowLevel Q b : ℝ) := by exact_mod_cast hlo
  have hhiR : (b : ℝ) * (chenQuotientRowLevel Q b : ℝ) ≤
      2 * ((Q + 1 : ℕ) : ℝ) := by exact_mod_cast hhi
  have hl := Real.log_le_log hQR hloR
  have hu := Real.log_le_log (mul_pos hbR hDR) hhiR
  rw [Real.log_mul hbR.ne' hDR.ne'] at hl hu
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hQR.ne'] at hu
  exact ⟨hl, hu⟩

/-- The row-rounding loss is at most log 2 / log N, uniformly in b. -/
theorem chenQuotientRowLevel_log_ratio_error {N Q b : ℕ}
    (hN : 2 ≤ N) (hb : 0 < b) (hbQ : b ≤ Q + 1) :
    |Real.log (chenQuotientRowLevel Q b : ℝ) / Real.log (N : ℝ) +
      Real.log (b : ℝ) / Real.log (N : ℝ) -
      Real.log ((Q + 1 : ℕ) : ℝ) / Real.log (N : ℝ)| ≤
        Real.log 2 / Real.log (N : ℝ) := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  obtain ⟨hlo, hhi⟩ := chenQuotientRowLevel_log_bounds hb hbQ
  have hl := div_le_div_of_nonneg_right hlo hlog.le
  have hu := div_le_div_of_nonneg_right hhi hlog.le
  simp only [add_div] at hl hu
  have hround : 0 ≤ Real.log 2 / Real.log (N : ℝ) :=
    div_nonneg (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le hlog.le
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Every fixed power range strictly below the square-root exponent is
inside the actual cap eventually. The threshold is before the choice of b. -/
theorem eventually_powerBound_le_chenInitialLevelCap (B beta : ℝ)
    (hbeta : beta < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ, (b : ℝ) ≤ (N : ℝ) ^ beta →
      b ≤ chenInitialLevelCap B N := by
  have hlarge := (tendsto_log_chenInitialRosserD_div_log B).eventually
    (lt_mem_nhds hbeta)
  filter_upwards [hlarge, eventually_ge_atTop (2 : ℕ)] with N hratio hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := lt_trans zero_lt_one hN1
  have hlog := Real.log_pos hN1
  have hDpos : (0 : ℝ) < chenInitialRosserD B N := by
    unfold chenInitialRosserD
    positivity
  have hlogpow : Real.log ((N : ℝ) ^ beta) <
      Real.log (chenInitialRosserD B N : ℝ) := by
    rw [Real.log_rpow hNpos beta]
    exact (lt_div_iff₀ hlog).mp hratio
  have hpow : (N : ℝ) ^ beta < (chenInitialRosserD B N : ℝ) :=
    (Real.log_lt_log_iff (Real.rpow_pos_of_pos hNpos beta) hDpos).mp hlogpow
  intro b hb
  have hbD : b < chenInitialRosserD B N := by exact_mod_cast (hb.trans_lt hpow)
  unfold chenInitialRosserD at hbD
  omega

/-- Uniform moving-multiplier profile. No limit of b itself is assumed. -/
theorem eventually_chenQuotientRosserD_log_profile (B beta : ℝ)
    (hbeta : beta < 1 / 2) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ, 0 < b → (b : ℝ) ≤ (N : ℝ) ^ beta →
      b ≤ chenInitialLevelCap B N ∧
      |Real.log (chenQuotientRosserD B N b : ℝ) / Real.log (N : ℝ) -
        ((1 / 2 : ℝ) - Real.log (b : ℝ) / Real.log (N : ℝ))| < epsilon := by
  have hlogNat : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hround : ∀ᶠ N : ℕ in atTop,
      Real.log 2 / Real.log (N : ℝ) < epsilon / 2 :=
    (hlogNat.const_div_atTop (Real.log 2)).eventually
      (gt_mem_nhds (half_pos hepsilon))
  have hmain := Metric.tendsto_nhds.mp
    (tendsto_log_chenInitialRosserD_div_log B) (epsilon / 2) (half_pos hepsilon)
  filter_upwards [eventually_powerBound_le_chenInitialLevelCap B beta hbeta,
    hround, hmain, eventually_ge_atTop (2 : ℕ)] with N hcap hr hm hN
  intro b hb hbpower
  have hbQ := hcap b hbpower
  refine ⟨hbQ, ?_⟩
  have he := chenQuotientRowLevel_log_ratio_error hN hb (Nat.le_succ_of_le hbQ)
  have hm' : |Real.log (chenInitialRosserD B N : ℝ) / Real.log (N : ℝ) -
      (1 / 2 : ℝ)| < epsilon / 2 := by simpa only [Real.dist_eq] using hm
  change |Real.log (chenQuotientRosserD B N b : ℝ) / Real.log (N : ℝ) +
      Real.log (b : ℝ) / Real.log (N : ℝ) -
      Real.log (chenInitialRosserD B N : ℝ) / Real.log (N : ℝ)| ≤ _ at he
  calc
    _ = |(Real.log (chenQuotientRosserD B N b : ℝ) / Real.log (N : ℝ) +
          Real.log (b : ℝ) / Real.log (N : ℝ) -
          Real.log (chenInitialRosserD B N : ℝ) / Real.log (N : ℝ)) +
        (Real.log (chenInitialRosserD B N : ℝ) / Real.log (N : ℝ) - 1 / 2)| := by
          congr 1
          ring
    _ ≤ _ := abs_add_le _ _
    _ < epsilon := by linarith

/-- Uniform profile at any fixed positive power cutoff. -/
theorem eventually_chenQuotientRosserT_profile (B beta a : ℝ)
    (hbeta : beta < 1 / 2) (ha : 0 < a)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ, 0 < b → (b : ℝ) ≤ (N : ℝ) ^ beta →
      |chenQuotientRosserT B a N b -
        (((1 / 2 : ℝ) - Real.log (b : ℝ) / Real.log (N : ℝ)) / a)| < epsilon := by
  filter_upwards [eventually_chenQuotientRosserD_log_profile B beta hbeta
    (epsilon * a) (mul_pos hepsilon ha), eventually_ge_atTop (2 : ℕ)]
    with N hprofile hN
  intro b hb hbpower
  have h := (hprofile b hb hbpower).2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have heq : chenQuotientRosserT B a N b -
      (((1 / 2 : ℝ) - Real.log (b : ℝ) / Real.log (N : ℝ)) / a) =
      (Real.log (chenQuotientRosserD B N b : ℝ) / Real.log (N : ℝ) -
        ((1 / 2 : ℝ) - Real.log (b : ℝ) / Real.log (N : ℝ))) / a := by
    unfold chenQuotientRosserT
    rw [Real.log_rpow hNpos a]
    field_simp [ha.ne', hlog] <;> ring
  rw [heq, abs_div, abs_of_pos ha]
  exact (div_lt_iff₀ ha).mpr h

/-- A lower parameter gate needs a genuine fixed gap. In particular
sigma=2 is only justified when beta < 1/2 - 2*a. -/
theorem eventually_chenQuotientRosserT_gt (B beta a sigma : ℝ)
    (hbeta : beta < 1 / 2) (ha : 0 < a)
    (hgap : sigma < ((1 / 2 : ℝ) - beta) / a) :
    ∀ᶠ N : ℕ in atTop, ∀ b : ℕ, 0 < b → (b : ℝ) ≤ (N : ℝ) ^ beta →
      sigma < chenQuotientRosserT B a N b := by
  let eta : ℝ := (((1 / 2 : ℝ) - beta) / a - sigma) / 2
  have heta : 0 < eta := by dsimp [eta]; linarith
  filter_upwards [eventually_chenQuotientRosserT_profile B beta a hbeta ha eta heta,
    eventually_ge_atTop (2 : ℕ)] with N hprofile hN
  intro b hb hbpower
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hlogb := Real.log_le_log hbR hbpower
  rw [Real.log_rpow (lt_trans zero_lt_one hN1) beta] at hlogb
  have hu : Real.log (b : ℝ) / Real.log (N : ℝ) ≤ beta :=
    (div_le_iff₀ (Real.log_pos hN1)).mpr hlogb
  have hvalue : ((1 / 2 : ℝ) - beta) / a ≤
      ((1 / 2 : ℝ) - Real.log (b : ℝ) / Real.log (N : ℝ)) / a :=
    div_le_div_of_nonneg_right (by linarith) ha.le
  have h := (abs_lt.mp (hprofile b hb hbpower)).1
  dsimp [eta] at h
  linarith

/-- One fixed exponent bounds every literal selected multiplier. -/
def chenUpsilon36MultiplierExponent : ℝ :=
  50 / 309 + ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))

/-- All original selector bands fit the same strict square-root gap. -/
theorem chenUpsilon36_multipliers_le_power {N : ℕ} (hN : (1 : ℝ) ≤ N) :
    (∀ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)),
      (p : ℝ) ≤ (N : ℝ) ^ chenUpsilon36MultiplierExponent) ∧
    (∀ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
        ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))),
      (p : ℝ) ≤ (N : ℝ) ^ chenUpsilon36MultiplierExponent) ∧
    (∀ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
        ((N : ℝ) ^ (50 / 309 : ℝ)),
      ((t.1 * t.2 : ℕ) : ℝ) ≤ (N : ℝ) ^ chenUpsilon36MultiplierExponent) ∧
    (∀ t ∈ chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
        ((N : ℝ) ^ (50 / 309 : ℝ))
        ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))),
      ((t.1 * t.2 : ℕ) : ℝ) ≤ (N : ℝ) ^ chenUpsilon36MultiplierExponent) := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    have hupper := (Finset.mem_filter.mp hp).2.2
    exact hupper.le.trans (Real.rpow_le_rpow_of_exponent_le hN
      (by norm_num [chenUpsilon36MultiplierExponent]))
  · intro p hp
    have hupper := (Finset.mem_filter.mp hp).2.2
    exact hupper.le.trans (Real.rpow_le_rpow_of_exponent_le hN
      (by norm_num [chenUpsilon36MultiplierExponent]))
  · intro t ht
    obtain ⟨_, _, hlt, hupper⟩ := Finset.mem_filter.mp ht
    have hfirst : (t.1 : ℝ) ≤ (N : ℝ) ^ (50 / 309 : ℝ) :=
      (by exact_mod_cast hlt.le : (t.1 : ℝ) ≤ t.2).trans hupper.le
    calc
      ((t.1 * t.2 : ℕ) : ℝ) ≤
          (N : ℝ) ^ (50 / 309 : ℝ) * (N : ℝ) ^ (50 / 309 : ℝ) := by
        rw [Nat.cast_mul]
        exact mul_le_mul hfirst hupper.le (Nat.cast_nonneg _) (by positivity)
      _ = (N : ℝ) ^ ((50 / 309 : ℝ) + 50 / 309) := (Real.rpow_add hNpos _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN
        (by norm_num [chenUpsilon36MultiplierExponent])
  · intro t ht
    obtain ⟨_, _, hfirst, _, hsecond⟩ := Finset.mem_filter.mp ht
    calc
      ((t.1 * t.2 : ℕ) : ℝ) ≤
          (N : ℝ) ^ (50 / 309 : ℝ) *
            (N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)) := by
        rw [Nat.cast_mul]
        exact mul_le_mul hfirst.le hsecond.le (Nat.cast_nonneg _) (by positivity)
      _ = _ := (Real.rpow_add hNpos _ _).symm

/-- All selected multipliers are inside Q eventually, including the full
sixth band. The threshold does not depend on a selected label or weights. -/
theorem eventually_chenUpsilon36_multiplier_cap (B : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (∀ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)), p ≤ chenInitialLevelCap B N) ∧
      (∀ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
          ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))),
        p ≤ chenInitialLevelCap B N) ∧
      (∀ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
          ((N : ℝ) ^ (50 / 309 : ℝ)), t.1 * t.2 ≤ chenInitialLevelCap B N) ∧
      (∀ t ∈ chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
          ((N : ℝ) ^ (50 / 309 : ℝ))
          ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))),
        t.1 * t.2 ≤ chenInitialLevelCap B N) := by
  filter_upwards [eventually_powerBound_le_chenInitialLevelCap B
    chenUpsilon36MultiplierExponent (by norm_num [chenUpsilon36MultiplierExponent]),
    eventually_ge_atTop (1 : ℕ)] with N hcap hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨h₃, h₄, h₅, h₆⟩ := chenUpsilon36_multipliers_le_power hNR
  exact ⟨fun p hp => hcap p (h₃ p hp), fun p hp => hcap p (h₄ p hp),
    fun t ht => hcap (t.1 * t.2) (h₅ t ht),
    fun t ht => hcap (t.1 * t.2) (h₆ t ht)⟩

end

end ImbalancedChen
