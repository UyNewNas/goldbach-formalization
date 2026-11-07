import ImbalancedChen.P1OriginalFifthMovingHarmonicEnvelope
import ImbalancedChen.PowerErrorBudget

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Concrete moving scales and a proved zero limit for the literal original
fifth smallRemainder at a(N)=omega/(16 log log N). No remainder, density
limit, prime-distribution estimate, or normalization bound is assumed.
The positive singular-series lower constant is the actual infinite product.
This does not control the middle shells between a(N) and a fixed cutoff.
-/

namespace ImbalancedChen.P1OriginalFifthMovingScaleLimit

noncomputable section

open Filter Topology
open scoped Classical BigOperators
open P1OriginalCoarseFifthContinuation
open HistoricalThirdCoarse.P1OriginalCoarseFifth
open P1OriginalFifthMovingHarmonicEnvelope

def movingBudget (N : ℕ) : ℝ := 8 * Real.log (Real.log (N : ℝ))

def movingCutoff (omega : ℝ) (N : ℕ) : ℝ :=
  omega / (16 * Real.log (Real.log (N : ℝ)))

abbrev evenTargets : Filter ℕ :=
  atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}

private theorem tendsto_log_nat :
    Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem tendsto_loglog_nat :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_log_nat

/-- The existing finite fourth checker supplies the inherited-cap
compatibility automatically, including the unselected fallback branch. -/
theorem old5_ge_original_third_of_h34Check
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (hcheck : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (j : Label5 m) :
    HistoricalThirdCoarse.levelExponent (e : ℝ)
      (HistoricalThirdCoarse.box m (thirdOwner j)) ≤ (old5 e chi m omega J4 cap4 j : ℝ) := by
  have hthird : (P1OriginalCoarseContinuation.thirdCellExponent e m
      (historicalPrefixProject (by omega : 4 ≤ 5) j) : ℝ) =
      HistoricalThirdCoarse.levelExponent (e : ℝ)
        (HistoricalThirdCoarse.box m (thirdOwner j)) := by
    rw [P1OriginalCoarseContinuation.cast_thirdCellExponent]
    simp only [historicalPrefixProject_comp, thirdOwner]
  unfold old5
  dsimp only
  split_ifs with hsel
  · have hc := P1OriginalCoarseContinuation.h34Check_sound
      e chi m omega J4 cap4 hcheck _ hsel
    have hr : (P1OriginalCoarseContinuation.thirdCellExponent e m
        (historicalPrefixProject (by omega : 4 ≤ 5) j) : ℝ) ≤
        (cap4 (historicalPrefixProject (by omega : 4 ≤ 5) j) : ℝ) := by
      exact_mod_cast hc
    simpa only [hthird] using hr
  · exact hthird.symm.le

/-- The moving cutoff genuinely decreases to zero for every fixed omega. -/
theorem movingCutoff_tendsto_zero (omega : ℝ) :
    Tendsto (movingCutoff omega) atTop (𝓝 0) := by
  exact (tendsto_loglog_nat.const_mul_atTop
    (by norm_num : (0 : ℝ) < 16)).const_div_atTop omega

/-- All source-budget inequalities are established from logarithmic growth.
They are uniform in the enumeration cap and do not mention prime tuples. -/
theorem eventually_moving_scale_budgets (omega : ℝ) (homega : 0 < omega) :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧ 0 < movingCutoff omega N ∧ movingCutoff omega N ≤ omega / 6 ∧
      2 ≤ movingBudget N ∧ movingCutoff omega N * movingBudget N ≤ omega / 2 ∧
      (movingBudget N) ^ 13 ≤ (omega / 2) * Real.log (N : ℝ) ∧
      Real.exp 1 ≤ (omega / 2) * Real.log (N : ℝ) := by
  have hp : Tendsto (fun x : ℝ => (8 * Real.log x) ^ 13 / x)
      atTop (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => (Real.log x) ^ 13 / x)
        atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 13 one_ne_zero
    convert h.const_mul ((8 : ℝ) ^ 13) using 1 <;> simp only [mul_zero]
    funext x
    ring
  have hpower := (hp.comp tendsto_log_nat).eventually
    (gt_mem_nhds (half_pos homega))
  have hlog := (tendsto_log_nat.const_mul_atTop (half_pos homega)).eventually
    (eventually_ge_atTop (Real.exp 1))
  filter_upwards [eventually_ge_atTop (2 : ℕ), hpower, hlog,
    tendsto_loglog_nat.eventually (eventually_ge_atTop 1)] with N hN hpN hlN hllN
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hll : 0 < Real.log (Real.log (N : ℝ)) := by linarith
  have hprod : movingCutoff omega N * movingBudget N = omega / 2 := by
    unfold movingCutoff movingBudget
    field_simp [hll.ne']
    <;> ring
  refine ⟨hN, div_pos homega (by positivity), ?_, ?_, hprod.le, ?_, hlN⟩
  · unfold movingCutoff
    apply (div_le_iff₀ (by positivity : 0 < 16 * Real.log (Real.log (N : ℝ)))).mpr
    have hm := mul_le_mul_of_nonneg_left hllN homega.le
    nlinarith
  · unfold movingBudget
    linarith
  · exact ((div_lt_iff₀ hlogN).mp hpN).le

def harmonicFactor (N : ℕ) : ℝ :=
  2 * (1 + Real.log (Nat.ceil ((N : ℝ) ^ (19 / 96 : ℝ)) : ℝ))

def normalizedMovingMajorant (N : ℕ) : ℝ :=
  |Real.log (N : ℝ) / singularSeries N| * (harmonicFactor N) ^ 5 *
    Real.exp (-movingBudget N)

/-- The physical ceiling has only a logarithmic loss. This is a finite
inequality, obtained from ceil(N^rho)<=N^2, not from prime asymptotics. -/
theorem harmonicFactor_bounds (N : ℕ) (hN : 2 ≤ N)
    (hlog : 1 ≤ Real.log (N : ℝ)) :
    0 ≤ harmonicFactor N ∧ harmonicFactor N ≤ 6 * Real.log (N : ℝ) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hn (by norm_num : (19 / 96 : ℝ) ≤ 1)
  have hceil1 : (1 : ℝ) ≤ (Nat.ceil ((N : ℝ) ^ (19 / 96 : ℝ)) : ℝ) :=
    (Real.one_le_rpow hn (by norm_num : (0 : ℝ) ≤ 19 / 96)).trans (Nat.le_ceil _)
  have hceil : (Nat.ceil ((N : ℝ) ^ (19 / 96 : ℝ)) : ℝ) ≤ (N : ℝ) ^ 2 := by
    have hc := (Nat.ceil_lt_add_one
      (Real.rpow_nonneg (Nat.cast_nonneg N) (19 / 96 : ℝ))).le
    have hNsq : (N : ℝ) + 1 ≤ (N : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((N : ℝ) - 2)]
    exact hc.trans ((add_le_add_right hpow 1).trans hNsq)
  have hceilLog : Real.log (Nat.ceil ((N : ℝ) ^ (19 / 96 : ℝ)) : ℝ) ≤
      2 * Real.log (N : ℝ) := by
    have hh := Real.log_le_log (lt_of_lt_of_le zero_lt_one hceil1) hceil
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  unfold harmonicFactor
  constructor
  · have hc0 := Real.log_nonneg hceil1
    positivity
  · linarith

/-- Exact suppression paid by the chosen moving source parameter. -/
theorem exp_neg_movingBudget (N : ℕ) (hlog : 0 < Real.log (N : ℝ)) :
    Real.exp (-movingBudget N) = 1 / (Real.log (N : ℝ)) ^ 8 := by
  simp only [movingBudget, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hlog, one_div]

/-- The actual singular series is bounded below by twinPrimeConstant>0.
Together with five harmonic losses, exp(-8 loglogN) leaves log(N)^(-2). -/
theorem eventually_normalizedMovingMajorant_le :
    ∀ᶠ N : ℕ in atTop,
      normalizedMovingMajorant N ≤
        ((6 : ℝ) ^ 5 / twinPrimeConstant) / (Real.log (N : ℝ)) ^ 2 := by
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    tendsto_log_nat.eventually (eventually_ge_atTop 1)] with N hN hlog1
  have hlog : 0 < Real.log (N : ℝ) := by linarith
  obtain ⟨hH0, hH⟩ := harmonicFactor_bounds N hN hlog1
  have hscale : |Real.log (N : ℝ) / singularSeries N| ≤
      Real.log (N : ℝ) / twinPrimeConstant := by
    rw [abs_of_nonneg (div_nonneg hlog.le (singularSeries_pos N).le)]
    exact div_le_div_of_nonneg_left hlog.le twinPrimeConstant_pos
      (twinPrimeConstant_le_singularSeries N)
  unfold normalizedMovingMajorant
  calc
    _ ≤ (Real.log (N : ℝ) / twinPrimeConstant) *
        (6 * Real.log (N : ℝ)) ^ 5 * Real.exp (-movingBudget N) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul hscale (pow_le_pow_left₀ hH0 hH 5)
        (pow_nonneg hH0 5) (div_nonneg hlog.le twinPrimeConstant_pos.le)
    _ = _ := by
      rw [exp_neg_movingBudget N hlog]
      field_simp [hlog.ne', twinPrimeConstant_pos.ne']
      <;> ring

/-- Unconditional decay of the actual normalization times the harmonic
prime-tuple ceiling and the complete moving exponential source factor. -/
theorem normalizedMovingMajorant_tendsto_zero :
    Tendsto normalizedMovingMajorant atTop (𝓝 0) := by
  have hpow : Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (n := 2) (by norm_num)).comp tendsto_log_nat
  have hupper := hpow.const_div_atTop ((6 : ℝ) ^ 5 / twinPrimeConstant)
  apply squeeze_zero' ?_ eventually_normalizedMovingMajorant_le hupper
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    tendsto_log_nat.eventually (eventually_ge_atTop 1)] with N hN hlog
  have hH := (harmonicFactor_bounds N hN hlog).1
  unfold normalizedMovingMajorant
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hH 5)) (Real.exp_pos _).le

/-- The literal original arithmetic remainder vanishes at the explicit
moving cutoff along even targets, uniformly for every covering cap function.
Only finite original cap-compatibility checks remain as geometric inputs.
No middle-shell or fixed-a interchange is asserted. -/
theorem original_smallRemainder_movingCutoff_tendsto_zero
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (homega : 0 < omega)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (h34 : ∀ j ∈ selectedFifthCells e chi m omega J5,
      HistoricalThirdCoarse.levelExponent (e : ℝ)
        (HistoricalThirdCoarse.box m (thirdOwner j)) ≤ (old5 e chi m omega J4 cap4 j : ℝ))
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => P1OriginalFifthLimit.smallRemainder e chi m omega
      (movingCutoff omega N) J4 cap4 J5 cap5 N (cap N)) evenTargets (𝓝 0) := by
  obtain ⟨A, B, K, hA, hB, _hK, hbound⟩ :=
    exists_original_smallRemainder_moving_exp_harmonic_bound
  let D : ℝ := 2 * (A + B * Real.exp (Real.sqrt K)) *
    ((selectedFifthCells e chi m omega J5).card : ℝ)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hmajor : Tendsto (fun N : ℕ => D * normalizedMovingMajorant N)
      evenTargets (𝓝 0) := by
    simpa only [mul_zero] using
      (normalizedMovingMajorant_tendsto_zero.const_mul D).mono_left inf_le_left
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_ hmajor
  filter_upwards [(eventually_moving_scale_budgets omega homega).filter_mono inf_le_left,
    hcap, (show ∀ᶠ N : ℕ in evenTargets, 0 < N ∧ Even N from
      (Filter.eventually_mem_principal _).filter_mono inf_le_right)] with N hb hc he
  obtain ⟨hN, _ha0, ha, hT, haT, hbudget, hlog⟩ := hb
  have hh := hbound e chi m omega (movingCutoff omega N) (movingBudget N)
    homega ha hT haT J4 cap4 J5 cap5 h45 h34 N (cap N) (by omega) he.2 hc hbudget hlog
  calc
    _ ≤ _ := hh
    _ = D * normalizedMovingMajorant N := by
      dsimp [D, normalizedMovingMajorant, harmonicFactor]
      ring

/-- The moving original fifth tail requires only the literal h34/h45
finite checkers, not an independently supplied inherited-level inequality. -/
theorem original_smallRemainder_movingCutoff_tendsto_zero_of_checks
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ) (homega : 0 < omega)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (h34 : P1OriginalCoarseContinuation.h34Check e chi m omega J4 cap4 = true)
    (h45 : h45Check e chi m omega J4 cap4 J5 cap5 = true)
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => P1OriginalFifthLimit.smallRemainder e chi m omega
      (movingCutoff omega N) J4 cap4 J5 cap5 N (cap N)) evenTargets (𝓝 0) := by
  apply original_smallRemainder_movingCutoff_tendsto_zero
    e chi m omega homega J4 cap4 J5 cap5 h45 _ cap hcap
  intro j _hj
  exact old5_ge_original_third_of_h34Check e chi m omega J4 cap4 h34 j

end

end ImbalancedChen.P1OriginalFifthMovingScaleLimit
