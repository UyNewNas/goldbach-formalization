import ImbalancedChen.P1OriginalFifthMiddleShellFiniteBudget
import ImbalancedChen.P1OriginalFifthMovingScaleLimit

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The middle-shell lower cutoff is the actual previously chosen movingCutoff,
omega/(16 loglog N). Its physical prime-box endpoint tends past two, and
its occupied-index Mertens error vanishes. These facts are established with
the moving cutoff inside every expression; no fixed-delta limit is reused.

The final theorem gives a genuine O(a) quadratic weighted-prime moment for
the whole original selected shell movingCutoff(omega,N)<=t5<a. The constant
precedes a, every target and every original policy/selected cell. Conversion
of the actual lower source difference to the quadratic kernel is separate.
-/

namespace ImbalancedChen.P1OriginalFifthMiddleShellMovingLimit

noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P1OriginalCoarseFifthContinuation
open P1OriginalFifthMovingScaleLimit
open P1OriginalFifthMiddleShellFiniteBudget

private theorem log_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem loglog_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (N:ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp log_nat_atTop

/-- The number of occupied reciprocal bins divided by log N tends to
zero at the actual moving cutoff, for each fixed positive upper cutoff. -/
theorem moving_index_error_tendsto_zero (omega a : ℝ) (homega : 0<omega) :
    Tendsto (fun N : ℕ => (a/movingCutoff omega N+1)/Real.log (N:ℝ))
      atTop (𝓝 0) := by
  have hlogratio : Tendsto (fun N : ℕ =>
      Real.log (Real.log (N:ℝ))/Real.log (N:ℝ)) atTop (𝓝 0) := by
    have hh : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact hh.comp log_nat_atTop
  have hh := (hlogratio.const_mul (16*a/omega)).add (log_nat_atTop.const_div_atTop 1)
  simp only [mul_zero,zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ),
    loglog_nat_atTop.eventually (eventually_ge_atTop 1)] with N hN hll
  have hlog : 0<Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hll0 : Real.log (Real.log (N:ℝ))≠0 := by linarith
  unfold movingCutoff
  field_simp [homega.ne',hlog.ne',hll0]
  <;> ring

/-- The exact weakest common physical endpoint used by the finite shell
budget is eventually at least two. -/
theorem eventually_moving_shell_endpoint (omega a : ℝ)
    (homega : 0<omega) (ha : 0<a) :
    ∀ᶠ N : ℕ in atTop,
      2≤(N:ℝ)^(a/(a/movingCutoff omega N+1)) := by
  have hlog2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have herr := (moving_index_error_tendsto_zero omega a homega).eventually
    (gt_mem_nhds (div_pos ha hlog2))
  filter_upwards [herr,eventually_moving_scale_budgets omega homega] with N he hb
  have hN : 1<N := by have := hb.1; omega
  have hlogN : 0<Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hd : 0<movingCutoff omega N := hb.2.1
  have hden : 0<a/movingCutoff omega N+1 := by positivity
  have hmul : Real.log 2*(a/movingCutoff omega N+1) ≤ a*Real.log (N:ℝ) := by
    have hh := (div_le_div_iff₀ hlogN hlog2).mp he.le
    nlinarith
  have hexp : Real.log 2≤(a/(a/movingCutoff omega N+1))*Real.log (N:ℝ) := by
    have hh := (le_div_iff₀ hden).mpr hmul
    convert hh using 1 <;> ring
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  calc
    (2:ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp ((a/(a/movingCutoff omega N+1))*Real.log (N:ℝ)) :=
      Real.exp_le_exp.mpr hexp
    _ = _ := by rw [Real.rpow_def_of_pos hn]; congr 1; ring

def scalarShellBudget (K omega a : ℝ) (N : ℕ) : ℝ :=
  4*a+(a/movingCutoff omega N+1)*(6*K/Real.log (N:ℝ))

/-- The complete finite-shell scalar budget has limit 4a. -/
theorem scalarShellBudget_tendsto (K omega a : ℝ) (homega : 0<omega) :
    Tendsto (scalarShellBudget K omega a) atTop (𝓝 (4*a)) := by
  have hh := (moving_index_error_tendsto_zero omega a homega).mul_const (6*K)
  have hh' : Tendsto (fun N : ℕ =>
      (a/movingCutoff omega N+1)*(6*K/Real.log (N:ℝ))) atTop (𝓝 0) := by
    convert hh using 1 <;> simp only [zero_mul]
    funext N
    ring
  simpa only [scalarShellBudget,add_zero] using hh'.const_add (4*a)

theorem eventually_scalarShellBudget_le_five_a (K omega a : ℝ)
    (homega : 0<omega) (ha : 0<a) :
    ∀ᶠ N : ℕ in atTop, scalarShellBudget K omega a N≤5*a := by
  have hh := (scalarShellBudget_tendsto K omega a homega).eventually
    (gt_mem_nhds (by linarith : 4*a<5*a))
  exact hh.mono (fun _ h => h.le)

/-- An actual arithmetic O(a) bound for the moving middle shell. The
constant is independent of the policy, selected label, target and cap.
Only the THREE fixed-positive prefix masses use their legitimate Mertens
limit; both last coordinates were treated by moving-interval estimates. -/
theorem exists_original_moving_middle_shell_quadratic_Oa
    (omega : ℝ) (homega : 0<omega) (homegaRho : omega<(19/96:ℝ)) :
    ∃ D : ℝ,0≤D ∧
      ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (a : ℝ),0<a → a≤(19/96:ℝ) →
      ∀ J5 : Finset (Label5 m),
      ∀ᶠ N : ℕ in evenTargets,∀ cap : ℕ,
      (N:ℝ)^(19/96:ℝ)≤(cap:ℝ) → ∀ (j : Label5 m),
      j∈selectedFifthCells e chi m omega J5 →
      shellMoment e chi m omega (movingCutoff omega N) a N cap j≤D*a := by
  obtain ⟨K,hK,hbound⟩ := exists_uniform_original_middle_shell_moment_bound
  let H : ℝ := Real.log ((19/96:ℝ)/omega)+1
  let C : ℝ := 2*((19/96:ℝ)*(1+K/Real.log 2))
  have hlog2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hH : 0<H := by
    have hh : 0<Real.log ((19/96:ℝ)/omega) :=
      Real.log_pos ((one_lt_div homega).mpr homegaRho)
    dsimp [H]
    linarith
  have hC : 0≤C := by
    have hK0 : 0≤K := by linarith
    dsimp [C]
    positivity
  refine ⟨5*H^3*C,by positivity,?_⟩
  intro e chi m a ha haRho J5
  have hprefix : ∀ᶠ N : ℕ in atTop,
      actualPrimeReciprocalMass N omega (19/96:ℝ)≤H := by
    have hh := (tendsto_actualPrimeReciprocalMass homega homegaRho).eventually
      (gt_mem_nhds (by dsimp [H]; linarith : Real.log ((19/96:ℝ)/omega)<H))
    exact hh.mono (fun _ h => h.le)
  filter_upwards [hprefix.filter_mono inf_le_left,
    (eventually_moving_shell_endpoint omega a homega ha).filter_mono inf_le_left,
    (eventually_scalarShellBudget_le_five_a K omega a homega ha).filter_mono inf_le_left,
    (eventually_moving_scale_budgets omega homega).filter_mono inf_le_left,
    (show ∀ᶠ N : ℕ in evenTargets,0<N ∧ Even N from
      (Filter.eventually_mem_principal _).filter_mono inf_le_right)]
    with N hpref hscale hbudget hlegal heven cap hcap j hj
  have hN : 1<N := by have := hlegal.1; omega
  have hM : 0≤actualPrimeReciprocalMass N omega (19/96:ℝ) := by
    unfold actualPrimeReciprocalMass
    apply Finset.sum_nonneg
    intro p hp
    have hp1 : (1:ℝ)<p := by exact_mod_cast (mem_roughPrimeFinset.mp hp).2.1.one_lt
    positivity
  have hB : 0≤scalarShellBudget K omega a N := by
    have hK0 : 0≤K := by linarith
    have hd : 0<movingCutoff omega N := hlegal.2.1
    have hlogN : 0<Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
    unfold scalarShellBudget
    positivity
  have hm := hbound e chi m omega (movingCutoff omega N) a hlegal.2.1 ha haRho
    J5 N cap hN heven.2 hcap j hj hscale
  calc
    _ ≤ (actualPrimeReciprocalMass N omega (19/96:ℝ))^3*C*
        scalarShellBudget K omega a N := hm
    _ ≤ H^3*C*scalarShellBudget K omega a N :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hM hpref 3) hC) hB
    _ ≤ H^3*C*(5*a) := mul_le_mul_of_nonneg_left hbudget (mul_nonneg (pow_nonneg hH.le 3) hC)
    _ = _ := by ring

end
end ImbalancedChen.P1OriginalFifthMiddleShellMovingLimit
