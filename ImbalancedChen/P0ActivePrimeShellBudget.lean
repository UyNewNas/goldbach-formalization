import ImbalancedChen.ActualHistoricalThirdTupleDictionary
import ImbalancedChen.P1OriginalFourthMovingPrimeIntervalBound

/-!
Quantitative mass of the original retained active third-prime shell.
The source finset retains the original firstStop and both raw-Q3 cube tests;
only its third prime is restricted to [N^omega,N^(omega+delta)).
The absolute interval constant is extracted from the existing proved finite
prime interval theorem. No shell-mass, density or final coefficient bound is
an input. SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P0ActivePrimeShellBudget

noncomputable section
open scoped Classical BigOperators
open Filter Topology
open HistoricalThirdCoarse
open HistoricalThirdCoarse.P1ActualTuple
open P1OriginalFourthMovingPrimeIntervalBound

local notation "ρ" => (19 / 96 : ℝ)

/-- The actual original active retained carrier, with one additional strict
upper face on the third prime. The active lower face remains inclusive. -/
def shellTuples (e chi : ℝ) (m : ℕ) (omega delta : ℝ) (N cap : ℕ) :
    Finset (Fin 3 → ℕ) :=
  (activeRetainedTuples e chi m omega N cap ((N : ℝ) ^ ρ)).filter
    (fun p => (p 2 : ℝ) < (N : ℝ) ^ (omega + delta))

def shellMass (e chi : ℝ) (m : ℕ) (omega delta : ℝ) (N cap : ℕ) : ℝ :=
  ∑ p ∈ shellTuples e chi m omega delta N cap,
    ∏ i, 1 / ((p i : ℝ) - 1)

/-- Every coordinate is above the original active third cutoff, because
processing order is strictly decreasing. No cell selection is substituted. -/
theorem shellTuples_subset_box (e chi : ℝ) (m : ℕ) (omega delta : ℝ)
    (N cap : ℕ) :
    shellTuples e chi m omega delta N cap ⊆
      actualPrimeBoxTuples N (fun _ : Fin 3 => omega)
        (fun i => if i = 2 then omega + delta else ρ) := by
  intro p hp
  obtain ⟨hp, hupper⟩ := Finset.mem_filter.mp hp
  obtain ⟨hret, hactive⟩ := Finset.mem_filter.mp hp
  have hfront := (Finset.mem_filter.mp hret).1
  have hd := (mem_firstExitFrontierTuples_iff_of_decreasing 2
    (policy e chi m omega (N : ℝ))
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ ρ))
    (roughPrimeUniverse_pairwise_gt N cap 0 ((N : ℝ) ^ ρ)) p).mp hfront
  have hlower : (N : ℝ) ^ omega ≤ (p 2 : ℝ) :=
    (active_triple omega (N : ℝ) (p 0) (p 1) (p 2)).mp hactive
  apply mem_actualPrimeBoxTuples_iff.mpr
  intro i
  have hi := mem_roughPrimeUniverse.mp (hd.2.1 i)
  have hlast : p 2 ≤ p i := hd.1.antitone (show i ≤ (2 : Fin 3) by omega)
  refine ⟨hi.2.1, hi.2.2.1, hlower.trans (by exact_mod_cast hlast), ?_⟩
  by_cases hi2 : i = 2
  · simpa only [hi2, if_pos rfl] using hupper
  · simpa only [if_neg hi2] using hi.2.2.2.2

/-- Finite shell domination with the actual target-deleted interval sums.
All original admission tests remain on the left. -/
theorem shellMass_le_interval_product (e chi : ℝ) (m : ℕ)
    (omega delta : ℝ) (N cap : ℕ) :
    shellMass e chi m omega delta N cap ≤
      (actualPrimeReciprocalMass N omega ρ) ^ 2 *
        actualPrimeReciprocalMass N omega (omega + delta) := by
  calc
    _ ≤ actualPrimeBoxMass N (fun _ : Fin 3 => omega)
        (fun i => if i = 2 then omega + delta else ρ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (shellTuples_subset_box e chi m omega delta N cap)
      intro p hp _
      exact actualPrimeBoxWeight_nonneg hp
    _ = _ := by
      rw [actualPrimeBoxMass_eq_prod]
      simp [Fin.prod_univ_three, pow_two]

private theorem intervalMass_nonneg (N : ℕ) (a b : ℝ) :
    0 ≤ actualPrimeReciprocalMass N a b := by
  unfold actualPrimeReciprocalMass
  apply Finset.sum_nonneg
  intro p hp
  have hp1 : (1 : ℝ) < p := by
    exact_mod_cast (mem_roughPrimeFinset.mp hp).2.1.one_lt
  positivity

private theorem intervalMass_le_ratio
    (K : ℝ)
    (hK : ∀ (N cap : ℕ), Even N → ∀ w z : ℝ, 2 ≤ w → w ≤ z →
      (∑ p ∈ roughPrimeFinset N cap w z, 1 / ((p : ℝ) - 1)) ≤
        Real.log z / Real.log w * (1 + K / Real.log w) - 1)
    (N : ℕ) (hN : 1 < N) (hEven : Even N)
    (omega beta : ℝ) (homega : 0 < omega) (horder : omega ≤ beta)
    (hfloor : 2 ≤ (N : ℝ) ^ omega) :
    actualPrimeReciprocalMass N omega beta ≤
      (beta / omega) * (1 + K / (omega * Real.log (N : ℝ))) - 1 := by
  have h := actualPrimeReciprocalMass_le_moving_ratio K hK N hEven
    omega beta hfloor horder hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have heq :
      Real.log ((N : ℝ) ^ beta) / Real.log ((N : ℝ) ^ omega) *
        (1 + K / Real.log ((N : ℝ) ^ omega)) - 1 =
      (beta / omega) * (1 + K / (omega * Real.log (N : ℝ))) - 1 := by
    rw [Real.log_rpow hNpos, Real.log_rpow hNpos]
    field_simp [homega.ne', hlog.ne']
    <;> ring
  rwa [heq] at h

/-- An absolute constant works for every original active shell and every
cap. The only size condition is the explicit scalar inequality
K*rho <= delta*omega*log N. Thus the bound also handles moving delta,
without invoking a fixed-endpoint Mertens limit. -/
theorem exists_uniform_active_shell_bound :
    ∃ K : ℝ, 1 < K ∧
      ∀ (e chi : ℝ) (m : ℕ) (omega delta : ℝ),
        0 < omega → 0 < delta → omega + delta ≤ ρ →
      ∀ (N cap : ℕ), 1 < N → Even N →
        K * ρ ≤ delta * omega * Real.log (N : ℝ) →
        shellMass e chi m omega delta N cap ≤
          (8 * ρ ^ 2 / omega ^ 3) * delta := by
  obtain ⟨K, hK, hinterval⟩ := exists_uniform_reciprocal_interval_bound
  refine ⟨K, hK, ?_⟩
  intro e chi m omega delta homega hdelta hwidth N cap hN hEven hscale
  have hrho : (0 : ℝ) < ρ := by norm_num
  have hK0 : 0 < K := by linarith
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hL : 0 < omega * Real.log (N : ℝ) := mul_pos homega hlog
  have hdRho : delta ≤ ρ := by linarith
  have hKL : K ≤ omega * Real.log (N : ℝ) := by
    apply (mul_le_mul_right hdelta).mp
    calc
      K * delta ≤ K * ρ := mul_le_mul_of_nonneg_left hdRho hK0.le
      _ ≤ (omega * Real.log (N : ℝ)) * delta := by nlinarith [hscale]
  have hlogtwo : Real.log (2 : ℝ) ≤ omega * Real.log (N : ℝ) := by
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfloor : 2 ≤ (N : ℝ) ^ omega := by
    calc
      (2 : ℝ) = Real.exp (Real.log (2 : ℝ)) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (omega * Real.log (N : ℝ)) := Real.exp_le_exp.mpr hlogtwo
      _ = (N : ℝ) ^ omega := by
        rw [Real.rpow_def_of_pos hNpos]
        congr 1
        ring
  have hunit : K / (omega * Real.log (N : ℝ)) ≤ 1 :=
    (div_le_one hL).mpr hKL
  have hsmall : K / (omega * Real.log (N : ℝ)) ≤ delta / ρ := by
    apply (div_le_div_iff₀ hL hrho).mpr
    nlinarith [hscale]
  have hpref : actualPrimeReciprocalMass N omega ρ ≤ 2 * ρ / omega := by
    have h := intervalMass_le_ratio K hinterval N hN hEven omega ρ
      homega (by linarith) hfloor
    have hmul := mul_le_mul_of_nonneg_left hunit
      (div_nonneg hrho.le homega.le)
    nlinarith
  have htail : actualPrimeReciprocalMass N omega (omega + delta) ≤
      2 * delta / omega := by
    have h := intervalMass_le_ratio K hinterval N hN hEven omega (omega + delta)
      homega (by linarith) hfloor
    have herror : ((omega + delta) / omega) *
        (K / (omega * Real.log (N : ℝ))) ≤ delta / omega := by
      calc
        _ ≤ (ρ / omega) * (delta / ρ) := by
          apply mul_le_mul
          · exact div_le_div_of_nonneg_right hwidth homega.le
          · exact hsmall
          · exact div_nonneg hK0.le hL.le
          · exact div_nonneg hrho.le homega.le
        _ = _ := by field_simp [hrho.ne', homega.ne']; ring
    have heq : ((omega + delta) / omega) *
        (1 + K / (omega * Real.log (N : ℝ))) - 1 =
        delta / omega + ((omega + delta) / omega) *
          (K / (omega * Real.log (N : ℝ))) := by
      field_simp [homega.ne', hlog.ne']
      <;> ring
    rw [heq] at h
    linarith
  calc
    _ ≤ (actualPrimeReciprocalMass N omega ρ) ^ 2 *
        actualPrimeReciprocalMass N omega (omega + delta) :=
      shellMass_le_interval_product e chi m omega delta N cap
    _ ≤ (2 * ρ / omega) ^ 2 * (2 * delta / omega) := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (intervalMass_nonneg N omega ρ) hpref 2
      · exact htail
      · exact intervalMass_nonneg N omega (omega + delta)
      · exact sq_nonneg _
    _ = (8 * ρ ^ 2 / omega ^ 3) * delta := by
      field_simp [homega.ne']
      <;> ring

/-- The same explicit linear constant is uniform in all original source
parameters and enumeration caps once omega and delta are fixed. -/
theorem eventually_active_shell_mass_le_linear (omega delta : ℝ)
    (homega : 0 < omega) (hdelta : 0 < delta) (hwidth : omega + delta ≤ ρ) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∀ (e chi : ℝ) (m cap : ℕ),
        shellMass e chi m omega delta N cap ≤
          (8 * ρ ^ 2 / omega ^ 3) * delta := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_active_shell_bound
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun N : ℕ => delta * omega * Real.log (N : ℝ))
      atTop atTop := hlog.const_mul_atTop (mul_pos hdelta homega)
  filter_upwards [eventually_gt_atTop (1 : ℕ),
    hscale.eventually (eventually_ge_atTop (K * ρ))] with N hN hs hEven e chi m cap
  exact hbound e chi m omega delta homega hdelta hwidth N cap hN hEven hs

end
end ImbalancedChen.P0ActivePrimeShellBudget