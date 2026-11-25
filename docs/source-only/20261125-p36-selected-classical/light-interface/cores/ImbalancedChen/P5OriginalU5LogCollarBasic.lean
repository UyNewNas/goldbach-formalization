import ImbalancedChen.P5OriginalU5ScalarSmoothCutoffs
import ImbalancedChen.P5LicensedOriginalIntegerProfile
import Mathlib

/-! Source-only exact declaration extraction for the actual U5 count consumer.
No elaboration or kernel acceptance is claimed. -/
namespace ImbalancedChen.P5Z.ActualSingletonLogCollarFamily
noncomputable section
open Classical Set Filter Topology
open ActualEtaPsiOccurrenceBudget ActualSingletonPrimeTestFamily
open LicensedOriginalIntegerProfile
open scoped BigOperators

def scaledChi (delta x : ℝ) : ℝ := chiLog (x / delta)

def profile (beta delta : ℝ) (N : ℕ) (u : Fin 1 → ℝ) : ℝ :=
  if 2 ≤ N then
    if 0 < u 0 then eta (u 0 / (N : ℝ)^beta) *
      scaledChi delta (Real.log (u 0) - Real.log (N : ℝ)) else 0
  else 0

def integerWeight (beta delta : ℝ) (N : ℕ) (u : Fin 1 → ℕ) : ℝ :=
  profile beta delta N (fun i => (u i : ℝ))

theorem scaledChi_smooth (delta : ℝ) : ContDiff ℝ ∞ (scaledChi delta) :=
  chiLog_smooth.comp (contDiff_id.div_const delta)

theorem profile_bounds (beta delta : ℝ) (N : ℕ) (u : Fin 1 → ℝ) :
    0 ≤ profile beta delta N u ∧ profile beta delta N u ≤ 1 := by
  by_cases hN : 2 ≤ N <;> by_cases hu : 0 < u 0
  · simp only [profile, if_pos hN, if_pos hu, scaledChi, chiLog]
    refine ⟨mul_nonneg (eta_bounds _).1 (chi_bounds _).1, ?_⟩
    exact (mul_le_mul (eta_bounds _).2 (chi_bounds _).2 (chi_bounds _).1 zero_le_one).
      trans_eq (by norm_num)
  all_goals simp [profile, hN, hu]

theorem profile_zero_below (beta delta : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (u : Fin 1 → ℝ) (hu : u 0 ≤ (N : ℝ)^beta) : profile beta delta N u = 0 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hA : 0 < (N : ℝ)^beta := Real.rpow_pos_of_pos hNr _
  by_cases hp : 0 < u 0
  · simp only [profile, if_pos hN, if_pos hp]
    rw [eta_zero ((div_le_iff₀ hA).mpr (by simpa using hu)), zero_mul]
  · simp [profile, hN, hp]

theorem profile_eventually_zero (beta delta : ℝ) (N : ℕ) (u : Fin 1 → ℝ)
    (hu : u 0 ≤ 0) : profile beta delta N =ᶠ[𝓝 u] 0 := by
  by_cases hN : 2 ≤ N
  · have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hA : 0 < (N : ℝ)^beta := Real.rpow_pos_of_pos hNr _
    have hopen : IsOpen {x : Fin 1 → ℝ | x 0 < (N : ℝ)^beta} :=
      isOpen_lt (continuous_apply 0) continuous_const
    filter_upwards [hopen.mem_nhds (hu.trans_lt hA)] with x hx
    exact profile_zero_below beta delta hN x hx.le
  · simp only [profile, if_neg hN]
    exact Filter.Eventually.of_forall (fun _ => rfl)

theorem profile_smooth (beta delta : ℝ) (N : ℕ) :
    ContDiff ℝ ∞ (profile beta delta N) := by
  by_cases hN : 2 ≤ N
  · apply contDiff_iff_contDiffAt.mpr
    intro u
    by_cases hu : 0 < u 0
    · have hlog : ContDiffAt ℝ ∞ (fun x : Fin 1 → ℝ => Real.log (x 0)) u :=
        (Real.contDiffAt_log hu.ne').comp u (contDiff_apply ℝ ℝ 0).contDiffAt
      have hraw := ((eta_smooth.comp
        ((contDiff_apply ℝ ℝ 0).div_const _)).contDiffAt).mul
        ((scaledChi_smooth delta).contDiffAt.comp u (hlog.sub contDiffAt_const))
      have hopen : IsOpen {x : Fin 1 → ℝ | 0 < x 0} :=
        isOpen_lt continuous_const (continuous_apply 0)
      have heq : profile beta delta N =ᶠ[𝓝 u]
          (fun x => eta (x 0 / (N : ℝ)^beta) *
            scaledChi delta (Real.log (x 0) - Real.log (N : ℝ))) := by
        filter_upwards [hopen.mem_nhds hu] with x hx
        simp only [profile, if_pos hN, if_pos hx]
      exact hraw.congr_of_eventuallyEq heq
    · exact (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Fin 1 → ℝ => (0 : ℝ)) u).
        congr_of_eventuallyEq (profile_eventually_zero beta delta N u (le_of_not_gt hu))
  · simp only [profile, if_neg hN]
    exact contDiff_const

theorem profile_one_on_original_range (beta : ℝ) {delta : ℝ} (hdelta : 0 < delta)
    {N : ℕ} (hN : 2 ≤ N) (u : Fin 1 → ℝ)
    (hlo : 2 * (N : ℝ)^beta ≤ u 0) (hhi : u 0 ≤ (N : ℝ)) :
    profile beta delta N u = 1 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hA : 0 < (N : ℝ)^beta := Real.rpow_pos_of_pos hNr _
  have hu : 0 < u 0 := lt_of_lt_of_le (by positivity : 0 < 2 * (N : ℝ)^beta) hlo
  have he : 2 ≤ u 0 / (N : ℝ)^beta := (le_div_iff₀ hA).mpr hlo
  have hlog : Real.log (u 0) - Real.log (N : ℝ) ≤ 0 :=
    sub_nonpos.mpr (Real.log_le_log hu hhi)
  have hscaled : (Real.log (u 0) - Real.log (N : ℝ)) / delta ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hlog hdelta.le
  have hc : scaledChi delta (Real.log (u 0) - Real.log (N : ℝ)) = 1 := by
    exact chi_one (Real.exp_le_one_iff.mpr hscaled)
  simp only [profile, if_pos hN, if_pos hu, eta_one he, hc, one_mul]

theorem profile_support (beta : ℝ) {delta : ℝ} (hdelta : 0 < delta)
    {N : ℕ} {u : Fin 1 → ℝ} (hu : profile beta delta N u ≠ 0) :
    2 ≤ N ∧ (N : ℝ)^beta < u 0 ∧
      u 0 < (N : ℝ) * Real.exp (delta * Real.log 2) := by
  have hN : 2 ≤ N := by
    by_contra h
    exact hu (by simp [profile, h])
  have hp : 0 < u 0 := by
    by_contra h
    exact hu (by simp [profile, hN, h])
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  refine ⟨hN, ?_, ?_⟩
  · by_contra h
    exact hu (profile_zero_below beta delta hN u (le_of_not_gt h))
  · have harg : (Real.log (u 0) - Real.log (N : ℝ)) / delta < Real.log 2 := by
      by_contra h
      have htwo : 2 ≤ Real.exp ((Real.log (u 0) - Real.log (N : ℝ)) / delta) := by
        calc
          (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
          _ ≤ _ := Real.exp_le_exp.mpr (le_of_not_gt h)
      exact hu (by simp [profile, hN, hp, scaledChi, chiLog, chi_zero htwo])
    have hlog : Real.log (u 0) < Real.log (N : ℝ) + delta * Real.log 2 := by
      have h := (div_lt_iff₀ hdelta).mp harg
      nlinarith
    calc
      u 0 = Real.exp (Real.log (u 0)) := (Real.exp_log hp).symm
      _ < Real.exp (Real.log (N : ℝ) + delta * Real.log 2) := Real.exp_lt_exp.mpr hlog
      _ = _ := by rw [Real.exp_add, Real.exp_log hNr]

theorem exp_log_two_chord {delta : ℝ} (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    Real.exp (delta * Real.log 2) ≤ 1 + delta := by
  have h := _root_.convexOn_exp.2 (x := (0 : ℝ)) (by trivial)
    (y := Real.log 2) (by trivial) (a := 1 - delta) (b := delta)
    (by linarith) hdelta (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  nlinarith

theorem profile_support_short (beta : ℝ) {delta : ℝ} (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) {N : ℕ} {u : Fin 1 → ℝ}
    (hu : profile beta delta N u ≠ 0) :
    2 ≤ N ∧ (N : ℝ)^beta < u 0 ∧ u 0 < (N : ℝ) * (1 + delta) := by
  have h := profile_support beta hdelta hu
  exact ⟨h.1, h.2.1, h.2.2.trans_le
    (mul_le_mul_of_nonneg_left (exp_log_two_chord hdelta.le hdelta1) (by positivity))⟩

theorem profile_zero_above (beta : ℝ) {delta : ℝ} (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) (N : ℕ) (u : Fin 1 → ℝ)
    (hu : (N : ℝ) * (1 + delta) ≤ u 0) : profile beta delta N u = 0 := by
  by_contra h
  exact (not_lt_of_ge hu) (profile_support_short beta hdelta hdelta1 h).2.2

def logWidth (B N : ℕ) : ℝ := (Real.log 2 / Real.log ((N : ℝ) + 2))^B

theorem logWidth_bounds (B : ℕ) {N : ℕ} (hN : 2 ≤ N) :
    0 < logWidth B N ∧ logWidth B N ≤ 1 := by
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hN2 : (2 : ℝ) ≤ (N : ℝ) + 2 := by positivity
  have hlog : Real.log 2 ≤ Real.log ((N : ℝ) + 2) := Real.log_le_log (by norm_num) hN2
  have hlogpos : 0 < Real.log ((N : ℝ) + 2) := h2.trans_le hlog
  exact ⟨pow_pos (div_pos h2 hlogpos) _, pow_le_one₀ (div_nonneg h2.le hlogpos.le)
    ((div_le_one hlogpos).mpr hlog)⟩

theorem logWidth_le_inverse_log (B : ℕ) {N : ℕ} (hN : 2 ≤ N) :
    logWidth B N ≤ 1 / Real.log ((N : ℝ) + 2)^B := by
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
  have hlog21 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hp : Real.log (2 : ℝ)^B ≤ 1 := pow_le_one₀ hlog2 hlog21
  dsimp [logWidth]
  rw [div_pow]
  exact div_le_div_of_nonneg_right hp (pow_nonneg
    (Real.log_nonneg (by positivity : (1 : ℝ) ≤ (N : ℝ) + 2)) B)

def singletonLicence (beta delta : ℝ) (N : ℕ) : Licence 1 (integerWeight beta delta N) where
  ambient := profile beta delta N
  smooth := profile_smooth beta delta N
  agrees_on_primes := by intro u hu; rfl

end
end ImbalancedChen.P5Z.ActualSingletonLogCollarFamily

