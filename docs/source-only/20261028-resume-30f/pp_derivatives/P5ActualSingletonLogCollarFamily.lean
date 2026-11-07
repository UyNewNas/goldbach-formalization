import ImbalancedChen.P5ActualSingletonPrimeTestFamily
import ImbalancedChen.P4BSmoothProfileDirectionalDerivativeBudget
import Mathlib

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
A narrow upper collar for the genuine independent singleton prime test.
The real function is fixed independently of every modulus and coefficient.
The width-dependent Euler bound is proved from the fixed chiLog jets and
actual ordered Leibniz; no mixedEuler conclusion is an input.
-/
namespace ImbalancedChen.P5Z.ActualSingletonLogCollarFamily
noncomputable section
open Classical Set Filter Topology
open scoped BigOperators
open ActualEtaPsiOccurrenceBudget ActualSingletonPrimeTestFamily
open AllWordAmbientOccurrenceBound OccurrenceWordFourFactorLeibniz
open NativeSelectedFourOrderedEuler
open AdmissibleAllRankIntegerGeometricFamily LicensedOriginalIntegerProfile

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

/-- The original upper prime endpoint is in the actual plateau. -/
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

/-- Exact real support, with a genuinely narrow logarithmic upper collar. -/
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

/-- Convexity of the exponential between 0 and log2 gives an exact
linear collar bound, with no numerical exponential evaluation. -/
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

/-- The actual caller can take the integer upper-reserve width ceil(N*delta). -/
theorem profile_zero_above (beta : ℝ) {delta : ℝ} (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) (N : ℕ) (u : Fin 1 → ℝ)
    (hu : (N : ℝ) * (1 + delta) ≤ u 0) : profile beta delta N u = 0 := by
  by_contra h
  exact (not_lt_of_ge hu) (profile_support_short beta hdelta hdelta1 h).2.2

/-- Exact positive multiplicative chart; repeated occurrence letters still
enter the same scalar sum and no rank factor is paid. -/
theorem profile_log_chart (beta delta : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (p : Fin 1 → ℝ) (hp : 0 < p 0) :
    (fun z => profile beta delta N (multiplicativeChart p z)) =
      fun z => scalarLift (Real.log (p 0 / (N : ℝ)^beta)) etaLog z *
        scalarLift (Real.log (p 0) - Real.log (N : ℝ)) (scaledChi delta) z := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hA : 0 < (N : ℝ)^beta := Real.rpow_pos_of_pos hNr _
  funext z
  have hz : 0 < multiplicativeChart p z 0 := mul_pos hp (Real.exp_pos _)
  simp only [profile, if_pos hN, if_pos hz, scalarLift, Fin.sum_univ_one,
    etaLog, multiplicativeChart, Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.exp_add, Real.exp_log (div_pos hp hA)]
  congr 1
  · congr 1
    ring
  · congr 1
    ring

theorem scaledChi_order_bound (q : ℕ) {delta : ℝ} (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) (M : ℝ) (hM : 1 ≤ M)
    (hb : ∀ d ≤ q, ∀ x, |iteratedDeriv d etaLog x| ≤ M) :
    ∀ d ≤ q, ∀ x, |iteratedDeriv d (scaledChi delta) x| ≤ M * (delta⁻¹)^q := by
  have hInv : 1 ≤ delta⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hdelta).mpr (by simpa using hdelta1)
  intro d hd x
  have heq : scaledChi delta = fun t => chiLog (0 + delta⁻¹ * t) := by
    funext t
    simp [scaledChi, div_eq_mul_inv, mul_comm]
  rw [heq, P4B.iteratedDeriv_comp_real_affine d chiLog chiLog_smooth,
    abs_mul, abs_pow, abs_of_nonneg (inv_nonneg.mpr hdelta.le)]
  calc
    delta⁻¹ ^ d * |iteratedDeriv d chiLog (0 + delta⁻¹ * x)| ≤ delta⁻¹ ^ d * M :=
      mul_le_mul_of_nonneg_left (chiLog_order_bound q M hM hb d hd _) (by positivity)
    _ ≤ delta⁻¹ ^ q * M := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hInv hd) (zero_le_one.trans hM)
    _ = _ := mul_comm _ _

/-- A positive natural constant before beta, width, target, point and word.
Only the proven collar cost delta^(-q) remains. -/
theorem collar_mixedEuler (q : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (beta delta : ℝ), 0 < delta → delta ≤ 1 →
      ∀ (N : ℕ) (w : List (Fin 1)) (p : Fin 1 → ℝ), w.length ≤ q →
      |eulerWord w (profile beta delta N) p| ≤ (C : ℝ) * (delta⁻¹)^q := by
  obtain ⟨M, hM, hm⟩ := finite_order_constants etaLog exists_etaLog_order_bound q
  let K : ℝ := (4 : ℝ)^q * (M * M)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨Nat.ceil K + 1, by omega, ?_⟩
  intro beta delta hdelta hdelta1 N w p hw
  have hceil : K ≤ ((Nat.ceil K + 1 : ℕ) : ℝ) := by
    have h := Nat.le_ceil K
    push_cast
    linarith
  have hInv : 1 ≤ delta⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hdelta).mpr (by simpa using hdelta1)
  let S : ℝ := (delta⁻¹)^q
  have hS : 1 ≤ S := by
    dsimp [S]
    calc
      (1 : ℝ) = 1^q := (one_pow q).symm
      _ ≤ (delta⁻¹)^q := pow_le_pow_left₀ zero_le_one hInv q
  have hfinal : K * S ≤ ((Nat.ceil K + 1 : ℕ) : ℝ) * S :=
    mul_le_mul_of_nonneg_right hceil (zero_le_one.trans hS)
  apply le_trans ?_ hfinal
  by_cases hN : 2 ≤ N
  · by_cases hp : 0 < p 0
    · let bE := Real.log (p 0 / (N : ℝ)^beta)
      let bH := Real.log (p 0) - Real.log (N : ℝ)
      let E : (Fin 1 → ℝ) → ℝ := scalarLift bE etaLog
      let H : (Fin 1 → ℝ) → ℝ := scalarLift bH (scaledChi delta)
      have hE : ContDiff ℝ ∞ E := etaLog_smooth.comp
        (by fun_prop : ContDiff ℝ ∞ (fun z : Fin 1 → ℝ => bE + ∑ i, z i))
      have hH : ContDiff ℝ ∞ H := (scaledChi_smooth delta).comp
        (by fun_prop : ContDiff ℝ ∞ (fun z : Fin 1 → ℝ => bH + ∑ i, z i))
      have be (v : List (Fin 1)) (hv : v.length ≤ w.length) : |occWord v E 0| ≤ M := by
        rw [show E = scalarLift bE etaLog from rfl, occWord_scalarLift]
        exact hm v.length (hv.trans hw) _
      have bh (v : List (Fin 1)) (hv : v.length ≤ w.length) :
          |occWord v H 0| ≤ M * S := by
        rw [show H = scalarLift bH (scaledChi delta) from rfl, occWord_scalarLift]
        exact scaledChi_order_bound q hdelta hdelta1 M hM hm v.length (hv.trans hw) _
      have hraw := occWord_four_bound E H (fun _ => 1) (fun _ => 1)
        hE hH contDiff_const contDiff_const w 0 M (M * S) 1 1
        (zero_le_one.trans hM) (by positivity) zero_le_one zero_le_one be bh
        (fun v hv => occurrence_one_bound v 0) (fun v hv => occurrence_one_bound v 0)
      have hchart : (fun y => profile beta delta N (multiplicativeChart p y)) =
          fun y => E y * H y * (1 : ℝ) * 1 := by
        rw [profile_log_chart beta delta hN p hp]
        funext y
        simp [E, H, bE, bH]
      rw [← hchart] at hraw
      have he := orderedEuler_occurrence_dictionary (profile beta delta N)
        (profile_smooth beta delta N) w p 0
      have hid : |eulerWord w (profile beta delta N) p| =
          |occWord w (fun y => profile beta delta N (multiplicativeChart p y)) 0| := by
        simpa using congrArg abs he
      rw [hid]
      simp only [mul_one] at hraw
      apply hraw.trans
      calc
        (4 : ℝ)^w.length * (M * (M * S)) ≤ (4 : ℝ)^q * (M * (M * S)) :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hw) (by positivity)
        _ = K * S := by dsimp [K]; ring
    · rw [(eulerWord_eventually_zero w _ p
        (profile_eventually_zero beta delta N p (le_of_not_gt hp))).eq_of_nhds, abs_zero]
      positivity
  · have hz : profile beta delta N = 0 := by simp [profile, hN]
    rw [(eulerWord_eventually_zero w _ p
      (Filter.Eventually.of_forall (fun x => congrFun hz x))).eq_of_nhds, abs_zero]
    positivity

/-- A concrete inverse-polylogarithmic width; using log2 avoids any
numerical exponential certificate. The index B is fixed before N. -/
def logWidth (B N : ℕ) : ℝ := (Real.log 2 / Real.log ((N : ℝ) + 2))^B

theorem logWidth_bounds (B : ℕ) {N : ℕ} (hN : 2 ≤ N) :
    0 < logWidth B N ∧ logWidth B N ≤ 1 := by
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hN2 : (2 : ℝ) ≤ (N : ℝ) + 2 := by positivity
  have hlog : Real.log 2 ≤ Real.log ((N : ℝ) + 2) := Real.log_le_log (by norm_num) hN2
  have hlogpos : 0 < Real.log ((N : ℝ) + 2) := h2.trans_le hlog
  exact ⟨pow_pos (div_pos h2 hlogpos) _, pow_le_one₀ (div_nonneg h2.le hlogpos.le)
    ((div_le_one hlogpos).mpr hlog)⟩

/-- This chosen width is at most 1/log(N+2)^B, exactly the width used
by the production endpoint payment. -/
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

/-- The actual selected narrow profile has the allowed polylogarithmic
syntactic mixedEuler bound, uniformly before beta,N,point and ordered word. -/
theorem logWidth_mixedEuler (B q : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (beta : ℝ) (N : ℕ) (w : List (Fin 1)) (p : Fin 1 → ℝ),
      w.length ≤ q → |eulerWord w (profile beta (logWidth B N) N) p| ≤
        (C : ℝ) * Real.log ((N : ℝ) + 2)^(B * q) := by
  obtain ⟨C0, hC0, hb⟩ := collar_mixedEuler q
  let K : ℝ := (C0 : ℝ) / Real.log 2^(B * q)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨Nat.ceil K + 1, by omega, ?_⟩
  intro beta N w p hw
  by_cases hN : 2 ≤ N
  · have hwidth := logWidth_bounds B hN
    have h := hb beta (logWidth B N) hwidth.1 hwidth.2 N w p hw
    have hscale : (C0 : ℝ) * (logWidth B N)⁻¹^q =
        K * Real.log ((N : ℝ) + 2)^(B * q) := by
      dsimp [logWidth, K]
      simp only [inv_pow, inv_div, div_pow, ← pow_mul]
      ring
    rw [hscale] at h
    apply h.trans
    have hceil : K ≤ ((Nat.ceil K + 1 : ℕ) : ℝ) := by
      have hc := Nat.le_ceil K
      push_cast
      linarith
    exact mul_le_mul_of_nonneg_right hceil (by positivity)
  · have hz : profile beta (logWidth B N) N = 0 := by simp [profile, hN]
    rw [(eulerWord_eventually_zero w _ p
      (Filter.Eventually.of_forall (fun x => congrFun hz x))).eq_of_nhds, abs_zero]
    have hlog : 0 ≤ Real.log ((N : ℝ) + 2) :=
      Real.log_nonneg (by positivity)
    positivity

/-- The same natural constant is chosen before every HB occurrence count,
repeated owner map and positive dyadic scale. -/
theorem logWidth_occurrence_budget (B q : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ beta N m (owner : Fin m → Fin 1) (U : Fin m → ℝ)
      (w : List (Fin m)) z, w.length ≤ q →
      |occWord w (fun y => profile beta (logWidth B N) N
        (fun i => groupProduct owner U i y)) z| ≤
        (C : ℝ) * Real.log ((N : ℝ) + 2)^(B * q) := by
  obtain ⟨C, hC, hb⟩ := logWidth_mixedEuler B q
  refine ⟨C, hC, ?_⟩
  intro beta N m owner U w z hw
  rw [occWord_ambient owner U _ (profile_smooth beta (logWidth B N) N) w z]
  exact hb beta N (w.map owner) _ (by simpa using hw)

theorem logWidth_family_support {beta : ℝ} (hbeta : 0 < beta) (B : ℕ)
    {N : ℕ} {u : Fin 1 → ℝ} (hu : profile beta (logWidth B N) N u ≠ 0) :
    (∀ i, (N : ℝ)^beta ≤ u i) ∧ (∏ i, u i) ≤ 2 * (N : ℝ) := by
  have hN : 2 ≤ N := by
    by_contra h
    exact hu (by simp [profile, h])
  have hd := logWidth_bounds B hN
  have hs := profile_support_short beta hd.1 hd.2 hu
  constructor
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi] using hs.2.1.le
  · simp only [Fin.prod_univ_one]
    calc
      u 0 ≤ (N : ℝ) * (1 + logWidth B N) := hs.2.2.le
      _ ≤ (N : ℝ) * (1 + 1) := mul_le_mul_of_nonneg_left (add_le_add_left hd.2 1) (by positivity)
      _ = 2 * (N : ℝ) := by ring

theorem logWidth_finite_prime_support (beta : ℝ) (B N : ℕ) :
    Set.Finite {u : Fin 1 → ℕ | (∀ i, (u i).Prime) ∧
      integerWeight beta (logWidth B N) N u ≠ 0} := by
  let bank : Finset (Fin 1 → ℕ) := Fintype.piFinset (fun _ => Finset.range (2 * N + 1))
  apply bank.finite_toSet.subset
  intro u hu
  have hN : 2 ≤ N := by
    by_contra h
    exact hu.2 (by simp [integerWeight, profile, h])
  have hd := logWidth_bounds B hN
  have hs := profile_support_short beta hd.1 hd.2 hu.2
  apply Finset.mem_piFinset.mpr
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  have hupper : (N : ℝ) * (1 + logWidth B N) ≤ 2 * (N : ℝ) := by
    calc
      (N : ℝ) * (1 + logWidth B N) ≤ (N : ℝ) * (1 + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hd.2 1) (by positivity)
      _ = 2 * (N : ℝ) := by ring
  have hreal : (u 0 : ℝ) < 2 * (N : ℝ) := hs.2.2.trans_le hupper
  have hcast : (u 0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by push_cast; linarith
  simpa [hi] using (Finset.mem_range.mpr (by exact_mod_cast hcast))

structure LogCollarFamilyFields (beta : ℝ) (B : ℕ) : Prop where
  exponent_pos : 0 < beta
  smooth : ∀ N, ContDiff ℝ ∞ (profile beta (logWidth B N) N)
  support : ∀ N u, profile beta (logWidth B N) N u ≠ 0 →
    (∀ i, (N : ℝ)^beta ≤ u i) ∧ (∏ i, u i) ≤ 2 * (N : ℝ)
  finitePrimeSupport : ∀ N, Set.Finite {u : Fin 1 → ℕ | (∀ i, (u i).Prime) ∧
    integerWeight beta (logWidth B N) N u ≠ 0}
  mixedEuler : ∀ q, ∃ C : ℕ, 0 < C ∧ ∀ N (w : List (Fin 1)) u,
    w.length ≤ q → |eulerWord w (profile beta (logWidth B N) N) u| ≤
      (C : ℝ) * Real.log ((N : ℝ) + 2)^(B * q)

theorem logWidth_family_fields {beta : ℝ} (hbeta : 0 < beta) (B : ℕ) :
    LogCollarFamilyFields beta B := by
  constructor
  · exact hbeta
  · intro N
    exact profile_smooth beta (logWidth B N) N
  · intro N u hu
    exact logWidth_family_support hbeta B hu
  · exact logWidth_finite_prime_support beta B
  · intro q
    obtain ⟨C, hC, hb⟩ := logWidth_mixedEuler B q
    exact ⟨C, hC, fun N w u hw => hb beta N w u hw⟩

def singletonLicence (beta delta : ℝ) (N : ℕ) : Licence 1 (integerWeight beta delta N) where
  ambient := profile beta delta N
  smooth := profile_smooth beta delta N
  agrees_on_primes := by intro u hu; rfl

end
end ImbalancedChen.P5Z.ActualSingletonLogCollarFamily
