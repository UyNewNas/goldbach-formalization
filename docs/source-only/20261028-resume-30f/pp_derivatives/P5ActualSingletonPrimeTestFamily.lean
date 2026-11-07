import ImbalancedChen.P5ActualEtaPsiOccurrenceBudget
import ImbalancedChen.P5NativeSelectedFourOrderedEuler
import ImbalancedChen.P5LicensedOriginalIntegerProfile
import Mathlib

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
A genuine independent ORIGINAL prime-test u for the production singleton
Chen-prime-prefix caller. The physical prefix and residual divisor do not
occur in this function. The lower trim 2*N^beta is exact; the prime ceiling
p<=N lies in the plateau, while the smooth upper collar ends at 2*N.
-/
namespace ImbalancedChen.P5Z.ActualSingletonPrimeTestFamily
noncomputable section
open Classical Set Filter Topology
open scoped BigOperators
open ActualEtaPsiOccurrenceBudget
open AllWordAmbientOccurrenceBound OccurrenceWordFourFactorLeibniz
open NativeSelectedFourOrderedEuler
open AdmissibleAllRankIntegerGeometricFamily LicensedOriginalIntegerProfile

def profile (beta : ℝ) (N : ℕ) (u : Fin 1 → ℝ) : ℝ :=
  if 2 ≤ N then eta (u 0 / (N : ℝ)^beta) * chi (u 0 / (N : ℝ)) else 0

def integerWeight (beta : ℝ) (N : ℕ) (u : Fin 1 → ℕ) : ℝ :=
  profile beta N (fun i => (u i : ℝ))

theorem chi_smooth : ContDiff ℝ ∞ chi := contDiff_const.sub eta_smooth

theorem chi_bounds (s : ℝ) : 0 ≤ chi s ∧ chi s ≤ 1 := by
  obtain ⟨h0, h1⟩ := eta_bounds s
  unfold chi
  constructor <;> linarith

theorem chi_one {s : ℝ} (hs : s ≤ 1) : chi s = 1 := by
  simp [chi, eta_zero hs]
theorem chi_zero {s : ℝ} (hs : 2 ≤ s) : chi s = 0 := by
  simp [chi, eta_one hs]

theorem profile_smooth (beta : ℝ) (N : ℕ) : ContDiff ℝ ∞ (profile beta N) := by
  by_cases hN : 2 ≤ N
  · simp only [profile, if_pos hN]
    exact (eta_smooth.comp ((contDiff_apply ℝ ℝ 0).div_const _)).mul
      (chi_smooth.comp ((contDiff_apply ℝ ℝ 0).div_const _))
  · simp only [profile, if_neg hN]
    exact contDiff_const

theorem profile_bounds (beta : ℝ) (N : ℕ) (u : Fin 1 → ℝ) :
    0 ≤ profile beta N u ∧ profile beta N u ≤ 1 := by
  by_cases hN : 2 ≤ N
  · simp only [profile, if_pos hN]
    refine ⟨mul_nonneg (eta_bounds _).1 (chi_bounds _).1, ?_⟩
    exact (mul_le_mul (eta_bounds _).2 (chi_bounds _).2 (chi_bounds _).1 zero_le_one).
      trans_eq (by norm_num)
  · simp [profile, hN]

theorem profile_zero_below (beta : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (u : Fin 1 → ℝ) (hu : u 0 ≤ (N : ℝ)^beta) : profile beta N u = 0 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hA : 0 < (N : ℝ)^beta := Real.rpow_pos_of_pos hNr _
  simp only [profile, if_pos hN]
  rw [eta_zero ((div_le_iff₀ hA).mpr (by simpa using hu)), zero_mul]

theorem profile_support (beta : ℝ) {N : ℕ} {u : Fin 1 → ℝ}
    (hu : profile beta N u ≠ 0) :
    2 ≤ N ∧ (N : ℝ)^beta < u 0 ∧ u 0 < 2 * (N : ℝ) := by
  have hN : 2 ≤ N := by
    by_contra h
    exact hu (by simp [profile, h])
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  refine ⟨hN, ?_, ?_⟩
  · by_contra h
    exact hu (profile_zero_below beta hN u (le_of_not_gt h))
  · by_contra h
    have hh : 2 ≤ u 0 / (N : ℝ) := (le_div_iff₀ hNr).mpr (le_of_not_gt h)
    exact hu (by simp [profile, hN, chi_zero hh])

/-- The original prime range <=N is unaltered beyond the exact trim. -/
theorem profile_one_on_original_range (beta : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (u : Fin 1 → ℝ) (hlo : 2 * (N : ℝ)^beta ≤ u 0) (hhi : u 0 ≤ (N : ℝ)) :
    profile beta N u = 1 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hA : 0 < (N : ℝ)^beta := Real.rpow_pos_of_pos hNr _
  have he : 2 ≤ u 0 / (N : ℝ)^beta := (le_div_iff₀ hA).mpr hlo
  have hc : u 0 / (N : ℝ) ≤ 1 := (div_le_iff₀ hNr).mpr (by simpa using hhi)
  simp [profile, hN, eta_one he, chi_one hc]

def chiLog (x : ℝ) : ℝ := chi (Real.exp x)
theorem chiLog_smooth : ContDiff ℝ ∞ chiLog := chi_smooth.comp Real.contDiff_exp

theorem chiLog_order_bound (q : ℕ) (M : ℝ) (hM : 1 ≤ M)
    (hb : ∀ d ≤ q, ∀ x, |iteratedDeriv d etaLog x| ≤ M) :
    ∀ d ≤ q, ∀ x, |iteratedDeriv d chiLog x| ≤ M := by
  intro d hd x
  by_cases hz : d = 0
  · subst d
    simp only [iteratedDeriv_zero]
    have hchi := chi_bounds (Real.exp x)
    change |chi (Real.exp x)| ≤ M
    have hb0 : |chi (Real.exp x)| ≤ 1 := by
      simpa only [abs_of_nonneg hchi.1] using hchi.2
    exact hb0.trans hM
  · have he : ContDiffAt ℝ d etaLog x := etaLog_smooth.contDiffAt.of_le (by simp)
    have hc : ContDiffAt ℝ d (fun _ : ℝ => (1 : ℝ)) x := contDiffAt_const
    change |iteratedDeriv d (fun y => 1 - etaLog y) x| ≤ M
    rw [iteratedDeriv_fun_sub hc he, iteratedDeriv_const, if_neg hz]
    simpa using hb d hd x

theorem occWord_const {m : ℕ} (w : List (Fin m)) (c : ℝ) :
    occWord w (fun _ : Fin m → ℝ => c) = if w = [] then (fun _ => c) else 0 := by
  induction w with
  | nil => simp [occWord]
  | cons a w ih =>
      simp only [List.cons_ne_nil, if_false]
      change occOne a (occWord w (fun _ : Fin m → ℝ => c)) = 0
      rw [ih]
      split_ifs <;> funext z <;> simp [occOne]

theorem occurrence_one_bound {m : ℕ} (w : List (Fin m)) (z : Fin m → ℝ) :
    |occWord w (fun _ : Fin m → ℝ => (1 : ℝ)) z| ≤ 1 := by
  rw [occWord_const]
  split_ifs <;> simp

/-- Exact scalar-log factors of the native multiplicative chart. -/
theorem profile_log_chart (beta : ℝ) {N : ℕ} (hN : 2 ≤ N)
    (p : Fin 1 → ℝ) (hp : 0 < p 0) :
    (fun z => profile beta N (multiplicativeChart p z)) =
      fun z => scalarLift (Real.log (p 0 / (N : ℝ)^beta)) etaLog z *
        scalarLift (Real.log (p 0 / (N : ℝ))) chiLog z := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hA : 0 < (N : ℝ)^beta := Real.rpow_pos_of_pos hNr _
  funext z
  simp only [profile, if_pos hN, multiplicativeChart, scalarLift, Fin.sum_univ_one,
    etaLog, chiLog, Real.exp_add, Real.exp_log (div_pos hp hA),
    Real.exp_log (div_pos hp hNr)]
  congr 1 <;> congr 1 <;> ring

/-- The natural constant is chosen before beta,N,p and every ordered
word. It is derived from fixed etaLog constants and genuine word Leibniz. -/
theorem singleton_mixedEuler (q : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (beta : ℝ) (N : ℕ) (w : List (Fin 1)) (p : Fin 1 → ℝ),
      w.length ≤ q → |eulerWord w (profile beta N) p| ≤ (C : ℝ) := by
  obtain ⟨M, hM, hm⟩ := finite_order_constants etaLog exists_etaLog_order_bound q
  let K : ℝ := (4 : ℝ)^q * (M * M)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨Nat.ceil K + 1, by omega, ?_⟩
  intro beta N w p hw
  have hceil : K ≤ ((Nat.ceil K + 1 : ℕ) : ℝ) := by
    have h := Nat.le_ceil K
    push_cast
    linarith
  apply le_trans ?_ hceil
  by_cases hN : 2 ≤ N
  · by_cases hp : 0 < p 0
    · let bE := Real.log (p 0 / (N : ℝ)^beta)
      let bC := Real.log (p 0 / (N : ℝ))
      let E : (Fin 1 → ℝ) → ℝ := scalarLift bE etaLog
      let H : (Fin 1 → ℝ) → ℝ := scalarLift bC chiLog
      have hE : ContDiff ℝ ∞ E := etaLog_smooth.comp
        (by fun_prop : ContDiff ℝ ∞ (fun z : Fin 1 → ℝ => bE + ∑ i, z i))
      have hH : ContDiff ℝ ∞ H := chiLog_smooth.comp
        (by fun_prop : ContDiff ℝ ∞ (fun z : Fin 1 → ℝ => bC + ∑ i, z i))
      have be (v : List (Fin 1)) (hv : v.length ≤ w.length) : |occWord v E 0| ≤ M := by
        rw [show E = scalarLift bE etaLog from rfl, occWord_scalarLift]
        exact hm v.length (hv.trans hw) _
      have bh (v : List (Fin 1)) (hv : v.length ≤ w.length) : |occWord v H 0| ≤ M := by
        rw [show H = scalarLift bC chiLog from rfl, occWord_scalarLift]
        exact chiLog_order_bound q M hM hm v.length (hv.trans hw) _
      have hraw := occWord_four_bound E H (fun _ => 1) (fun _ => 1)
        hE hH contDiff_const contDiff_const w 0 M M 1 1
        (zero_le_one.trans hM) (zero_le_one.trans hM) zero_le_one zero_le_one be bh
        (fun v hv => occurrence_one_bound v 0) (fun v hv => occurrence_one_bound v 0)
      have hchart : (fun y => profile beta N (multiplicativeChart p y)) =
          fun y => E y * H y * (1 : ℝ) * 1 := by
        rw [profile_log_chart beta hN p hp]
        funext y
        simp [E, H, bE, bC]
      rw [← hchart] at hraw
      have he := orderedEuler_occurrence_dictionary (profile beta N) (profile_smooth beta N) w p 0
      have hid : |eulerWord w (profile beta N) p| =
          |occWord w (fun y => profile beta N (multiplicativeChart p y)) 0| := by
        simpa using congrArg abs he
      rw [hid]
      apply hraw.trans
      dsimp [K]
      simpa using mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hw) (by positivity : 0 ≤ M * M)
    · have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
      have hA : 0 < (N : ℝ)^beta := Real.rpow_pos_of_pos hNr _
      have hopen : IsOpen {x : Fin 1 → ℝ | x 0 < (N : ℝ)^beta} :=
        isOpen_lt (continuous_apply 0) continuous_const
      have hz : profile beta N =ᶠ[𝓝 p] 0 := by
        filter_upwards [hopen.mem_nhds ((le_of_not_gt hp).trans_lt hA)] with x hx
        exact profile_zero_below beta hN x hx.le
      rw [(eulerWord_eventually_zero w _ p hz).eq_of_nhds, abs_zero]
      exact hK
  · have hz : profile beta N = 0 := by simp [profile, hN]
    rw [(eulerWord_eventually_zero w _ p
      (Filter.Eventually.of_forall (fun x => congrFun hz x))).eq_of_nhds, abs_zero]
    exact hK

/-- Real lower/product fields at the actual licensed beta=1-kappa margin. -/
theorem singleton_family_support {beta : ℝ} (hbeta : 0 < beta)
    {N : ℕ} {u : Fin 1 → ℝ} (hu : profile beta N u ≠ 0) :
    (∀ i, (N : ℝ)^beta ≤ u i) ∧ (∏ i, u i) ≤ 2 * (N : ℝ) := by
  have h := profile_support beta hu
  constructor
  · intro i
    have : i = 0 := Subsingleton.elim _ _
    simpa [this] using h.2.1.le
  · simpa only [Fin.prod_univ_one] using h.2.2.le

theorem singleton_finite_prime_support (beta : ℝ) (N : ℕ) :
    Set.Finite {u : Fin 1 → ℕ | (∀ i, (u i).Prime) ∧ integerWeight beta N u ≠ 0} := by
  let bank : Finset (Fin 1 → ℕ) := Fintype.piFinset (fun _ => Finset.range (2 * N + 1))
  apply bank.finite_toSet.subset
  intro u hu
  apply Finset.mem_piFinset.mpr
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  have hs := (profile_support beta hu.2).2.2
  have hcast : (u 0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by push_cast; linarith
  simpa [hi] using (Finset.mem_range.mpr (by exact_mod_cast hcast))

def singletonLicence (beta : ℝ) (N : ℕ) : Licence 1 (integerWeight beta N) where
  ambient := profile beta N
  smooth := profile_smooth beta N
  agrees_on_primes := by intro u hu; rfl

/-- Full fixed-rank fields of this actually constructed independent test.
The singleton caller association is supplied by its production source;
these fields do not assert absent original ranks or a whole PP theorem. -/
structure SingletonFamilyFields (beta : ℝ) : Prop where
  exponent_pos : 0 < beta
  smooth : ∀ N, ContDiff ℝ ∞ (profile beta N)
  support : ∀ N u, profile beta N u ≠ 0 →
    (∀ i, (N : ℝ)^beta ≤ u i) ∧ (∏ i, u i) ≤ 2 * (N : ℝ)
  finitePrimeSupport : ∀ N, Set.Finite {u : Fin 1 → ℕ |
    (∀ i, (u i).Prime) ∧ integerWeight beta N u ≠ 0}
  mixedEuler : ∀ q : ℕ, ∃ C B : ℕ, 0 < C ∧ ∀ N (w : List (Fin 1)) u,
    w.length ≤ q → |eulerWord w (profile beta N) u| ≤
      (C : ℝ) * Real.log ((N : ℝ) + 2)^B

theorem singleton_family_fields {beta : ℝ} (hbeta : 0 < beta) :
    SingletonFamilyFields beta := by
  constructor
  · exact hbeta
  · exact profile_smooth beta
  · intro N u hu
    exact singleton_family_support hbeta hu
  · exact singleton_finite_prime_support beta
  · intro q
    obtain ⟨C, hC, hb⟩ := singleton_mixedEuler q
    refine ⟨C, 0, hC, ?_⟩
    intro N w u hw
    simpa only [pow_zero, mul_one] using hb beta N w u hw

end
end ImbalancedChen.P5Z.ActualSingletonPrimeTestFamily
