import ImbalancedChen.P5OriginalPrimeEndpointDivisors
import ImbalancedChen.TotientReciprocalBudget
import ImbalancedChen.PowerErrorBudget
import ImbalancedChen.P5zElevenErrorTransport
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Logarithmic payment of the original singleton endpoint

The divisor summatory function is evaluated by finite Fubini, then bounded
using the pinned harmonic theorem. Combined with the existing proved
reciprocal-totient budget, this pays the actual sharp/smooth singleton PP
endpoint correction for the same causal rho. No smooth distribution,
lower trim, causal support licence or adopted density is supplied.
SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5OriginalPrimeEndpoint

noncomputable section
open scoped BigOperators
open Classical Filter Topology

/-- The exact hyperbolic divisor sum, including the empty case D=0. -/
theorem sum_divisors_card_eq_sum_floor (D : ℕ) :
    (∑ n ∈ Finset.Icc 1 D, (n.divisors.card : ℝ)) =
      ∑ d ∈ Finset.Icc 1 D, ((D / d : ℕ) : ℝ) := by
  have hdiv : ∀ n ∈ Finset.Icc 1 D,
      n.divisors = (Finset.Icc 1 D).filter (fun d => d ∣ n) := by
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
    ext d
    constructor
    · intro hd
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨Nat.pos_of_mem_divisors hd,
          (Nat.le_of_dvd hn0 (Nat.dvd_of_mem_divisors hd)).trans (Finset.mem_Icc.mp hn).2⟩,
        Nat.dvd_of_mem_divisors hd⟩
    · intro hd
      exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2,ne_of_gt hn0⟩
  have hI : Finset.Ioc 0 D = Finset.Icc 1 D := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_Icc]
    omega
  calc
    _ = ∑ n ∈ Finset.Icc 1 D, ∑ d ∈ Finset.Icc 1 D,
        if d ∣ n then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hdiv n hn]
      simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
    _ = ∑ d ∈ Finset.Icc 1 D, ∑ n ∈ Finset.Icc 1 D,
        if d ∣ n then (1 : ℝ) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      have hcard := Nat.Ioc_filter_dvd_card_eq_div D d
      rw [hI] at hcard
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using congrArg (fun n : ℕ => (n : ℝ)) hcard

/-- Integer division is paid by the corresponding real quotient. -/
theorem sum_divisors_card_le_harmonic (D : ℕ) :
    (∑ n ∈ Finset.Icc 1 D, (n.divisors.card : ℝ)) ≤
      (D : ℝ) * (harmonic D : ℝ) := by
  rw [sum_divisors_card_eq_sum_floor]
  have hH : (harmonic D : ℝ) = ∑ d ∈ Finset.Icc 1 D, 1 / (d : ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
  rw [hH,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast (show 0 < d by have := (Finset.mem_Icc.mp hd).1; omega)
  have hmul : ((D / d : ℕ) : ℝ) * (d : ℝ) ≤ D := by
    exact_mod_cast Nat.div_mul_le_self D d
  have hquot := (le_div_iff₀ hdpos).mpr hmul
  simpa only [div_eq_mul_inv,one_div] using hquot

/-- The classical divisor summatory logarithmic bound, with constant one. -/
theorem sum_divisors_card_le_log (D : ℕ) :
    (∑ n ∈ Finset.Icc 1 D, (n.divisors.card : ℝ)) ≤
      (D : ℝ) * (1 + Real.log (D : ℝ)) := by
  exact (sum_divisors_card_le_harmonic D).trans
    (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log D) (Nat.cast_nonneg _))

/-- Full explicit endpoint payment. The first logarithm counts endpoint
integer divisors; the second pays the literal exact coprime PP mean. -/
theorem actual_causal_singleton_endpoint_log_le
    (retainEven : List ℕ → Bool) (N cap P D M : ℕ) (w z L : ℝ)
    (S Q : Finset ℕ) (sharp smooth : ℕ → ℝ)
    (hEven : Even N) (hN : 2 < N) (hS : S ⊆ chenPrimePrefix P)
    (hQ : Q ⊆ Finset.Icc 1 M)
    (hwindow : ∀ p ∈ S, distance N p ≤ D)
    (hagree : ∀ p ∈ chenPrimePrefix P, p ∉ S → sharp p = smooth p)
    (hdelta : ∀ p ∈ S, |sharp p-smooth p| ≤ 1) :
    |Part3.primeProductSignedError 1 P N Q (actualLowerSmallRoughRho retainEven N cap w z L)
        (P5S1SingletonPP.singletonWeight P sharp) -
      Part3.primeProductSignedError 1 P N Q (actualLowerSmallRoughRho retainEven N cap w z L)
        (P5S1SingletonPP.singletonWeight P smooth)| ≤
      2 * (D : ℝ) * (1 + Real.log (D : ℝ)) +
        8 * (D : ℝ) * (1 + Real.log (max 1 (M : ℝ))) := by
  have hr : (∑ q ∈ Q, |actualLowerSmallRoughRho retainEven N cap w z L q| /
      (Nat.totient q : ℝ)) ≤ 4 * (1 + Real.log (max 1 (M : ℝ))) := by
    refine le_trans ?_ (sum_reciprocal_totient_subset_le_log Q M hQ)
    apply Finset.sum_le_sum
    intro q hq
    exact div_le_div_of_nonneg_right
      (actualLowerSmallRoughRho_abs_le_one retainEven N cap w z L q) (Nat.cast_nonneg _)
  refine (actual_causal_singleton_sharp_smooth_le retainEven N cap P D w z L
    S Q sharp smooth hEven hN hS hwindow hagree hdelta).trans ?_
  have ht := mul_le_mul_of_nonneg_left (sum_divisors_card_le_log D) (by norm_num : (0 : ℝ) ≤ 2)
  have hm := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2 * (D : ℝ))
  calc
    _ ≤ 2 * ((D : ℝ) * (1 + Real.log (D : ℝ))) +
        (2 * (D : ℝ)) * (4 * (1 + Real.log (max 1 (M : ℝ)))) := add_le_add ht hm
    _ = _ := by ring

/-- At sublinear physical level M<=N, endpoint loss is at most
10 D (1+log N). D=0 is included and needs no logarithm positivity. -/
theorem actual_causal_singleton_endpoint_logN_le
    (retainEven : List ℕ → Bool) (N cap P D M : ℕ) (w z L : ℝ)
    (S Q : Finset ℕ) (sharp smooth : ℕ → ℝ)
    (hEven : Even N) (hN : 2 < N) (hS : S ⊆ chenPrimePrefix P)
    (hQ : Q ⊆ Finset.Icc 1 M) (hMN : M ≤ N) (hDN : D ≤ N)
    (hwindow : ∀ p ∈ S, distance N p ≤ D)
    (hagree : ∀ p ∈ chenPrimePrefix P, p ∉ S → sharp p = smooth p)
    (hdelta : ∀ p ∈ S, |sharp p-smooth p| ≤ 1) :
    |Part3.primeProductSignedError 1 P N Q (actualLowerSmallRoughRho retainEven N cap w z L)
        (P5S1SingletonPP.singletonWeight P sharp) -
      Part3.primeProductSignedError 1 P N Q (actualLowerSmallRoughRho retainEven N cap w z L)
        (P5S1SingletonPP.singletonWeight P smooth)| ≤
      10 * (D : ℝ) * (1 + Real.log (N : ℝ)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogD : Real.log (D : ℝ) ≤ Real.log (N : ℝ) := by
    by_cases hD : D = 0
    · simpa only [hD,Nat.cast_zero,Real.log_zero] using Real.log_nonneg hN1
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hD)
        (by exact_mod_cast hDN)
  have hlogM : Real.log (max 1 (M : ℝ)) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (max_le hN1 (by exact_mod_cast hMN))
  refine (actual_causal_singleton_endpoint_log_le retainEven N cap P D M w z L
    S Q sharp smooth hEven hN hS hQ hwindow hagree hdelta).trans ?_
  have ht := mul_le_mul_of_nonneg_left (add_le_add_left hlogD 1)
    (by positivity : 0 ≤ 2 * (D : ℝ))
  have hm := mul_le_mul_of_nonneg_left (add_le_add_left hlogM 1)
    (by positivity : 0 ≤ 8 * (D : ℝ))
  calc
    _ ≤ 2 * (D : ℝ) * (1 + Real.log (N : ℝ)) +
        8 * (D : ℝ) * (1 + Real.log (N : ℝ)) := add_le_add ht hm
    _ = _ := by ring

/-- Explicit algebra for a logarithmically short endpoint window. The
additive one is the genuine ceiling loss and is paid by log^(A+1)<=X. -/
theorem log_window_cost_le (A : ℕ) (X ell d : ℝ)
    (hell : 1 ≤ ell) (hX : 0 ≤ X) (hd0 : 0 ≤ d)
    (hd : d ≤ X / ell ^ (A + 3) + 1)
    (hlarge : ell ^ (A + 1) ≤ X) :
    10 * d * (1 + ell) ≤ 40 * X / ell ^ A := by
  have hepos : 0 < ell := zero_lt_one.trans_le hell
  have ht0 : 0 ≤ X / ell ^ A := div_nonneg hX (pow_nonneg hepos.le _)
  have heq : (X / ell ^ (A + 3)) * ell = (X / ell ^ A) / ell ^ 2 := by
    simp only [pow_add,pow_succ]
    field_simp [hepos.ne'] <;> ring
  have hfirst : (X / ell ^ (A + 3)) * ell ≤ X / ell ^ A := by
    rw [heq]
    exact div_le_self ht0 (one_le_pow₀ hell)
  have hsecond : ell ≤ X / ell ^ A := by
    apply (le_div_iff₀ (pow_pos hepos A)).mpr
    simpa only [pow_succ,mul_comm] using hlarge
  have hdell : d * ell ≤ 2 * (X / ell ^ A) := by
    have hh := mul_le_mul_of_nonneg_right hd hepos.le
    rw [add_mul,one_mul] at hh
    linarith
  have htwice : 1 + ell ≤ 2 * ell := by linarith
  calc
    _ ≤ 10 * d * (2 * ell) :=
      mul_le_mul_of_nonneg_left htwice (by positivity)
    _ = 20 * (d * ell) := by ring
    _ ≤ 20 * (2 * (X / ell ^ A)) :=
      mul_le_mul_of_nonneg_left hdell (by norm_num)
    _ = _ := by ring

/-- Proved logarithmic payment with one threshold before all finite
endpoint carriers and policies. A+3 reproduces the manuscript's fixed
polylogarithmic smoothing width, including the natural ceiling loss. -/
theorem eventually_log_window_cost_le (A : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ D : ℕ,
      D ≤ Nat.ceil ((N : ℝ) / Real.log (N : ℝ) ^ (A + 3)) →
        D ≤ N ∧ 10 * (D : ℝ) * (1 + Real.log (N : ℝ)) ≤
          40 * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  have hsmall : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ (A + 1) / (N : ℝ) < 1 := by
    have hh := (tendsto_nat_log_pow_div_rpow (A + 1)
      (by norm_num : (0 : ℝ) < 1)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    simpa only [Real.rpow_one] using hh
  filter_upwards [hsmall,eventually_one_le_nat_log,eventually_ge_atTop (1 : ℕ)]
    with N hsmallN hlog hN
  intro D hD
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogpos : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hX0 : 0 ≤ (N : ℝ) / Real.log (N : ℝ) ^ (A + 3) := by positivity
  have hceil : Nat.ceil ((N : ℝ) / Real.log (N : ℝ) ^ (A + 3)) ≤ N :=
    Nat.ceil_le.mpr (div_le_self (Nat.cast_nonneg _) (one_le_pow₀ hlog))
  have hwidth : (D : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) ^ (A + 3) + 1 := by
    exact (show (D : ℝ) ≤ (Nat.ceil ((N : ℝ) /
      Real.log (N : ℝ) ^ (A + 3)) : ℝ) by exact_mod_cast hD).trans
      (Nat.ceil_lt_add_one hX0).le
  have hlarge : Real.log (N : ℝ) ^ (A + 1) ≤ (N : ℝ) := by
    have hh := (div_lt_iff₀ hNpos).mp hsmallN
    simpa only [one_mul] using hh.le
  exact ⟨hD.trans hceil,log_window_cost_le A (N : ℝ) (Real.log (N : ℝ))
    (D : ℝ) hlog (Nat.cast_nonneg _) (Nat.cast_nonneg _) hwidth hlarge⟩

/-- Actual original sharp/smooth singleton PP endpoint error has any
prescribed logarithmic saving. This proves only endpoint transfer; smooth
PP and the lower-prime trim remain open and are never premises here. -/
theorem eventually_actual_causal_singleton_endpoint_log_saving (A : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (retainEven : List ℕ → Bool) (cap P D M : ℕ)
      (w z L : ℝ) (S Q : Finset ℕ) (sharp smooth : ℕ → ℝ),
      Even N → S ⊆ chenPrimePrefix P → Q ⊆ Finset.Icc 1 M → M ≤ N →
      D ≤ Nat.ceil ((N : ℝ) / Real.log (N : ℝ) ^ (A + 3)) →
      (∀ p ∈ S, distance N p ≤ D) →
      (∀ p ∈ chenPrimePrefix P, p ∉ S → sharp p = smooth p) →
      (∀ p ∈ S, |sharp p-smooth p| ≤ 1) →
      |Part3.primeProductSignedError 1 P N Q (actualLowerSmallRoughRho retainEven N cap w z L)
          (P5S1SingletonPP.singletonWeight P sharp) -
        Part3.primeProductSignedError 1 P N Q (actualLowerSmallRoughRho retainEven N cap w z L)
          (P5S1SingletonPP.singletonWeight P smooth)| ≤
        40 * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  filter_upwards [eventually_log_window_cost_le A,eventually_ge_atTop (3 : ℕ)] with N hcost hN
  intro retainEven cap P D M w z L S Q sharp smooth hEven hS hQ hMN hD hwindow hagree hdelta
  exact (actual_causal_singleton_endpoint_logN_le retainEven N cap P D M w z L
    S Q sharp smooth hEven (by omega) hS hQ hMN (hcost D hD).1 hwindow hagree hdelta).trans
      (hcost D hD).2

/-- The concrete width ceil(N/log^6 N) is paid in the unchanged actual
singular normalization, uniformly in the policy, support and prime cap. -/
theorem eventually_actual_causal_singleton_endpoint_normalized
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ (retainEven : List ℕ → Bool) (cap P D M : ℕ)
      (w z L : ℝ) (S Q : Finset ℕ) (sharp smooth : ℕ → ℝ),
      Even N → S ⊆ chenPrimePrefix P → Q ⊆ Finset.Icc 1 M → M ≤ N →
      D ≤ Nat.ceil ((N : ℝ) / Real.log (N : ℝ) ^ 6) →
      (∀ p ∈ S, distance N p ≤ D) →
      (∀ p ∈ chenPrimePrefix P, p ∉ S → sharp p = smooth p) →
      (∀ p ∈ S, |sharp p-smooth p| ≤ 1) →
      |Part3.primeProductSignedError 1 P N Q (actualLowerSmallRoughRho retainEven N cap w z L)
          (P5S1SingletonPP.singletonWeight P sharp) -
        Part3.primeProductSignedError 1 P N Q (actualLowerSmallRoughRho retainEven N cap w z L)
          (P5S1SingletonPP.singletonWeight P smooth)| ≤
        epsilon * singularNormalization N := by
  filter_upwards [eventually_actual_causal_singleton_endpoint_log_saving 3,
    p5z_eventually_logCube_le_singularNormalization 40 epsilon hepsilon] with N hendpoint hpaid
  intro retainEven cap P D M w z L S Q sharp smooth hEven hS hQ hMN hD hwindow hagree hdelta
  exact (hendpoint retainEven cap P D M w z L S Q sharp smooth hEven hS hQ hMN
    hD hwindow hagree hdelta).trans hpaid

end
end ImbalancedChen.P5OriginalPrimeEndpoint
