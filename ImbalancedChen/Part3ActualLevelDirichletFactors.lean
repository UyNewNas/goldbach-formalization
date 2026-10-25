import ImbalancedChen.P0RamanujanPrimePowerValues
import ImbalancedChen.Part3RamanujanMultiplicativity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Actual level-restricted prime-power Ramanujan Dirichlet factors

SOURCE ONLY / UNCOMPILED / ZERO PROOF CREDIT (2026-10-25).

The local tail is the literal sum over exponents k>=e, where e can be
v_p(N). For nonzero integer frequency n, the actual Ramanujan coefficients
vanish beyond v_p(|n|)+1, including their negative boundary coefficient.
Thus every restricted local factor is an explicit finite geometric
polynomial, without a convergence or Euler-product premise.

At n=0 the coefficients are the actual totient prime-power coefficients.
Their infinite local tail is instead a convergent geometric series when
|pX|<1. For the genuine Dirichlet ratio X=exp(-w log p), this condition is
proved from Re(w)>1. Finite-prefix subtraction gives the exact local
level correction. No global Euler product or all-level formula is assumed.
-/

namespace ImbalancedChen.Part3.ActualLevelDirichletFactors

noncomputable section

open Finset Complex
open scoped BigOperators
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode
open ImbalancedChen.Part3.RamanujanPrimePowerValues20261025a

/-- Literal local tail over all actual exponents k=j+e. -/
def localTail (p : ℕ) (n : ℤ) (e : ℕ) (X : ℂ) : ℂ :=
  ∑' j : ℕ, ramanujan (p ^ (j + e)) n * X ^ (j + e)

/-- The positive-exponent tail begins at h+1. -/
def positiveLocalTail (p : ℕ) (n : ℤ) (h : ℕ) (X : ℂ) : ℂ :=
  ∑' j : ℕ, ramanujan (p ^ (h + j + 1)) n * X ^ (h + j + 1)

private theorem power_dvd_iff_valuation {p : ℕ} (hp : p.Prime)
    {n : ℤ} (hn : n ≠ 0) (k : ℕ) :
    ((p ^ k : ℕ) : ℤ) ∣ n ↔ k ≤ padicValNat p n.natAbs := by
  have hcast : ((p ^ k : ℕ) : ℤ) ∣ n ↔ p ^ k ∣ n.natAbs := by
    constructor
    · intro h
      exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h)
    · intro h
      exact Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr h)
  exact hcast.trans (padicValNat_dvd_iff_le_of_ne_one hp.ne_one (Int.natAbs_ne_zero.mpr hn))

/-- Only the already-proved exact coefficients are converted to valuation
indices here; no Ramanujan evaluation is assumed or re-proved. -/
private theorem coefficient_succ_eq {p : ℕ} (hp : p.Prime)
    {n : ℤ} (hn : n ≠ 0) (k : ℕ) :
    ramanujan (p ^ (k + 1)) n =
      if k + 1 ≤ padicValNat p n.natAbs then
        (p : ℂ) ^ k * ((p : ℂ) - 1)
      else if k ≤ padicValNat p n.natAbs then -(p : ℂ) ^ k else 0 := by
  rw [ramanujan_prime_pow_values hp k n,
    power_dvd_iff_valuation hp hn (k + 1), power_dvd_iff_valuation hp hn k]
  simp only [Nat.cast_pow]

theorem positiveLocalTail_summable_nonzero {p : ℕ} (hp : p.Prime)
    {n : ℤ} (hn : n ≠ 0) (h : ℕ) (X : ℂ) :
    Summable (fun j : ℕ => ramanujan (p ^ (h + j + 1)) n * X ^ (h + j + 1)) := by
  apply summable_of_ne_finset_zero (s := range (padicValNat p n.natAbs + 1))
  intro j hj
  have hlarge : padicValNat p n.natAbs + 1 ≤ j := by
    simpa only [mem_range, not_lt] using hj
  rw [coefficient_succ_eq hp hn (h + j)]
  simp only [if_neg (by omega : ¬h + j + 1 ≤ padicValNat p n.natAbs),
    if_neg (by omega : ¬h + j ≤ padicValNat p n.natAbs), zero_mul]

/-- Exact finite geometric polynomial, including the negative coefficient
at exponent v_p(|n|)+1. A cutoff above that exponent gives zero. -/
theorem positiveLocalTail_nonzero_eq {p : ℕ} (hp : p.Prime)
    {n : ℤ} (hn : n ≠ 0) (h : ℕ) (X : ℂ) :
    positiveLocalTail p n h X =
      if h ≤ padicValNat p n.natAbs then
        ((p : ℂ) - 1) * X * ((p : ℂ) * X) ^ h *
          (∑ j ∈ range (padicValNat p n.natAbs - h), ((p : ℂ) * X) ^ j) -
          (p : ℂ) ^ padicValNat p n.natAbs * X ^ (padicValNat p n.natAbs + 1)
      else 0 := by
  classical
  let m : ℕ := padicValNat p n.natAbs
  by_cases hh : h ≤ m
  · rw [if_pos hh]
    let d : ℕ := m - h
    have hhd : h + d = m := Nat.add_sub_of_le hh
    have hcut : ∀ j ∉ range (d + 1),
        ramanujan (p ^ (h + j + 1)) n * X ^ (h + j + 1) = 0 := by
      intro j hj
      have hjlarge : d + 1 ≤ j := by simpa only [mem_range, not_lt] using hj
      rw [coefficient_succ_eq hp hn (h + j)]
      simp only [if_neg (by dsimp [m, d] at *; omega : ¬h + j + 1 ≤ padicValNat p n.natAbs),
        if_neg (by dsimp [m, d] at *; omega : ¬h + j ≤ padicValNat p n.natAbs), zero_mul]
    unfold positiveLocalTail
    rw [tsum_eq_sum hcut, sum_range_succ]
    have hmain : (∑ j ∈ range d, ramanujan (p ^ (h + j + 1)) n * X ^ (h + j + 1)) =
        (((p : ℂ) - 1) * X * ((p : ℂ) * X) ^ h) *
          ∑ j ∈ range d, ((p : ℂ) * X) ^ j := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      have hjd : j < d := mem_range.mp hj
      have hfull : h + j + 1 ≤ padicValNat p n.natAbs := by dsimp [d, m] at *; omega
      rw [coefficient_succ_eq hp hn (h + j), if_pos hfull]
      simp only [pow_add, pow_succ, mul_pow]
      ring
    have hlast : ramanujan (p ^ (h + d + 1)) n * X ^ (h + d + 1) =
        -(p : ℂ) ^ m * X ^ (m + 1) := by
      rw [hhd, coefficient_succ_eq hp hn m]
      simp only [m, if_neg (Nat.not_succ_le_self _), if_pos le_rfl]
    rw [hmain, hlast]
    dsimp [d, m]
    ring
  · rw [if_neg hh]
    unfold positiveLocalTail
    apply tsum_eq_zero
    intro j
    rw [coefficient_succ_eq hp hn (h + j)]
    simp only [if_neg (by dsimp [m] at hh; omega : ¬h + j + 1 ≤ padicValNat p n.natAbs),
      if_neg (by dsimp [m] at hh; omega : ¬h + j ≤ padicValNat p n.natAbs), zero_mul]

/-- Explicit finite local factor at a nonzero frequency. -/
def nonzeroLocalPolynomial (p m e : ℕ) (X : ℂ) : ℂ :=
  if e = 0 then
    1 + ((p : ℂ) - 1) * X * (∑ j ∈ range m, ((p : ℂ) * X) ^ j) -
      (p : ℂ) ^ m * X ^ (m + 1)
  else if e - 1 ≤ m then
    ((p : ℂ) - 1) * X * ((p : ℂ) * X) ^ (e - 1) *
      (∑ j ∈ range (m - (e - 1)), ((p : ℂ) * X) ^ j) -
      (p : ℂ) ^ m * X ^ (m + 1)
  else 0

private theorem localTail_succ (p : ℕ) (n : ℤ) (h : ℕ) (X : ℂ) :
    localTail p n (h + 1) X = positiveLocalTail p n h X := by
  unfold localTail positiveLocalTail
  apply tsum_congr
  intro j
  have he : j + (h + 1) = h + j + 1 := by omega
  rw [he]

private theorem localTail_zero_of_positive_summable (p : ℕ) (n : ℤ) (X : ℂ)
    (hs : Summable (fun j : ℕ => ramanujan (p ^ (j + 1)) n * X ^ (j + 1))) :
    localTail p n 0 X = 1 + positiveLocalTail p n 0 X := by
  have h := tsum_eq_zero_add' (f := fun k : ℕ => ramanujan (p ^ k) n * X ^ k) hs
  simpa only [localTail, positiveLocalTail, Nat.add_zero, Nat.zero_add, pow_zero,
    ramanujan_modulus_one, mul_one] using h

theorem localTail_nonzero_eq_polynomial {p : ℕ} (hp : p.Prime)
    {n : ℤ} (hn : n ≠ 0) (e : ℕ) (X : ℂ) :
    localTail p n e X = nonzeroLocalPolynomial p (padicValNat p n.natAbs) e X := by
  cases e with
  | zero =>
    have hs := positiveLocalTail_summable_nonzero hp hn 0 X
    rw [localTail_zero_of_positive_summable p n X (by simpa only [Nat.zero_add] using hs),
      positiveLocalTail_nonzero_eq hp hn 0 X]
    simp only [nonzeroLocalPolynomial, if_pos rfl, Nat.zero_le, if_true,
      pow_zero, mul_one, Nat.sub_zero]
    ring
  | succ h =>
    rw [localTail_succ, positiveLocalTail_nonzero_eq hp hn h X]
    simp only [nonzeroLocalPolynomial, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]

/-- Closed finite-geometric form when the ratio is not one. The preceding
polynomial formula also covers the ratio-one case without division. -/
theorem positiveLocalTail_nonzero_geometric_closed {p : ℕ} (hp : p.Prime)
    {n : ℤ} (hn : n ≠ 0) (h : ℕ) (X : ℂ) (hne : (p : ℂ) * X ≠ 1) :
    positiveLocalTail p n h X =
      if h ≤ padicValNat p n.natAbs then
        ((p : ℂ) - 1) * X * ((p : ℂ) * X) ^ h *
          ((((p : ℂ) * X) ^ (padicValNat p n.natAbs - h) - 1) / ((p : ℂ) * X - 1)) -
          (p : ℂ) ^ padicValNat p n.natAbs * X ^ (padicValNat p n.natAbs + 1)
      else 0 := by
  rw [positiveLocalTail_nonzero_eq hp hn h X]
  split_ifs with hh
  · rw [geom_sum_eq hne]
  · rfl

/-- At zero frequency the positive tail is the actual totient geometric
series. It is infinite, unlike every nonzero-frequency tail. -/
theorem positiveLocalTail_zero_eq {p : ℕ} (hp : p.Prime)
    (h : ℕ) (X : ℂ) (hratio : ‖(p : ℂ) * X‖ < 1) :
    positiveLocalTail p 0 h X =
      (((p : ℂ) - 1) * X * ((p : ℂ) * X) ^ h) * (1 - (p : ℂ) * X)⁻¹ := by
  have hterm (j : ℕ) : ramanujan (p ^ (h + j + 1)) 0 * X ^ (h + j + 1) =
      (((p : ℂ) - 1) * X * ((p : ℂ) * X) ^ h) * ((p : ℂ) * X) ^ j := by
    rw [ramanujan_prime_pow_values hp (h + j) 0]
    simp only [dvd_zero, if_true, Nat.cast_pow, pow_add, pow_succ, mul_pow]
    ring
  unfold positiveLocalTail
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hratio]

theorem positiveLocalTail_summable_zero {p : ℕ} (hp : p.Prime)
    (h : ℕ) (X : ℂ) (hratio : ‖(p : ℂ) * X‖ < 1) :
    Summable (fun j : ℕ => ramanujan (p ^ (h + j + 1)) 0 * X ^ (h + j + 1)) := by
  apply (((summable_geometric_of_norm_lt_one hratio).mul_left
    (((p : ℂ) - 1) * X * ((p : ℂ) * X) ^ h))).congr
  intro j
  rw [ramanujan_prime_pow_values hp (h + j) 0]
  simp only [dvd_zero, if_true, Nat.cast_pow, pow_add, pow_succ, mul_pow]
  ring

/-- Exact rational local factor at zero frequency, with the level cutoff. -/
def zeroLocalRational (p e : ℕ) (X : ℂ) : ℂ :=
  if e = 0 then (1 - X) / (1 - (p : ℂ) * X)
  else (((p : ℂ) - 1) * X * ((p : ℂ) * X) ^ (e - 1)) / (1 - (p : ℂ) * X)

theorem localTail_zero_eq_rational {p : ℕ} (hp : p.Prime)
    (e : ℕ) (X : ℂ) (hratio : ‖(p : ℂ) * X‖ < 1) :
    localTail p 0 e X = zeroLocalRational p e X := by
  have hne : (p : ℂ) * X ≠ 1 := by
    intro h
    simpa only [h, norm_one, lt_self_iff_false] using hratio
  have hden : 1 - (p : ℂ) * X ≠ 0 := sub_ne_zero.mpr hne.symm
  cases e with
  | zero =>
    have hs := positiveLocalTail_summable_zero hp 0 X hratio
    rw [localTail_zero_of_positive_summable p 0 X (by simpa only [Nat.zero_add] using hs),
      positiveLocalTail_zero_eq hp 0 X hratio]
    simp only [zeroLocalRational, if_pos rfl, pow_zero, mul_one]
    field_simp [hden]
    ring
  | succ h =>
    rw [localTail_succ, positiveLocalTail_zero_eq hp h X hratio]
    simp only [zeroLocalRational, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, div_eq_mul_inv]

/-- Actual full local coefficient summability. The nonzero frequency case
has finite support; only the zero-frequency case needs a geometric ratio. -/
theorem local_coefficient_summable {p : ℕ} (hp : p.Prime)
    (n : ℤ) (X : ℂ) (hratio : ‖(p : ℂ) * X‖ < 1) :
    Summable (fun k : ℕ => ramanujan (p ^ k) n * X ^ k) := by
  apply (summable_nat_add_iff 1).mp
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.zero_add] using positiveLocalTail_summable_zero hp 0 X hratio
  · simpa only [Nat.zero_add] using positiveLocalTail_summable_nonzero hp hn 0 X

/-- The exact finite local level correction. Every summability hypothesis
is discharged from the actual Ramanujan coefficients above. -/
theorem localTail_finite_correction {p : ℕ} (hp : p.Prime)
    (n : ℤ) (e : ℕ) (X : ℂ) (hratio : ‖(p : ℂ) * X‖ < 1) :
    localTail p n e X = localTail p n 0 X -
      ∑ k ∈ range e, ramanujan (p ^ k) n * X ^ k := by
  have h := (local_coefficient_summable hp n X hratio).sum_add_tsum_nat_add e
  apply (eq_sub_iff_add_eq).mpr
  simpa only [localTail, Nat.add_zero, add_comm] using h

/-- The genuine local Dirichlet ratio p^(-w), written without a branch
choice because p is a positive real prime. -/
def primeRatio (p : ℕ) (w : ℂ) : ℂ :=
  Complex.exp (-w * (Real.log (p : ℝ) : ℂ))

theorem primeRatio_pow (p : ℕ) (w : ℂ) (k : ℕ) :
    primeRatio p w ^ k = Complex.exp (-(k : ℂ) * w * (Real.log (p : ℝ) : ℂ)) := by
  unfold primeRatio
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem norm_prime_mul_primeRatio_lt_one {p : ℕ} (hp : p.Prime)
    (w : ℂ) (hw : 1 < w.re) : ‖(p : ℂ) * primeRatio p w‖ < 1 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hpR
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  have hpnorm : ‖(p : ℂ)‖ = (p : ℝ) := by simp
  rw [norm_mul, hpnorm, primeRatio, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  rw [show (p : ℝ) = Real.exp (Real.log (p : ℝ)) from (Real.exp_log hp0).symm,
    ← Real.exp_add, ← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  have hneg : (1 - w.re) * Real.log (p : ℝ) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hlog
  nlinarith

/-- Exact bridge to the literal restricted Dirichlet summands. At a
positive level N take e=padicValNat p N. -/
theorem localTail_primeRatio_eq_actual (p : ℕ) (n : ℤ) (e : ℕ) (w : ℂ) :
    localTail p n e (primeRatio p w) =
      ∑' j : ℕ, ramanujan (p ^ (j + e)) n *
        Complex.exp (-((j + e : ℕ) : ℂ) * w * (Real.log (p : ℝ) : ℂ)) := by
  unfold localTail
  apply tsum_congr
  intro j
  rw [primeRatio_pow]

/-- Actual zero-frequency level-local factor, with geometric convergence
proved directly from Re(w)>1 rather than assumed. -/
theorem localTail_zero_primeRatio {p : ℕ} (hp : p.Prime)
    (N : ℕ) (w : ℂ) (hw : 1 < w.re) :
    localTail p 0 (padicValNat p N) (primeRatio p w) =
      zeroLocalRational p (padicValNat p N) (primeRatio p w) :=
  localTail_zero_eq_rational hp _ _ (norm_prime_mul_primeRatio_lt_one hp w hw)

/-- Actual nonzero-frequency level-local factor is a finite polynomial
for every complex parameter; no global Dirichlet/Euler identity is used. -/
theorem localTail_nonzero_primeRatio {p : ℕ} (hp : p.Prime)
    {n : ℤ} (hn : n ≠ 0) (N : ℕ) (w : ℂ) :
    localTail p n (padicValNat p N) (primeRatio p w) =
      nonzeroLocalPolynomial p (padicValNat p n.natAbs) (padicValNat p N) (primeRatio p w) :=
  localTail_nonzero_eq_polynomial hp hn _ _

/-- Actual positive-level correction at e=v_p(N), with the analytic
geometric condition proved from the genuine complex Dirichlet parameter. -/
theorem levelLocal_primeRatio_finite_correction {p : ℕ} (hp : p.Prime)
    (N : ℕ) (n : ℤ) (w : ℂ) (hw : 1 < w.re) :
    localTail p n (padicValNat p N) (primeRatio p w) =
      localTail p n 0 (primeRatio p w) -
        ∑ k ∈ range (padicValNat p N), ramanujan (p ^ k) n * primeRatio p w ^ k :=
  localTail_finite_correction hp n _ _ (norm_prime_mul_primeRatio_lt_one hp w hw)
end

end ImbalancedChen.Part3.ActualLevelDirichletFactors