import ImbalancedChen.Part3ActualRamanujanFiniteLevelEulerSplit
import ImbalancedChen.Part3ActualTotientDirichletSeries
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

/-!
# Actual initial-domain level Ramanujan zeta factors

SOURCE ONLY / UNCOMPILED / ZERO PROOF CREDIT (2026-10-25).

The full local factor is (1-X)/(1-pX) at zero frequency and
(1-X)*sum_(j<=v_p(|n|))(pX)^j at nonzero frequency. For the actual
Dirichlet ratio X=p^(-w), Re(w)>1 proves |pX|<1 and |X|<1; the finite
geometric sum is genuinely nonzero. Thus every division used below has a
proved nonzero denominator on the initial convergence domain.

The actual finite-prime extraction identity supplies the coprime-complement
series as the full actual series divided by this nonzero finite product.
The already-proved actual Ramanujan/totient zeta formulas then yield exact
coprime and restricted-level formulas: Re(w)>1 at nonzero frequency and
Re(w)>2 at zero frequency. No continuation or pole cancellation outside
these domains is asserted.
-/

namespace ImbalancedChen.Part3.ActualRamanujanLevelZetaFactors

noncomputable section

open Set Finset Complex
open scoped BigOperators
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode
open ImbalancedChen.Part3.ActualLevelDirichletFactors
open ImbalancedChen.Part3.ActualRamanujanSinglePrimeLevelSplit
open ImbalancedChen.Part3.ActualRamanujanFiniteLevelEulerSplit
open ImbalancedChen.Part3ActualRamanujanDirichletSeries
open ImbalancedChen.Part3.ActualTotientDirichletSeries

/-- The genuine local ratios lie strictly in both required unit disks. -/
theorem prime_ratio_norm_bounds {p : ℕ} (hp : p.Prime) (w : ℂ) (hw : 1 < w.re) :
    ‖(p : ℂ) * ((p : ℂ) ^ (-w))‖ < 1 ∧ ‖(p : ℂ) ^ (-w)‖ < 1 := by
  have hr : ‖(p : ℂ) * ((p : ℂ) ^ (-w))‖ < 1 := by
    rw [prime_cpow_eq_primeRatio hp w]
    exact norm_prime_mul_primeRatio_lt_one hp w hw
  refine ⟨hr, ?_⟩
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hpnorm : ‖(p : ℂ)‖ = (p : ℝ) := by simp
  calc
    ‖(p : ℂ) ^ (-w)‖ ≤ (p : ℝ) * ‖(p : ℂ) ^ (-w)‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp1 (norm_nonneg _)
    _ = ‖(p : ℂ) * ((p : ℂ) ^ (-w))‖ := by rw [norm_mul, hpnorm]
    _ < 1 := hr

private theorem one_sub_ne_zero_of_norm_lt_one {x : ℂ} (hx : ‖x‖ < 1) : 1 - x ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  simpa only [← h, norm_one, lt_self_iff_false] using hx

/-- A finite geometric sum of positive length is nonzero inside the unit disk. -/
theorem finite_geom_ne_zero_of_norm_lt_one {r : ℂ} (hr : ‖r‖ < 1) (m : ℕ) :
    (∑ j ∈ range (m + 1), r ^ j) ≠ 0 := by
  have hr1 : r ≠ 1 := by
    intro h
    simpa only [h, norm_one, lt_self_iff_false] using hr
  have hp : r ^ (m + 1) ≠ 1 := by
    intro h
    have hnorm : ‖r ^ (m + 1)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg r) hr (Nat.succ_ne_zero m)
    simpa only [h, norm_one, lt_self_iff_false] using hnorm
  rw [geom_sum_eq hr1]
  exact div_ne_zero (sub_ne_zero.mpr hp) (sub_ne_zero.mpr hr1)

/-- Exact full local factor at nonzero frequency; the boundary term from
the actual Ramanujan evaluation is retained and cancels algebraically. -/
theorem full_localTail_nonzero_factor {p : ℕ} (hp : p.Prime)
    {n : ℤ} (hn : n ≠ 0) (X : ℂ) :
    localTail p n 0 X = (1 - X) *
      ∑ j ∈ range (padicValNat p n.natAbs + 1), ((p : ℂ) * X) ^ j := by
  rw [localTail_nonzero_eq_polynomial hp hn 0 X]
  simp only [nonzeroLocalPolynomial, if_pos rfl, sum_range_succ]
  have hboundary : (p : ℂ) ^ padicValNat p n.natAbs * X ^ (padicValNat p n.natAbs + 1) =
      X * ((p : ℂ) * X) ^ padicValNat p n.natAbs := by
    rw [mul_pow, pow_succ]
    ring
  rw [hboundary]
  have hgeom := geom_sum_mul ((p : ℂ) * X) (padicValNat p n.natAbs)
  linear_combination hgeom

/-- Every full actual local factor is genuinely nonzero for Re(w)>1.
The full zero-frequency global series still requires Re(w)>2 below. -/
theorem full_localTail_nonzero {p : ℕ} (hp : p.Prime)
    (n : ℤ) (w : ℂ) (hw : 1 < w.re) : localTail p n 0 ((p : ℂ) ^ (-w)) ≠ 0 := by
  obtain ⟨hr, hX⟩ := prime_ratio_norm_bounds hp w hw
  have hnum : 1 - (p : ℂ) ^ (-w) ≠ 0 := one_sub_ne_zero_of_norm_lt_one hX
  by_cases hn : n = 0
  · subst n
    rw [localTail_zero_eq_rational hp 0 _ hr, zeroLocalRational, if_pos rfl]
    exact div_ne_zero hnum (one_sub_ne_zero_of_norm_lt_one hr)
  · rw [full_localTail_nonzero_factor hp hn]
    exact mul_ne_zero hnum (finite_geom_ne_zero_of_norm_lt_one hr _)

/-- The local zero-frequency correction is the precise elementary
scattering factor; both cancelled denominators are proved nonzero. -/
theorem zero_localCorrection_succ {p : ℕ} (hp : p.Prime)
    (e : ℕ) (w : ℂ) (hw : 1 < w.re) :
    localTail p 0 (e + 1) ((p : ℂ) ^ (-w)) / localTail p 0 0 ((p : ℂ) ^ (-w)) =
      (((p : ℂ) - 1) * ((p : ℂ) ^ (-w)) *
        ((p : ℂ) * ((p : ℂ) ^ (-w))) ^ e) / (1 - (p : ℂ) ^ (-w)) := by
  obtain ⟨hr, hX⟩ := prime_ratio_norm_bounds hp w hw
  have hden : 1 - (p : ℂ) * ((p : ℂ) ^ (-w)) ≠ 0 := one_sub_ne_zero_of_norm_lt_one hr
  have hnum : 1 - (p : ℂ) ^ (-w) ≠ 0 := one_sub_ne_zero_of_norm_lt_one hX
  rw [localTail_zero_eq_rational hp (e + 1) _ hr, localTail_zero_eq_rational hp 0 _ hr]
  simp only [zeroLocalRational, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
    Nat.add_sub_cancel, if_pos rfl]
  field_simp [hden, hnum] <;> ring

/-- The full local factors associated to the finite level-prime set. -/
def fullLocalProduct (N : ℕ) (n : ℤ) (w : ℂ) : ℂ :=
  ∏ p ∈ N.primeFactors, localTail p n 0 ((p : ℂ) ^ (-w))

/-- The finite level correction, only divided on the proved initial domain. -/
def localCorrectionProduct (N : ℕ) (n : ℤ) (w : ℂ) : ℂ :=
  ∏ p ∈ N.primeFactors,
    localTail p n (padicValNat p N) ((p : ℂ) ^ (-w)) / localTail p n 0 ((p : ℂ) ^ (-w))

theorem fullLocalProduct_ne_zero (N : ℕ) (n : ℤ) (w : ℂ) (hw : 1 < w.re) :
    fullLocalProduct N n w ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact full_localTail_nonzero (Nat.prime_of_mem_primeFactors hp) n w hw

/-- The true full series splits into full local factors and the actual
coprime complement by the earlier finite extraction theorem at exponent zero. -/
theorem fullSeries_eq_localProduct_mul_coprimeSeries
    (N : ℕ) (hN : N ≠ 0) (n : ℤ) (w : ℂ)
    (hw : (if n = 0 then (2 : ℝ) else 1) < w.re) :
    restrictedSeries 1 n w = fullLocalProduct N n w * coprimeSeries N n w := by
  have h := excludedSeries_finite_prime_extraction (fun _ => 0) n w hw
    N.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp) ∅ (by simp) (by simp)
  simpa only [pow_zero, prod_const_one, excludedSeries_empty, empty_union,
    excludedSeries_primeFactors_one N hN n w, fullLocalProduct] using h

/-- Division is performed only after the finite local product has been
proved nonzero on the actual convergence domain. -/
theorem coprimeSeries_eq_full_div_localProduct
    (N : ℕ) (hN : N ≠ 0) (n : ℤ) (w : ℂ)
    (hw : (if n = 0 then (2 : ℝ) else 1) < w.re) :
    coprimeSeries N n w = restrictedSeries 1 n w / fullLocalProduct N n w := by
  have hw1 : 1 < w.re := by
    by_cases hn : n = 0
    · have hw2 : 2 < w.re := by simpa only [if_pos hn] using hw
      linarith
    · exact by simpa only [if_neg hn] using hw
  apply (eq_div_iff (fullLocalProduct_ne_zero N n w hw1)).mpr
  simpa only [mul_comm] using (fullSeries_eq_localProduct_mul_coprimeSeries N hN n w hw).symm

/-- Exact restricted-level correction in terms of the actual full series. -/
theorem restrictedSeries_eq_full_mul_localCorrection
    (N : ℕ) (hN : N ≠ 0) (n : ℤ) (w : ℂ)
    (hw : (if n = 0 then (2 : ℝ) else 1) < w.re) :
    restrictedSeries N n w = restrictedSeries 1 n w * localCorrectionProduct N n w := by
  rw [restrictedSeries_finite_level_product N hN n w hw,
    coprimeSeries_eq_full_div_localProduct N hN n w hw]
  unfold localCorrectionProduct fullLocalProduct
  rw [prod_div_distrib]
  ring

/-- Literal full nonzero-frequency series equals its already-proved
actual divisor-factor / zeta quotient. -/
theorem fullSeries_nonzero_zeta_formula (n : ℤ) (hn : n ≠ 0) (w : ℂ) (hw : 1 < w.re) :
    restrictedSeries 1 n w = divisorFactor n.natAbs w / riemannZeta w := by
  calc
    _ = LSeries (fun c : ℕ => ramanujan c n) w := by
      unfold restrictedSeries LSeries
      apply tsum_congr
      intro c
      rw [if_pos (one_dvd c)]
      have hzero : ramanujan 0 n = 0 := by simp [ramanujan, kloosterman]
      exact (LSeries.term_def₀ hzero w c).symm
    _ = _ := ramanujan_LSeries_eq_divisorFactor_div_zeta n hn hw

private theorem ramanujan_zero_eq_totientCoeff (c : ℕ) : ramanujan c 0 = totientCoeff c := by
  by_cases hc : c = 0
  · subst c
    simp [ramanujan, kloosterman, totientCoeff]
  · letI : NeZero c := ⟨hc⟩
    exact ramanujan_at_zero

/-- Literal full zero-frequency series equals the actual totient zeta quotient. -/
theorem fullSeries_zero_zeta_formula (w : ℂ) (hw : 2 < w.re) :
    restrictedSeries 1 0 w = riemannZeta (w - 1) / riemannZeta w := by
  calc
    _ = LSeries totientCoeff w := by
      unfold restrictedSeries LSeries
      apply tsum_congr
      intro c
      rw [if_pos (one_dvd c), LSeries.term_def₀ totientCoeff_zero]
      unfold actualTerm
      rw [ramanujan_zero_eq_totientCoeff]
    _ = _ := totient_LSeries_eq_zeta_quotient hw

theorem coprimeSeries_nonzero_zeta_formula
    (N : ℕ) (hN : N ≠ 0) (n : ℤ) (hn : n ≠ 0) (w : ℂ) (hw : 1 < w.re) :
    coprimeSeries N n w =
      (divisorFactor n.natAbs w / riemannZeta w) / fullLocalProduct N n w := by
  rw [coprimeSeries_eq_full_div_localProduct N hN n w (by simpa only [if_neg hn] using hw),
    fullSeries_nonzero_zeta_formula n hn w hw]

theorem coprimeSeries_zero_zeta_formula
    (N : ℕ) (hN : N ≠ 0) (w : ℂ) (hw : 2 < w.re) :
    coprimeSeries N 0 w =
      (riemannZeta (w - 1) / riemannZeta w) / fullLocalProduct N 0 w := by
  rw [coprimeSeries_eq_full_div_localProduct N hN 0 w (by simpa only [if_pos rfl] using hw),
    fullSeries_zero_zeta_formula w hw]

theorem restrictedSeries_nonzero_zeta_formula
    (N : ℕ) (hN : N ≠ 0) (n : ℤ) (hn : n ≠ 0) (w : ℂ) (hw : 1 < w.re) :
    restrictedSeries N n w =
      (divisorFactor n.natAbs w / riemannZeta w) * localCorrectionProduct N n w := by
  rw [restrictedSeries_eq_full_mul_localCorrection N hN n w (by simpa only [if_neg hn] using hw),
    fullSeries_nonzero_zeta_formula n hn w hw]

theorem restrictedSeries_zero_zeta_formula
    (N : ℕ) (hN : N ≠ 0) (w : ℂ) (hw : 2 < w.re) :
    restrictedSeries N 0 w =
      (riemannZeta (w - 1) / riemannZeta w) * localCorrectionProduct N 0 w := by
  rw [restrictedSeries_eq_full_mul_localCorrection N hN 0 w (by simpa only [if_pos rfl] using hw),
    fullSeries_zero_zeta_formula w hw]

end

end ImbalancedChen.Part3.ActualRamanujanLevelZetaFactors