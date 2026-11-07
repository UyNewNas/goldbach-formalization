import ImbalancedChen.Part3ActualLevelDirichletFactors
import ImbalancedChen.Part3ActualRamanujanDirichletSeries
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

/-!
# Actual single-prime extraction from a level-restricted Ramanujan Dirichlet series

SOURCE ONLY / UNCOMPILED / ZERO PROOF CREDIT (2026-10-25).

A proved integer bijection decomposes each nonzero multiple of p^e
uniquely as p^(j+e)*m with p coprime to m. The actual Ramanujan coefficient
and the genuine complex Dirichlet power multiply under this decomposition.
All relevant series and the double product series are absolutely convergent:
Re(w)>1 for nonzero frequency and Re(w)>2 at zero frequency.

For p coprime to M, the literal restriction p^e*M divides c becomes exactly
M divides m in the coprime complement. This proves one genuine extraction
step for every positive level N, with e=N.factorization p and complementary
level ordCompl[p] N. No local factor is divided out, so zeros cause no loss.
The full finite-prime iteration is not assumed or asserted in this module.
-/

namespace ImbalancedChen.Part3.ActualRamanujanSinglePrimeLevelSplit

noncomputable section

open Set Finset Complex
open scoped BigOperators
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode
open ImbalancedChen.Part3.RamanujanMultiplicativeGcdBound20261025a
open ImbalancedChen.Part3ActualRamanujanDirichletSeries
open ImbalancedChen.Part3.ActualLevelDirichletFactors

/-- The actual arithmetic Dirichlet summand, with its true zero at c=0. -/
def actualTerm (n : ℤ) (w : ℂ) (c : ℕ) : ℂ := ramanujan c n * (c : ℂ) ^ (-w)

@[simp] theorem actualTerm_zero (n : ℤ) (w : ℂ) : actualTerm n w 0 = 0 := by
  simp [actualTerm, ramanujan, kloosterman]

/-- This bound supplies the zero-frequency convergence range directly
from the actual gcd estimate, independently of a zeta quotient identity. -/
theorem actualTerm_norm_summable_above_two (n : ℤ) (w : ℂ) (hw : 2 < w.re) :
    Summable (fun c : ℕ => ‖actualTerm n w c‖) := by
  have hL : LSeriesSummable (fun c : ℕ => ramanujan c n) w := by
    apply LSeriesSummable_of_le_const_mul_rpow (x := 2) hw
    refine ⟨1, ?_⟩
    intro c hc
    have hbound : ‖ramanujan c n‖ ≤ (c : ℝ) :=
      (norm_ramanujan_le_gcd c n).trans (by
        exact_mod_cast Nat.gcd_le_left n.natAbs (Nat.pos_of_ne_zero hc))
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, one_mul] using hbound
  have hzero : ramanujan 0 n = 0 := by simp [ramanujan, kloosterman]
  have hraw : Summable (actualTerm n w) :=
    hL.congr (fun c => LSeries.term_def₀ hzero w c)
  exact summable_norm_iff.mpr hraw

/-- Both actual frequency ranges are supplied without a convergence input. -/
theorem actualTerm_norm_summable (n : ℤ) (w : ℂ)
    (hw : (if n = 0 then (2 : ℝ) else 1) < w.re) :
    Summable (fun c : ℕ => ‖actualTerm n w c‖) := by
  by_cases hn : n = 0
  · exact actualTerm_norm_summable_above_two n w (by simpa only [if_pos hn] using hw)
  · exact ramanujan_power_norm_summable n hn (by simpa only [if_neg hn] using hw)

/-- CRT multiplicativity and multiplicativity of positive real complex
powers combine for the actual signed summand. -/
theorem actualTerm_mul_of_coprime (n : ℤ) (w : ℂ) {a b : ℕ} (hab : a.Coprime b) :
    actualTerm n w (a * b) = actualTerm n w a * actualTerm n w b := by
  simp only [actualTerm, ramanujan_coprime_mul hab n, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow]
  ring

theorem actualTerm_prime_power (n : ℤ) (w : ℂ) (p k : ℕ) :
    actualTerm n w (p ^ k) = ramanujan (p ^ k) n * ((p : ℂ) ^ (-w)) ^ k := by
  unfold actualTerm
  rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul p k (-w), Complex.cpow_nat_mul]

/-- The local cpow ratio is exactly the previously defined exponential
Dirichlet ratio; positivity of the actual prime fixes the logarithm. -/
theorem prime_cpow_eq_primeRatio {p : ℕ} (hp : p.Prime) (w : ℂ) :
    (p : ℂ) ^ (-w) = primeRatio p w := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hp.ne_zero),
    primeRatio, ← Complex.natCast_log]
  congr 1
  ring

abbrev PrimeComplement (p : ℕ) := {m : ℕ // p.Coprime m}
abbrev PrimePowerCarrier (p e : ℕ) := {c : ℕ // c ≠ 0 ∧ p ^ e ∣ c}

private theorem complement_ne_zero {p : ℕ} (hp : p.Prime) (m : PrimeComplement p) :
    m.1 ≠ 0 := by
  have hnot : ¬p ∣ m.1 := hp.coprime_iff_not_dvd.mp m.2
  intro hm
  rw [hm] at hnot
  exact hnot (dvd_zero p)

theorem primePowerComplement_factorization {p : ℕ} (hp : p.Prime)
    (k : ℕ) (m : PrimeComplement p) : (p ^ k * m.1).factorization p = k := by
  rw [Nat.factorization_mul (pow_ne_zero k hp.ne_zero) (complement_ne_zero hp m),
    Finsupp.add_apply, Nat.factorization_pow_self hp,
    Nat.factorization_eq_zero_of_not_dvd (hp.coprime_iff_not_dvd.mp m.2), add_zero]

/-- Actual unique factorization at the prime p, including a prescribed
minimum exponent e. There are no duplicated or omitted positive integers. -/
def primePowerLevelEquiv {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (ℕ × PrimeComplement p) ≃ PrimePowerCarrier p e where
  toFun t := ⟨p ^ (t.1 + e) * t.2.1,
    mul_ne_zero (pow_ne_zero _ hp.ne_zero) (complement_ne_zero hp t.2),
    dvd_trans (pow_dvd_pow p (by omega : e ≤ t.1 + e)) (dvd_mul_right _ _)⟩
  invFun c := (c.1.factorization p - e,
    ⟨c.1 / p ^ (c.1.factorization p), Nat.coprime_ordCompl hp c.2.1⟩)
  left_inv := by
    rintro ⟨j, m⟩
    apply Prod.ext
    · change (p ^ (j + e) * m.1).factorization p - e = j
      rw [primePowerComplement_factorization hp (j + e) m, Nat.add_sub_cancel]
    · apply Subtype.ext
      change (p ^ (j + e) * m.1) / p ^ ((p ^ (j + e) * m.1).factorization p) = m.1
      exact Nat.ordCompl_pow_mul_of_not_dvd (j + e) hp (hp.coprime_iff_not_dvd.mp m.2)
  right_inv := by
    intro c
    apply Subtype.ext
    change p ^ ((c.1.factorization p - e) + e) * (c.1 / p ^ (c.1.factorization p)) = c.1
    have he : e ≤ c.1.factorization p := (hp.pow_dvd_iff_le_factorization c.2.1).mp c.2.2
    rw [Nat.sub_add_cancel he]
    exact Nat.ordProj_mul_ordCompl_eq_self c.1 p

@[simp] theorem primePowerLevelEquiv_value {p : ℕ} (hp : p.Prime)
    (e : ℕ) (t : ℕ × PrimeComplement p) :
    ((primePowerLevelEquiv hp e) t).1 = p ^ (t.1 + e) * t.2.1 := rfl

/-- The remaining level condition transports to the actual coprime
complement under the explicit integer bijection. -/
theorem level_constraint_iff {p M : ℕ} (hp : p.Prime) (hM : p.Coprime M)
    (e j : ℕ) (m : PrimeComplement p) :
    p ^ e * M ∣ p ^ (j + e) * m.1 ↔ M ∣ m.1 := by
  have heq : p ^ (j + e) * m.1 = p ^ e * (p ^ j * m.1) := by rw [pow_add]; ring
  rw [heq, Nat.mul_dvd_mul_iff_left (pow_pos hp.pos e)]
  exact (hM.symm.pow_right j).dvd_mul_left

/-- The actual series on multiples of a given level. -/
def restrictedSeries (N : ℕ) (n : ℤ) (w : ℂ) : ℂ :=
  ∑' c : ℕ, if N ∣ c then actualTerm n w c else 0

/-- The actual remaining-level series on integers coprime to p. -/
def coprimeComplementSeries (p M : ℕ) (n : ℤ) (w : ℂ) : ℂ :=
  ∑' m : PrimeComplement p, if M ∣ m.1 then actualTerm n w m.1 else 0

theorem restrictedSeries_norm_summable (N : ℕ) (n : ℤ) (w : ℂ)
    (hw : (if n = 0 then (2 : ℝ) else 1) < w.re) :
    Summable (fun c : ℕ => ‖if N ∣ c then actualTerm n w c else 0‖) := by
  apply (actualTerm_norm_summable n w hw).of_nonneg_of_le (fun c => norm_nonneg _) ?_
  intro c
  split_ifs <;> simp only [norm_zero, le_rfl, norm_nonneg]

/-- A genuine one-prime finite Euler modification, retaining the entire
remaining level M. No full local factor is divided out. -/
theorem restrictedSeries_single_prime_split {p M : ℕ} (hp : p.Prime) (hM : p.Coprime M)
    (e : ℕ) (n : ℤ) (w : ℂ) (hw : (if n = 0 then (2 : ℝ) else 1) < w.re) :
    restrictedSeries (p ^ e * M) n w =
      localTail p n e ((p : ℂ) ^ (-w)) * coprimeComplementSeries p M n w := by
  classical
  let F : ℕ → ℂ := fun c => if p ^ e * M ∣ c then actualTerm n w c else 0
  have hsupport : Function.support F ⊆ {c : ℕ | c ≠ 0 ∧ p ^ e ∣ c} := by
    intro c hc
    have hc0 : c ≠ 0 := by
      intro hzero
      apply hc
      simp [F, hzero]
    have hd : p ^ e * M ∣ c := by
      by_contra hd
      exact hc (by simp only [F, if_neg hd])
    exact ⟨hc0, dvd_trans (dvd_mul_right (p ^ e) M) hd⟩
  have hraw := actualTerm_norm_summable n w hw
  have hlocal : Summable (fun j : ℕ => ‖actualTerm n w (p ^ (j + e))‖) :=
    hraw.comp_injective (fun a b hab => Nat.add_right_cancel ((Nat.pow_right_injective hp.one_lt) hab))
  have hcomplement : Summable (fun m : PrimeComplement p =>
      ‖if M ∣ m.1 then actualTerm n w m.1 else 0‖) := by
    apply (hraw.subtype (fun m : ℕ => p.Coprime m)).of_nonneg_of_le (fun m => norm_nonneg _) ?_
    intro m
    split_ifs <;> simp only [norm_zero, le_rfl, norm_nonneg]
  have hsub : (∑' c : PrimePowerCarrier p e, F c.1) = ∑' c : ℕ, F c :=
    tsum_subtype_eq_of_support_subset hsupport
  calc
    _ = ∑' c : PrimePowerCarrier p e, F c.1 := hsub.symm
    _ = ∑' t : ℕ × PrimeComplement p, F ((primePowerLevelEquiv hp e) t).1 :=
      ((primePowerLevelEquiv hp e).tsum_eq (fun c : PrimePowerCarrier p e => F c.1)).symm
    _ = ∑' t : ℕ × PrimeComplement p,
        actualTerm n w (p ^ (t.1 + e)) *
          (if M ∣ t.2.1 then actualTerm n w t.2.1 else 0) := by
      apply tsum_congr
      intro t
      rw [primePowerLevelEquiv_value]
      dsimp only [F]
      rw [level_constraint_iff hp hM e t.1 t.2]
      by_cases hm : M ∣ t.2.1
      · rw [if_pos hm, if_pos hm]
        exact actualTerm_mul_of_coprime n w (t.2.2.pow_left (t.1 + e))
      · simp only [if_neg hm, mul_zero]
    _ = (∑' j : ℕ, actualTerm n w (p ^ (j + e))) *
        (∑' m : PrimeComplement p, if M ∣ m.1 then actualTerm n w m.1 else 0) :=
      (tsum_mul_tsum_of_summable_norm hlocal hcomplement).symm
    _ = localTail p n e ((p : ℂ) ^ (-w)) * coprimeComplementSeries p M n w := by
      congr 1
      unfold localTail
      apply tsum_congr
      intro j
      exact actualTerm_prime_power n w p (j + e)

/-- The unrestricted coprime-complement split at a pure prime-power level. -/
theorem restrictedSeries_prime_power_split {p : ℕ} (hp : p.Prime)
    (e : ℕ) (n : ℤ) (w : ℂ) (hw : (if n = 0 then (2 : ℝ) else 1) < w.re) :
    restrictedSeries (p ^ e) n w =
      localTail p n e ((p : ℂ) ^ (-w)) *
        (∑' m : PrimeComplement p, actualTerm n w m.1) := by
  simpa only [mul_one, coprimeComplementSeries, one_dvd, if_true] using
    restrictedSeries_single_prime_split hp (Nat.coprime_one_right p) e n w hw

/-- Actual extraction from any positive level N. Its precise remaining
level is the canonical p-free integer part, so this is an iteration step
rather than a proposed global Euler formula. -/
theorem restrictedSeries_level_prime_extraction {p : ℕ} (hp : p.Prime)
    (N : ℕ) (hN : N ≠ 0) (n : ℤ) (w : ℂ)
    (hw : (if n = 0 then (2 : ℝ) else 1) < w.re) :
    restrictedSeries N n w =
      localTail p n (N.factorization p) ((p : ℂ) ^ (-w)) *
        coprimeComplementSeries p (N / p ^ (N.factorization p)) n w := by
  have hM : p.Coprime (N / p ^ (N.factorization p)) := Nat.coprime_ordCompl hp hN
  have hlevel : p ^ (N.factorization p) * (N / p ^ (N.factorization p)) = N :=
    Nat.ordProj_mul_ordCompl_eq_self N p
  simpa only [hlevel] using
    restrictedSeries_single_prime_split hp hM (N.factorization p) n w hw

end

end ImbalancedChen.Part3.ActualRamanujanSinglePrimeLevelSplit