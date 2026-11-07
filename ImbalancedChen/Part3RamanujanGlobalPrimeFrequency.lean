import ImbalancedChen.Part3RamanujanPrimeFrequencyRecurrence

/-! The actual prime-free complement is invariant under n -> p*n, by
unit scaling of the literal Ramanujan sum. This transports the local
frequency recurrence to the absolutely convergent global Dirichlet series.
No held Fourier coefficient assembly is used.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Complex
open scoped BigOperators
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode
open ImbalancedChen.Part3.ActualLevelDirichletFactors
open ImbalancedChen.Part3.ActualRamanujanSinglePrimeLevelSplit
open ImbalancedChen.Part3.ActualRamanujanLevelZetaFactors
open ImbalancedChen.Part3.RamanujanPrimeFrequencyRecurrence20261026b

namespace ImbalancedChen.Part3.RamanujanGlobalPrimeFrequency20261026b

/-- Actual coefficient identity for every prime-free modulus, obtained
from the permutation of its unit residues. -/
theorem actualTerm_prime_frequency {p : ℕ} (hp : p.Prime)
    (m : PrimeComplement p) (n : ℤ) (w : ℂ) :
    actualTerm ((p : ℤ) * n) w m.1 = actualTerm n w m.1 := by
  have hm0 : m.1 ≠ 0 := by
    intro hz
    have hnot := hp.coprime_iff_not_dvd.mp m.2
    exact hnot (by simp [hz])
  letI : NeZero m.1 := ⟨hm0⟩
  have hu : IsUnit ((p : ℤ) : ZMod m.1) :=
    (isUnit_intCast_iff_natAbs_coprime (c := m.1) (p : ℤ)).mpr
      (by simpa only [Int.natAbs_natCast] using m.2)
  unfold actualTerm
  rw [ramanujan_unit_scaling n (p : ℤ) hu]

/-- The entire genuine complement series, retaining an arbitrary
remaining level M, is unchanged by this frequency multiplication. -/
theorem coprimeComplement_prime_frequency {p : ℕ} (hp : p.Prime)
    (M : ℕ) (n : ℤ) (w : ℂ) :
    coprimeComplementSeries p M ((p : ℤ) * n) w =
      coprimeComplementSeries p M n w := by
  unfold coprimeComplementSeries
  apply tsum_congr
  intro m
  rw [actualTerm_prime_frequency hp m n w]

private theorem full_prime_split {p : ℕ} (hp : p.Prime)
    (n : ℤ) (hn : n ≠ 0) (w : ℂ) (hw : 1 < w.re) :
    restrictedSeries 1 n w = localTail p n 0 ((p : ℂ) ^ (-w)) *
      coprimeComplementSeries p 1 n w := by
  simpa only [pow_zero, one_mul] using
    restrictedSeries_single_prime_split hp (Nat.coprime_one_right p) 0 n w
      (by simpa only [if_neg hn] using hw)

private theorem restricted_prime_split {p : ℕ} (hp : p.Prime)
    (n : ℤ) (hn : n ≠ 0) (w : ℂ) (hw : 1 < w.re) :
    restrictedSeries p n w = localTail p n 1 ((p : ℂ) ^ (-w)) *
      coprimeComplementSeries p 1 n w := by
  simpa only [pow_one, mul_one] using
    restrictedSeries_single_prime_split hp (Nat.coprime_one_right p) 1 n w
      (by simpa only [if_neg hn] using hw)

/-- True global coefficient recurrence. Every sum is the original
absolutely convergent Dirichlet series, rather than a formal local product. -/
theorem restrictedSeries_prime_frequency {p : ℕ} (hp : p.Prime)
    (n : ℤ) (hn : n ≠ 0) (w : ℂ) (hw : 1 < w.re) :
    (1 - (p : ℂ) ^ (-w)) * restrictedSeries p ((p : ℤ) * n) w =
      (p : ℂ) ^ (-w) *
        ((p : ℂ) * restrictedSeries 1 n w - restrictedSeries 1 ((p : ℤ) * n) w) := by
  have hpn : (p : ℤ) * n ≠ 0 := mul_ne_zero (by exact_mod_cast hp.ne_zero) hn
  rw [restricted_prime_split hp _ hpn w hw,
    full_prime_split hp n hn w hw, full_prime_split hp _ hpn w hw,
    coprimeComplement_prime_frequency hp 1 n w]
  have h := restricted_localTail_prime_frequency hp hn ((p : ℂ) ^ (-w))
  linear_combination (coprimeComplementSeries p 1 n w) * h

/-- Literal divisibility gate: the quotient-frequency full series occurs
only if p divides n; otherwise its contribution is exactly zero. -/
theorem restrictedSeries_divisibility_recurrence {p : ℕ} (hp : p.Prime)
    (n : ℤ) (hn : n ≠ 0) (w : ℂ) (hw : 1 < w.re) :
    (1 - (p : ℂ) ^ (-w)) * restrictedSeries p n w =
      (p : ℂ) ^ (-w) *
        ((p : ℂ) * (if (p : ℤ) ∣ n then restrictedSeries 1 (n / (p : ℤ)) w else 0) -
          restrictedSeries 1 n w) := by
  classical
  by_cases hd : (p : ℤ) ∣ n
  · rw [if_pos hd]
    have hm : (p : ℤ) * (n / (p : ℤ)) = n := Int.mul_ediv_cancel' hd
    have hq : n / (p : ℤ) ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at hm
      exact hn hm.symm
    simpa only [hm] using restrictedSeries_prime_frequency hp (n / (p : ℤ)) hq w hw
  · rw [if_neg hd, mul_zero, zero_sub]
    rw [restricted_prime_split hp n hn w hw, full_prime_split hp n hn w hw]
    obtain ⟨hf, ht⟩ := prime_free_localTail hp hn hd ((p : ℂ) ^ (-w))
    rw [hf, ht]
    ring

/-- Solved actual prime-level coefficient, with the local denominator
proved nonzero on Re(w)>1, including both frequency branches. -/
theorem restrictedSeries_divisibility_formula {p : ℕ} (hp : p.Prime)
    (n : ℤ) (hn : n ≠ 0) (w : ℂ) (hw : 1 < w.re) :
    restrictedSeries p n w =
      ((p : ℂ) ^ (-w) *
        ((p : ℂ) * (if (p : ℤ) ∣ n then restrictedSeries 1 (n / (p : ℤ)) w else 0) -
          restrictedSeries 1 n w)) / (1 - (p : ℂ) ^ (-w)) := by
  have hx := (prime_ratio_norm_bounds hp w hw).2
  have hden : 1 - (p : ℂ) ^ (-w) ≠ 0 := by
    intro hz
    have he : (p : ℂ) ^ (-w) = 1 := (sub_eq_zero.mp hz).symm
    simpa only [he, norm_one, lt_self_iff_false] using hx
  apply (eq_div_iff hden).mpr
  simpa only [mul_comm] using restrictedSeries_divisibility_recurrence hp n hn w hw

end ImbalancedChen.Part3.RamanujanGlobalPrimeFrequency20261026b
