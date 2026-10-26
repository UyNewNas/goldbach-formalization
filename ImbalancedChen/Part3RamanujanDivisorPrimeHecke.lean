import ImbalancedChen.Part3RamanujanGlobalPrimeFrequency

/-! Arithmetic prime Hecke recurrence derived from the genuine convergent
Ramanujan series, with the quotient-frequency gate retained. Zeta is
cancelled only after its actual nonvanishing on Re(w)>1 is supplied.
No held Fourier coefficient source is used.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Complex Finset
open scoped BigOperators
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode
open ImbalancedChen.Part3.ActualLevelDirichletFactors
open ImbalancedChen.Part3.ActualRamanujanSinglePrimeLevelSplit
open ImbalancedChen.Part3.ActualRamanujanLevelZetaFactors
open ImbalancedChen.Part3ActualRamanujanDirichletSeries
open ImbalancedChen.Part3.RamanujanGlobalPrimeFrequency20261026b

namespace ImbalancedChen.Part3.RamanujanDivisorPrimeHecke20261026b

private theorem fullSeries_prime_decomposition {p : ℕ} (hp : p.Prime)
    (n : ℤ) (hn : n ≠ 0) (w : ℂ) (hw : 1 < w.re) :
    restrictedSeries 1 n w = coprimeComplementSeries p 1 n w + restrictedSeries p n w := by
  have hfull := restrictedSeries_single_prime_split hp (Nat.coprime_one_right p)
    0 n w (by simpa only [if_neg hn] using hw)
  have hrest := restrictedSeries_single_prime_split hp (Nat.coprime_one_right p)
    1 n w (by simpa only [if_neg hn] using hw)
  simp only [pow_zero, one_mul] at hfull
  simp only [pow_one, mul_one] at hrest
  have htail := localTail_finite_correction hp n 1 ((p : ℂ) ^ (-w))
    (prime_ratio_norm_bounds hp w hw).1
  simp only [sum_range_one, pow_zero, ramanujan_modulus_one, mul_one] at htail
  rw [hfull, hrest, htail]
  ring

/-- The actual global Dirichlet coefficients obey the prime Hecke
recurrence. The missing quotient frequency contributes zero exactly. -/
theorem fullSeries_prime_hecke {p : ℕ} (hp : p.Prime)
    (n : ℤ) (hn : n ≠ 0) (w : ℂ) (hw : 1 < w.re) :
    restrictedSeries 1 ((p : ℤ) * n) w =
      (1 + (p : ℂ) * (p : ℂ) ^ (-w)) * restrictedSeries 1 n w -
        (p : ℂ) * (p : ℂ) ^ (-w) *
          (if (p : ℤ) ∣ n then restrictedSeries 1 (n / (p : ℤ)) w else 0) := by
  have hpn : (p : ℤ) * n ≠ 0 := mul_ne_zero (by exact_mod_cast hp.ne_zero) hn
  have h1 := restrictedSeries_prime_frequency hp n hn w hw
  have h2 := restrictedSeries_divisibility_recurrence hp n hn w hw
  have hdN := fullSeries_prime_decomposition hp n hn w hw
  have hdP := fullSeries_prime_decomposition hp ((p : ℤ) * n) hpn w hw
  rw [coprimeComplement_prime_frequency hp 1 n w] at hdP
  linear_combination h1 + (1 - (p : ℂ) ^ (-w)) * hdP -
    (1 - (p : ℂ) ^ (-w)) * hdN - h2

/-- The genuine finite divisor coefficients inherit that recurrence.
This is an arithmetic supplier for the two prime channels, independently
of any physical Fourier or spectral reconstruction theorem. -/
theorem divisorFactor_prime_hecke {p : ℕ} (hp : p.Prime)
    (n : ℤ) (hn : n ≠ 0) (w : ℂ) (hw : 1 < w.re) :
    divisorFactor (((p : ℤ) * n).natAbs) w =
      (1 + (p : ℂ) * (p : ℂ) ^ (-w)) * divisorFactor n.natAbs w -
        (p : ℂ) * (p : ℂ) ^ (-w) *
          (if (p : ℤ) ∣ n then divisorFactor (n / (p : ℤ)).natAbs w else 0) := by
  classical
  have hpn : (p : ℤ) * n ≠ 0 := mul_ne_zero (by exact_mod_cast hp.ne_zero) hn
  have h := fullSeries_prime_hecke hp n hn w hw
  have hz : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hw
  rw [fullSeries_nonzero_zeta_formula _ hpn w hw,
    fullSeries_nonzero_zeta_formula n hn w hw] at h
  by_cases hd : (p : ℤ) ∣ n
  · have hm : (p : ℤ) * (n / (p : ℤ)) = n := Int.mul_ediv_cancel' hd
    have hq : n / (p : ℤ) ≠ 0 := by
      intro he
      rw [he, mul_zero] at hm
      exact hn hm.symm
    simp only [if_pos hd] at h ⊢
    rw [fullSeries_nonzero_zeta_formula _ hq w hw] at h
    apply (div_left_inj' hz).mp
    simpa only [sub_div, mul_div_assoc] using h
  · simp only [if_neg hd, mul_zero, sub_zero] at h ⊢
    apply (div_left_inj' hz).mp
    simpa only [mul_div_assoc] using h

end ImbalancedChen.Part3.RamanujanDivisorPrimeHecke20261026b
