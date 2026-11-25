import ImbalancedChen.CurrentChenUpsilon1011JointSource
import ImbalancedChen.CurrentChenQuotientUpperRosser
import Mathlib.Tactic.FieldSimp

/-!
# Current tenth mean: the genuine overlapping local modulus

The quotient is sifted at p₂, while its multiplier contains p₁<p₂.
Consequently the coprime-multiplier Upsilon 3--6 density is inapplicable.
This file proves the finite upper mean with the actual denominator
phi((p₁*p₂*p₃*p₄)*d), its signed AP error and signed centre correction.
There is no analytic estimate among its hypotheses.

SOURCE-WRITTEN, UNCOMPILED. No verification execution is authorized.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Classical

namespace P5U10OriginalMean

abbrev Label := (ℕ × ℕ) × (ℕ × ℕ)

def multiplier (t : Label) : ℕ := t.1.1 * t.1.2 * t.2.1 * t.2.2

def selector (N : ℕ) : Finset Label :=
  chenY10PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
    ((N : ℝ) ^ (19 / 125 : ℝ))

/-- Four actual prime labels give a positive multiplier. -/
theorem multiplier_pos {N : ℕ} {t : Label} (ht : t ∈ selector N) :
    0 < multiplier t := by
  obtain ⟨hc, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨h12, h34⟩ := Finset.mem_product.mp hc
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp h12
  obtain ⟨h3, h4⟩ := Finset.mem_product.mp h34
  exact mul_pos (mul_pos (mul_pos
    (mem_chenAdditivePrimeCarrier.mp h1).2.1.pos
    (mem_chenAdditivePrimeCarrier.mp h2).2.1.pos)
    (mem_chenAdditivePrimeCarrier.mp h3).2.1.pos)
    (mem_chenAdditivePrimeCarrier.mp h4).2.1.pos

/-- The first prime really belongs to the sieve at the second prime.
This is an arithmetic overlap, rather than an endpoint convention. -/
theorem first_mem_sievePrimes {N : ℕ} {t : Label} (ht : t ∈ selector N) :
    t.1.1 ∈ sievePrimes N t.1.2 := by
  obtain ⟨hc, _, h12, _⟩ := Finset.mem_filter.mp ht
  have h1 := (Finset.mem_product.mp (Finset.mem_product.mp hc).1).1
  obtain ⟨_, hp, hcop⟩ := mem_chenAdditivePrimeCarrier.mp h1
  exact mem_sievePrimes.mpr ⟨h12, hp, hp.coprime_iff_not_dvd.mp hcop⟩

/-- In particular the pre-existing coprime-multiplier density API cannot
be specialized to this source at its literal p₂ cutoff. -/
theorem multiplier_not_coprime_sieveProduct {N : ℕ} {t : Label}
    (ht : t ∈ selector N) :
    ¬ Nat.Coprime (multiplier t) (sieveProduct N t.1.2) := by
  have hmem := first_mem_sievePrimes ht
  have hp := (mem_sievePrimes.mp hmem).2.1
  have hfirst : t.1.1 ∣ multiplier t :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  have hsieve : t.1.1 ∣ sieveProduct N t.1.2 := by
    unfold sieveProduct
    exact Finset.dvd_prod_of_mem id hmem
  intro hcop
  exact hp.coprime_iff_not_dvd.mp (hcop.of_dvd_left hfirst) hsieve

/-- At the overlapping first prime the genuine local density is 1/p₁,
not 1/(p₁-1). This exact equality does not invoke an asymptotic. -/
theorem first_local_ratio {N : ℕ} {t : Label} (ht : t ∈ selector N) :
    (Nat.totient (multiplier t) : ℝ) /
        (Nat.totient (multiplier t * t.1.1) : ℝ) = 1 / (t.1.1 : ℝ) := by
  have hp := (mem_sievePrimes.mp (first_mem_sievePrimes ht)).2.1
  have hd : t.1.1 ∣ multiplier t :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  have hphi : Nat.totient (multiplier t * t.1.1) =
      t.1.1 * Nat.totient (multiplier t) := by
    rw [mul_comm, Nat.totient_mul_of_prime_of_dvd hp hd]
  have hp0 : (t.1.1 : ℝ) ≠ 0 := (Nat.cast_pos.mpr hp.pos).ne'
  have hphi0 : (Nat.totient (multiplier t) : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (Nat.totient_pos.mpr (multiplier_pos ht))).ne'
  rw [hphi, Nat.cast_mul]
  field_simp [hp0, hphi0]

/-- The unchanged actual upper coefficient, with its tuple-dependent
enumeration cap, cutoff and level. No multiplier-coprimality gate occurs. -/
def coefficient (N : ℕ) (t : Label) (L : ℝ) (d : ℕ) : ℝ :=
  actualSmallRosserPlus N t.1.2 (t.1.2 : ℝ) L d

def support (N : ℕ) (t : Label) : Finset ℕ :=
  actualSmallRosserSupport N t.1.2 (t.1.2 : ℝ)

/-- The density uses the full physical modulus even when d contains p₁. -/
def overlapDensity (N : ℕ) (t : Label) (L : ℝ) : ℝ :=
  ∑ d ∈ support N t, coefficient N t L d /
    (Nat.totient (multiplier t * d) : ℝ)

def signedAPError (N : ℕ) (M : ℝ) (t : Label) (L : ℝ) : ℝ :=
  ∑ d ∈ support N t, coefficient N t L d *
    chenQuotientPrimeAPError N M (multiplier t * d)

def signedCentre (N : ℕ) (t : Label) (L : ℝ) : ℝ :=
  ∑ d ∈ support N t, coefficient N t L d *
    chenCentrePrimeAPCount N N (multiplier t * d)

/-- Exact main/error identity. The signed coefficient and full modulus
are identical in all three terms; no totient multiplicativity is used. -/
theorem row_main_and_errors (N : ℕ) (M : ℝ) (t : Label) (L : ℝ) :
    (∑ d ∈ support N t, coefficient N t L d *
      (chenPrimeAPCount N N (multiplier t * d) -
        chenCentrePrimeAPCount N N (multiplier t * d))) =
      M * overlapDensity N t L + signedAPError N M t L - signedCentre N t L := by
  unfold overlapDensity signedAPError signedCentre chenQuotientPrimeAPError
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- A concrete finite upper mean for each original tenth fibre. The
only conditions are the actual Rosser level's pointwise legality. -/
theorem row_upper (N : ℕ) (M : ℝ) (t : Label) (L : ℝ)
    (hL : 1 < L) (hpL : (t.1.2 : ℝ) ≤ L) :
    ((chenSiftedQuotientPrimeSource N (multiplier t) (t.1.2 : ℝ)).card : ℝ) ≤
      M * overlapDensity N t L + signedAPError N M t L - signedCentre N t L := by
  rw [← row_main_and_errors]
  exact currentChen_quotient_actualRosser_upper N (multiplier t) t.1.2
    (t.1.2 : ℝ) L le_rfl hL hpL

/-- The actual U10 count, at the unchanged exponents, has a finite mean
with the overlapping density and both signed errors fully exposed. -/
theorem currentChenUpsilon10_upper (N : ℕ) (M : ℝ) (L : Label → ℝ)
    (hL : ∀ t ∈ selector N, 1 < L t)
    (hpL : ∀ t ∈ selector N, (t.1.2 : ℝ) ≤ L t) :
    currentChenUpsilon10 N ≤
      M * (∑ t ∈ selector N, overlapDensity N t (L t)) +
        (∑ t ∈ selector N, signedAPError N M t (L t)) -
        ∑ t ∈ selector N, signedCentre N t (L t) := by
  rw [currentChenUpsilon10_eq_siftedQuotientPrimeSource]
  change (∑ t ∈ selector N,
    ((chenSiftedQuotientPrimeSource N (multiplier t) (t.1.2 : ℝ)).card : ℝ)) ≤ _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro t ht
  exact row_upper N M t (L t) (hL t ht) (hpL t ht)

/-- A concrete legal level at every actual tuple gives an unconditional
finite inequality. Distribution and density asymptotics are still open. -/
theorem currentChenUpsilon10_upper_maxLevel (N : ℕ) (M : ℝ) :
    currentChenUpsilon10 N ≤
      M * (∑ t ∈ selector N, overlapDensity N t (max 2 (t.1.2 : ℝ))) +
        (∑ t ∈ selector N, signedAPError N M t (max 2 (t.1.2 : ℝ))) -
        ∑ t ∈ selector N, signedCentre N t (max 2 (t.1.2 : ℝ)) := by
  exact currentChenUpsilon10_upper N M (fun t => max 2 (t.1.2 : ℝ))
    (fun t _ => lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _))
    (fun t _ => le_max_right _ _)

/-- Coefficients have unit absolute bound even on overlapping moduli. -/
theorem coefficient_abs_le_one (N : ℕ) (t : Label) (L : ℝ) (d : ℕ) :
    |coefficient N t L d| ≤ 1 :=
  actualSmallRosserPlus_abs_le_one N t.1.2 (t.1.2 : ℝ) L d

/-- The signed error admits this exact rowwise absolute AP budget;
no invented injectivity of (t,d) ↦ multiplier(t)*d is needed. -/
theorem abs_signedAPError_le (N : ℕ) (M : ℝ) (t : Label) (L : ℝ) :
    |signedAPError N M t L| ≤
      ∑ d ∈ support N t, |chenQuotientPrimeAPError N M (multiplier t * d)| := by
  unfold signedAPError
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right (coefficient_abs_le_one N t L d)
    (abs_nonneg _)).trans_eq (one_mul _)

theorem abs_signedCentre_le (N : ℕ) (t : Label) (L : ℝ) :
    |signedCentre N t L| ≤
      ∑ d ∈ support N t, chenCentrePrimeAPCount N N (multiplier t * d) := by
  unfold signedCentre
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d _
  rw [abs_mul, abs_of_nonneg (chenCentrePrimeAPCount_nonneg _ _ _)]
  exact (mul_le_mul_of_nonneg_right (coefficient_abs_le_one N t L d)
    (chenCentrePrimeAPCount_nonneg _ _ _)).trans_eq (one_mul _)

/-- Literal full product cap for every nonzero coefficient at the
existing Q-dependent level. This uses the actual four-prime positivity. -/
theorem active_physical_cap {N Q : ℕ} {t : Label} (ht : t ∈ selector N)
    {d : ℕ} (hd : coefficient N t (chenQuotientRowLevel Q (multiplier t) : ℝ) d ≠ 0) :
    multiplier t * d ≤ Q := by
  have hactive := (actualSmallRosserPlus_active hd).2.1
  have hlt : d < chenQuotientRowLevel Q (multiplier t) := by exact_mod_cast hactive
  exact (lt_chenQuotientRowLevel_iff (multiplier_pos ht)).mp hlt

/-- The first-overlap branch actually contains a repeated p₁ in the
physical modulus. Dropping non-squarefree moduli would lose this branch. -/
theorem first_sq_dvd_physical {t : Label} {d : ℕ} (hd : t.1.1 ∣ d) :
    t.1.1 ^ 2 ∣ multiplier t * d := by
  have hb : t.1.1 ∣ multiplier t :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  simpa only [pow_two] using mul_dvd_mul hb hd

/-- The current positive four-prefix Buchstab argument has the following
actual compact range. The old Li--Liu lower wall 17/4 does not apply. -/
theorem buchstab_argument_bounds {r q s t : ℝ}
    (hr : (417 / 5000 : ℝ) ≤ r) (hrq : r ≤ q) (hqs : q ≤ s)
    (hst : s ≤ t) (ht : t ≤ (19 / 125 : ℝ)) :
    (49 / 19 : ℝ) ≤ (1 - r - q - s - t) / q ∧
      (1 - r - q - s - t) / q ≤ (3332 / 417 : ℝ) := by
  have hq : 0 < q := by linarith
  constructor
  · apply (le_div_iff₀ hq).mpr
    linarith
  · apply (div_le_iff₀ hq).mpr
    linarith

/-- All four original labels remain in the switched kernel; the second
smallest label q is the roughness coordinate and occurs twice below. -/
def switchedKernel (K : ℝ) (omega : ℝ → ℝ) (r q s t : ℝ) : ℝ :=
  K * omega ((1 - r - q - s - t) / q) / (r * q ^ 2 * s * t)

theorem switchedKernel_nonneg {K r q s t : ℝ} {omega : ℝ → ℝ}
    (hK : 0 ≤ K) (hr : (417 / 5000 : ℝ) ≤ r) (hrq : r ≤ q)
    (hqs : q ≤ s) (hst : s ≤ t) (ht : t ≤ (19 / 125 : ℝ))
    (homega : ∀ u ∈ Set.Icc (49 / 19 : ℝ) (3332 / 417 : ℝ), 0 ≤ omega u) :
    0 ≤ switchedKernel K omega r q s t := by
  have hr0 : 0 < r := by linarith
  have hq0 : 0 < q := hr0.trans_le hrq
  have hs0 : 0 < s := hq0.trans_le hqs
  have ht0 : 0 < t := hs0.trans_le hst
  exact div_nonneg (mul_nonneg hK (homega _ (buchstab_argument_bounds hr hrq hqs hst ht)))
    (mul_pos (mul_pos (mul_pos hr0 (sq_pos_of_pos hq0)) hs0) ht0).le

end P5U10OriginalMean

end

end ImbalancedChen
