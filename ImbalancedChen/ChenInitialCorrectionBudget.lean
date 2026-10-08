import ImbalancedChen.ChenInitialPrimeSource
import ImbalancedChen.TotientReciprocalBudget
import ImbalancedChen.BoundaryArbitraryLog
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Paying the actual initial-prime-source corrections

The inclusive prefix and every correction below are the literal objects
of `ChenInitialPrimeSource`. For a positive integer `k`, its distinct-prime
product proves `omega(k) <= log k / log 2`. Thus, for positive moduli at
most `D <= sqrt N`, both centre-prime and modulus-prime corrections have
total cost at most `(17 / log 2) * sqrt N * (log N)^2`, once `log N >= 1`.
This is negligible at every fixed logarithmic accuracy by the already
proved power-log limit. The threshold is uniform in the chosen moduli,
the real sieve cutoff, and the evenness proof.

The signed identities retain the negative modulus-prime atom. The final
conditional application takes ordinary inclusive prime-AP errors over
primitive classes, with any common main term. No prime distribution
theorem, PNT, lower sieve estimate, or Upsilon bound is assumed or proved.
Receiver one remains in the source; nothing in this file changes it.

The logarithm APIs were checked at mathlib revision
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, in
`Analysis/SpecialFunctions/Log/Basic.lean`. The product bound is the
existing `chen_pow_primeFactors_card_le`; reciprocal-totient and power-log
estimates are the proved local theorems, not new analytic hypotheses.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators

/-- The logarithmic distinct-prime bound includes `k = 1`, but excludes
`k = 0`, whose prime-factor convention cannot count this prefix. -/
theorem chen_primeFactors_card_le_log {k : ℕ} (hk : 0 < k) :
    (k.primeFactors.card : ℝ) ≤ Real.log (k : ℝ) / Real.log 2 := by
  have hpow : (2 : ℝ) ^ k.primeFactors.card ≤ (k : ℝ) :=
    chen_pow_primeFactors_card_le hk.ne' (by norm_num)
      (fun p hp _ => by exact_mod_cast hp.two_le)
  have hlog := Real.log_le_log (by positivity :
    (0 : ℝ) < (2 : ℝ) ^ k.primeFactors.card) hpow
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog

theorem chenPrimeDivisorCount_nonneg (N k : ℕ) :
    0 ≤ chenPrimeDivisorCount N k := by
  unfold chenPrimeDivisorCount
  positivity

theorem chenCentrePrimeAPCount_nonneg (N a d : ℕ) :
    0 ≤ chenCentrePrimeAPCount N a d := by
  unfold chenCentrePrimeAPCount
  positivity

/-- A prefix can contain only a subset of the prime factors of positive
`k`. In particular, this does not identify the `k = 0` prefix with empty. -/
theorem chenPrimeDivisorCount_le_primeFactors_card (N : ℕ) {k : ℕ}
    (hk : 0 < k) :
    chenPrimeDivisorCount N k ≤ (k.primeFactors.card : ℝ) := by
  classical
  have hsub : (chenPrimePrefix N).filter (fun p => p ∣ k) ⊆ k.primeFactors := by
    intro p hp
    obtain ⟨hp, hpk⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(mem_chenPrimePrefix.mp hp).2, hpk, hk.ne'⟩
  unfold chenPrimeDivisorCount
  exact_mod_cast Finset.card_le_card hsub

/-- Explicit unconditional logarithmic bound for each actual divisor
correction in the inclusive prefix, including the prime-centre endpoint. -/
theorem chenPrimeDivisorCount_le_log (N : ℕ) {k : ℕ} (hk : 0 < k) :
    chenPrimeDivisorCount N k ≤ Real.log (k : ℝ) / Real.log 2 :=
  (chenPrimeDivisorCount_le_primeFactors_card N hk).trans
    (chen_primeFactors_card_le_log hk)

theorem chenPrimeDivisorCount_le_log_center {N k : ℕ}
    (hk : 0 < k) (hkN : k ≤ N) :
    chenPrimeDivisorCount N k ≤ Real.log (N : ℝ) / Real.log 2 := by
  refine (chenPrimeDivisorCount_le_log N hk).trans ?_
  exact div_le_div_of_nonneg_right
    (Real.log_le_log (by exact_mod_cast hk) (by exact_mod_cast hkN))
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- The progression correction is an actual subset of centre divisors. -/
theorem chenCentrePrimeAPCount_le_divisorCount (N a d : ℕ) :
    chenCentrePrimeAPCount N a d ≤ chenPrimeDivisorCount N N := by
  classical
  have hsub :
      (chenPrimePrefix N).filter (fun p => Nat.ModEq d p a ∧ p ∣ N) ⊆
        (chenPrimePrefix N).filter (fun p => p ∣ N) := by
    intro p hp
    obtain ⟨hp, _, hpd⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hp, hpd⟩
  unfold chenCentrePrimeAPCount chenPrimeDivisorCount
  exact_mod_cast Finset.card_le_card hsub

/-- The full positive primitive-modulus support, retaining modulus one. -/
def chenInitialPrimitiveModuli (N D : ℕ) : Finset ℕ :=
  (Finset.Icc 1 D).filter (fun d => Nat.Coprime d N)

@[simp] theorem mem_chenInitialPrimitiveModuli {N D d : ℕ} :
    d ∈ chenInitialPrimitiveModuli N D ↔ 1 ≤ d ∧ d ≤ D ∧ Nat.Coprime d N := by
  simp only [chenInitialPrimitiveModuli, Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem chenInitialPrimitiveModuli_subset (N D : ℕ) :
    chenInitialPrimitiveModuli N D ⊆ Finset.Icc 1 D :=
  Finset.filter_subset _ _

/-- Exact signed correction from the total prime-prefix AP error. -/
def chenInitialPrimeAPCorrection (N d : ℕ) : ℝ :=
  chenPrimeDivisorCount N N / (Nat.totient d : ℝ) - chenCentrePrimeAPCount N N d

/-- Exact signed correction from the coprime-normalized prefix error.
The modulus-prime count is subtracted, even on primitive modulus support. -/
def chenInitialPrimitiveCorrection (N d : ℕ) : ℝ :=
  (chenPrimeDivisorCount N N - chenPrimeDivisorCount N d) /
    (Nat.totient d : ℝ) - chenCentrePrimeAPCount N N d

/-- The modulus-prime atom separates with its negative sign. -/
theorem chenInitialPrimitiveCorrection_eq_primeAP_sub (N d : ℕ) :
    chenInitialPrimitiveCorrection N d = chenInitialPrimeAPCorrection N d -
      chenPrimeDivisorCount N d / (Nat.totient d : ℝ) := by
  unfold chenInitialPrimitiveCorrection chenInitialPrimeAPCorrection
  ring

/-- A prime modulus lying in the inclusive prefix contributes exactly
one, whether or not it is coprime to the centre. It cannot be erased by
putting a primitive-residue mask on the entire prime prefix. -/
theorem chenPrimeDivisorCount_prime_modulus {N p : ℕ}
    (hp : Nat.Prime p) (hpN : p ≤ N) : chenPrimeDivisorCount N p = 1 := by
  classical
  have hf : (chenPrimePrefix N).filter (fun q => q ∣ p) = {p} := by
    ext q
    rw [Finset.mem_filter, mem_chenPrimePrefix, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, hq⟩, hqp⟩
      exact (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
    · rintro rfl
      exact ⟨⟨hpN, hp⟩, dvd_rfl⟩
  unfold chenPrimeDivisorCount
  rw [hf]
  norm_num

theorem chenInitialPrimitiveCorrection_prime_modulus {N p : ℕ}
    (hp : Nat.Prime p) (hpN : p ≤ N) :
    chenInitialPrimitiveCorrection N p = chenInitialPrimeAPCorrection N p -
      1 / (Nat.totient p : ℝ) := by
  rw [chenInitialPrimitiveCorrection_eq_primeAP_sub,
    chenPrimeDivisorCount_prime_modulus hp hpN]

/-- A positive majorant paying both literal exceptional prime sets. -/
def chenInitialCorrectionCost (N : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ d ∈ S, (chenPrimeDivisorCount N N + chenPrimeDivisorCount N d) /
    (Nat.totient d : ℝ) + chenCentrePrimeAPCount N N d

theorem chenInitialCorrectionCost_nonneg (N : ℕ) (S : Finset ℕ) :
    0 ≤ chenInitialCorrectionCost N S := by
  apply Finset.sum_nonneg
  intro d _
  exact add_nonneg
    (div_nonneg (add_nonneg (chenPrimeDivisorCount_nonneg N N)
      (chenPrimeDivisorCount_nonneg N d)) (Nat.cast_nonneg _))
    (chenCentrePrimeAPCount_nonneg N N d)

theorem chenInitialBoundingSieve_rem_sub_primeAP_error
    (N : ℕ) (z : ℝ) (hN : Even N) (d : ℕ) :
    (chenInitialBoundingSieve N z hN).rem d -
      (chenPrimeAPCount N N d - ((chenPrimePrefix N).card : ℝ) /
        (Nat.totient d : ℝ)) = chenInitialPrimeAPCorrection N d := by
  rw [chenInitialBoundingSieve_rem_eq_primeAP_error]
  unfold chenInitialPrimeAPCorrection
  ring

theorem chenInitialBoundingSieve_rem_sub_primitive_error
    (N : ℕ) (z : ℝ) (hN : Even N) (d : ℕ) :
    (chenInitialBoundingSieve N z hN).rem d -
      finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N d =
        chenInitialPrimitiveCorrection N d := by
  rw [chenInitialBoundingSieve_rem_eq_primitive_error]
  unfold chenInitialPrimitiveCorrection
  ring

private theorem chen_abs_sub_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |a - b| ≤ a + b := by
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_chenInitialPrimeAPCorrection_le (N d : ℕ) :
    |chenInitialPrimeAPCorrection N d| ≤
      (chenPrimeDivisorCount N N + chenPrimeDivisorCount N d) /
        (Nat.totient d : ℝ) + chenCentrePrimeAPCount N N d := by
  unfold chenInitialPrimeAPCorrection
  refine (chen_abs_sub_le_add
    (div_nonneg (chenPrimeDivisorCount_nonneg N N) (Nat.cast_nonneg _))
    (chenCentrePrimeAPCount_nonneg N N d)).trans ?_
  exact add_le_add
    (div_le_div_of_nonneg_right (le_add_of_nonneg_right
      (chenPrimeDivisorCount_nonneg N d)) (Nat.cast_nonneg _)) le_rfl

theorem abs_chenInitialPrimitiveCorrection_le (N d : ℕ) :
    |chenInitialPrimitiveCorrection N d| ≤
      (chenPrimeDivisorCount N N + chenPrimeDivisorCount N d) /
        (Nat.totient d : ℝ) + chenCentrePrimeAPCount N N d := by
  unfold chenInitialPrimitiveCorrection
  have hphi : 0 ≤ (Nat.totient d : ℝ) := Nat.cast_nonneg _
  have hcn := chenPrimeDivisorCount_nonneg N N
  have hcd := chenPrimeDivisorCount_nonneg N d
  have hcc := chenCentrePrimeAPCount_nonneg N N d
  have hleft := div_le_div_of_nonneg_right (show
    -(chenPrimeDivisorCount N N + chenPrimeDivisorCount N d) ≤
      chenPrimeDivisorCount N N - chenPrimeDivisorCount N d by linarith) hphi
  have hright := div_le_div_of_nonneg_right (show
    chenPrimeDivisorCount N N - chenPrimeDivisorCount N d ≤
      chenPrimeDivisorCount N N + chenPrimeDivisorCount N d by linarith) hphi
  rw [neg_div] at hleft
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- This is the sum of the actual replacement errors, not an assumed
bound on a new abstract remainder. -/
theorem sum_abs_chenInitial_rem_sub_primitive_le_cost
    (N : ℕ) (z : ℝ) (hN : Even N) (S : Finset ℕ) :
    (∑ d ∈ S, |(chenInitialBoundingSieve N z hN).rem d -
      finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N d|) ≤
        chenInitialCorrectionCost N S := by
  simp_rw [chenInitialBoundingSieve_rem_sub_primitive_error]
  exact Finset.sum_le_sum (fun d _ => abs_chenInitialPrimitiveCorrection_le N d)

theorem sum_abs_chenInitial_rem_sub_primeAP_le_cost
    (N : ℕ) (z : ℝ) (hN : Even N) (S : Finset ℕ) :
    (∑ d ∈ S, |(chenInitialBoundingSieve N z hN).rem d -
      (chenPrimeAPCount N N d - ((chenPrimePrefix N).card : ℝ) /
        (Nat.totient d : ℝ))|) ≤ chenInitialCorrectionCost N S := by
  simp_rw [chenInitialBoundingSieve_rem_sub_primeAP_error]
  exact Finset.sum_le_sum (fun d _ => abs_chenInitialPrimeAPCorrection_le N d)

/-- Explicit finite cost. The `D = 0` family is empty and is included.
The estimate itself is valid for any selected positive moduli. -/
theorem chenInitialCorrectionCost_le_log {N D : ℕ} (hN : 0 < N)
    (hD : D ≤ N) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 D) :
    chenInitialCorrectionCost N S ≤
      (Real.log (N : ℝ) / Real.log 2) *
        ((D : ℝ) + 8 * (1 + Real.log (max 1 (D : ℝ)))) := by
  classical
  let B : ℝ := Real.log (N : ℝ) / Real.log 2
  have hB : 0 ≤ B := div_nonneg (Real.log_natCast_nonneg N)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hcn : chenPrimeDivisorCount N N ≤ B := chenPrimeDivisorCount_le_log N hN
  have hpoint : ∀ d ∈ S,
      (chenPrimeDivisorCount N N + chenPrimeDivisorCount N d) /
        (Nat.totient d : ℝ) + chenCentrePrimeAPCount N N d ≤
          (2 * B) * (1 / (Nat.totient d : ℝ)) + B := by
    intro d hd
    obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp (hS hd)
    have hcd : chenPrimeDivisorCount N d ≤ B :=
      chenPrimeDivisorCount_le_log_center (by omega) (hdD.trans hD)
    have hcc := (chenCentrePrimeAPCount_le_divisorCount N N d).trans hcn
    calc
      _ ≤ (B + B) / (Nat.totient d : ℝ) + B :=
        add_le_add (div_le_div_of_nonneg_right (add_le_add hcn hcd)
          (Nat.cast_nonneg _)) hcc
      _ = _ := by ring
  have hcard : (S.card : ℝ) ≤ (D : ℝ) := by
    have hc : S.card ≤ D := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hS
    exact_mod_cast hc
  have hrec := sum_reciprocal_totient_subset_le_log S D hS
  calc
    chenInitialCorrectionCost N S ≤
        ∑ d ∈ S, (2 * B) * (1 / (Nat.totient d : ℝ)) + B :=
      Finset.sum_le_sum hpoint
    _ = (2 * B) * (∑ d ∈ S, 1 / (Nat.totient d : ℝ)) + (S.card : ℝ) * B := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * B) * (4 * (1 + Real.log (max 1 (D : ℝ)))) + (D : ℝ) * B :=
      add_le_add (mul_le_mul_of_nonneg_left hrec (by positivity))
        (mul_le_mul_of_nonneg_right hcard hB)
    _ = _ := by dsimp [B]; ring

/-- Below the square-root level every literal correction is paid by a
fixed sublinear power times two logarithms. -/
theorem chenInitialCorrectionCost_le_sqrt_log_sq {N D : ℕ}
    (hN : 0 < N) (hlog : 1 ≤ Real.log (N : ℝ))
    (hD : (D : ℝ) ≤ Real.sqrt (N : ℝ))
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 D) :
    chenInitialCorrectionCost N S ≤
      (17 / Real.log 2) * (N : ℝ) ^ (1 / 2 : ℝ) * (Real.log (N : ℝ)) ^ 2 := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hsqrt1 : 1 ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr hN1
  have hsqrtN : Real.sqrt (N : ℝ) ≤ (N : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr hN1)
  have hDN : D ≤ N := by exact_mod_cast hD.trans hsqrtN
  have hlogD : Real.log (max 1 (D : ℝ)) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (max_le hN1 (hD.trans hsqrtN))
  have hB : 0 ≤ Real.log (N : ℝ) / Real.log 2 :=
    div_nonneg (by linarith) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hbracket : (D : ℝ) + 8 * (1 + Real.log (max 1 (D : ℝ))) ≤
      17 * Real.sqrt (N : ℝ) * Real.log (N : ℝ) := by
    have hm1 := mul_nonneg (sub_nonneg.mpr hsqrt1) (sub_nonneg.mpr hlog)
    have hm2 := mul_nonneg (Real.sqrt_nonneg (N : ℝ)) (sub_nonneg.mpr hlog)
    nlinarith
  calc
    chenInitialCorrectionCost N S ≤ (Real.log (N : ℝ) / Real.log 2) *
        ((D : ℝ) + 8 * (1 + Real.log (max 1 (D : ℝ)))) :=
      chenInitialCorrectionCost_le_log hN hDN S hS
    _ ≤ (Real.log (N : ℝ) / Real.log 2) *
        (17 * Real.sqrt (N : ℝ) * Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hbracket hB
    _ = _ := by rw [Real.sqrt_eq_rpow]; ring

/-- Uniform arbitrary fixed logarithmic accuracy for the actual positive
correction sum. This has no prime-AP distribution premise. -/
theorem eventually_chenInitialCorrectionCost_le_logAccuracy (A : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ D : ℕ, ∀ S : Finset ℕ,
        (D : ℝ) ≤ Real.sqrt (N : ℝ) → S ⊆ chenInitialPrimitiveModuli N D →
        chenInitialCorrectionCost N S ≤
          epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_powerLog_le_logAccuracy (17 / Real.log 2) (1 / 2) 2 A
      (by norm_num) epsilon hepsilon,
      eventually_one_le_nat_log, eventually_ge_atTop (1 : ℕ)]
    with N hpower hlog hN
  intro D S hD hS
  exact (chenInitialCorrectionCost_le_sqrt_log_sq (by omega) hlog hD S
    (hS.trans (chenInitialPrimitiveModuli_subset N D))).trans hpower

/-- Actual primitive-prefix replacement errors have arbitrary logarithmic
accuracy, uniformly in the true sieve cutoff and even centre. -/
theorem eventually_sum_abs_chenInitial_rem_sub_primitive_le_logAccuracy (A : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ z : ℝ, ∀ hN : Even N, ∀ D : ℕ, ∀ S : Finset ℕ,
        (D : ℝ) ≤ Real.sqrt (N : ℝ) → S ⊆ chenInitialPrimitiveModuli N D →
        (∑ d ∈ S, |(chenInitialBoundingSieve N z hN).rem d -
          finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N d|) ≤
            epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  intro epsilon hepsilon
  filter_upwards [eventually_chenInitialCorrectionCost_le_logAccuracy A epsilon hepsilon]
    with N hcost
  intro z hN D S hD hS
  exact (sum_abs_chenInitial_rem_sub_primitive_le_cost N z hN S).trans
    (hcost D S hD hS)

/-- The corresponding total-prefix normalization is paid as well; no
prime-prefix cardinality has been replaced by an analytic main term. -/
theorem eventually_sum_abs_chenInitial_rem_sub_primeAP_le_logAccuracy (A : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ z : ℝ, ∀ hN : Even N, ∀ D : ℕ, ∀ S : Finset ℕ,
        (D : ℝ) ≤ Real.sqrt (N : ℝ) → S ⊆ chenInitialPrimitiveModuli N D →
        (∑ d ∈ S, |(chenInitialBoundingSieve N z hN).rem d -
          (chenPrimeAPCount N N d - ((chenPrimePrefix N).card : ℝ) /
            (Nat.totient d : ℝ))|) ≤
              epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  intro epsilon hepsilon
  filter_upwards [eventually_chenInitialCorrectionCost_le_logAccuracy A epsilon hepsilon]
    with N hcost
  intro z hN D S hD hS
  exact (sum_abs_chenInitial_rem_sub_primeAP_le_cost N z hN S).trans
    (hcost D S hD hS)

/-- Genuine sieve divisors automatically lie in the primitive support.
Positivity is retained explicitly when selecting the level. -/
theorem chenInitial_sieve_moduli_subset (N D : ℕ) (z : ℝ) :
    ((Finset.Icc 1 D).filter (fun d => d ∣ sieveProduct N (Nat.ceil z))) ⊆
      chenInitialPrimitiveModuli N D := by
  intro d hd
  obtain ⟨hd, hdiv⟩ := Finset.mem_filter.mp hd
  obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
  exact mem_chenInitialPrimitiveModuli.mpr
    ⟨hd1, hdD, coprime_of_dvd_sieveProduct hdiv⟩

/-- In particular the actual allowed sieve-divisor error sum is paid at
arbitrary logarithmic accuracy, without enlarging its source or deleting
the prime-modulus atom. -/
theorem eventually_sum_abs_chenInitial_sieve_rem_sub_primitive_le_logAccuracy (A : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ z : ℝ, ∀ hN : Even N, ∀ D : ℕ,
        (D : ℝ) ≤ Real.sqrt (N : ℝ) →
        (∑ d ∈ Finset.Icc 1 D with d ∣ sieveProduct N (Nat.ceil z),
          |(chenInitialBoundingSieve N z hN).rem d -
            finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N d|) ≤
              epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_sum_abs_chenInitial_rem_sub_primitive_le_logAccuracy A epsilon hepsilon]
    with N hcost
  intro z hN D hD
  exact hcost z hN D _ hD (chenInitial_sieve_moduli_subset N D z)

/-- Triangle transfer uses precisely the actual primitive-prefix error. -/
theorem sum_abs_chenInitial_rem_le_primitive_add_cost
    (N : ℕ) (z : ℝ) (hN : Even N) (S : Finset ℕ) :
    (∑ d ∈ S, |(chenInitialBoundingSieve N z hN).rem d|) ≤
      (∑ d ∈ S, |finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N d|) +
        chenInitialCorrectionCost N S := by
  calc
    _ ≤ ∑ d ∈ S,
        |finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N d| +
          |chenInitialPrimitiveCorrection N d| := by
      apply Finset.sum_le_sum
      intro d _
      have heq : (chenInitialBoundingSieve N z hN).rem d =
          finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N d +
            chenInitialPrimitiveCorrection N d := by
        have h := chenInitialBoundingSieve_rem_sub_primitive_error N z hN d
        linarith
      rw [heq]
      exact abs_add_le _ _
    _ ≤ _ := by
      rw [Finset.sum_add_distrib]
      exact add_le_add le_rfl (Finset.sum_le_sum
        (fun d _ => abs_chenInitialPrimitiveCorrection_le N d))

/-- Finite ordinary-BV-shaped composition, after the correction payment.
The main term may depend on the modulus but is common to its primitive
classes. The AP count is literally `P <= N`; `E` is not assumed small. -/
theorem sum_abs_chenInitial_rem_le_ordinary_primeAP_budget
    (N : ℕ) (z : ℝ) (hN : Even N) (D : ℕ) (S : Finset ℕ)
    (hS : S ⊆ chenInitialPrimitiveModuli N D) (M E : ℕ → ℝ)
    (hE : ∀ d ∈ S, ∀ a : ℕ, a < d → Nat.Coprime a d →
      |chenPrimeAPCount N a d - M d| ≤ E d) :
    (∑ d ∈ S, |(chenInitialBoundingSieve N z hN).rem d|) ≤
      2 * (∑ d ∈ S, E d) + chenInitialCorrectionCost N S := by
  have hprefix : ∀ d ∈ S,
      |finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N d| ≤ 2 * E d := by
    intro d hd
    obtain ⟨hd1, _, hcop⟩ := mem_chenInitialPrimitiveModuli.mp (hS hd)
    apply abs_finitePrimitiveDiscrepancy_le_two_mul_of_uniform_primitive
      (chenPrimePrefix N) (fun _ => 1) (M d) (E d) N d (by omega) hcop.symm
    intro a ha hacop
    have hmass : finiteCongruenceMass (chenPrimePrefix N) (fun _ => 1) a d =
        chenPrimeAPCount N a d := by
      simp [finiteCongruenceMass, chenPrimeAPCount]
    rw [hmass]
    exact hE d hd a ha hacop
  refine (sum_abs_chenInitial_rem_le_primitive_add_cost N z hN S).trans ?_
  apply add_le_add _ le_rfl
  simpa only [Finset.mul_sum] using Finset.sum_le_sum hprefix

/-- Once an ordinary inclusive prime-AP supplier gives a literal summed
error budget, the genuine initial sieve pays only a proved negligible
additive correction. This is an implication, not a BV theorem. -/
theorem eventually_chenInitial_rem_le_ordinary_primeAP_logAccuracy (A : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ z : ℝ, ∀ hN : Even N, ∀ D : ℕ, ∀ S : Finset ℕ,
        (D : ℝ) ≤ Real.sqrt (N : ℝ) → S ⊆ chenInitialPrimitiveModuli N D →
        ∀ M E : ℕ → ℝ,
          (∀ d ∈ S, ∀ a : ℕ, a < d → Nat.Coprime a d →
            |chenPrimeAPCount N a d - M d| ≤ E d) →
          (∑ d ∈ S, |(chenInitialBoundingSieve N z hN).rem d|) ≤
            2 * (∑ d ∈ S, E d) + epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  intro epsilon hepsilon
  filter_upwards [eventually_chenInitialCorrectionCost_le_logAccuracy A epsilon hepsilon]
    with N hcost
  intro z hN D S hD hS M E hE
  exact (sum_abs_chenInitial_rem_le_ordinary_primeAP_budget N z hN D S hS M E hE).trans
    (add_le_add le_rfl (hcost D S hD hS))

end

end ImbalancedChen
