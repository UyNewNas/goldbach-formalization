import ImbalancedChen.RealHalfProductMass
import ImbalancedChen.PowerErrorBudget

/-!
# Finite high/low envelope for the arbitrary-real half-product source

This is the arbitrary-real counterpart of `HalfProductMassSplit`.  It compares
the literal uncut source with the high-prime prefix sum on
`N^(b/(1+b)) < r ≤ sqrt N`.  The low part is paid by the genuine prime
rectangle with complementary exponent `1/(1+b)`, and the high order loss is
paid by the prime square.  Equality at the power split is assigned to the low
range and prime squares are retained.

All statements are finite.  No PNT, Mertens theorem, sieve estimate or target
bad-count bound is assumed.
-/

namespace ImbalancedChen

noncomputable section

open Filter Asymptotics Topology
open scoped BigOperators

/-- The larger-prime fibre of the arbitrary-real ordered source. -/
def realHalfProductPrimeFibre (b : ℝ) (N r : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc r (N / r)).filter fun q =>
    Nat.Prime q ∧ (q : ℝ) ^ b < (r : ℝ)

@[simp] theorem mem_realHalfProductPrimeFibre {b : ℝ} {N r q : ℕ} :
    q ∈ realHalfProductPrimeFibre b N r ↔
      r ≤ q ∧ q ≤ N / r ∧ Nat.Prime q ∧ (q : ℝ) ^ b < (r : ℝ) := by
  classical
  simp only [realHalfProductPrimeFibre, Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- The smaller prime of an actual ordered pair is at most `sqrt N`. -/
theorem realHalfProductPairs_fst_mem_primesLE_sqrt {b T : ℝ} {N : ℕ}
    {a : ℕ × ℕ} (ha : a ∈ realHalfProductPairs b N T) :
    a.1 ∈ Nat.primesLE (Nat.sqrt N) := by
  rcases a with ⟨r, q⟩
  obtain ⟨hr, _, hrq, _, _, hN⟩ := mem_realHalfProductPairs.mp ha
  exact Nat.mem_primesLE.mpr
    ⟨Nat.le_sqrt.mpr ((Nat.mul_le_mul_left r hrq).trans hN), hr⟩

/-- Projection onto the second coordinate is a bijection in one fixed fibre. -/
theorem realHalfProductPairs_fst_fibre_card {b : ℝ} {N r : ℕ}
    (hr : Nat.Prime r) :
    ((realHalfProductPairs b N 0).filter (fun a => a.1 = r)).card =
      (realHalfProductPrimeFibre b N r).card := by
  classical
  refine Finset.card_bij (fun a _ => a.2) ?_ ?_ ?_
  · rintro ⟨s, q⟩ ha
    rcases Finset.mem_filter.mp ha with ⟨ha, hs⟩
    dsimp only at hs
    subst s
    obtain ⟨_, hq, hrq, hpow, _, hN⟩ := mem_realHalfProductPairs.mp ha
    exact mem_realHalfProductPrimeFibre.mpr
      ⟨hrq, (Nat.le_div_iff_mul_le hr.pos).mpr
        (by simpa only [Nat.mul_comm] using hN), hq, hpow⟩
  · intro a ha c hc hac
    have ha' := (Finset.mem_filter.mp ha).2
    have hc' := (Finset.mem_filter.mp hc).2
    exact Prod.ext (ha'.trans hc'.symm) hac
  · intro q hq
    obtain ⟨hrq, hqN, hprime, hpow⟩ := mem_realHalfProductPrimeFibre.mp hq
    refine ⟨(r, q), Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
    exact mem_realHalfProductPairs.mpr
      ⟨hr, hprime, hrq, hpow, Nat.cast_nonneg _,
        by simpa only [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le hr.pos).mp hqN⟩

/-- Exact fibre sum for the uncut arbitrary-real source. -/
theorem realHalfProductSource_card_eq_sum_primeFibre (b : ℝ) (N : ℕ) :
    (realHalfProductSource b N 0).card =
      ∑ r ∈ Nat.primesLE (Nat.sqrt N),
        (realHalfProductPrimeFibre b N r).card := by
  classical
  rw [← realHalfProductPairs_card_eq]
  have hc : (realHalfProductPairs b N 0).card =
      ∑ r ∈ Nat.primesLE (Nat.sqrt N),
        ((realHalfProductPairs b N 0).filter (fun a => a.1 = r)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun a ha => realHalfProductPairs_fst_mem_primesLE_sqrt ha)
  rw [hc]
  apply Finset.sum_congr rfl
  intro r hr
  exact realHalfProductPairs_fst_fibre_card (Nat.mem_primesLE.mp hr).2

/-- Exact low/high partition, with equality at the split assigned low. -/
theorem realHalfProductSource_card_eq_low_add_high (b : ℝ) (N A : ℕ) :
    (realHalfProductSource b N 0).card =
      (∑ r ∈ halfProductLowPrimes N A,
        (realHalfProductPrimeFibre b N r).card) +
      ∑ r ∈ halfProductHighPrimes N A,
        (realHalfProductPrimeFibre b N r).card := by
  classical
  rw [realHalfProductSource_card_eq_sum_primeFibre]
  simpa only [halfProductLowPrimes, halfProductHighPrimes, not_le] using
    (Finset.sum_filter_add_sum_filter_not (Nat.primesLE (Nat.sqrt N))
      (fun r => r ≤ A) (fun r => (realHalfProductPrimeFibre b N r).card)).symm

theorem realHalfProductPrimeFibre_card_le_prefix (b : ℝ) (N r : ℕ) :
    (realHalfProductPrimeFibre b N r).card ≤ Nat.primeCounting (N / r) := by
  classical
  have hs : realHalfProductPrimeFibre b N r ⊆ Nat.primesLE (N / r) := by
    intro q hq
    obtain ⟨_, hqN, hprime, _⟩ := mem_realHalfProductPrimeFibre.mp hq
    exact Nat.mem_primesLE.mpr ⟨hqN, hprime⟩
  exact (Finset.card_le_card hs).trans_eq
    (Nat.primesLE_card_eq_primeCounting (N / r))

theorem realHalfProductPrimeFibre_card_le_of_bound {b : ℝ} {N r B : ℕ}
    (hB : ∀ q ∈ realHalfProductPrimeFibre b N r, q ≤ B) :
    (realHalfProductPrimeFibre b N r).card ≤ Nat.primeCounting B := by
  classical
  have hs : realHalfProductPrimeFibre b N r ⊆ Nat.primesLE B := by
    intro q hq
    exact Nat.mem_primesLE.mpr
      ⟨hB q hq, (mem_realHalfProductPrimeFibre.mp hq).2.2.1⟩
  exact (Finset.card_le_card hs).trans_eq
    (Nat.primesLE_card_eq_primeCounting B)

/-- In a high fibre, automatic badness leaves exactly the ordering loss
`pi(r-1)`; the diagonal square is included. -/
theorem realHalfProductPrimeFibre_card_add_order_loss {b : ℝ} {N r : ℕ}
    (hr : r ∈ Nat.primesLE (Nat.sqrt N))
    (hbad : ∀ q, Nat.Prime q → q ≤ N / r → (q : ℝ) ^ b < (r : ℝ)) :
    (realHalfProductPrimeFibre b N r).card + Nat.primeCounting (r - 1) =
      Nat.primeCounting (N / r) := by
  classical
  obtain ⟨hrN, hprime⟩ := Nat.mem_primesLE.mp hr
  have heq : realHalfProductPrimeFibre b N r =
      (Finset.Icc r (N / r)).filter Nat.Prime := by
    ext q
    simp only [mem_realHalfProductPrimeFibre, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hrq, hqN, hq, _⟩
      exact ⟨⟨hrq, hqN⟩, hq⟩
    · rintro ⟨⟨hrq, hqN⟩, hq⟩
      exact ⟨hrq, hqN, hq, hbad q hq hqN⟩
  have hself : r ≤ N / r :=
    (Nat.le_div_iff_mul_le hprime.pos).mpr (Nat.le_sqrt.mp hrN)
  rw [heq, card_primes_Icc_eq_primeCounting_sub hprime.pos]
  exact Nat.sub_add_cancel
    (Nat.monotone_primeCounting ((Nat.sub_le r 1).trans hself))

theorem realHalfProduct_low_mass_le_rectangle {b : ℝ} {N A B : ℕ}
    (hB : ∀ r ∈ halfProductLowPrimes N A,
      ∀ q ∈ realHalfProductPrimeFibre b N r, q ≤ B) :
    (∑ r ∈ halfProductLowPrimes N A,
      (realHalfProductPrimeFibre b N r).card) ≤
      Nat.primeCounting A * Nat.primeCounting B := by
  calc
    (∑ r ∈ halfProductLowPrimes N A,
        (realHalfProductPrimeFibre b N r).card) ≤
        ∑ _r ∈ halfProductLowPrimes N A, Nat.primeCounting B := by
      exact Finset.sum_le_sum
        (fun r hr => realHalfProductPrimeFibre_card_le_of_bound (hB r hr))
    _ = (halfProductLowPrimes N A).card * Nat.primeCounting B := by simp
    _ ≤ Nat.primeCounting A * Nat.primeCounting B :=
      Nat.mul_le_mul_right _ (halfProductLowPrimes_card_le N A)

theorem realHalfProduct_prefix_le_high_mass_add_square {b : ℝ} {N A : ℕ}
    (hbad : ∀ r ∈ halfProductHighPrimes N A,
      ∀ q, Nat.Prime q → q ≤ N / r → (q : ℝ) ^ b < (r : ℝ)) :
    halfProductPrimePrefixMass N A ≤
      (∑ r ∈ halfProductHighPrimes N A,
        (realHalfProductPrimeFibre b N r).card) +
      Nat.primeCounting (Nat.sqrt N) ^ 2 := by
  classical
  have heq : halfProductPrimePrefixMass N A =
      (∑ r ∈ halfProductHighPrimes N A,
        (realHalfProductPrimeFibre b N r).card) +
      ∑ r ∈ halfProductHighPrimes N A, Nat.primeCounting (r - 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r hr =>
      (realHalfProductPrimeFibre_card_add_order_loss
        (Finset.mem_filter.mp hr).1 (hbad r hr)).symm)
  have horder : (∑ r ∈ halfProductHighPrimes N A,
      Nat.primeCounting (r - 1)) ≤
      Nat.primeCounting (Nat.sqrt N) ^ 2 := by
    calc
      (∑ r ∈ halfProductHighPrimes N A, Nat.primeCounting (r - 1)) ≤
          ∑ _r ∈ halfProductHighPrimes N A,
            Nat.primeCounting (Nat.sqrt N) := by
        apply Finset.sum_le_sum
        intro r hr
        exact Nat.monotone_primeCounting ((Nat.sub_le r 1).trans
          (Nat.mem_primesLE.mp (Finset.mem_filter.mp hr).1).1)
      _ = (halfProductHighPrimes N A).card *
          Nat.primeCounting (Nat.sqrt N) := by simp
      _ ≤ Nat.primeCounting (Nat.sqrt N) *
          Nat.primeCounting (Nat.sqrt N) :=
        Nat.mul_le_mul_right _ (halfProductHighPrimes_card_le N A)
      _ = Nat.primeCounting (Nat.sqrt N) ^ 2 := (pow_two _).symm
  rw [heq]
  exact Nat.add_le_add_left horder _

/-- Purely finite envelope at an arbitrary integer split. -/
theorem realHalfProductSource_primePrefix_envelope {b : ℝ} {N A B : ℕ}
    (hB : ∀ r ∈ halfProductLowPrimes N A,
      ∀ q ∈ realHalfProductPrimeFibre b N r, q ≤ B)
    (hbad : ∀ r ∈ halfProductHighPrimes N A,
      ∀ q, Nat.Prime q → q ≤ N / r → (q : ℝ) ^ b < (r : ℝ)) :
    |((realHalfProductSource b N 0).card : ℝ) -
        (halfProductPrimePrefixMass N A : ℝ)| ≤
      (Nat.primeCounting A : ℝ) * Nat.primeCounting B +
        (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 := by
  have hsplit := realHalfProductSource_card_eq_low_add_high b N A
  have hlo := realHalfProduct_low_mass_le_rectangle hB
  have hhi := realHalfProduct_prefix_le_high_mass_add_square hbad
  have hhigh : (∑ r ∈ halfProductHighPrimes N A,
      (realHalfProductPrimeFibre b N r).card) ≤
      halfProductPrimePrefixMass N A :=
    Finset.sum_le_sum
      (fun r _ => realHalfProductPrimeFibre_card_le_prefix b N r)
  have hupper : (realHalfProductSource b N 0).card ≤
      halfProductPrimePrefixMass N A +
        Nat.primeCounting A * Nat.primeCounting B := by omega
  have hlower : halfProductPrimePrefixMass N A ≤
      (realHalfProductSource b N 0).card +
        Nat.primeCounting (Nat.sqrt N) ^ 2 := by omega
  have hupperR : ((realHalfProductSource b N 0).card : ℝ) ≤
      (halfProductPrimePrefixMass N A : ℝ) +
        (Nat.primeCounting A : ℝ) * Nat.primeCounting B := by
    exact_mod_cast hupper
  have hlowerR : (halfProductPrimePrefixMass N A : ℝ) ≤
      ((realHalfProductSource b N 0).card : ℝ) +
        (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 := by
    exact_mod_cast hlower
  have hrect : (0 : ℝ) ≤
      (Nat.primeCounting A : ℝ) * Nat.primeCounting B := by positivity
  have hsq : (0 : ℝ) ≤
      (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 := sq_nonneg _
  apply abs_le.mpr
  constructor <;> linarith

/-- Arbitrary-real analytic-facing prime-prefix approximation. -/
def realHalfProductMassApprox (b : ℝ) (N : ℕ) : ℕ :=
  halfProductPrimePrefixMass N
    (Nat.floor ((N : ℝ) ^ realHalfProductMassAlpha b))

/-- Explicit finite envelope at the exact arbitrary-real power split. -/
theorem realHalfProductSource_mass_split_envelope {b : ℝ}
    (hb : 0 < b) {N : ℕ} (hN : 0 < N) :
    |((realHalfProductSource b N 0).card : ℝ) -
        (realHalfProductMassApprox b N : ℝ)| ≤
      (Nat.primeCounting
          (Nat.floor ((N : ℝ) ^ realHalfProductMassAlpha b)) : ℝ) *
        Nat.primeCounting
          (Nat.floor ((N : ℝ) ^ realHalfProductMassBeta b)) +
      (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 := by
  classical
  unfold realHalfProductMassApprox
  apply realHalfProductSource_primePrefix_envelope
  · intro r hr q hq
    have hrle := (Finset.mem_filter.mp hr).2
    have hrR : (r : ℝ) ≤ (N : ℝ) ^ realHalfProductMassAlpha b :=
      (Nat.cast_le.mpr hrle).trans
        (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    have hrprime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hr).1).2
    have hqprime := (mem_realHalfProductPrimeFibre.mp hq).2.2.1
    apply Nat.le_floor
    exact (realHalfProduct_low_prime_lt_power hb hN hrprime.pos hqprime.pos hrR
      (mem_realHalfProductPrimeFibre.mp hq).2.2.2).le
  · intro r hr q hq hqN
    obtain ⟨hrS, hrA⟩ := Finset.mem_filter.mp hr
    have hrprime := (Nat.mem_primesLE.mp hrS).2
    have hlarge : (N : ℝ) ^ realHalfProductMassAlpha b < (r : ℝ) := by
      by_contra hn
      exact (not_le_of_gt hrA) (Nat.le_floor (le_of_not_gt hn))
    apply realHalfProduct_high_prime_bad hb hrprime.pos hq.pos _ hlarge
    simpa only [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le hrprime.pos).mp hqN

/-- The real-cutoff source is the corresponding filter of the uncut source. -/
theorem realHalfProductSource_eq_zero_filter (b : ℝ) (N : ℕ) (T : ℝ) :
    realHalfProductSource b N T =
      (realHalfProductSource b N 0).filter (fun m : ℕ => T ≤ (m : ℝ)) := by
  classical
  ext m
  simp only [mem_realHalfProductSource, Finset.mem_filter]
  constructor
  · rintro ⟨hmN, hT, hm⟩
    exact ⟨⟨hmN, Nat.cast_nonneg m, hm⟩, hT⟩
  · rintro ⟨⟨hmN, _, hm⟩, hT⟩
    exact ⟨hmN, hT, hm⟩

def smallRealHalfProductSource (b : ℝ) (N : ℕ) (T : ℝ) : Finset ℕ := by
  classical
  exact (realHalfProductSource b N 0).filter (fun m : ℕ => (m : ℝ) < T)

theorem realHalfProductSource_zero_card_eq_cutoff_add_small
    (b : ℝ) (N : ℕ) (T : ℝ) :
    (realHalfProductSource b N 0).card =
      (realHalfProductSource b N T).card +
        (smallRealHalfProductSource b N T).card := by
  classical
  rw [realHalfProductSource_eq_zero_filter b N T]
  have h := Finset.card_filter_add_card_filter_not
    (s := realHalfProductSource b N 0) (fun m : ℕ => T ≤ (m : ℝ))
  simpa only [smallRealHalfProductSource, not_le] using h.symm

theorem smallRealHalfProductSource_card_le_ceil (b : ℝ) (N : ℕ) (T : ℝ) :
    (smallRealHalfProductSource b N T).card ≤ Nat.ceil T := by
  classical
  have hs : smallRealHalfProductSource b N T ⊆ Finset.range (Nat.ceil T) := by
    intro m hm
    exact Finset.mem_range.mpr
      (Nat.lt_ceil.mpr (Finset.mem_filter.mp hm).2)
  exact (Finset.card_le_card hs).trans_eq (Finset.card_range _)

/-- The lower product cutoff used in the current manuscript, written with
the manuscript parameter `κ₀`.  Keeping `κ` explicit makes the formal
statement independent of the later numerical choice of `κ₀`. -/
def manuscriptHalfProductCutoff (κ : ℝ) (N : ℕ) : ℝ :=
  2 * (N : ℝ) ^ (1 - κ)

theorem manuscriptHalfProductCutoff_nonneg (κ : ℝ) (N : ℕ) :
    0 ≤ manuscriptHalfProductCutoff κ N := by
  exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg N) _)

/-- For every fixed positive `κ`, the current manuscript cutoff
`2 N^(1-κ)` (including the exact ceiling unit) is negligible on the
`N / log N` scale used by the ordered semiprime mass. -/
theorem eventually_manuscriptHalfProductCutoff_add_one_le_massScale
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop,
        manuscriptHalfProductCutoff κ N + 1 ≤
          epsilon * ((N : ℝ) / Real.log (N : ℝ)) := by
  intro epsilon hepsilon
  have hdecay : Tendsto (fun N : ℕ =>
      2 * (Real.log (N : ℝ) / (N : ℝ) ^ κ)) atTop (𝓝 0) := by
    simpa only [pow_one, mul_zero] using
      (tendsto_nat_log_pow_div_rpow 1 hκ).const_mul 2
  have heps2 : 0 < epsilon / 2 := half_pos hepsilon
  have hsmall : ∀ᶠ N : ℕ in atTop,
      2 * (Real.log (N : ℝ) / (N : ℝ) ^ κ) < epsilon / 2 :=
    hdecay.eventually (gt_mem_nhds heps2)
  have hscale : Tendsto (fun N : ℕ => (N : ℝ) / Real.log (N : ℝ))
      atTop atTop := by
    have h := ((Real.tendsto_exp_div_pow_atTop 1).comp
      Real.tendsto_log_atTop).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    simp only [Function.comp_apply, Real.exp_log hNpos, pow_one]
  have hunit : ∀ᶠ N : ℕ in atTop,
      1 ≤ (epsilon / 2) * ((N : ℝ) / Real.log (N : ℝ)) :=
    (hscale.const_mul_atTop heps2).eventually (eventually_ge_atTop 1)
  filter_upwards [hsmall, hunit, eventually_ge_atTop (2 : ℕ)]
    with N hsmallN hunitN hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hpowpos : 0 < (N : ℝ) ^ κ := Real.rpow_pos_of_pos hNpos κ
  have hbase : 0 ≤ (N : ℝ) / Real.log (N : ℝ) :=
    div_nonneg hNpos.le hlogpos.le
  have hcutoff : manuscriptHalfProductCutoff κ N ≤
      (epsilon / 2) * ((N : ℝ) / Real.log (N : ℝ)) := by
    calc
      manuscriptHalfProductCutoff κ N =
          (2 * (Real.log (N : ℝ) / (N : ℝ) ^ κ)) *
            ((N : ℝ) / Real.log (N : ℝ)) := by
        unfold manuscriptHalfProductCutoff
        rw [Real.rpow_sub hNpos, Real.rpow_one]
        field_simp [ne_of_gt hNpos, ne_of_gt hlogpos, ne_of_gt hpowpos]
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmallN.le hbase
  linarith

/-- Cutoff envelope with the exact ceiling loss. -/
theorem realHalfProductSource_mass_split_cutoff_envelope {b : ℝ}
    (hb : 0 < b) {N : ℕ} (hN : 0 < N) (T : ℝ) :
    |((realHalfProductSource b N T).card : ℝ) -
        (realHalfProductMassApprox b N : ℝ)| ≤
      (Nat.primeCounting
          (Nat.floor ((N : ℝ) ^ realHalfProductMassAlpha b)) : ℝ) *
        Nat.primeCounting
          (Nat.floor ((N : ℝ) ^ realHalfProductMassBeta b)) +
      (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 + Nat.ceil T := by
  have hmass := abs_le.mp (realHalfProductSource_mass_split_envelope hb hN)
  have hpart : ((realHalfProductSource b N 0).card : ℝ) =
      ((realHalfProductSource b N T).card : ℝ) +
        ((smallRealHalfProductSource b N T).card : ℝ) := by
    exact_mod_cast realHalfProductSource_zero_card_eq_cutoff_add_small b N T
  have hsmall : ((smallRealHalfProductSource b N T).card : ℝ) ≤
      (Nat.ceil T : ℝ) := by
    exact_mod_cast smallRealHalfProductSource_card_le_ceil b N T
  have hsmall0 : (0 : ℝ) ≤ (smallRealHalfProductSource b N T).card :=
    Nat.cast_nonneg _
  have hceil0 : (0 : ℝ) ≤ Nat.ceil T := Nat.cast_nonneg _
  apply abs_le.mpr
  constructor <;> linarith [hmass.1, hmass.2]

/-- Under the same explicit real-PNT witness used by the rational mass module,
the literal arbitrary-real cutoff source differs from its high-prime prefix
approximation by `o(N / log N)` in epsilon-eventual form.  The cutoff is the
actual `logCutoff`; no target mass estimate is assumed. -/
theorem eventually_realHalfProductSource_massApprox_error_of_real_pnt
    (hPNT : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ x : ℝ, (Nat.primeCounting (Nat.floor x) : ℝ) =
        (1 + c x) * x / Real.log x)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      |((realHalfProductSource b N (logCutoff N)).card : ℝ) -
          (realHalfProductMassApprox b N : ℝ)| ≤
        epsilon * ((N : ℝ) / Real.log (N : ℝ)) := by
  let a : ℝ := realHalfProductMassAlpha b
  let d : ℝ := realHalfProductMassBeta b
  have ha : 0 < a := (realHalfProductMass_exponents hb hb1).1
  have hd : 0 < d := (realHalfProductMass_exponents hb hb1).2.2.1
  have had : a + d = 1 := (realHalfProductMass_exponents hb hb1).2.2.2.2
  let C : ℝ := (2 / a) * (2 / d) + 16
  have heps3 : 0 < epsilon / 3 := div_pos hepsilon (by norm_num)
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgeomRatio : Tendsto (fun N : ℕ => C / Real.log (N : ℝ))
      atTop (𝓝 0) := hlog.const_div_atTop C
  have hcutRatio : Tendsto (fun N : ℕ => 1 / (Real.log (N : ℝ)) ^ 9)
      atTop (𝓝 0) := by
    have hpow : Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ 9) atTop atTop :=
      (tendsto_pow_atTop (α := ℝ) (n := 9) (by norm_num)).comp hlog
    exact hpow.const_div_atTop 1
  have hscale : Tendsto (fun N : ℕ => (N : ℝ) / Real.log (N : ℝ))
      atTop atTop := by
    have h := ((Real.tendsto_exp_div_pow_atTop 1).comp
      Real.tendsto_log_atTop).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    simp only [Function.comp_apply, Real.exp_log hNpos, pow_one]
  have hunit : ∀ᶠ N : ℕ in atTop,
      1 ≤ (epsilon / 3) * ((N : ℝ) / Real.log (N : ℝ)) :=
    (hscale.const_mul_atTop heps3).eventually (eventually_ge_atTop 1)
  filter_upwards
    [eventually_primeCounting_rpow_le_of_real_pnt hPNT ha,
      eventually_primeCounting_rpow_le_of_real_pnt hPNT hd,
      eventually_primeCounting_rpow_le_of_real_pnt hPNT
        (show (0 : ℝ) < 1 / 2 by norm_num),
      hgeomRatio.eventually (gt_mem_nhds heps3),
      hcutRatio.eventually (gt_mem_nhds heps3), hunit,
      eventually_ge_atTop (2 : ℕ)]
    with N hA hD hHalf hgeomSmall hcutSmall hunitN hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hbase : 0 ≤ (N : ℝ) / Real.log (N : ℝ) :=
    div_nonneg (Nat.cast_nonneg N) hlogpos.le
  have hpower : (N : ℝ) ^ a * (N : ℝ) ^ d = (N : ℝ) := by
    rw [← Real.rpow_add hNpos, had, Real.rpow_one]
  have hrectangle :
      (Nat.primeCounting (Nat.floor ((N : ℝ) ^ a)) : ℝ) *
          Nat.primeCounting (Nat.floor ((N : ℝ) ^ d)) ≤
        ((2 / a) * (2 / d)) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
    calc
      (Nat.primeCounting (Nat.floor ((N : ℝ) ^ a)) : ℝ) *
          Nat.primeCounting (Nat.floor ((N : ℝ) ^ d)) ≤
          ((2 / a) * (N : ℝ) ^ a / Real.log (N : ℝ)) *
            ((2 / d) * (N : ℝ) ^ d / Real.log (N : ℝ)) :=
        mul_le_mul hA hD (Nat.cast_nonneg _) (by positivity)
      _ = ((2 / a) * (2 / d)) *
          ((N : ℝ) ^ a * (N : ℝ) ^ d) / (Real.log (N : ℝ)) ^ 2 := by ring
      _ = ((2 / a) * (2 / d)) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
        rw [hpower]
  have hSqrt : (Nat.primeCounting (Nat.sqrt N) : ℝ) ≤
      4 * Real.sqrt (N : ℝ) / Real.log (N : ℝ) := by
    simpa only [← Real.sqrt_eq_rpow, Real.nat_floor_real_sqrt_eq_nat_sqrt,
      show (2 : ℝ) / (1 / 2) = 4 by norm_num] using hHalf
  have hsquare : (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 ≤
      16 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
    calc
      (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 ≤
          (4 * Real.sqrt (N : ℝ) / Real.log (N : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hSqrt 2
      _ = 16 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
        norm_num
  have hgeometric :
      (Nat.primeCounting (Nat.floor ((N : ℝ) ^ a)) : ℝ) *
          Nat.primeCounting (Nat.floor ((N : ℝ) ^ d)) +
          (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 ≤
        C * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
    calc
      _ ≤ ((2 / a) * (2 / d)) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 +
          16 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 :=
        add_le_add hrectangle hsquare
      _ = C * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by dsimp [C]; ring
  have hgeometricCost : C * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 ≤
      (epsilon / 3) * ((N : ℝ) / Real.log (N : ℝ)) := by
    calc
      _ = (C / Real.log (N : ℝ)) *
          ((N : ℝ) / Real.log (N : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hgeomSmall.le hbase
  have hcutoffCost : logCutoff N ≤
      (epsilon / 3) * ((N : ℝ) / Real.log (N : ℝ)) := by
    calc
      logCutoff N = (1 / (Real.log (N : ℝ)) ^ 9) *
          ((N : ℝ) / Real.log (N : ℝ)) := by
        unfold logCutoff
        field_simp [ne_of_gt hlogpos]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcutSmall.le hbase
  have hceil : (Nat.ceil (logCutoff N) : ℝ) ≤ logCutoff N + 1 :=
    (Nat.ceil_lt_add_one (logCutoff_nonneg N)).le
  calc
    |((realHalfProductSource b N (logCutoff N)).card : ℝ) -
        (realHalfProductMassApprox b N : ℝ)| ≤
        (Nat.primeCounting (Nat.floor ((N : ℝ) ^ a)) : ℝ) *
          Nat.primeCounting (Nat.floor ((N : ℝ) ^ d)) +
          (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 + Nat.ceil (logCutoff N) := by
      simpa only [a, d] using
        realHalfProductSource_mass_split_cutoff_envelope hb (by omega) (logCutoff N)
    _ ≤ C * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 + (logCutoff N + 1) :=
      add_le_add hgeometric hceil
    _ ≤ epsilon * ((N : ℝ) / Real.log (N : ℝ)) := by
      linarith [hgeometricCost, hcutoffCost, hunitN]

/-- Current-manuscript version of the preceding source envelope.  Here the
source is cut at the literal lower wall `2 N^(1-κ₀)` rather than at the
historical logarithmic auxiliary cutoff.  Only positivity of the fixed
parameter `κ₀` is needed to make this discarded range `o(N / log N)`. -/
theorem eventually_realHalfProductSource_manuscriptCutoff_massApprox_error_of_real_pnt
    (hPNT : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ x : ℝ, (Nat.primeCounting (Nat.floor x) : ℝ) =
        (1 + c x) * x / Real.log x)
    {b κ : ℝ} (hb : 0 < b) (hb1 : b < 1) (hκ : 0 < κ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      |((realHalfProductSource b N
          (manuscriptHalfProductCutoff κ N)).card : ℝ) -
          (realHalfProductMassApprox b N : ℝ)| ≤
        epsilon * ((N : ℝ) / Real.log (N : ℝ)) := by
  let a : ℝ := realHalfProductMassAlpha b
  let d : ℝ := realHalfProductMassBeta b
  have ha : 0 < a := (realHalfProductMass_exponents hb hb1).1
  have hd : 0 < d := (realHalfProductMass_exponents hb hb1).2.2.1
  have had : a + d = 1 := (realHalfProductMass_exponents hb hb1).2.2.2.2
  let C : ℝ := (2 / a) * (2 / d) + 16
  have heps2 : 0 < epsilon / 2 := half_pos hepsilon
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgeomRatio : Tendsto (fun N : ℕ => C / Real.log (N : ℝ))
      atTop (𝓝 0) := hlog.const_div_atTop C
  filter_upwards
    [eventually_primeCounting_rpow_le_of_real_pnt hPNT ha,
      eventually_primeCounting_rpow_le_of_real_pnt hPNT hd,
      eventually_primeCounting_rpow_le_of_real_pnt hPNT
        (show (0 : ℝ) < 1 / 2 by norm_num),
      hgeomRatio.eventually (gt_mem_nhds heps2),
      eventually_manuscriptHalfProductCutoff_add_one_le_massScale hκ
        (epsilon / 2) heps2,
      eventually_ge_atTop (2 : ℕ)]
    with N hA hD hHalf hgeomSmall hcutoffCost hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hN1
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hbase : 0 ≤ (N : ℝ) / Real.log (N : ℝ) :=
    div_nonneg (Nat.cast_nonneg N) hlogpos.le
  have hpower : (N : ℝ) ^ a * (N : ℝ) ^ d = (N : ℝ) := by
    rw [← Real.rpow_add hNpos, had, Real.rpow_one]
  have hrectangle :
      (Nat.primeCounting (Nat.floor ((N : ℝ) ^ a)) : ℝ) *
          Nat.primeCounting (Nat.floor ((N : ℝ) ^ d)) ≤
        ((2 / a) * (2 / d)) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
    calc
      (Nat.primeCounting (Nat.floor ((N : ℝ) ^ a)) : ℝ) *
          Nat.primeCounting (Nat.floor ((N : ℝ) ^ d)) ≤
          ((2 / a) * (N : ℝ) ^ a / Real.log (N : ℝ)) *
            ((2 / d) * (N : ℝ) ^ d / Real.log (N : ℝ)) :=
        mul_le_mul hA hD (Nat.cast_nonneg _) (by positivity)
      _ = ((2 / a) * (2 / d)) *
          ((N : ℝ) ^ a * (N : ℝ) ^ d) / (Real.log (N : ℝ)) ^ 2 := by ring
      _ = ((2 / a) * (2 / d)) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
        rw [hpower]
  have hSqrt : (Nat.primeCounting (Nat.sqrt N) : ℝ) ≤
      4 * Real.sqrt (N : ℝ) / Real.log (N : ℝ) := by
    simpa only [← Real.sqrt_eq_rpow, Real.nat_floor_real_sqrt_eq_nat_sqrt,
      show (2 : ℝ) / (1 / 2) = 4 by norm_num] using hHalf
  have hsquare : (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 ≤
      16 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
    calc
      (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 ≤
          (4 * Real.sqrt (N : ℝ) / Real.log (N : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hSqrt 2
      _ = 16 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
        norm_num
  have hgeometric :
      (Nat.primeCounting (Nat.floor ((N : ℝ) ^ a)) : ℝ) *
          Nat.primeCounting (Nat.floor ((N : ℝ) ^ d)) +
          (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 ≤
        C * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by
    calc
      _ ≤ ((2 / a) * (2 / d)) * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 +
          16 * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 :=
        add_le_add hrectangle hsquare
      _ = C * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 := by dsimp [C]; ring
  have hgeometricCost : C * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 ≤
      (epsilon / 2) * ((N : ℝ) / Real.log (N : ℝ)) := by
    calc
      _ = (C / Real.log (N : ℝ)) *
          ((N : ℝ) / Real.log (N : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hgeomSmall.le hbase
  have hceil : (Nat.ceil (manuscriptHalfProductCutoff κ N) : ℝ) ≤
      manuscriptHalfProductCutoff κ N + 1 :=
    (Nat.ceil_lt_add_one (manuscriptHalfProductCutoff_nonneg κ N)).le
  calc
    |((realHalfProductSource b N
        (manuscriptHalfProductCutoff κ N)).card : ℝ) -
        (realHalfProductMassApprox b N : ℝ)| ≤
        (Nat.primeCounting (Nat.floor ((N : ℝ) ^ a)) : ℝ) *
          Nat.primeCounting (Nat.floor ((N : ℝ) ^ d)) +
          (Nat.primeCounting (Nat.sqrt N) : ℝ) ^ 2 +
            Nat.ceil (manuscriptHalfProductCutoff κ N) := by
      simpa only [a, d] using
        realHalfProductSource_mass_split_cutoff_envelope hb (by omega)
          (manuscriptHalfProductCutoff κ N)
    _ ≤ C * (N : ℝ) / (Real.log (N : ℝ)) ^ 2 +
        (manuscriptHalfProductCutoff κ N + 1) :=
      add_le_add hgeometric hceil
    _ ≤ epsilon * ((N : ℝ) / Real.log (N : ℝ)) := by
      linarith [hgeometricCost, hcutoffCost]

/-- Uniform real-PNT control converts the arbitrary-real prime-prefix
approximation to the literal fixed-test reciprocal-prime sum. -/
theorem eventually_realHalfProductMassApprox_weighted_error_of_real_pnt
    (hPNT : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ x : ℝ, (Nat.primeCounting (Nat.floor x) : ℝ) =
        (1 + c x) * x / Real.log x)
    (b : ℝ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      |(realHalfProductMassApprox b N : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) -
          realHalfProductMassWeightedPrimeSum b N| ≤
        epsilon * realHalfProductMassWeightedPrimeSum b N := by
  classical
  filter_upwards
    [eventually_primeCounting_uniform_sqrt_tail_of_real_pnt hPNT epsilon hepsilon,
      eventually_ge_atTop (2 : ℕ)] with N htail hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hscale : 0 < (N : ℝ) / Real.log (N : ℝ) :=
    div_pos (zero_lt_one.trans hN1) (Real.log_pos hN1)
  have hterm : ∀ r ∈ halfProductHighPrimes N
      (Nat.floor ((N : ℝ) ^ realHalfProductMassAlpha b)),
      |(Nat.primeCounting (N / r) : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) -
          (1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ)| ≤
        epsilon *
          ((1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ)) := by
    intro r hr
    obtain ⟨hrpos, hrN, htailr⟩ := halfProductHighPrimes_real_endpoint hr
    have happrox := (htail ((N : ℝ) / (r : ℝ)) htailr).2.2
    rw [halfProduct_nat_floor_div (Nat.cast_pos.mp hrpos)] at happrox
    have hid := halfProduct_normalized_prime_mainTerm hN hrpos hrN
    calc
      |(Nat.primeCounting (N / r) : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) -
          (1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ)| =
          |(Nat.primeCounting (N / r) : ℝ) -
            ((N : ℝ) / (r : ℝ)) / Real.log ((N : ℝ) / (r : ℝ))| /
              ((N : ℝ) / Real.log (N : ℝ)) := by
        rw [← hid, ← sub_div, abs_div, abs_of_pos hscale]
      _ ≤ (epsilon * (((N : ℝ) / (r : ℝ)) /
          Real.log ((N : ℝ) / (r : ℝ)))) /
          ((N : ℝ) / Real.log (N : ℝ)) :=
        div_le_div_of_nonneg_right happrox hscale.le
      _ = epsilon *
          ((1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ)) := by
        rw [mul_div_assoc, hid]
  rw [realHalfProductMassApprox, halfProductPrimePrefixMass, Nat.cast_sum,
    Finset.sum_div, realHalfProductMassWeightedPrimeSum,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ r ∈ halfProductHighPrimes N
        (Nat.floor ((N : ℝ) ^ realHalfProductMassAlpha b)),
        |(Nat.primeCounting (N / r) : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) -
          (1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ halfProductHighPrimes N
        (Nat.floor ((N : ℝ) ^ realHalfProductMassAlpha b)),
        epsilon *
          ((1 / (1 - Real.log (r : ℝ) / Real.log (N : ℝ))) / (r : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The explicit PNT witness and standard weighted-prime Mertens integral
give the arbitrary-real prefix limit with coefficient `log(1/b)`. -/
theorem tendsto_realHalfProductMassApprox_of_real_pnt_and_weighted_mertens
    (hPNT : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ x : ℝ, (Nat.primeCounting (Nat.floor x) : ℝ) =
        (1 + c x) * x / Real.log x)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hMertens : Tendsto (fun N : ℕ =>
      realPrimeReciprocalLogIntervalSum (fun u => 1 / (1 - u)) N
        (realHalfProductMassAlpha b) (1 / 2)) atTop
      (𝓝 (∫ u in realHalfProductMassAlpha b..(1 / 2 : ℝ),
        (1 / (1 - u)) / u))) :
    Tendsto (fun N : ℕ => (realHalfProductMassApprox b N : ℝ) /
      ((N : ℝ) / Real.log (N : ℝ)))
      atTop (𝓝 (Real.log (1 / b))) := by
  let L : ℝ := Real.log (1 / b)
  have hw : Tendsto (realHalfProductMassWeightedPrimeSum b) atTop (𝓝 L) :=
    tendsto_realHalfProductMassWeightedPrimeSum_of_integral_limit hb hb1 hMertens
  have hC : 0 < |L| + 1 := by positivity
  have hbounded : ∀ᶠ N : ℕ in atTop,
      realHalfProductMassWeightedPrimeSum b N < |L| + 1 :=
    hw.eventually (gt_mem_nhds (lt_of_le_of_lt (le_abs_self L) (lt_add_one _)))
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  have hsmall : 0 < (epsilon / 2) / (|L| + 1) :=
    div_pos (half_pos hepsilon) hC
  have hnear := (Metric.tendsto_nhds.mp hw) (epsilon / 2) (half_pos hepsilon)
  filter_upwards
    [eventually_realHalfProductMassApprox_weighted_error_of_real_pnt hPNT b
      ((epsilon / 2) / (|L| + 1)) hsmall, hbounded, hnear]
    with N herr hbound hnearN
  rw [Real.dist_eq] at hnearN ⊢
  have herrsmall : |(realHalfProductMassApprox b N : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)) -
        realHalfProductMassWeightedPrimeSum b N| < epsilon / 2 := by
    calc
      _ ≤ ((epsilon / 2) / (|L| + 1)) *
          realHalfProductMassWeightedPrimeSum b N := herr
      _ < ((epsilon / 2) / (|L| + 1)) * (|L| + 1) :=
        mul_lt_mul_of_pos_left hbound hsmall
      _ = epsilon / 2 := div_mul_cancel₀ _ (ne_of_gt hC)
  have htriangle := abs_add_le
    ((realHalfProductMassApprox b N : ℝ) /
      ((N : ℝ) / Real.log (N : ℝ)) -
      realHalfProductMassWeightedPrimeSum b N)
    (realHalfProductMassWeightedPrimeSum b N - L)
  dsimp [L] at htriangle hnearN
  have heq : (realHalfProductMassApprox b N : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)) -
        realHalfProductMassWeightedPrimeSum b N +
        (realHalfProductMassWeightedPrimeSum b N - Real.log (1 / b)) =
      (realHalfProductMassApprox b N : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)) - Real.log (1 / b) := by ring
  rw [heq] at htriangle
  linarith

/-- Conditional arbitrary-real mass theorem for the literal finite source at
the literal logarithmic cutoff.  Its only unproved analytic inputs are the
displayed real PNT witness and standard weighted-prime Mertens integral. -/
theorem tendsto_realHalfProductSource_logCutoff_mass_of_real_pnt_and_weighted_mertens
    (hPNT : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ x : ℝ, (Nat.primeCounting (Nat.floor x) : ℝ) =
        (1 + c x) * x / Real.log x)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hMertens : Tendsto (fun N : ℕ =>
      realPrimeReciprocalLogIntervalSum (fun u => 1 / (1 - u)) N
        (realHalfProductMassAlpha b) (1 / 2)) atTop
      (𝓝 (∫ u in realHalfProductMassAlpha b..(1 / 2 : ℝ),
        (1 / (1 - u)) / u))) :
    Tendsto (fun N : ℕ =>
      ((realHalfProductSource b N (logCutoff N)).card : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)))
      atTop (𝓝 (Real.log (1 / b))) := by
  have hprefix :=
    tendsto_realHalfProductMassApprox_of_real_pnt_and_weighted_mertens
      hPNT hb hb1 hMertens
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  have hnear := (Metric.tendsto_nhds.mp hprefix)
    (epsilon / 2) (half_pos hepsilon)
  filter_upwards
    [eventually_realHalfProductSource_massApprox_error_of_real_pnt
      hPNT hb hb1 (epsilon / 2) (half_pos hepsilon), hnear,
      eventually_ge_atTop (2 : ℕ)] with N herr hnearN hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hscale : 0 < (N : ℝ) / Real.log (N : ℝ) :=
    div_pos (zero_lt_one.trans hN1) (Real.log_pos hN1)
  have herrsmall :
      |((realHalfProductSource b N (logCutoff N)).card : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) -
        (realHalfProductMassApprox b N : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ))| ≤ epsilon / 2 := by
    rw [← sub_div, abs_div, abs_of_pos hscale]
    exact (div_le_iff₀ hscale).mpr herr
  rw [Real.dist_eq] at hnearN ⊢
  have htriangle := abs_add_le
    (((realHalfProductSource b N (logCutoff N)).card : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)) -
      (realHalfProductMassApprox b N : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)))
    ((realHalfProductMassApprox b N : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)) - Real.log (1 / b))
  have heq :
      ((realHalfProductSource b N (logCutoff N)).card : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) -
        (realHalfProductMassApprox b N : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) +
        ((realHalfProductMassApprox b N : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) - Real.log (1 / b)) =
      ((realHalfProductSource b N (logCutoff N)).card : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) - Real.log (1 / b) := by ring
  rw [heq] at htriangle
  linarith

/-- Conditional ordered bad-semiprime mass theorem at the lower cutoff used
by the current manuscript.  The conclusion is the exact coefficient
`log (1 / b)` and retains the manuscript's strict badness wall and diagonal
prime squares.  The only analytic premises are the displayed uniform real
PNT witness and weighted-prime Mertens limit. -/
theorem tendsto_realHalfProductSource_manuscriptCutoff_mass_of_real_pnt_and_weighted_mertens
    (hPNT : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ => (1 : ℝ)) ∧
      ∀ x : ℝ, (Nat.primeCounting (Nat.floor x) : ℝ) =
        (1 + c x) * x / Real.log x)
    {b κ : ℝ} (hb : 0 < b) (hb1 : b < 1) (hκ : 0 < κ)
    (hMertens : Tendsto (fun N : ℕ =>
      realPrimeReciprocalLogIntervalSum (fun u => 1 / (1 - u)) N
        (realHalfProductMassAlpha b) (1 / 2)) atTop
      (𝓝 (∫ u in realHalfProductMassAlpha b..(1 / 2 : ℝ),
        (1 / (1 - u)) / u))) :
    Tendsto (fun N : ℕ =>
      ((realHalfProductSource b N
        (manuscriptHalfProductCutoff κ N)).card : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)))
      atTop (𝓝 (Real.log (1 / b))) := by
  have hprefix :=
    tendsto_realHalfProductMassApprox_of_real_pnt_and_weighted_mertens
      hPNT hb hb1 hMertens
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  have hnear := (Metric.tendsto_nhds.mp hprefix)
    (epsilon / 2) (half_pos hepsilon)
  filter_upwards
    [eventually_realHalfProductSource_manuscriptCutoff_massApprox_error_of_real_pnt
      hPNT hb hb1 hκ (epsilon / 2) (half_pos hepsilon), hnear,
      eventually_ge_atTop (2 : ℕ)] with N herr hnearN hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hscale : 0 < (N : ℝ) / Real.log (N : ℝ) :=
    div_pos (zero_lt_one.trans hN1) (Real.log_pos hN1)
  have herrsmall :
      |((realHalfProductSource b N
          (manuscriptHalfProductCutoff κ N)).card : ℝ) /
            ((N : ℝ) / Real.log (N : ℝ)) -
        (realHalfProductMassApprox b N : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ))| ≤ epsilon / 2 := by
    rw [← sub_div, abs_div, abs_of_pos hscale]
    exact (div_le_iff₀ hscale).mpr herr
  rw [Real.dist_eq] at hnearN ⊢
  have htriangle := abs_add_le
    (((realHalfProductSource b N
        (manuscriptHalfProductCutoff κ N)).card : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) -
      (realHalfProductMassApprox b N : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)))
    ((realHalfProductMassApprox b N : ℝ) /
        ((N : ℝ) / Real.log (N : ℝ)) - Real.log (1 / b))
  have heq :
      ((realHalfProductSource b N
        (manuscriptHalfProductCutoff κ N)).card : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) -
        (realHalfProductMassApprox b N : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) +
        ((realHalfProductMassApprox b N : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) - Real.log (1 / b)) =
      ((realHalfProductSource b N
        (manuscriptHalfProductCutoff κ N)).card : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ)) - Real.log (1 / b) := by ring
  rw [heq] at htriangle
  linarith

end

end ImbalancedChen
