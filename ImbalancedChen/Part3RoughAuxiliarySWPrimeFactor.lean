import ImbalancedChen.Part3RoughAuxiliarySW
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryPrimeSWUniform

/-!
# Unweighted chart-rough Siegel–Walfisz input from primes

Separate every integer greater than one at its largest prime factor. The
prime variable then ranges over a single interval. For Möbius, equality of
that prime with the largest prime factor of the cofactor contributes zero.
The remaining sign is the negative Möbius value of the cofactor. This
reduces both rough coefficients to the pinned prime Siegel–Walfisz estimate
with the same exact primitive coprime mean.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset Filter
open scoped BigOperators

private def largestPrimeFactor (n : ℕ) : ℕ := n.primeFactors.sup id

private theorem le_largestPrimeFactor {n p : ℕ}
    (hn : n ≠ 0) (hp : p.Prime) (hpn : p ∣ n) : p ≤ largestPrimeFactor n :=
  Finset.le_sup (f := id) (hp.mem_primeFactors hpn hn)

private theorem largestPrimeFactor_mem {n : ℕ} (hn : n ≠ 0) (hn1 : n ≠ 1) :
    largestPrimeFactor n ∈ n.primeFactors := by
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
  have hne : n.primeFactors.Nonempty := ⟨p, hp.mem_primeFactors hpn hn⟩
  simpa only [largestPrimeFactor, Set.image_id, Finset.mem_coe] using
    Finset.sup_mem_of_nonempty (f := id) hne

private theorem largestPrimeFactor_mul {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hmax : largestPrimeFactor m ≤ p) : largestPrimeFactor (m * p) = p := by
  apply le_antisymm
  · apply Finset.sup_le_iff.mpr
    intro r hr
    obtain ⟨hrp, hrd, _⟩ := Nat.mem_primeFactors.mp hr
    rcases hrp.dvd_mul.mp hrd with h | h
    · exact (le_largestPrimeFactor hm.ne' hrp h).trans hmax
    · exact (Nat.le_of_dvd hp.pos h)
  · exact le_largestPrimeFactor (Nat.mul_pos hm hp.pos).ne' hp (dvd_mul_left p m)

private theorem largestPrimeFactor_le_of_dvd {m n : ℕ} (hn : n ≠ 0) (hmn : m ∣ n) :
    largestPrimeFactor m ≤ largestPrimeFactor n := by
  apply Finset.sup_le_iff.mpr
  intro p hp
  obtain ⟨hprime, hpm, _⟩ := Nat.mem_primeFactors.mp hp
  exact le_largestPrimeFactor hn hprime (hpm.trans hmn)

/-- The unweighted coefficient of the selected rough slot. -/
def roughPrimeFactorSlot (signed : Bool) (z n : ℕ) : ℂ :=
  if signed then roughMoebiusSlot z n else roughOneSlot z n

/-- Rounding the cutoff down preserves the strict rough-prime predicate. -/
theorem roughPrimeFactorSlot_floor_eq (signed : Bool) (z : ℝ) (n : ℕ) (hz : 0 ≤ z) :
    roughPrimeFactorSlot signed ⌊z⌋₊ n =
      if signed then roughMoebiusSlot z n else roughOneSlot z n := by
  cases signed <;>
    simp [roughPrimeFactorSlot, roughMoebiusSlot, roughOneSlot, Nat.cast_lt, Nat.floor_lt hz]

private def roughPrimeFactorCofactor (signed : Bool) (z n : ℕ) : ℂ :=
  if signed then -roughMoebiusSlot z n else roughOneSlot z n

private def roughPrimeFactorLower (signed : Bool) (z L m : ℕ) : ℕ :=
  max (max z (L / m)) (if signed then largestPrimeFactor m else largestPrimeFactor m - 1)

private theorem mem_roughPrimeFactorInterval {signed : Bool} {z L H m p : ℕ}
    (hm : 0 < m) (hp : 0 < p) :
    p ∈ Ioc (roughPrimeFactorLower signed z L m) (H / m) ↔
      z < p ∧ (L < m * p ∧ m * p ≤ H) ∧
        (if signed then largestPrimeFactor m < p else largestPrimeFactor m ≤ p) := by
  simp only [mem_Ioc, roughPrimeFactorLower, max_lt_iff, Nat.div_lt_iff_lt_mul hm,
    Nat.le_div_iff_mul_le hm, mul_comm p m]
  cases signed <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

private theorem sum_eq_sum_largestPrimeFactor {R : Type*} [AddCommMonoid R]
    (z L H : ℕ) (hL : 1 ≤ L) (w : ℕ → R) :
    (∑ n ∈ (Ioc L H).filter (fun n => z < largestPrimeFactor n), w n) =
      ∑ m ∈ Icc 1 (H / (z + 1)),
        ∑ p ∈ Ioc (roughPrimeFactorLower false z L m) (H / m),
          if p.Prime then w (m * p) else 0 := by
  simp only [← Finset.sum_filter]
  rw [Finset.sum_sigma' (Icc 1 (H / (z + 1)))
    (fun m => (Ioc (roughPrimeFactorLower false z L m) (H / m)).filter Nat.Prime)
    (fun m p => w (m * p))]
  symm
  refine Finset.sum_bij' (fun u _ => u.1 * u.2)
    (fun n _ => ⟨n / largestPrimeFactor n, largestPrimeFactor n⟩) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    obtain ⟨hum, hup⟩ := Finset.mem_sigma.mp hu
    obtain ⟨hpi, hp⟩ := Finset.mem_filter.mp hup
    have hm : 0 < u.1 := (Finset.mem_Icc.mp hum).1
    obtain ⟨hzp, hI, hmax⟩ := (mem_roughPrimeFactorInterval hm hp.pos).mp hpi
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr hI, ?_⟩
    rwa [largestPrimeFactor_mul hm hp hmax]
  · intro n hn
    obtain ⟨hnI, hzn⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnL, hnH⟩ := Finset.mem_Ioc.mp hnI
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    obtain ⟨hp, hpn, _⟩ := Nat.mem_primeFactors.mp (largestPrimeFactor_mem hn0 hn1)
    have heq := Nat.div_mul_cancel hpn
    have hm : 0 < n / largestPrimeFactor n :=
      Nat.pos_of_ne_zero fun h => hn0 (by simpa [h] using heq.symm)
    have hmH : n / largestPrimeFactor n ≤ H / (z + 1) := by
      apply (Nat.le_div_iff_mul_le (by omega)).mpr
      calc
        _ ≤ (n / largestPrimeFactor n) * largestPrimeFactor n :=
          Nat.mul_le_mul_left _ (by omega)
        _ = n := heq
        _ ≤ H := hnH
    have hmax : largestPrimeFactor (n / largestPrimeFactor n) ≤ largestPrimeFactor n :=
      largestPrimeFactor_le_of_dvd hn0 ⟨largestPrimeFactor n, heq.symm⟩
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hm, hmH⟩, Finset.mem_filter.mpr ⟨?_, hp⟩⟩
    exact (mem_roughPrimeFactorInterval hm hp.pos).mpr
      ⟨hzn, by simpa only [heq] using And.intro hnL hnH, hmax⟩
  · intro u hu
    obtain ⟨hum, hup⟩ := Finset.mem_sigma.mp hu
    obtain ⟨hpi, hp⟩ := Finset.mem_filter.mp hup
    have hm : 0 < u.1 := (Finset.mem_Icc.mp hum).1
    have hmax := ((mem_roughPrimeFactorInterval hm hp.pos).mp hpi).2.2
    rw [largestPrimeFactor_mul hm hp hmax]
    rcases u with ⟨m, p⟩
    exact congrArg (fun n : ℕ => (⟨n, p⟩ : Σ _ : ℕ, ℕ)) (Nat.mul_div_cancel m hp.pos)
  · intro n hn
    obtain ⟨hnI, _⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnL, _⟩ := Finset.mem_Ioc.mp hnI
    exact Nat.div_mul_cancel
      (Nat.dvd_of_mem_primeFactors (largestPrimeFactor_mem (by omega) (by omega)))
  · intros
    rfl

private theorem roughOneSlot_mul_prime {z m p : ℕ} (hp : p.Prime) (hzp : z < p) :
    roughOneSlot z (m * p) = roughOneSlot z m := by
  have hiff : (∀ r : ℕ, r.Prime → r ∣ m * p → (z : ℝ) < (r : ℝ)) ↔
      (∀ r : ℕ, r.Prime → r ∣ m → (z : ℝ) < (r : ℝ)) := by
    constructor
    · intro h r hr hrd
      exact h r hr (hrd.trans (dvd_mul_right m p))
    · intro h r hr hrd
      rcases hr.dvd_mul.mp hrd with hdm | hdp
      · exact h r hr hdm
      · have hrp : r = p := (Nat.dvd_prime hp |>.mp hdp).resolve_left hr.ne_one
        exact_mod_cast hrp ▸ hzp
  simp only [roughOneSlot, hiff]

private theorem roughPrimeFactorSlot_mul {signed : Bool} {z m p : ℕ}
    (hm : 0 < m) (hp : p.Prime) (hzp : z < p) (hmax : largestPrimeFactor m ≤ p) :
    roughPrimeFactorSlot signed z (m * p) =
      if (if signed then largestPrimeFactor m < p else True) then
        roughPrimeFactorCofactor signed z m else 0 := by
  cases signed
  · simp [roughPrimeFactorSlot, roughPrimeFactorCofactor, roughOneSlot_mul_prime hp hzp]
  · simp only [roughPrimeFactorSlot, roughPrimeFactorCofactor, if_true]
    by_cases hlt : largestPrimeFactor m < p
    · have hcop : m.Coprime p := by
        by_contra hnc
        have hpm : p ∣ m := hp.dvd_iff_not_coprime.mpr (fun h => hnc h.symm)
        exact (not_le_of_gt hlt) (le_largestPrimeFactor hm.ne' hp hpm)
      rw [if_pos hlt, roughMoebiusSlot, roughOneSlot_mul_prime hp hzp,
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
        ArithmeticFunction.moebius_apply_prime hp, Int.cast_mul]
      simp [roughMoebiusSlot]
    · have heq : largestPrimeFactor m = p := hmax.antisymm (Nat.le_of_not_gt hlt)
      have hm1 : m ≠ 1 := by
        intro hm1
        have hp0 : p = 0 := by simpa [hm1, largestPrimeFactor] using heq.symm
        exact hp.ne_zero hp0
      have hpm : p ∣ m := by
        rw [← heq]
        exact Nat.dvd_of_mem_primeFactors (largestPrimeFactor_mem hm.ne' hm1)
      have hns : ¬Squarefree (m * p) := by
        intro hs
        exact Nat.squarefree_iff_prime_squarefree.mp hs p hp
          (mul_dvd_mul_right hpm p)
      simp [hlt, roughMoebiusSlot, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]

private theorem roughPrimeFactorSlot_support (signed : Bool) (z n : ℕ)
    (hn : roughPrimeFactorSlot signed z n ≠ 0) :
    ∀ p : ℕ, p.Prime → p ∣ n → (z : ℝ) < (p : ℝ) := by
  cases signed
  · exact roughOneSlot_support z n hn
  · exact roughMoebiusSlot_support z n hn

private theorem roughPrimeFactorCofactor_norm_le (signed : Bool) (z m : ℕ) :
    ‖roughPrimeFactorCofactor signed z m‖ ≤ 1 := by
  cases signed
  · exact roughOneSlot_norm_le z m
  · simpa [roughPrimeFactorCofactor] using roughMoebiusSlot_norm_le z m

private def roughSWPrimitiveKernel (q b n : ℕ) : ℂ :=
  (if Nat.ModEq q n b then 1 else 0) -
    (if n.Coprime q then 1 else 0) / (q.totient : ℂ)

private theorem auxiliarySWError_one_eq_sum_primitiveKernel
    (S : Finset ℕ) (α : ℕ → ℂ) (q b : ℕ) :
    auxiliarySWError S α 1 q b =
      ∑ n ∈ S, α n * roughSWPrimitiveKernel q b n := by
  simp only [auxiliarySWError, roughSWPrimitiveKernel, Nat.coprime_one_right_eq_true,
    and_true, one_mul, mul_sub, sum_sub_distrib, sum_div]
  congr 1 <;> apply sum_congr rfl <;> intro n _ <;> split_ifs <;> simp [div_eq_mul_inv]

private def roughPrimeFactorResidue (q b m : ℕ) [NeZero q] : ℕ :=
  ((m : ZMod q)⁻¹ * (b : ZMod q)).val

private theorem roughPrimeFactorResidue_modEq {q b m : ℕ} [NeZero q]
    (hmq : m.Coprime q) : m * roughPrimeFactorResidue q b m ≡ b [MOD q] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul]
  simp only [roughPrimeFactorResidue, ZMod.natCast_zmod_val, ← mul_assoc,
    ZMod.coe_mul_inv_eq_one m hmq, one_mul]

private theorem roughPrimeFactorResidue_coprime {q b m : ℕ} [NeZero q]
    (hb : b.Coprime q) (hmq : m.Coprime q) : (roughPrimeFactorResidue q b m).Coprime q := by
  have hm'b : (m * roughPrimeFactorResidue q b m).Coprime q := by
    change (m * roughPrimeFactorResidue q b m).gcd q = 1
    rw [(roughPrimeFactorResidue_modEq (b := b) hmq).gcd_eq, hb.gcd_eq_one]
  exact (Nat.coprime_mul_iff_left.mp hm'b).2

private theorem roughSWPrimitiveKernel_mul {q b m : ℕ} [NeZero q]
    (hb : b.Coprime q) (p : ℕ) :
    roughSWPrimitiveKernel q b (m * p) =
      if m.Coprime q then roughSWPrimitiveKernel q (roughPrimeFactorResidue q b m) p else 0 := by
  by_cases hmq : m.Coprime q
  · have hmb := roughPrimeFactorResidue_modEq (b := b) hmq
    have hAP : m * p ≡ b [MOD q] ↔ p ≡ roughPrimeFactorResidue q b m [MOD q] :=
      ⟨fun h => Nat.ModEq.cancel_left_of_coprime hmq.symm.gcd_eq_one (h.trans hmb.symm),
        fun h => (h.mul_left m).trans hmb⟩
    have hcop : (m * p).Coprime q ↔ p.Coprime q :=
      Nat.coprime_mul_iff_left.trans (and_iff_right hmq)
    rw [if_pos hmq]
    simp only [roughSWPrimitiveKernel, hAP, hcop]
  · have hnc : ¬(m * p).Coprime q := fun h => hmq (Nat.coprime_mul_iff_left.mp h).1
    have hAP : ¬m * p ≡ b [MOD q] := by
      intro h
      apply hnc
      change (m * p).gcd q = 1
      rw [h.gcd_eq, hb.gcd_eq_one]
    simp [roughSWPrimitiveKernel, hAP, hnc, hmq]

open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry in
private def roughSWPrimeIndicator (p : ℕ) : ℂ := (primeSWBeta p : ℂ)

private theorem roughSWPrimeIndicator_eq (p : ℕ) :
    roughSWPrimeIndicator p = if p.Prime then 1 else 0 := by
  by_cases hp : p.Prime <;>
    simp [roughSWPrimeIndicator,
      MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.primeSWBeta, hp]

private theorem roughPrimeFactorInterval_subset (signed : Bool) (z L H m : ℕ) :
    Ioc (roughPrimeFactorLower signed z L m) (H / m) ⊆
      Ioc (roughPrimeFactorLower false z L m) (H / m) := by
  apply Ioc_subset_Ioc_left
  cases signed
  · exact le_rfl
  · exact max_le_max_left _ (Nat.sub_le ..)

/-- The exact largest-prime expansion preserves both the primitive AP mass
and its coprime mean. A nonunit cofactor has zero contribution to both. -/
private theorem auxiliarySWError_roughPrimeFactorSlot_eq_sum
    (signed : Bool) (z L H q b : ℕ) [NeZero q] (hL : 1 ≤ L) (hb : b.Coprime q) :
    auxiliarySWError (Ioc L H) (roughPrimeFactorSlot signed z) 1 q b =
      ∑ m ∈ Icc 1 (H / (z + 1)),
        if m.Coprime q then
          roughPrimeFactorCofactor signed z m *
            auxiliarySWError (Ioc (roughPrimeFactorLower signed z L m) (H / m))
              roughSWPrimeIndicator 1 q (roughPrimeFactorResidue q b m)
        else 0 := by
  let w := fun n => roughPrimeFactorSlot signed z n * roughSWPrimitiveKernel q b n
  rw [auxiliarySWError_one_eq_sum_primitiveKernel]
  change (∑ n ∈ Ioc L H, w n) = _
  have hfilter : (∑ n ∈ Ioc L H, w n) =
      ∑ n ∈ (Ioc L H).filter (fun n => z < largestPrimeFactor n), w n := by
    symm
    apply sum_subset (filter_subset _ _)
    intro n hn hnt
    have hnL := (Finset.mem_Ioc.mp hn).1
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by omega
    obtain ⟨hp, hpd, _⟩ := Nat.mem_primeFactors.mp (largestPrimeFactor_mem hn0 hn1)
    have hzero : roughPrimeFactorSlot signed z n = 0 := by
      by_contra hne
      have hlt := roughPrimeFactorSlot_support signed z n hne _ hp hpd
      exact hnt (Finset.mem_filter.mpr ⟨hn, by exact_mod_cast hlt⟩)
    simp [w, hzero]
  rw [hfilter, sum_eq_sum_largestPrimeFactor z L H hL w]
  apply sum_congr rfl
  intro m hm
  have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
  simp only [w, roughSWPrimitiveKernel_mul hb]
  by_cases hmq : m.Coprime q
  · simp only [if_pos hmq]
    let f := fun p => if p.Prime then roughPrimeFactorSlot signed z (m * p) *
      roughSWPrimitiveKernel q (roughPrimeFactorResidue q b m) p else 0
    change (∑ p ∈ Ioc (roughPrimeFactorLower false z L m) (H / m), f p) = _
    have hsub := roughPrimeFactorInterval_subset signed z L H m
    have hrestrict : (∑ p ∈ Ioc (roughPrimeFactorLower signed z L m) (H / m), f p) =
        ∑ p ∈ Ioc (roughPrimeFactorLower false z L m) (H / m), f p := by
      apply sum_subset hsub
      intro p hpI hpNot
      by_cases hp : p.Prime
      · obtain ⟨hzp, hpRange, hmax⟩ := (mem_roughPrimeFactorInterval hm0 hp.pos).mp hpI
        have hnot : ¬(if signed then largestPrimeFactor m < p else True) := by
          intro h
          apply hpNot
          exact (mem_roughPrimeFactorInterval hm0 hp.pos).mpr
            ⟨hzp, hpRange, by cases signed <;> simp_all⟩
        simp only [f, if_pos hp, roughPrimeFactorSlot_mul hm0 hp hzp hmax, if_neg hnot,
          zero_mul]
      · simp [f, hp]
    rw [← hrestrict, auxiliarySWError_one_eq_sum_primitiveKernel, Finset.mul_sum]
    apply sum_congr rfl
    intro p hpI
    by_cases hp : p.Prime
    · obtain ⟨hzp, _, hmax⟩ := (mem_roughPrimeFactorInterval hm0 hp.pos).mp hpI
      have hmax' : largestPrimeFactor m ≤ p := by
        cases signed
        · exact hmax
        · exact le_of_lt hmax
      have hkeep : (if signed then largestPrimeFactor m < p else True) := by
        cases signed
        · trivial
        · exact hmax
      simp only [f, if_pos hp, roughSWPrimeIndicator_eq, one_mul,
        roughPrimeFactorSlot_mul hm0 hp hzp hmax', if_pos hkeep]
    · simp [f, roughSWPrimeIndicator_eq, hp]
  · simp [hmq]

open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry in
private theorem auxiliarySWError_roughSWPrimeIndicator_eq_cast (S : Finset ℕ) (q b : ℕ) :
    auxiliarySWError S roughSWPrimeIndicator 1 q b =
      (betaCoprimeAPDiscrepancy S primeSWBeta q 1 b : ℂ) := by
  simp only [auxiliarySWError, betaCoprimeAPDiscrepancy, coprimeMass,
    Nat.coprime_one_right_eq_true, and_true, true_and, mul_one, one_mul,
    Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast,
    apply_ite Complex.ofReal, Complex.ofReal_zero, roughSWPrimeIndicator]

open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry in
private theorem eventually_norm_auxiliarySWError_primeIndicator (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ L H q b : ℕ,
      2 ≤ L → H ≤ N → 0 < q → b.Coprime q →
      ‖auxiliarySWError (Ioc L H) roughSWPrimeIndicator 1 q b‖ ≤
        C * (N : ℝ) / Real.log N ^ B := by
  obtain ⟨C, hC, hSW⟩ := primeSW_uniform_eventually B
  refine ⟨C, hC, ?_⟩
  filter_upwards [hSW, eventually_ge_atTop (3 : ℕ)] with N hSW hN
  intro L H q b hL hH hq hb
  by_cases hLH : L ≤ H
  · have h := hSW (L : ℝ) (H : ℝ) (by exact_mod_cast hLH)
      (by simpa using (show L ∈ Icc 2 N from mem_Icc.mpr ⟨hL, hLH.trans hH⟩))
      (by simpa using (show H ∈ Icc 2 N from mem_Icc.mpr ⟨hL.trans hLH, hH⟩))
      q 1 hq Nat.one_pos b hb
    rw [auxiliarySWError_roughSWPrimeIndicator_eq_cast, Complex.norm_real]
    simpa [primeSWInterval] using h
  · rw [Ioc_eq_empty_of_le (by omega), auxiliarySWError]
    have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    simp only [sum_empty, zero_div, sub_zero, norm_zero]
    positivity

/-- The prime Siegel–Walfisz bound gives a sum of uniform errors at the
actual quotient scales. The lower cutoff for every prime guarantees
`z + 1 ≤ H / m`; the threshold is chosen before all the endpoints, cutoff,
modulus, residue and coefficient choices. -/
theorem eventually_norm_auxiliarySWError_roughPrimeFactorSlot_le_sum (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N₀ : ℕ in atTop,
      ∀ signed : Bool, ∀ z L H q b : ℕ,
        N₀ ≤ z → 2 ≤ z → 1 ≤ L → 0 < q → b.Coprime q →
        ‖auxiliarySWError (Ioc L H) (roughPrimeFactorSlot signed z) 1 q b‖ ≤
          ∑ m ∈ Icc 1 (H / (z + 1)), C * (↑(H / m) : ℝ) / Real.log (↑(H / m) : ℝ) ^ B := by
  obtain ⟨C, hC, hSW⟩ := eventually_norm_auxiliarySWError_primeIndicator B
  refine ⟨C, hC, ?_⟩
  rw [Filter.eventually_atTop] at hSW ⊢
  obtain ⟨N₀, hSW⟩ := hSW
  refine ⟨N₀, ?_⟩
  intro N hN signed z L H q b hNz hz hL hq hb
  let : NeZero q := ⟨hq.ne'⟩
  rw [auxiliarySWError_roughPrimeFactorSlot_eq_sum signed z L H q b hL hb]
  refine (norm_sum_le _ _).trans (sum_le_sum fun m hm => ?_)
  have hm0 : 0 < m := (mem_Icc.mp hm).1
  have hzHm : z + 1 ≤ H / m := (Nat.le_div_iff_mul_le hm0).mpr (by
    rw [mul_comm]
    exact (Nat.le_div_iff_mul_le (Nat.succ_pos z)).mp (mem_Icc.mp hm).2)
  by_cases hmq : m.Coprime q
  · rw [if_pos hmq, norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (roughPrimeFactorCofactor_norm_le signed z m)).trans ?_
    exact hSW (H / m) (by omega) (roughPrimeFactorLower signed z L m) (H / m) q
      (roughPrimeFactorResidue q b m) (hz.trans ((le_max_left _ _).trans (le_max_left _ _)))
      le_rfl hq (roughPrimeFactorResidue_coprime hb hmq)
  · rw [if_neg hmq, norm_zero]
    have hl : 0 ≤ Real.log (↑(H / m) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ H / m))
    positivity

end

end ImbalancedChen.Part3
