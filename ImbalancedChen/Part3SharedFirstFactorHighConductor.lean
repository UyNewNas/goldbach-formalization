import ImbalancedChen.Part3SharedFirstFactorDispersion
import ImbalancedChen.Part3PolynomialResidueDivisorBound

/-!
# Finite foundations for the auxiliary high-conductor large sieve

The full character level and the auxiliary coprime mask are retained in
the exact Mobius expansion. Divisor multiplicity is attached to the
conductor before a subpower estimate is used. The arguments below have
no large-sieve supplier, bad-support budget, or distribution hypothesis.

The public high-conductor mean theorem retains the full imprimitive level
and is proved from the sharp primitive cell mean by exact finite conductor
regrouping. Only conductor divisor multiplicity receives a subpower bound;
the first term retains its saving at the high-conductor cutoff.
-/

namespace ImbalancedChen.Part3.SharedFirstFactorHighConductor

noncomputable section

open Classical Finset
open scoped BigOperators Pointwise
open AnalyticNumberTheory.LargeSieve
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private def divisorTau (n : ℕ) : ℝ := (n.divisors.card : ℝ)

private theorem divisorTau_nonneg (n : ℕ) : 0 ≤ divisorTau n := by
  exact Nat.cast_nonneg _

/-- Local finite extraction of `Mathlib/Data/Finset/NatDivisors`, which
is not imported by either parent. Its pointwise-finset dependencies are
already reachable through the complex-number parent. -/
private theorem divisors_mul_eq (a b : ℕ) :
    (a * b).divisors = a.divisors * b.divisors := by
  ext n
  simp_rw [Finset.mem_mul, Nat.mem_divisors, Nat.dvd_mul, mul_ne_zero_iff,
    ← exists_and_left, ← exists_and_right]
  simp only [and_assoc, and_comm, and_left_comm]

private theorem divisorTau_mul_le (a b : ℕ) :
    divisorTau (a * b) ≤ divisorTau a * divisorTau b := by
  unfold divisorTau
  rw [divisors_mul_eq]
  exact_mod_cast (Finset.card_mul_le (s := a.divisors) (t := b.divisors))

private theorem sum_moebius_divisors_complex (n : ℕ) :
    (∑ e ∈ n.divisors, (ArithmeticFunction.moebius e : ℂ)) =
      if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ ↦ f n)
    (ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℂ))
  simpa only [ArithmeticFunction.coe_zeta_mul_apply,
    ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply] using h

private theorem coprime_indicator_complex {q : ℕ} (hq : q ≠ 0) (n : ℕ) :
    (if n.Coprime q then (1 : ℂ) else 0) =
      ∑ e ∈ q.divisors,
        if e ∣ n then (ArithmeticFunction.moebius e : ℂ) else 0 := by
  have hg : n.gcd q ≠ 0 :=
    (Nat.gcd_pos_of_pos_right n (Nat.pos_of_ne_zero hq)).ne'
  have heq : q.divisors.filter (fun e ↦ e ∣ n) = (n.gcd q).divisors := by
    ext e
    simp [Nat.mem_divisors, hq, hg, Nat.dvd_gcd_iff, and_comm]
  rw [← Finset.sum_filter, heq, sum_moebius_divisors_complex]

private theorem moebius_norm_sq_le_one (e : ℕ) :
    ‖(ArithmeticFunction.moebius e : ℂ)‖ ^ 2 ≤ 1 := by
  have habs := ArithmeticFunction.abs_moebius_le_one (n := e)
  have hcases : ArithmeticFunction.moebius e = -1 ∨
      ArithmeticFunction.moebius e = 0 ∨ ArithmeticFunction.moebius e = 1 := by
    rcases abs_le.mp habs with ⟨hlo, hhi⟩
    omega
  rcases hcases with h | h | h <;> simp [h]

private theorem character_eq_primitive_indicator {q : ℕ} (hq : 0 < q)
    (chi : DirichletCharacter ℂ q) (n : ℕ) :
    chi (n : ZMod q) =
      chi.primitiveCharacter (n : ZMod chi.conductor) *
        (if n.Coprime q then (1 : ℂ) else 0) := by
  let : NeZero q := ⟨hq.ne'⟩
  by_cases hn : n.Coprime q
  · rw [if_pos hn, mul_one]
    symm
    simpa only [Int.cast_natCast] using
      chi.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr hn)
  · rw [if_neg hn, mul_zero]
    exact MulChar.map_nonunit chi
      (fun h ↦ hn ((ZMod.isUnit_iff_coprime n q).mp h))

/-- This bijection preserves the complete divisor fibre and has no
coprimality assumption between the scale and the quotient. -/
private theorem sum_multiples (N e : ℕ) (he : 0 < e) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N with e ∣ n, f n) =
      ∑ m ∈ Finset.Icc 1 (N / e), f (e * m) := by
  symm
  refine Finset.sum_bij (fun m _ ↦ e * m) ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hm' := Finset.mem_Icc.mp hm
    exact ⟨⟨Nat.mul_pos he hm'.1,
      (Nat.mul_le_mul_left e hm'.2).trans (Nat.mul_div_le N e)⟩,
      dvd_mul_right e m⟩
  · intro m₁ hm₁ m₂ hm₂ h
    exact Nat.eq_of_mul_eq_mul_left he h
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    refine ⟨n / e, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨Nat.div_pos (Nat.le_of_dvd (Finset.mem_Icc.mp hn'.1).1 hn'.2) he,
        Nat.div_le_div_right (Finset.mem_Icc.mp hn'.1).2⟩
    · exact Nat.mul_div_cancel' hn'.2
  · intro m hm
    rfl

private theorem sum_multiples_real (N e : ℕ) (he : 0 < e) (f : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 N with e ∣ n, f n) =
      ∑ m ∈ Finset.Icc 1 (N / e), f (e * m) := by
  have h := sum_multiples N e he (fun n ↦ (f n : ℂ))
  exact_mod_cast h

/-- The auxiliary factor is not combined with the conductor or removed. -/
private theorem divisible_auxiliary_sum (N k e c : ℕ) (he : 0 < e)
    (b : ℕ → ℂ) (psi : DirichletCharacter ℂ c) :
    (∑ n ∈ Finset.Icc 1 N,
      if e ∣ n then (if n.Coprime k then b n else 0) * psi (n : ZMod c) else 0) =
      if e.Coprime k then
        psi (e : ZMod c) *
          ∑ m ∈ Finset.Icc 1 (N / e),
            (if m.Coprime k then b (e * m) else 0) * psi (m : ZMod c)
      else 0 := by
  rw [← Finset.sum_filter, sum_multiples N e he]
  by_cases hek : e.Coprime k
  · rw [if_pos hek, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hmk : m.Coprime k
    · rw [if_pos (Nat.coprime_mul_iff_left.mpr ⟨hek, hmk⟩), if_pos hmk,
        Nat.cast_mul, map_mul]
      ring
    · have hem : ¬(e * m).Coprime k :=
        fun h ↦ hmk (Nat.coprime_mul_iff_left.mp h).2
      rw [if_neg hem, if_neg hmk, zero_mul, zero_mul, mul_zero]
  · rw [if_neg hek]
    apply Finset.sum_eq_zero
    intro m hm
    have hem : ¬(e * m).Coprime k :=
      fun h ↦ hek (Nat.coprime_mul_iff_left.mp h).1
    rw [if_neg hem, zero_mul]

/-- Exact complex Mobius expansion at the full physical character level. -/
private theorem auxiliary_character_sum_eq_moebius {q : ℕ} (hq : 0 < q)
    (N k : ℕ) (b : ℕ → ℂ) (chi : DirichletCharacter ℂ q) :
    (∑ n ∈ Finset.Icc 1 N,
      (if n.Coprime k then b n else 0) * chi (n : ZMod q)) =
      ∑ e ∈ q.divisors, (ArithmeticFunction.moebius e : ℂ) *
        ∑ n ∈ Finset.Icc 1 N,
          if e ∣ n then
            (if n.Coprime k then b n else 0) *
              chi.primitiveCharacter (n : ZMod chi.conductor)
          else 0 := by
  calc
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ e ∈ q.divisors,
        if e ∣ n then (ArithmeticFunction.moebius e : ℂ) *
          ((if n.Coprime k then b n else 0) *
            chi.primitiveCharacter (n : ZMod chi.conductor)) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [character_eq_primitive_indicator hq chi n, coprime_indicator_complex hq.ne']
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hen : e ∣ n
      · simp only [if_pos hen]
        ring
      · simp only [if_neg hen, mul_zero]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hen : e ∣ n
      · simp only [if_pos hen]
      · simp only [if_neg hen, mul_zero]

/-- Both coprimality gates survive the multiple substitution. In
particular `(e, conductor)=1` is available before changing the level
fibre from `q` to `q/e`. -/
private theorem auxiliary_character_sum_eq_moebius_quotient {q : ℕ}
    (hq : 0 < q) (N k : ℕ) (b : ℕ → ℂ) (chi : DirichletCharacter ℂ q) :
    (∑ n ∈ Finset.Icc 1 N,
      (if n.Coprime k then b n else 0) * chi (n : ZMod q)) =
      ∑ e ∈ q.divisors,
        if e.Coprime (chi.conductor * k) then
          (ArithmeticFunction.moebius e : ℂ) *
            chi.primitiveCharacter (e : ZMod chi.conductor) *
              ∑ m ∈ Finset.Icc 1 (N / e),
                (if m.Coprime k then b (e * m) else 0) *
                  chi.primitiveCharacter (m : ZMod chi.conductor)
        else 0 := by
  rw [auxiliary_character_sum_eq_moebius hq N k b chi]
  apply Finset.sum_congr rfl
  intro e he
  have hepos : 0 < e := Nat.pos_of_mem_divisors he
  rw [divisible_auxiliary_sum N k e chi.conductor hepos b chi.primitiveCharacter]
  by_cases hek : e.Coprime k
  · rw [if_pos hek]
    by_cases hec : e.Coprime chi.conductor
    · rw [if_pos (hec.mul_right hek)]
      ring
    · have hegate : ¬e.Coprime (chi.conductor * k) :=
        fun h ↦ hec (Nat.coprime_mul_iff_right.mp h).1
      have hz : chi.primitiveCharacter (e : ZMod chi.conductor) = 0 :=
        MulChar.map_nonunit _
          (fun h ↦ hec ((ZMod.isUnit_iff_coprime e chi.conductor).mp h))
      rw [if_neg hegate, hz, zero_mul, mul_zero]
  · have hegate : ¬e.Coprime (chi.conductor * k) :=
      fun h ↦ hek (Nat.coprime_mul_iff_right.mp h).2
    rw [if_neg hek, if_neg hegate, mul_zero]

/-- The actual Mobius Cauchy loss is the divisor count at the full level;
neither the full-level nonunit mask nor the auxiliary gate is omitted. -/
private theorem auxiliary_character_sum_sq_le_moebius {q : ℕ}
    (hq : 0 < q) (N k : ℕ) (b : ℕ → ℂ) (chi : DirichletCharacter ℂ q) :
    ‖∑ n ∈ Finset.Icc 1 N,
      (if n.Coprime k then b n else 0) * chi (n : ZMod q)‖ ^ 2 ≤
      divisorTau q * ∑ e ∈ q.divisors,
        if e.Coprime (chi.conductor * k) then
          ‖∑ m ∈ Finset.Icc 1 (N / e),
            (if m.Coprime k then b (e * m) else 0) *
              chi.primitiveCharacter (m : ZMod chi.conductor)‖ ^ 2
        else 0 := by
  rw [auxiliary_character_sum_eq_moebius_quotient hq N k b chi]
  refine (norm_finset_sum_sq_le_card_mul_sum_norm_sq q.divisors _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (divisorTau_nonneg q)
  apply Finset.sum_le_sum
  intro e he
  by_cases hegate : e.Coprime (chi.conductor * k)
  · rw [if_pos hegate, if_pos hegate, norm_mul, norm_mul, mul_pow, mul_pow]
    have hpsi : ‖chi.primitiveCharacter (e : ZMod chi.conductor)‖ ^ 2 ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
        (chi.primitiveCharacter.norm_le_one (e : ZMod chi.conductor)) 2
    have hprod : ‖(ArithmeticFunction.moebius e : ℂ)‖ ^ 2 *
        ‖chi.primitiveCharacter (e : ZMod chi.conductor)‖ ^ 2 ≤ 1 := by
      simpa only [one_mul] using mul_le_mul (moebius_norm_sq_le_one e) hpsi
        (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    exact mul_le_of_le_one_left (sq_nonneg _) hprod
  · simp only [if_neg hegate, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact le_rfl

private theorem auxiliary_multiple_energy_le (N e k : ℕ) (he : 0 < e)
    (b : ℕ → ℂ) (hb : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) :
    (∑ m ∈ Finset.Icc 1 (N / e),
      ‖if m.Coprime k then b (e * m) else 0‖ ^ 2) ≤ ((N / e : ℕ) : ℝ) := by
  calc
    _ ≤ ∑ _m ∈ Finset.Icc 1 (N / e), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      by_cases hmk : m.Coprime k
      · rw [if_pos hmk]
        have hem : e * m ∈ Finset.Icc 1 N := by
          have hm' := Finset.mem_Icc.mp hm
          exact Finset.mem_Icc.mpr ⟨Nat.mul_pos he hm'.1,
            (Nat.mul_le_mul_left e hm'.2).trans (Nat.mul_div_le N e)⟩
        simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (hb _ hem) 2
      · simp only [if_neg hmk, norm_zero, zero_pow (by decide : 2 ≠ 0)]
        norm_num
    _ = _ := by simp

private theorem sum_tau_ratio_le (T : ℕ) :
    (∑ r ∈ Finset.Icc 1 T, divisorTau r * ((r : ℝ) / (r.totient : ℝ))) ≤
      (T : ℝ) * (1 + Real.log (T : ℝ)) ^ 3 := by
  by_cases hT : T = 0
  · subst T
    simp
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hT
  have hI : Finset.Icc 1 T = Finset.Ioc 0 T := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 T, divisorTau r ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
      have hratio : (r : ℝ) / (r.totient : ℝ) ≤ divisorTau r :=
        totientRatio_le_card_divisors r hrpos
      simpa only [pow_two] using
        mul_le_mul_of_nonneg_left hratio (divisorTau_nonneg r)
    _ ≤ _ := by
      rw [hI]
      have h := sum_fouvryTau_sq_le_real (k := 2) (by norm_num) hT1
      simpa only [Nat.floor_natCast, fouvryTau_two, divisorTau,
        show (2 : ℕ) ^ 2 - 1 = 3 by decide] using h

/-- The extra divisor multiplicity has a fixed second-moment cost in the
multiple fibre, rather than a global subpower in the full modulus. -/
private theorem tau_weighted_multiples_le (Q c : ℕ) (hc : 0 < c) :
    (∑ q ∈ Finset.Icc 1 Q with c ∣ q,
      divisorTau q * ((q : ℝ) / (q.totient : ℝ))) ≤
        divisorTau c * ((c : ℝ) / (c.totient : ℝ)) *
          ((Q / c : ℕ) : ℝ) * (1 + Real.log ((Q / c : ℕ) : ℝ)) ^ 3 := by
  rw [sum_multiples_real Q c hc]
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 (Q / c),
        (divisorTau c * divisorTau r) *
          (((c : ℝ) / (c.totient : ℝ)) * ((r : ℝ) / (r.totient : ℝ))) := by
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul
      · exact divisorTau_mul_le c r
      · exact multiple_totient_ratio_le_product c r hc (Finset.mem_Icc.mp hr).1
      · positivity
      · exact mul_nonneg (divisorTau_nonneg c) (divisorTau_nonneg r)
    _ = (divisorTau c * ((c : ℝ) / (c.totient : ℝ))) *
        ∑ r ∈ Finset.Icc 1 (Q / c),
          divisorTau r * ((r : ℝ) / (r.totient : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (sum_tau_ratio_le (Q / c))
        (mul_nonneg (divisorTau_nonneg c) (div_nonneg (by positivity) (by positivity)))

/-- A conductor and a Mobius divisor share one full-level fibre. The
factor `tau(c)` is kept at the conductor scale, not replaced by `Q^eta`. -/
private theorem tau_weighted_product_fibre_le (Q c e : ℕ)
    (hQ : 0 < Q) (hc : 0 < c) (he : 0 < e) :
    (∑ q ∈ Finset.Icc 1 Q with c * e ∣ q,
      divisorTau q * ((q : ℝ) / (q.totient : ℝ))) ≤
        (divisorTau c * ((c : ℝ) / (c.totient : ℝ))) *
          (divisorTau e / (e.totient : ℝ)) * ((Q : ℝ) / (c : ℝ)) *
            (1 + Real.log (Q : ℝ)) ^ 3 := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hphiC : (0 : ℝ) < c.totient := by exact_mod_cast Nat.totient_pos.mpr hc
  have hphiE : (0 : ℝ) < e.totient := by exact_mod_cast Nat.totient_pos.mpr he
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  let T : ℕ := Q / (c * e)
  have hTdiv : (T : ℝ) ≤ (Q : ℝ) / ((c : ℝ) * (e : ℝ)) := by
    apply (le_div_iff₀ (mul_pos hcR heR)).mpr
    have hnat : (c * e) * (Q / (c * e)) ≤ Q := Nat.mul_div_le Q (c * e)
    have hreal : (c : ℝ) * (e : ℝ) * (T : ℝ) ≤ Q := by exact_mod_cast hnat
    simpa only [mul_comm] using hreal
  have hlogT : 0 ≤ 1 + Real.log (T : ℝ) := by
    by_cases hT : T = 0
    · simp only [hT, Nat.cast_zero, Real.log_zero, add_zero]
      norm_num
    · have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hT
      linarith [Real.log_nonneg hT1]
  have hlog : 1 + Real.log (T : ℝ) ≤ 1 + Real.log (Q : ℝ) := by
    by_cases hT : T = 0
    · simp only [hT, Nat.cast_zero, Real.log_zero, add_zero]
      linarith [Real.log_nonneg hQR]
    · have hTpos : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero hT
      have hTQ : T ≤ Q := Nat.div_le_self Q (c * e)
      exact add_le_add le_rfl (Real.log_le_log hTpos (by exact_mod_cast hTQ))
  have hA : divisorTau (c * e) *
      (((c * e : ℕ) : ℝ) / ((c * e).totient : ℝ)) ≤
        (divisorTau c * divisorTau e) *
          (((c : ℝ) / (c.totient : ℝ)) * ((e : ℝ) / (e.totient : ℝ))) := by
    exact mul_le_mul (divisorTau_mul_le c e)
      (multiple_totient_ratio_le_product c e hc he) (by positivity)
      (mul_nonneg (divisorTau_nonneg c) (divisorTau_nonneg e))
  calc
    _ ≤ divisorTau (c * e) *
        (((c * e : ℕ) : ℝ) / ((c * e).totient : ℝ)) * (T : ℝ) *
          (1 + Real.log (T : ℝ)) ^ 3 :=
      tau_weighted_multiples_le Q (c * e) (Nat.mul_pos hc he)
    _ ≤ ((divisorTau c * divisorTau e) *
        (((c : ℝ) / (c.totient : ℝ)) * ((e : ℝ) / (e.totient : ℝ)))) *
          ((Q : ℝ) / ((c : ℝ) * (e : ℝ))) * (1 + Real.log (Q : ℝ)) ^ 3 := by
      have hupper : 0 ≤ (divisorTau c * divisorTau e) *
          (((c : ℝ) / (c.totient : ℝ)) * ((e : ℝ) / (e.totient : ℝ))) :=
        mul_nonneg (mul_nonneg (divisorTau_nonneg c) (divisorTau_nonneg e))
          (mul_nonneg (div_nonneg hcR.le hphiC.le) (div_nonneg heR.le hphiE.le))
      exact mul_le_mul (mul_le_mul hA hTdiv (Nat.cast_nonneg _) hupper)
        (pow_le_pow_left₀ hlogT hlog 3) (pow_nonneg hlogT 3)
        (mul_nonneg hupper (div_nonneg (Nat.cast_nonneg _) (mul_nonneg hcR.le heR.le)))
    _ = _ := by
      field_simp [hcR.ne', heR.ne', hphiC.ne', hphiE.ne']


/-- A high-conductor filter removes the physical principal character before
using the exact native conductor bijection. No character level is changed in
this finite identity. -/
private theorem sum_high_characters_by_conductor {q : ℕ} (hq : 0 < q)
    (R : ℕ) (hR : 0 < R) (F : (c : ℕ) → PrimitiveCharacter c → ℝ) :
    (∑ chi ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
        (fun chi ↦ R < chi.conductor),
      F chi.conductor (conductorPrimitiveCharacter chi)) =
      ∑ c ∈ q.divisors.filter (fun c ↦ R < c),
        ∑ psi : PrimitiveCharacter c, F c psi := by
  let : NeZero q := ⟨hq.ne'⟩
  have hfilter :
      (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
          (fun chi ↦ R < chi.conductor) =
        (nonprincipalCharacters q).filter (fun chi ↦ R < chi.conductor) := by
    ext chi
    simp only [nonprincipalCharacters, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_erase, and_true]
    constructor
    · intro hchi
      refine ⟨?_, hchi⟩
      intro heq
      subst chi
      rw [DirichletCharacter.conductor_one] at hchi
      omega
    · exact fun h ↦ h.2
  rw [hfilter, Finset.sum_filter,
    sum_nonprincipal_by_conductor hq
      (fun c psi ↦ if R < c then F c psi else 0)]
  simp only [nonprincipalConductors, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hRc : R < c
  · have hc2 : 2 ≤ c := by omega
    simp only [if_pos hc2, hRc, if_true]
  · simp only [if_neg hRc, Finset.sum_const_zero, ite_self]

private theorem sum_divisors_to_Icc {α : Type*} [AddCommMonoid α]
    (Q q : ℕ) (hq : 0 < q) (hqQ : q ≤ Q) (F : ℕ → α) :
    (∑ d ∈ q.divisors, F d) =
      ∑ d ∈ Finset.Icc 1 Q, if d ∣ q then F d else 0 := by
  have hset : q.divisors = (Finset.Icc 1 Q).filter (fun d ↦ d ∣ q) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro hd
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd.1 hq,
        (Nat.le_of_dvd hq hd.1).trans hqQ⟩, hd.1⟩
    · intro hd
      exact ⟨hd.2, hq.ne'⟩
  rw [hset, Finset.sum_filter]

/-- The `e` and conductor divisibilities combine only under the exact
Mobius coprimality gate; no assumption that the full level is primitive is
used. -/
private theorem product_divides_iff_of_coprime {q c e k : ℕ}
    (he : e.Coprime (c * k)) :
    c * e ∣ q ↔ c ∣ q ∧ e ∣ q := by
  constructor
  · intro h
    exact ⟨(dvd_mul_right c e).trans h, (dvd_mul_left e c).trans h⟩
  · intro h
    exact (Nat.coprime_mul_iff_right.mp he).1.symm.mul_dvd_of_dvd_of_dvd h.1 h.2


private theorem high_moebius_sum_at_level {q : ℕ} (hq : 0 < q)
    (Q R k : ℕ) (hqQ : q ≤ Q) (hR : 0 < R)
    (F : (c : ℕ) → ℕ → PrimitiveCharacter c → ℝ) :
    (∑ chi ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
        (fun chi ↦ R < chi.conductor),
      ∑ e ∈ q.divisors,
        if e.Coprime (chi.conductor * k) then
          F chi.conductor e (conductorPrimitiveCharacter chi) else 0) =
      ∑ c ∈ Finset.Icc 1 Q, ∑ e ∈ Finset.Icc 1 Q,
        if R < c ∧ e.Coprime (c * k) ∧ c * e ∣ q then
          ∑ psi : PrimitiveCharacter c, F c e psi else 0 := by
  rw [sum_high_characters_by_conductor hq R hR
    (fun c psi ↦ ∑ e ∈ q.divisors,
      if e.Coprime (c * k) then F c e psi else 0)]
  rw [Finset.sum_filter, sum_divisors_to_Icc Q q hq hqQ]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hcq : c ∣ q
  · rw [if_pos hcq]
    by_cases hRc : R < c
    · rw [if_pos hRc]
      simp_rw [sum_divisors_to_Icc Q q hq hqQ]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hegate : e.Coprime (c * k)
      · by_cases heq : e ∣ q
        · have hce : c * e ∣ q :=
            (product_divides_iff_of_coprime hegate).mpr ⟨hcq, heq⟩
          have hfull : R < c ∧ e.Coprime (c * k) ∧ c * e ∣ q :=
            ⟨hRc, hegate, hce⟩
          simp only [if_pos heq, if_pos hegate, if_pos hfull]
        · have hnce : ¬c * e ∣ q :=
            fun h ↦ heq ((product_divides_iff_of_coprime hegate).mp h).2
          simp only [if_neg heq, Finset.sum_const_zero, hnce, and_false, if_false]
      · simp [hegate]
    · rw [if_neg hRc]
      simp only [hRc, false_and, if_false, Finset.sum_const_zero]
  · rw [if_neg hcq]
    symm
    apply Finset.sum_eq_zero
    intro e he
    have hnce : ¬c * e ∣ q := fun h ↦ hcq ((dvd_mul_right c e).trans h)
    simp only [hnce, and_false, if_false]

/-- Exact triple regrouping of the full character-level Mobius fibres.
The only full-level weight is `w`; it may in particular be
`tau(q) * q / phi(q)`. -/
private theorem weighted_high_moebius_regroup
    (Q R k : ℕ) (hR : 0 < R) (w : ℕ → ℝ)
    (F : (c : ℕ) → ℕ → PrimitiveCharacter c → ℝ) :
    (∑ q ∈ Finset.Icc 1 Q, w q *
      ∑ chi ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
          (fun chi ↦ R < chi.conductor),
        ∑ e ∈ q.divisors,
          if e.Coprime (chi.conductor * k) then
            F chi.conductor e (conductorPrimitiveCharacter chi) else 0) =
      ∑ c ∈ Finset.Icc 1 Q, ∑ e ∈ Finset.Icc 1 Q,
        if R < c ∧ e.Coprime (c * k) then
          (∑ q ∈ Finset.Icc 1 Q with c * e ∣ q, w q) *
            ∑ psi : PrimitiveCharacter c, F c e psi else 0 := by
  calc
    _ = ∑ q ∈ Finset.Icc 1 Q, ∑ c ∈ Finset.Icc 1 Q,
        ∑ e ∈ Finset.Icc 1 Q,
          if R < c ∧ e.Coprime (c * k) ∧ c * e ∣ q then
            w q * ∑ psi : PrimitiveCharacter c, F c e psi else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [high_moebius_sum_at_level (Finset.mem_Icc.mp hq).1
        Q R k (Finset.mem_Icc.mp hq).2 hR F]
      simp only [Finset.mul_sum, mul_ite, mul_zero]
    _ = ∑ c ∈ Finset.Icc 1 Q, ∑ e ∈ Finset.Icc 1 Q,
        ∑ q ∈ Finset.Icc 1 Q,
          if R < c ∧ e.Coprime (c * k) ∧ c * e ∣ q then
            w q * ∑ psi : PrimitiveCharacter c, F c e psi else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro e he
      by_cases hRc : R < c
      · by_cases hegate : e.Coprime (c * k)
        · rw [if_pos ⟨hRc, hegate⟩, Finset.sum_filter, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro q hq
          by_cases hce : c * e ∣ q
          · rw [if_pos ⟨hRc, hegate, hce⟩, if_pos hce]
          · rw [if_neg (fun h ↦ hce h.2.2), if_neg hce, zero_mul]
        · simp only [hegate, false_and, and_false, if_false, Finset.sum_const_zero]
      · simp only [hRc, false_and, if_false, Finset.sum_const_zero]


private theorem sum_tau_inv_le (T : ℕ) :
    (∑ e ∈ Finset.Icc 1 T, divisorTau e / (e : ℝ)) ≤
      (1 + Real.log (T : ℝ)) ^ 2 := by
  have hI : Finset.Icc 1 T = Finset.Ioc 0 T := by
    ext e
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  simpa only [hI, fouvryTau_two, divisorTau] using sum_fouvryTau_div_le 2 T

/-- The native sharp primitive large sieve at spectral parameter zero,
applied to the complete auxiliary masked polynomial and its actual energy. -/
private theorem auxiliary_primitive_cell_mean_le
    (N e k D : ℕ) (he : 0 < e) (hD : 0 < D)
    (b : ℕ → ℂ) (hb : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) :
    (∑ c ∈ Finset.Ioc D (2 * D), (c.totient : ℝ)⁻¹ *
      ∑ psi : PrimitiveCharacter c,
        ‖∑ m ∈ Finset.Icc 1 (N / e),
          (if m.Coprime k then b (e * m) else 0) *
            psi.1 (m : ZMod c)‖ ^ 2) ≤
      (2 * chen1973Lemma6Eq19SharpConstant) *
        ((D : ℝ) + ((N / e : ℕ) : ℝ) / (D : ℝ)) * ((N / e : ℕ) : ℝ) := by
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have h := ChenLiuCoprimeProducer.polynomial_second_moment_energy
    (Finset.Icc 1 (N / e)) (fun m ↦ if m.Coprime k then b (e * m) else 0)
    (N / e) (fun _ h ↦ h) hDR (0 : ℂ)
  have hcell : ChenLiuCoprimeProducer.conductorCell (D : ℝ) =
      Finset.Ioc D (2 * D) := by
    have hcast : (2 : ℝ) * (D : ℝ) = ((2 * D : ℕ) : ℝ) := by norm_cast
    simp only [ChenLiuCoprimeProducer.conductorCell, hcast, Nat.floor_natCast]
  simp only [hcell, ChenLiuCoprimeProducer.polynomial, Complex.cpow_zero,
    div_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (auxiliary_multiple_energy_le N e k he b hb)
    (by have hC := chen1973Lemma6_eq19SharpConstant_pos; positivity))

/-- The two terms of the sharp-cell estimate keep one reciprocal Mobius
factor. Its divisor mean costs only two logarithms. -/
private theorem auxiliary_primitive_cell_mean_sum_le
    (N Q k D : ℕ) (hD : 0 < D)
    (b : ℕ → ℂ) (hb : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) :
    (∑ e ∈ Finset.Icc 1 Q, (divisorTau e / (e.totient : ℝ)) *
      ∑ c ∈ Finset.Ioc D (2 * D), (c.totient : ℝ)⁻¹ *
        ∑ psi : PrimitiveCharacter c,
          ‖∑ m ∈ Finset.Icc 1 (N / e),
            (if m.Coprime k then b (e * m) else 0) *
              psi.1 (m : ZMod c)‖ ^ 2) ≤
      (2 * chen1973Lemma6Eq19SharpConstant) *
        ((D : ℝ) * (N : ℝ) + (N : ℝ) ^ 2 / (D : ℝ)) *
          (1 + Real.log (Q : ℝ)) ^ 2 := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  calc
    _ ≤ ∑ e ∈ Finset.Icc 1 Q, (divisorTau e / (e.totient : ℝ)) *
        ((2 * chen1973Lemma6Eq19SharpConstant) *
          ((D : ℝ) + ((N / e : ℕ) : ℝ) / (D : ℝ)) *
            ((N / e : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro e he
      exact mul_le_mul_of_nonneg_left
        (auxiliary_primitive_cell_mean_le N e k D (Finset.mem_Icc.mp he).1 hD b hb)
        (div_nonneg (divisorTau_nonneg e) (Nat.cast_nonneg _))
    _ ≤ ∑ e ∈ Finset.Icc 1 Q,
        ((2 * chen1973Lemma6Eq19SharpConstant) *
          ((D : ℝ) * (N : ℝ) + (N : ℝ) ^ 2 / (D : ℝ))) *
            (divisorTau e / (e : ℝ)) := by
      apply Finset.sum_le_sum
      intro e he
      have hepos : 0 < e := (Finset.mem_Icc.mp he).1
      have heR : (0 : ℝ) < e := by exact_mod_cast hepos
      have hphi : (1 : ℝ) ≤ e.totient := by
        exact_mod_cast Nat.totient_pos.mpr hepos
      have hTdiv : ((N / e : ℕ) : ℝ) ≤ (N : ℝ) / (e : ℝ) := by
        apply (le_div_iff₀ heR).mpr
        have h := Nat.div_mul_le_self N e
        exact_mod_cast h
      have hTN : ((N / e : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N e
      have hprod : ((D : ℝ) + ((N / e : ℕ) : ℝ) / (D : ℝ)) *
          ((N / e : ℕ) : ℝ) ≤
            ((D : ℝ) * (N : ℝ) + (N : ℝ) ^ 2 / (D : ℝ)) / (e : ℝ) := by
        have hsq : ((N / e : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 / (e : ℝ) := by
          calc
            _ ≤ (N : ℝ) * ((N / e : ℕ) : ℝ) := by
              nlinarith [mul_nonneg (Nat.cast_nonneg (N / e)) (sub_nonneg.mpr hTN)]
            _ ≤ (N : ℝ) * ((N : ℝ) / (e : ℝ)) :=
              mul_le_mul_of_nonneg_left hTdiv (Nat.cast_nonneg N)
            _ = _ := by ring
        calc
          _ = (D : ℝ) * ((N / e : ℕ) : ℝ) +
              ((N / e : ℕ) : ℝ) ^ 2 / (D : ℝ) := by ring
          _ ≤ (D : ℝ) * ((N : ℝ) / (e : ℝ)) +
              ((N : ℝ) ^ 2 / (e : ℝ)) / (D : ℝ) := by gcongr
          _ = _ := by ring
      have htau : divisorTau e / (e.totient : ℝ) ≤ divisorTau e := by
        simpa only [div_one] using div_le_div_of_nonneg_left
          (divisorTau_nonneg e) (by norm_num : (0 : ℝ) < 1) hphi
      calc
        _ = (2 * chen1973Lemma6Eq19SharpConstant) *
            ((divisorTau e / (e.totient : ℝ)) *
              (((D : ℝ) + ((N / e : ℕ) : ℝ) / (D : ℝ)) *
                ((N / e : ℕ) : ℝ))) := by ring
        _ ≤ (2 * chen1973Lemma6Eq19SharpConstant) *
            (divisorTau e *
              (((D : ℝ) * (N : ℝ) + (N : ℝ) ^ 2 / (D : ℝ)) / (e : ℝ))) := by
          apply mul_le_mul_of_nonneg_left _
            (by have hC := chen1973Lemma6_eq19SharpConstant_pos; positivity)
          exact mul_le_mul htau hprod (by positivity) (divisorTau_nonneg e)
        _ = _ := by ring
    _ = ((2 * chen1973Lemma6Eq19SharpConstant) *
        ((D : ℝ) * (N : ℝ) + (N : ℝ) ^ 2 / (D : ℝ))) *
          ∑ e ∈ Finset.Icc 1 Q, divisorTau e / (e : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left (sum_tau_inv_le Q)
        (by have hC := chen1973Lemma6_eq19SharpConstant_pos; positivity)


/-- All physical character levels are now regrouped into conductor and
Mobius fibres. The conductor divisor loss remains local to `c`. -/
private theorem auxiliary_high_mean_le_conductor_majorant
    (N Q R k : ℕ) (hQ : 0 < Q) (hR : 0 < R) (b : ℕ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ chi ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
          (fun chi ↦ R < chi.conductor),
        ‖∑ n ∈ Finset.Icc 1 N,
          (if n.Coprime k then b n else 0) * chi (n : ZMod q)‖ ^ 2) ≤
      (Q : ℝ) * (1 + Real.log (Q : ℝ)) ^ 3 *
        ∑ c ∈ (Finset.Icc 1 Q).filter (fun c ↦ R < c),
          divisorTau c * (c.totient : ℝ)⁻¹ *
            ∑ e ∈ Finset.Icc 1 Q, (divisorTau e / (e.totient : ℝ)) *
              ∑ psi : PrimitiveCharacter c,
                ‖∑ m ∈ Finset.Icc 1 (N / e),
                  (if m.Coprime k then b (e * m) else 0) *
                    psi.1 (m : ZMod c)‖ ^ 2 := by
  let F : (c : ℕ) → ℕ → PrimitiveCharacter c → ℝ := fun c e psi ↦
    ‖∑ m ∈ Finset.Icc 1 (N / e),
      (if m.Coprime k then b (e * m) else 0) * psi.1 (m : ZMod c)‖ ^ 2
  have hF (c e : ℕ) (psi : PrimitiveCharacter c) : 0 ≤ F c e psi := sq_nonneg _
  have hlog : 0 ≤ 1 + Real.log (Q : ℝ) := by
    have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith [Real.log_nonneg hQ1]
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ chi ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
            (fun chi ↦ R < chi.conductor),
          divisorTau q * ∑ e ∈ q.divisors,
            if e.Coprime (chi.conductor * k) then
              F chi.conductor e (conductorPrimitiveCharacter chi) else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro chi hchi
      exact auxiliary_character_sum_sq_le_moebius (Finset.mem_Icc.mp hq).1 N k b chi
    _ = ∑ c ∈ Finset.Icc 1 Q, ∑ e ∈ Finset.Icc 1 Q,
        if R < c ∧ e.Coprime (c * k) then
          (∑ q ∈ Finset.Icc 1 Q with c * e ∣ q,
            divisorTau q * ((q : ℝ) / (q.totient : ℝ))) *
              ∑ psi : PrimitiveCharacter c, F c e psi else 0 := by
      rw [← weighted_high_moebius_regroup Q R k hR
        (fun q ↦ divisorTau q * ((q : ℝ) / (q.totient : ℝ))) F]
      apply Finset.sum_congr rfl
      intro q hq
      rw [← Finset.mul_sum]
      ring
    _ ≤ ∑ c ∈ Finset.Icc 1 Q, ∑ e ∈ Finset.Icc 1 Q,
        if R < c then
          ((divisorTau c * ((c : ℝ) / (c.totient : ℝ))) *
            (divisorTau e / (e.totient : ℝ)) * ((Q : ℝ) / (c : ℝ)) *
              (1 + Real.log (Q : ℝ)) ^ 3) *
                ∑ psi : PrimitiveCharacter c, F c e psi else 0 := by
      apply Finset.sum_le_sum
      intro c hc
      apply Finset.sum_le_sum
      intro e he
      by_cases hRc : R < c
      · rw [if_pos hRc]
        by_cases hegate : e.Coprime (c * k)
        · rw [if_pos ⟨hRc, hegate⟩]
          exact mul_le_mul_of_nonneg_right
            (tau_weighted_product_fibre_le Q c e hQ
              (Finset.mem_Icc.mp hc).1 (Finset.mem_Icc.mp he).1)
            (Finset.sum_nonneg fun psi _ ↦ hF c e psi)
        · rw [if_neg (by simp only [hegate, and_false, not_false_eq_true])]
          exact mul_nonneg
            (mul_nonneg
              (mul_nonneg
                (mul_nonneg
                  (mul_nonneg (divisorTau_nonneg c) (by positivity))
                  (div_nonneg (divisorTau_nonneg e) (by positivity)))
                (by positivity))
              (pow_nonneg hlog 3))
            (Finset.sum_nonneg fun psi _ ↦ hF c e psi)
      · simp only [hRc, false_and, if_false]
        exact le_rfl
    _ = _ := by
      symm
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hRc : R < c
      · simp only [if_pos hRc]
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        have hcR : (0 : ℝ) < c := by exact_mod_cast (Finset.mem_Icc.mp hc).1
        have hphiC : (0 : ℝ) < c.totient := by
          exact_mod_cast Nat.totient_pos.mpr (Finset.mem_Icc.mp hc).1
        have hphiE : (0 : ℝ) < e.totient := by
          exact_mod_cast Nat.totient_pos.mpr (Finset.mem_Icc.mp he).1
        dsimp only [F]
        field_simp [hcR.ne', hphiC.ne', hphiE.ne']
      · simp only [if_neg hRc, mul_zero, Finset.sum_const_zero]


private theorem auxiliary_conductor_cell_mean_le
    (N Q k D : ℕ) (hD : 0 < D)
    (b : ℕ → ℂ) (hb : ∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1)
    (T : ℝ) (hT : 0 ≤ T)
    (htau : ∀ c ∈ Finset.Ioc D (2 * D), divisorTau c ≤ T) :
    (∑ c ∈ Finset.Ioc D (2 * D), divisorTau c * (c.totient : ℝ)⁻¹ *
      ∑ e ∈ Finset.Icc 1 Q, (divisorTau e / (e.totient : ℝ)) *
        ∑ psi : PrimitiveCharacter c,
          ‖∑ m ∈ Finset.Icc 1 (N / e),
            (if m.Coprime k then b (e * m) else 0) *
              psi.1 (m : ZMod c)‖ ^ 2) ≤
      T * ((2 * chen1973Lemma6Eq19SharpConstant) *
        ((D : ℝ) * (N : ℝ) + (N : ℝ) ^ 2 / (D : ℝ)) *
          (1 + Real.log (Q : ℝ)) ^ 2) := by
  calc
    _ ≤ ∑ c ∈ Finset.Ioc D (2 * D), T * (c.totient : ℝ)⁻¹ *
        ∑ e ∈ Finset.Icc 1 Q, (divisorTau e / (e.totient : ℝ)) *
          ∑ psi : PrimitiveCharacter c,
            ‖∑ m ∈ Finset.Icc 1 (N / e),
              (if m.Coprime k then b (e * m) else 0) *
                psi.1 (m : ZMod c)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (htau c hc) (by positivity))
        (Finset.sum_nonneg fun e _ ↦ mul_nonneg
          (div_nonneg (divisorTau_nonneg e) (by positivity))
          (Finset.sum_nonneg fun psi _ ↦ sq_nonneg _))
    _ = T * (∑ e ∈ Finset.Icc 1 Q, (divisorTau e / (e.totient : ℝ)) *
        ∑ c ∈ Finset.Ioc D (2 * D), (c.totient : ℝ)⁻¹ *
          ∑ psi : PrimitiveCharacter c,
            ‖∑ m ∈ Finset.Icc 1 (N / e),
              (if m.Coprime k then b (e * m) else 0) *
                psi.1 (m : ZMod c)‖ ^ 2) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro psi hpsi
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (auxiliary_primitive_cell_mean_sum_le N Q k D hD b hb) hT

/-- A finite nonnegative cover inequality, allowing overlap between blocks. -/
private theorem sum_le_sum_of_block_cover (s J : Finset ℕ)
    (block : ℕ → Finset ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hcover : ∀ n ∈ s, ∃ j ∈ J, n ∈ block j) :
    (∑ n ∈ s, f n) ≤ ∑ j ∈ J, ∑ n ∈ block j, f n := by
  calc
    _ ≤ ∑ n ∈ s, ∑ j ∈ J, if n ∈ block j then f n else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨j, hj, hnj⟩ := hcover n hn
      simpa only [if_pos hnj] using
        (Finset.single_le_sum
          (f := fun i ↦ if n ∈ block i then f n else 0)
          (fun i hi ↦ by
            by_cases hni : n ∈ block i
            · rw [if_pos hni]
              exact hf n
            · rw [if_neg hni]) hj)
    _ = ∑ j ∈ J, ∑ n ∈ s with n ∈ block j, f n := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun n hn ↦ (Finset.mem_filter.mp hn).2) (fun n hn hn' ↦ hf n)

private def conductorWindows (R Q : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log2 Q + 1)).filter (fun j ↦ R * 2 ^ j < Q)

private theorem conductorWindows_card_le (R Q : ℕ) :
    (conductorWindows R Q).card ≤ Nat.log2 Q + 1 := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)

/-- Every strict high conductor belongs to a positive doubling window whose
lower endpoint is below the original full-level cutoff. -/
private theorem conductorWindows_cover (R Q : ℕ) (hR : 0 < R) (hQ : 0 < Q)
    (c : ℕ) (hcR : R < c) (hcQ : c ≤ Q) :
    ∃ j ∈ conductorWindows R Q, c ∈ Finset.Ioc (R * 2 ^ j) (2 * (R * 2 ^ j)) := by
  let m : ℕ := (c - 1) / R
  have hmpos : 0 < m := by
    exact Nat.div_pos (by omega) hR
  let j : ℕ := Nat.log2 m
  have hpowlow : 2 ^ j ≤ m := Nat.log2_self_le hmpos.ne'
  have hpowhi : m < 2 ^ (j + 1) := Nat.lt_log2_self
  have hmul : R * m ≤ c - 1 := Nat.mul_div_le (c - 1) R
  have hlow : R * 2 ^ j < c := by
    have h := Nat.mul_le_mul_left R hpowlow
    omega
  have hdiv : c - 1 < R * (m + 1) := by
    simpa only [mul_comm] using
      (Nat.div_lt_iff_lt_mul hR).mp (by omega : (c - 1) / R < m + 1)
  have hhigh : c ≤ 2 * (R * 2 ^ j) := by
    calc
      c ≤ R * (m + 1) := by omega
      _ ≤ R * 2 ^ (j + 1) := Nat.mul_le_mul_left R (by omega)
      _ = _ := by rw [Nat.pow_succ]; ring
  have hmQ : m ≤ Q := (Nat.div_le_self (c - 1) R).trans (by omega)
  have hj : j ≤ Nat.log2 Q :=
    (Nat.le_log2 hQ.ne').mpr (hpowlow.trans hmQ)
  refine ⟨j, ?_, Finset.mem_Ioc.mpr ⟨hlow, hhigh⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩


private theorem conductor_cell_scale_le {N Q D R eta : ℝ}
    (hN : 0 ≤ N) (hR : 0 < R) (hRD : R ≤ D) (hDQ : D ≤ Q)
    (heta : 0 < eta) (heta1 : eta < 1) :
    (2 * D) ^ eta * (D * N + N ^ 2 / D) ≤
      (2 : ℝ) ^ eta * (N ^ 2 / R ^ (1 - eta) + Q ^ (1 + eta) * N) := by
  have hD : 0 < D := hR.trans_le hRD
  have hpos : D ^ (1 + eta) ≤ Q ^ (1 + eta) :=
    Real.rpow_le_rpow hD.le hDQ (by linarith)
  have hneg : D ^ (eta - 1) ≤ 1 / R ^ (1 - eta) := by
    have h := Real.rpow_le_rpow_of_nonpos hR hRD (by linarith : eta - 1 ≤ 0)
    have heq : eta - 1 = -(1 - eta) := by ring
    simpa only [heq, Real.rpow_neg hR.le, one_div] using h
  calc
    _ = (2 : ℝ) ^ eta * (D ^ (1 + eta) * N + D ^ (eta - 1) * N ^ 2) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hD.le,
        show 1 + eta = eta + 1 by ring, Real.rpow_add_one hD.ne',
        Real.rpow_sub_one hD.ne']
      ring
    _ ≤ (2 : ℝ) ^ eta * (Q ^ (1 + eta) * N +
        (1 / R ^ (1 - eta)) * N ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right hpos hN)
          (mul_le_mul_of_nonneg_right hneg (sq_nonneg N)))
        (Real.rpow_nonneg (by norm_num) eta)
    _ = _ := by ring

private theorem conductorWindows_card_le_log (R Q : ℕ) (hQ : 0 < Q) :
    ((conductorWindows R Q).card : ℝ) ≤
      (1 + (Real.log 2)⁻¹) * (1 + Real.log (Q : ℝ)) := by
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hlogQ : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg hQ1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ ≤ ((Nat.log2 Q + 1 : ℕ) : ℝ) := by
      exact_mod_cast conductorWindows_card_le R Q
    _ ≤ Real.log (Q : ℝ) / Real.log 2 + 1 := by
      have h := Real.log2_le_logb Q
      simpa only [Nat.cast_add, Nat.cast_one, Real.logb, add_comm] using
        add_le_add_right h 1
    _ ≤ _ := by
      have hprod : 0 ≤ (Real.log 2)⁻¹ * Real.log (Q : ℝ) :=
        mul_nonneg (inv_nonneg.mpr hlog2.le) hlogQ
      have hinv : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr hlog2.le
      rw [div_eq_mul_inv]
      nlinarith


/-- Uniform high-conductor mean for arbitrary bounded coefficients, retaining
both the auxiliary coprime mask and the original, possibly imprimitive,
character level. The constant is selected before every varying parameter. -/
theorem auxiliary_highConductor_mean_le
    {eta : ℝ} (heta : 0 < eta) (heta1 : eta < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ N Q R k : ℕ,
        0 < N → 0 < Q → 0 < R → 0 < k →
        ∀ b : ℕ → ℂ,
          (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
          (∑ q ∈ Finset.Icc 1 Q,
            ((q : ℝ) / (q.totient : ℝ)) *
              ∑ χ ∈
                (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
                  (fun χ ↦ R < χ.conductor),
                ‖∑ n ∈ Finset.Icc 1 N,
                  (if n.Coprime k then b n else 0) *
                    χ (n : ZMod q)‖ ^ 2) ≤
            C * (1 + Real.log (2 * (N : ℝ) * (Q : ℝ))) ^ (12 : ℕ) *
              ((Q : ℝ) * (N : ℝ) ^ 2 / (R : ℝ) ^ (1 - eta) +
                (Q : ℝ) ^ (2 + eta) * (N : ℝ)) := by
  obtain ⟨Ctau, hCtau, htau⟩ :=
    PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
      (k := 2) (by norm_num) heta
  let A : ℝ := Ctau * (2 : ℝ) ^ eta * (2 * chen1973Lemma6Eq19SharpConstant)
  let H : ℝ := 1 + (Real.log 2)⁻¹
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (mul_pos hCtau (Real.rpow_pos_of_pos (by norm_num) eta))
      (mul_pos (by norm_num) chen1973Lemma6_eq19SharpConstant_pos)
  have hH : 0 < H := by
    dsimp only [H]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine ⟨A * H, mul_pos hA hH, ?_⟩
  intro N Q R k hN hQ hR _hk b hb
  let LQ : ℝ := 1 + Real.log (Q : ℝ)
  let L : ℝ := 1 + Real.log (2 * (N : ℝ) * (Q : ℝ))
  let S : ℝ := (N : ℝ) ^ 2 / (R : ℝ) ^ (1 - eta) +
    (Q : ℝ) ^ (1 + eta) * (N : ℝ)
  let B : ℝ := (Q : ℝ) * (N : ℝ) ^ 2 / (R : ℝ) ^ (1 - eta) +
    (Q : ℝ) ^ (2 + eta) * (N : ℝ)
  let f : ℕ → ℝ := fun c ↦ divisorTau c * (c.totient : ℝ)⁻¹ *
    ∑ e ∈ Finset.Icc 1 Q, (divisorTau e / (e.totient : ℝ)) *
      ∑ psi : PrimitiveCharacter c,
        ‖∑ m ∈ Finset.Icc 1 (N / e),
          (if m.Coprime k then b (e * m) else 0) *
            psi.1 (m : ZMod c)‖ ^ 2
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hLQ1 : 1 ≤ LQ := by
    dsimp only [LQ]
    linarith [Real.log_nonneg hQ1]
  have hLQL : LQ ≤ L := by
    dsimp only [LQ, L]
    have harg : (Q : ℝ) ≤ 2 * (N : ℝ) * (Q : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hN1) hQ0.le]
    linarith [Real.log_le_log hQ0 harg]
  have hL1 : 1 ≤ L := hLQ1.trans hLQL
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hQB : (Q : ℝ) * S = B := by
    have hqpow : (Q : ℝ) * (Q : ℝ) ^ (1 + eta) = (Q : ℝ) ^ (2 + eta) := by
      calc
        _ = (Q : ℝ) ^ (1 : ℝ) * (Q : ℝ) ^ (1 + eta) := by rw [Real.rpow_one]
        _ = (Q : ℝ) ^ (1 + (1 + eta)) :=
          (Real.rpow_add hQ0 1 (1 + eta)).symm
        _ = _ := by congr 1; ring
    dsimp only [S, B]
    calc
      _ = (Q : ℝ) * (N : ℝ) ^ 2 / (R : ℝ) ^ (1 - eta) +
          ((Q : ℝ) * (Q : ℝ) ^ (1 + eta)) * (N : ℝ) := by ring
      _ = _ := by rw [hqpow]
  have hf (c : ℕ) : 0 ≤ f c := by
    dsimp only [f]
    exact mul_nonneg (mul_nonneg (divisorTau_nonneg c) (by positivity))
      (Finset.sum_nonneg fun e _ ↦ mul_nonneg
        (div_nonneg (divisorTau_nonneg e) (by positivity))
        (Finset.sum_nonneg fun psi _ ↦ sq_nonneg _))
  have hwindow (j : ℕ) (hj : j ∈ conductorWindows R Q) :
      (∑ c ∈ Finset.Ioc (R * 2 ^ j) (2 * (R * 2 ^ j)), f c) ≤
        A * S * LQ ^ 2 := by
    let D : ℕ := R * 2 ^ j
    have hRD : R ≤ D := Nat.le_mul_of_pos_right R (Nat.pow_pos (by decide))
    have hD : 0 < D := hR.trans_le hRD
    have hDQ : D ≤ Q := by
      exact (Finset.mem_filter.mp hj).2.le
    have htauD : ∀ c ∈ Finset.Ioc D (2 * D),
        divisorTau c ≤ Ctau * (2 * (D : ℝ)) ^ eta := by
      intro c hc
      have hcpos : 0 < c := hD.trans (Finset.mem_Ioc.mp hc).1
      have hC : divisorTau c ≤ Ctau * (c : ℝ) ^ eta := by
        simpa only [divisorTau, fouvryTau_two] using htau c hcpos
      refine hC.trans (mul_le_mul_of_nonneg_left ?_ hCtau.le)
      exact Real.rpow_le_rpow (Nat.cast_nonneg c)
        (by exact_mod_cast (Finset.mem_Ioc.mp hc).2) heta.le
    have hcell := auxiliary_conductor_cell_mean_le N Q k D hD b hb
      (Ctau * (2 * (D : ℝ)) ^ eta) (by positivity) htauD
    have hscale := conductor_cell_scale_le (N := (N : ℝ))
      (Q := (Q : ℝ)) (D := (D : ℝ)) (R := (R : ℝ))
      (Nat.cast_nonneg N) hR0 (by exact_mod_cast hRD) (by exact_mod_cast hDQ)
      heta heta1
    calc
      _ ≤ (Ctau * (2 * (D : ℝ)) ^ eta) *
          ((2 * chen1973Lemma6Eq19SharpConstant) *
            ((D : ℝ) * (N : ℝ) + (N : ℝ) ^ 2 / (D : ℝ)) * LQ ^ 2) := hcell
      _ = (Ctau * (2 * chen1973Lemma6Eq19SharpConstant) * LQ ^ 2) *
          ((2 * (D : ℝ)) ^ eta *
            ((D : ℝ) * (N : ℝ) + (N : ℝ) ^ 2 / (D : ℝ))) := by ring
      _ ≤ (Ctau * (2 * chen1973Lemma6Eq19SharpConstant) * LQ ^ 2) *
          ((2 : ℝ) ^ eta * S) := by
        exact mul_le_mul_of_nonneg_left hscale
          (by have hC := chen1973Lemma6_eq19SharpConstant_pos; positivity)
      _ = A * S * LQ ^ 2 := by dsimp only [A]; ring
  have hcover : ∀ c ∈ (Finset.Icc 1 Q).filter (fun c ↦ R < c),
      ∃ j ∈ conductorWindows R Q,
        c ∈ Finset.Ioc (R * 2 ^ j) (2 * (R * 2 ^ j)) := by
    intro c hc
    exact conductorWindows_cover R Q hR hQ c
      (Finset.mem_filter.mp hc).2 (Finset.mem_Icc.mp (Finset.mem_filter.mp hc).1).2
  have hsum :
      (∑ c ∈ (Finset.Icc 1 Q).filter (fun c ↦ R < c), f c) ≤
        ((conductorWindows R Q).card : ℝ) * (A * S * LQ ^ 2) := by
    refine (sum_le_sum_of_block_cover _ (conductorWindows R Q)
      (fun j ↦ Finset.Ioc (R * 2 ^ j) (2 * (R * 2 ^ j))) f hf hcover).trans ?_
    calc
      _ ≤ ∑ j ∈ conductorWindows R Q, A * S * LQ ^ 2 :=
        Finset.sum_le_sum hwindow
      _ = _ := by simp [mul_comm]
  have hcard : ((conductorWindows R Q).card : ℝ) ≤ H * LQ :=
    conductorWindows_card_le_log R Q hQ
  have hlogpow : LQ ^ 6 ≤ L ^ 12 :=
    (pow_le_pow_left₀ (by linarith : 0 ≤ LQ) hLQL 6).trans
      (pow_le_pow_right₀ hL1 (by decide : 6 ≤ 12))
  calc
    _ ≤ (Q : ℝ) * LQ ^ 3 *
        ∑ c ∈ (Finset.Icc 1 Q).filter (fun c ↦ R < c), f c :=
      auxiliary_high_mean_le_conductor_majorant N Q R k hQ hR b
    _ ≤ (Q : ℝ) * LQ ^ 3 *
        (((conductorWindows R Q).card : ℝ) * (A * S * LQ ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (Q : ℝ) * LQ ^ 3 * (H * LQ * (A * S * LQ ^ 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcard (by positivity)) (by positivity)
    _ = (A * H) * LQ ^ 6 * B := by rw [← hQB]; ring
    _ ≤ (A * H) * L ^ 12 * B := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogpow (mul_nonneg hA.le hH.le)) hB
    _ = _ := rfl

end

end ImbalancedChen.Part3.SharedFirstFactorHighConductor
