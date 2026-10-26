import ImbalancedChen.Part3EisensteinAmplitudeMultiplicativity
import ImbalancedChen.Part3ActualRamanujanSinglePrimeLevelSplit

/-! Genuine finite distinct-prime exponent lattice, its positive integer
frequency map and injectivity. Actual normalized amplitudes split along
the literal head/tail integer product, by proved coprimality. No formal
coefficient or tuple uniqueness is an assumption.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Complex
open ImbalancedChen.Part3.NormalizedEisensteinPrimeAmplitude20261026b
open ImbalancedChen.Part3.EisensteinAmplitudeMultiplicativity20261026b
open ImbalancedChen.Part3.ActualRamanujanSinglePrimeLevelSplit

namespace ImbalancedChen.Part3.FinitePrimeExponentLattice20261026b

def PrimeExponentCarrier : List ℕ → Type
  | [] => PUnit
  | _ :: L => ℕ × PrimeExponentCarrier L

def exponentFrequency : (L : List ℕ) → PrimeExponentCarrier L → ℕ
  | [], _ => 1
  | p :: L, e => p ^ e.1 * exponentFrequency L e.2

def exponentWeight : (L : List ℕ) → (ℕ → ℂ) → PrimeExponentCarrier L → ℂ
  | [], _, _ => 1
  | p :: L, X, e => X p ^ e.1 * exponentWeight L X e.2

def finitePrimeEulerTerm (L : List ℕ) (t : ℝ) (X : ℕ → ℂ)
    (e : PrimeExponentCarrier L) : ℂ :=
  normalizedDivisorAmplitude (exponentFrequency L e) (1 / 2 + (t : ℂ) * Complex.I) *
    exponentWeight L X e

theorem exponentFrequency_pos (L : List ℕ) (hPrime : ∀ p ∈ L, p.Prime)
    (e : PrimeExponentCarrier L) : 0 < exponentFrequency L e := by
  induction L generalizing hPrime e with
  | nil => exact Nat.zero_lt_one
  | cons p L ih =>
      exact mul_pos (pow_pos (hPrime p (by simp)).pos e.1)
        (ih (fun q hq => hPrime q (List.mem_cons_of_mem _ hq)) e.2)

theorem exponentFrequency_coprime {p : ℕ} (hp : p.Prime)
    (L : List ℕ) (hPrime : ∀ q ∈ L, q.Prime) (hnot : p ∉ L)
    (e : PrimeExponentCarrier L) : p.Coprime (exponentFrequency L e) := by
  induction L generalizing hPrime hnot e with
  | nil => exact Nat.coprime_one_right p
  | cons q L ih =>
      have hpq : p ≠ q := by intro he; subst q; exact hnot (by simp)
      have hq : q.Prime := hPrime q (by simp)
      apply Nat.coprime_mul_iff_right.mpr
      exact ⟨((Nat.coprime_primes hp hq).mpr hpq).pow_right e.1,
        ih (fun r hr => hPrime r (List.mem_cons_of_mem _ hr))
          (fun hpL => hnot (List.mem_cons_of_mem _ hpL)) e.2⟩

/-- The head exponent is the native integer prime-factorization exponent. -/
theorem exponentFrequency_head_factorization {p : ℕ} (hp : p.Prime)
    (L : List ℕ) (hPrime : ∀ q ∈ L, q.Prime) (hnot : p ∉ L)
    (e : PrimeExponentCarrier (p :: L)) :
    (exponentFrequency (p :: L) e).factorization p = e.1 := by
  exact primePowerComplement_factorization hp e.1
    ⟨exponentFrequency L e.2, exponentFrequency_coprime hp L hPrime hnot e.2⟩

/-- Distinct-prime exponent coordinates neither duplicate nor collapse
their actual positive integer frequencies. -/
theorem exponentFrequency_injective (L : List ℕ) (hL : L.Nodup)
    (hPrime : ∀ p ∈ L, p.Prime) : Function.Injective (exponentFrequency L) := by
  induction L generalizing hL hPrime with
  | nil =>
      intro e f h
      cases e
      cases f
      rfl
  | cons p L ih =>
      have hp : p.Prime := hPrime p (by simp)
      have hTailPrime : ∀ q ∈ L, q.Prime := fun q hq => hPrime q (List.mem_cons_of_mem _ hq)
      obtain ⟨hnot, hTail⟩ := List.nodup_cons.mp hL
      intro e f hef
      have hh : e.1 = f.1 := by
        have h := congrArg (fun n : ℕ => n.factorization p) hef
        simpa only [exponentFrequency_head_factorization hp L hTailPrime hnot] using h
      apply Prod.ext hh
      apply ih hTail hTailPrime
      change p ^ e.1 * exponentFrequency L e.2 = p ^ f.1 * exponentFrequency L f.2 at hef
      rw [hh] at hef
      exact mul_left_cancel₀ (pow_ne_zero f.1 hp.ne_zero) hef

/-- Actual composite coefficient and weight split at the prime head. -/
theorem finitePrimeEulerTerm_cons {p : ℕ} (hp : p.Prime)
    (L : List ℕ) (hPrime : ∀ q ∈ L, q.Prime) (hnot : p ∉ L)
    (t : ℝ) (X : ℕ → ℂ) (e : PrimeExponentCarrier (p :: L)) :
    finitePrimeEulerTerm (p :: L) t X e =
      (normalizedDivisorAmplitude (p ^ e.1) (1 / 2 + (t : ℂ) * Complex.I) * X p ^ e.1) *
        finitePrimeEulerTerm L t X e.2 := by
  have hcop := (exponentFrequency_coprime hp L hPrime hnot e.2).pow_left e.1
  unfold finitePrimeEulerTerm
  simp only [exponentFrequency, exponentWeight]
  rw [normalizedAmplitude_mul_of_coprime hcop]
  ring

end ImbalancedChen.Part3.FinitePrimeExponentLattice20261026b
