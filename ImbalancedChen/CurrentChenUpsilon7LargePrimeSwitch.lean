import ImbalancedChen.CurrentChenUpsilon7SourceErrorBudget

/-!
# Exact large-original-prime switching for the seventh semiprime branch

The original outer selector and the ordered first cofactor prime are kept
as labels.  The last prime is switched to the original additive prime P
at the physical modulus p₁*p₂*r.  Its primality test and the inclusive
wall r <= s are retained on the recovered quotient (N-P)/(p₁*p₂*r).
In particular, p₂=r and r=s are allowed.  No mean estimate for this
moving prime-quotient AP is assumed or asserted.

The final finite-to-eventual transfer uses the previously proved unit and
small-original-prime budget with the literal ledger coefficient two.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical

/-- Original large additive primes in one physical prefix progression,
with the last-prime test and its ordered lower wall still present. -/
def currentChenUpsilon7LargePrimeSemiprimeAPSource (N : ℕ)
    (x : Σ _ : ℕ × ℕ, ℕ) : Finset ℕ :=
  (chenAdditivePrimeCarrier N).filter fun P =>
    (x.1.1 * x.1.2 * x.2) ∣ N - P ∧
      Nat.Prime ((N - P) / (x.1.1 * x.1.2 * x.2)) ∧
      x.2 ≤ (N - P) / (x.1.1 * x.1.2 * x.2) ∧
      (N : ℝ) ^ (1 / 5 : ℝ) < (P : ℝ)

/-- The actual finite switched count, retaining every original outer
label.  This is a count, not an asymptotic density or a supplied mean. -/
def currentChenUpsilon7LargePrimeSemiprimeAPSum (N : ℕ) : ℝ :=
  ∑ t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)),
    ∑ r ∈ (chenAdditivePrimeCarrier N).filter (fun r => t.2 ≤ r),
      ((currentChenUpsilon7LargePrimeSemiprimeAPSource N ⟨t, r⟩).card : ℝ)

private theorem seventh_switch_forward {N p₁ p₂ r s : ℕ}
    (hx : (⟨(p₁, p₂), (r, s)⟩ : Σ _ : ℕ × ℕ, ℕ × ℕ) ∈
      currentChenUpsilon7SemiprimeQuadruples N)
    (hlarge : (N : ℝ) ^ (1 / 5 : ℝ) <
      ((N - p₁ * p₂ * (r * s) : ℕ) : ℝ)) :
    (p₁, p₂) ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)) ∧
      r ∈ (chenAdditivePrimeCarrier N).filter (fun r => p₂ ≤ r) ∧
      N - p₁ * p₂ * (r * s) ∈
        currentChenUpsilon7LargePrimeSemiprimeAPSource N ⟨(p₁, p₂), r⟩ := by
  have houter := (Finset.mem_sigma.mp hx).1
  have hrc := (Finset.mem_product.mp
    (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).1).1
  obtain ⟨h₁, h₂, _hD, _ho, _hc, hr, hs, hcut, hrs, hlt, hP⟩ :=
    mem_currentChenUpsilon7SemiprimeQuadruples_iff.mp hx
  have ha : 0 < p₁ * p₂ * r := mul_pos
    (mul_pos (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos
      (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos) hr.pos
  have hreceiver : N - (N - p₁ * p₂ * (r * s)) = (p₁ * p₂ * r) * s := by
    rw [Nat.sub_sub_self hlt.le]
    ac_rfl
  have hquot : (N - (N - p₁ * p₂ * (r * s))) / (p₁ * p₂ * r) = s := by
    rw [hreceiver]
    exact Nat.mul_div_cancel_left s ha
  refine ⟨houter, Finset.mem_filter.mpr ⟨hrc, hcut⟩, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨hP, ?_, ?_, ?_, hlarge⟩
  · rw [hreceiver]
    exact dvd_mul_right _ _
  · simpa only [hquot] using hs
  · simpa only [hquot] using hrs

private theorem seventh_switch_backward {N : ℕ} {t : ℕ × ℕ} {r P : ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)))
    (hr : r ∈ (chenAdditivePrimeCarrier N).filter (fun r => t.2 ≤ r))
    (hP : P ∈ currentChenUpsilon7LargePrimeSemiprimeAPSource N ⟨t, r⟩) :
    (⟨t, (r, (N - P) / (t.1 * t.2 * r))⟩ : Σ _ : ℕ × ℕ, ℕ × ℕ) ∈
        currentChenUpsilon7SemiprimeQuadruples N ∧
      N - t.1 * t.2 * (r * ((N - P) / (t.1 * t.2 * r))) = P ∧
      (N : ℝ) ^ (1 / 5 : ℝ) < (P : ℝ) := by
  obtain ⟨hc, hD, ho, hcap⟩ := Finset.mem_filter.mp ht
  obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hc
  obtain ⟨hrc, hcut⟩ := Finset.mem_filter.mp hr
  obtain ⟨hPc, hd, hs, hrs, hlarge⟩ := Finset.mem_filter.mp hP
  have hPN := (mem_chenAdditivePrimeCarrier.mp hPc).1
  have hPpos := (mem_chenAdditivePrimeCarrier.mp hPc).2.1.pos
  have hmul : t.1 * t.2 * (r * ((N - P) / (t.1 * t.2 * r))) = N - P := by
    simpa only [← Nat.mul_assoc] using Nat.mul_div_cancel' hd
  have hlt : t.1 * t.2 * (r * ((N - P) / (t.1 * t.2 * r))) < N := by
    omega
  have hrecover : N - t.1 * t.2 * (r * ((N - P) / (t.1 * t.2 * r))) = P := by
    omega
  refine ⟨mem_currentChenUpsilon7SemiprimeQuadruples_iff.mpr ?_, hrecover, hlarge⟩
  exact ⟨h₁, h₂, hD, ho, hcap, (mem_chenAdditivePrimeCarrier.mp hrc).2.1,
    hs, hcut, hrs, hlt, by simpa only [hrecover] using hPc⟩

/-- Exact switching of the complete large-original-prime semiprime
branch.  There is no omission of equal prime factors or outer labels. -/
theorem currentChenUpsilon7_largePrime_semiprime_card_eq_APSum (N : ℕ) :
    (((currentChenUpsilon7SemiprimeQuadruples N).filter (fun x =>
      (N : ℝ) ^ (1 / 5 : ℝ) <
        ((N - x.1.1 * x.1.2 * (x.2.1 * x.2.2) : ℕ) : ℝ))).card : ℝ) =
      currentChenUpsilon7LargePrimeSemiprimeAPSum N := by
  let T : Finset (Σ _ : ℕ × ℕ, ℕ) :=
    (chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))).sigma fun t =>
      (chenAdditivePrimeCarrier N).filter (fun r => t.2 ≤ r)
  have hcard : ((currentChenUpsilon7SemiprimeQuadruples N).filter (fun x =>
      (N : ℝ) ^ (1 / 5 : ℝ) <
        ((N - x.1.1 * x.1.2 * (x.2.1 * x.2.2) : ℕ) : ℝ))).card =
      (T.sigma (currentChenUpsilon7LargePrimeSemiprimeAPSource N)).card := by
    refine Finset.card_bij'
      (fun x _ => ⟨⟨x.1, x.2.1⟩, N - x.1.1 * x.1.2 * (x.2.1 * x.2.2)⟩)
      (fun y _ => ⟨y.1.1, (y.1.2, (N - y.2) /
        (y.1.1.1 * y.1.1.2 * y.1.2))⟩) ?_ ?_ ?_ ?_
    · rintro ⟨⟨p₁, p₂⟩, ⟨r, s⟩⟩ hx
      obtain ⟨hx, hlarge⟩ := Finset.mem_filter.mp hx
      obtain ⟨ht, hr, hP⟩ := seventh_switch_forward hx hlarge
      exact Finset.mem_sigma.mpr ⟨Finset.mem_sigma.mpr ⟨ht, hr⟩, hP⟩
    · rintro ⟨⟨t, r⟩, P⟩ hy
      obtain ⟨htr, hP⟩ := Finset.mem_sigma.mp hy
      obtain ⟨ht, hr⟩ := Finset.mem_sigma.mp htr
      obtain ⟨hx, heq, hlarge⟩ := seventh_switch_backward ht hr hP
      exact Finset.mem_filter.mpr ⟨hx, by simpa only [heq] using hlarge⟩
    · rintro ⟨⟨p₁, p₂⟩, ⟨r, s⟩⟩ hx
      obtain ⟨hx, _⟩ := Finset.mem_filter.mp hx
      obtain ⟨h₁, h₂, _hD, _ho, _hc, hr, _hs, _hcut, _hrs, hlt, _hP⟩ :=
        mem_currentChenUpsilon7SemiprimeQuadruples_iff.mp hx
      have ha : 0 < p₁ * p₂ * r := mul_pos
        (mul_pos (mem_chenAdditivePrimeCarrier.mp h₁).2.1.pos
          (mem_chenAdditivePrimeCarrier.mp h₂).2.1.pos) hr.pos
      have heq : (N - (N - p₁ * p₂ * (r * s))) / (p₁ * p₂ * r) = s := by
        rw [Nat.sub_sub_self hlt.le]
        simpa only [← Nat.mul_assoc] using Nat.mul_div_cancel_left s ha
      simp only [heq]
    · rintro ⟨⟨t, r⟩, P⟩ hy
      obtain ⟨htr, hP⟩ := Finset.mem_sigma.mp hy
      obtain ⟨ht, hr⟩ := Finset.mem_sigma.mp htr
      have heq := (seventh_switch_backward ht hr hP).2.1
      simp only [heq]
  have hreal := congrArg (fun n : ℕ => (n : ℝ)) hcard
  simpa only [T, Finset.card_sigma, Nat.cast_sum, Finset.sum_sigma,
    currentChenUpsilon7LargePrimeSemiprimeAPSum] using hreal

/-- The accepted error budget leaves exactly the two large-original-prime
counts, with the original coefficient two.  The switched AP sum still
requires a genuine analytic upper mean. -/
theorem eventually_two_currentChenUpsilon7_le_largePrime_counts
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      2 * currentChenUpsilon7 N ≤
        2 * ((((currentChenUpsilon7PrimeTriples N).filter (fun x =>
          (N : ℝ) ^ (1 / 5 : ℝ) <
            ((N - x.1.1 * x.1.2 * x.2 : ℕ) : ℝ))).card : ℝ) +
          currentChenUpsilon7LargePrimeSemiprimeAPSum N) +
          epsilon * singularNormalization N := by
  filter_upwards [eventually_currentChenUpsilon7_unit_smallGoldbach_error_le
    epsilon hepsilon] with N herr
  have hp := Finset.card_filter_add_card_filter_not
    (s := currentChenUpsilon7PrimeTriples N) (fun x =>
      ((N - x.1.1 * x.1.2 * x.2 : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ))
  have hs := Finset.card_filter_add_card_filter_not
    (s := currentChenUpsilon7SemiprimeQuadruples N) (fun x =>
      ((N - x.1.1 * x.1.2 * (x.2.1 * x.2.2) : ℕ) : ℝ) ≤
        (N : ℝ) ^ (1 / 5 : ℝ))
  have hpR := congrArg (fun n : ℕ => (n : ℝ)) hp
  have hsR := congrArg (fun n : ℕ => (n : ℝ)) hs
  simp only [not_le, Nat.cast_add] at hpR hsR
  rw [currentChenUpsilon7_largePrime_semiprime_card_eq_APSum] at hsR
  rw [currentChenUpsilon7_eq_primeTriples_add_semiprimeQuadruples_add_unitFibres]
  linarith only [hpR, hsR, herr]

end

end ImbalancedChen
