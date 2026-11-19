import ImbalancedChen.P3ActualU6LowerGlobalMask
import ImbalancedChen.ChenInitialPrimeSource
import Mathlib.Tactic

/-!
P3.6: exact re-centring of the ACTUAL original U6 even-exit LOWER
source on the admissible additive-prime carrier.

Frozen paper: UyNewNas/chen-imbalanced-semiprimes@
9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
§1 (PP) and §4 (F); manuscript-body.tex, equation current-PP.

This is an exact finite count/mean identity, NOT a distribution bound.
The actual source A_N excludes primes dividing N. Its progression count
is inclusive prime AP count MINUS the centre-prime AP correction.
Its coprime source mass, however, is |A_N| minus the modulus-prime
divisor count. Thus the latter correction DOES NOT vanish even when
gcd(N, b*q)=1. In particular do not confuse target-coprimality with
primitive-source membership. The earlier original U6 three-block theorem
pays gcd(N,b*q)=1 for every original lower source pair.

All original physical moduli b*q, actual even LOWER integer rho, exact
pair labels, signs and sums are retained. There is no replacement of the
signed prime-product discrepancy by a fibrewise relative assertion.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualU6LowerActualPrimeCarrier

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualEvenLowerIntegerRho
open ImbalancedChen.P3ActualU6LowerGlobalMask

/-- Exact count-versus-primitive-mean dictionary for the ACTUAL
admissible additive prime source, with its indispensable modulus-prime
correction. This is an identity for each physical modulus d coprime to N.
No parity hypothesis on N and no analytic estimate is needed. -/
theorem actual_additive_source_AP_primitive_recenter
    (N d : ℕ) (hdN : Nat.Coprime d N) :
    chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d =
      ((chenAdditivePrimeCarrier N).card : ℝ) / (Nat.totient d : ℝ) +
        finitePrimitiveDiscrepancy
          (chenAdditivePrimeCarrier N) (fun _ => 1) N d -
        chenPrimeDivisorCount N d / (Nat.totient d : ℝ) := by
  have hAP :
      finiteCongruenceMass (chenAdditivePrimeCarrier N) (fun _ => 1) N d =
        chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d := by
    simpa [finiteCongruenceMass] using chenAdditivePrimeCarrier_AP_count N N d
  have hmass := chenAdditivePrimeCarrier_coprime_mass hdN
  unfold finitePrimitiveDiscrepancy
  rw [hAP, hmass]
  ring

/-- Exact signed finite PP arithmetic ledger for ANY integer coefficients,
provided the original physical modulus b*q is coprime to N. It pays
the centre-prime AP exclusion, but explicitly retains the different
modulus-prime correction; no discrepancy saving is inferred. -/
theorem signed_actual_additive_source_recenter
    (N b : ℕ) (Q : Finset ℕ) (rho : ℕ → ℤ)
    (hN : ∀ q ∈ Q, Nat.Coprime (b * q) N) :
    (∑ q ∈ Q, (rho q : ℝ) *
      (chenPrimeAPCount N N (b * q) -
       chenCentrePrimeAPCount N N (b * q))) =
      ((chenAdditivePrimeCarrier N).card : ℝ) *
        (∑ q ∈ Q, (rho q : ℝ) / (Nat.totient (b * q) : ℝ)) +
      (∑ q ∈ Q, (rho q : ℝ) *
        finitePrimitiveDiscrepancy
          (chenAdditivePrimeCarrier N) (fun _ => 1) N (b * q)) -
      (∑ q ∈ Q, (rho q : ℝ) *
        (chenPrimeDivisorCount N (b * q) /
         (Nat.totient (b * q) : ℝ))) := by
  calc
    _ =
      ∑ q ∈ Q,
        ((chenAdditivePrimeCarrier N).card : ℝ) *
          ((rho q : ℝ) / (Nat.totient (b * q) : ℝ)) +
        (rho q : ℝ) *
          finitePrimitiveDiscrepancy
            (chenAdditivePrimeCarrier N) (fun _ => 1) N (b * q) -
        (rho q : ℝ) *
          (chenPrimeDivisorCount N (b * q) /
            (Nat.totient (b * q) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [actual_additive_source_AP_primitive_recenter N (b * q) (hN q hq)]
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum]

/-- Actual U6 original-labelled signed lower sum: the genuine
even-first-exit coefficient and its pair multiplicities are put in
the *same* count and exact primitive mean, now centered on the admissible
prime carrier rather than the overinclusive prime prefix.
The full modulus is (t.1*t.2)*(s*r), never the quotient s*r alone. -/
theorem original_U6_lower_labelled_additive_source_recenter
    (N : ℕ) (t : ℕ × ℕ) (ht : t ∈ sixthSupport N)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ)
    (hwz : w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    let z := P5CausalRhoQuotientBridge.cutoff N
    let cap := Nat.ceil z
    let b := t.1 * t.2
    let Q := actualLowerSmallRoughModuli (policy t) N cap (w t) z
    let rho := actualEvenLowerIntegerRho (policy t) N cap (w t) z (L t)
    (∑ x ∈ P5CausalRhoFactorization.pairs (policy t) N cap (w t) z,
      (actualEvenLowerPairInt (policy t) N cap (w t) z (L t) x : ℝ) *
        (chenPrimeAPCount N N ((b * x.1) * x.2) -
         chenCentrePrimeAPCount N N ((b * x.1) * x.2))) =
      ((chenAdditivePrimeCarrier N).card : ℝ) *
        (∑ q ∈ Q, (rho q : ℝ) / (Nat.totient (b * q) : ℝ)) +
      (∑ q ∈ Q, (rho q : ℝ) *
        finitePrimitiveDiscrepancy
          (chenAdditivePrimeCarrier N) (fun _ => 1) N (b * q)) -
      (∑ q ∈ Q, (rho q : ℝ) *
        (chenPrimeDivisorCount N (b * q) /
         (Nat.totient (b * q) : ℝ))) := by
  dsimp
  rw [← actualEvenLowerIntegerRho_prefix_fubini
    (policy t) N (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
    (t.1 * t.2) (w t) (P5CausalRhoQuotientBridge.cutoff N) (L t)
    (fun d => chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d)]
  apply signed_actual_additive_source_recenter
  intro q hq
  exact (actual_u6_lower_full_modulus_global_mask
    N t ht policy w hwz hq).2

end
end ImbalancedChen.P3ActualU6LowerActualPrimeCarrier
