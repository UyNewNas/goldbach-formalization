import ImbalancedChen.P3TaggedPhysicalRhoPushforward
import ImbalancedChen.P3ActualU6SignedLowerCount
import Mathlib.Tactic

/-!
P3.6 manuscript-INTERNAL; pinned manuscript
UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion (PP), (T), (F).

Earlier work had an EXACT signed primitive discrepancy for every ORIGINAL U6
label t and every quotient q, at the full physical modulus (t.1*t.2)*q,
but had not provided one integer function of that physical modulus.

This file makes the actual tagged pushforward explicit. Finite support is
the union of physical images, whereas the INTEGER coefficient is the SUM of
the signed fibre coefficients. Thus distinct tags or pairs colliding on a
physical modulus are not discarded. The output is a U6 LOWER SUBSOURCE,
not the final PP compiler rho_N. Its signed discrepancy is exactly
reindexed, NOT bounded by this identity. In particular no claim that the
complete PP discrepancy is polylogarithmically small follows.

No new axioms or external analytic arguments.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualU6PhysicalRhoPushforward

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualEvenLowerIntegerRho
open ImbalancedChen.P3ActualU6AllRowsPrimitiveLedger

/-- Literal q carrier of the SAME original even first-exit LOWER rows. -/
private def actualU6Q (N : ℕ)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w : (ℕ × ℕ) → ℝ) (t : ℕ × ℕ) : Finset ℕ :=
  actualLowerSmallRoughModuli (policy t) N
    (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
    (w t) (P5CausalRhoQuotientBridge.cutoff N)

/-- Real physical support of the original labelled LOWER U6 subsource,
NOT an artificial independent full-PP support bound. -/
def actualU6PhysicalModuli (N : ℕ)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w : (ℕ × ℕ) → ℝ) : Finset ℕ :=
  taggedPhysicalModuli (sixthSupport N) (actualU6Q N policy w)
    (fun t q => (t.1 * t.2) * q)

/-- ONE INTEGER physical coefficient for the original U6 LOWER subsource.
The signed sum retains every t label, every allowed quotient q and the
original even-exit Rosser coefficient, including possible collisions. -/
def actualU6PhysicalIntegerRho (N : ℕ)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ) (d : ℕ) : ℤ :=
  taggedPhysicalIntegerRho
    (sixthSupport N) (actualU6Q N policy w)
    (fun t q => (t.1 * t.2) * q)
    (fun t q => actualEvenLowerIntegerRho (policy t) N
      (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
      (w t) (P5CausalRhoQuotientBridge.cutoff N) (L t) q) d

theorem actual_U6_physical_rho_zero_off_support
    (N : ℕ) (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ) (d : ℕ)
    (hd : d ∉ actualU6PhysicalModuli N policy w) :
    actualU6PhysicalIntegerRho N policy w L d = 0 := by
  exact tagged_physical_integer_rho_zero_off_support
    (sixthSupport N) (actualU6Q N policy w)
    (fun t q => (t.1 * t.2) * q)
    (fun t q => actualEvenLowerIntegerRho (policy t) N
      (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
      (w t) (P5CausalRhoQuotientBridge.cutoff N) (L t) q)
    d hd

/-- Exact same-INTEGER-rho rewrite of the UNPAID signed primitive
discrepancy for ALL original U6 labels, on complete physical moduli.
This is a true algebraic coupling step, not an analytic PP estimate;
the coefficient is a U6 LOWER component, not the final compiler rho_N. -/
theorem actual_U6_signed_discrepancy_same_physical_integer_rho
    (N : ℕ) (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ) :
    (∑ d ∈ actualU6PhysicalModuli N policy w,
      (actualU6PhysicalIntegerRho N policy w L d : ℝ) *
        finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N)
          (fun _ => 1) N d) =
      ∑ t ∈ sixthSupport N, rowPrimitiveDiscrepancy N policy w L t := by
  simpa [actualU6PhysicalModuli, actualU6PhysicalIntegerRho,
    actualU6Q, rowPrimitiveDiscrepancy] using
    (tagged_physical_pushforward_identity
      (sixthSupport N) (actualU6Q N policy w)
      (fun t q => (t.1 * t.2) * q)
      (fun t q => actualEvenLowerIntegerRho (policy t) N
        (Nat.ceil (P5CausalRhoQuotientBridge.cutoff N))
        (w t) (P5CausalRhoQuotientBridge.cutoff N) (L t) q)
      (fun d => finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N)
        (fun _ => 1) N d))


/-- The real U6 count has a genuine lower inequality against ONE
integer physical-rho signed discrepancy. Only the quotient-prime correction
is separated; the displayed offshift discrepancy is NOT estimated.
No claim relates this partial rho to the entire PP compiler. -/
theorem actual_U6_count_lower_one_integer_physical_discrepancy
    (N : ℕ) (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ)
    (hgates : ∀ t ∈ sixthSupport N,
      1 < L t ∧ w t ≤ L t ∧
        w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    (∑ t ∈ sixthSupport N, rowPrimitiveMean N policy w L t) +
      (∑ d ∈ actualU6PhysicalModuli N policy w,
        (actualU6PhysicalIntegerRho N policy w L d : ℝ) *
          finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N)
            (fun _ => 1) N d) -
      (∑ t ∈ sixthSupport N,
        rowQuotientPrimeCorrection N policy w L t) ≤
      ∑ t ∈ sixthSupport N, sixthWeight N t := by
  have hwz : ∀ t ∈ sixthSupport N,
      w t ≤ P5CausalRhoQuotientBridge.cutoff N := by
    intro t ht
    exact (hgates t ht).2.2
  have hledger :=
    all_original_U6_lower_labelled_recenter N policy w L hwz
  have hcount :=
    ImbalancedChen.P3ActualU6SignedLowerCount.literal_integer_labelledAP_le_actual_U6_count
      N policy w L hgates
  rw [hledger] at hcount
  rw [← actual_U6_signed_discrepancy_same_physical_integer_rho
    N policy w L] at hcount
  exact hcount

end
end ImbalancedChen.P3ActualU6PhysicalRhoPushforward
