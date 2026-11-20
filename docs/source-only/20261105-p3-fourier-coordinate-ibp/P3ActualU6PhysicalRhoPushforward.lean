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

/-- Physical union, used only as the indexing carrier. Union is safe here
because actual integer coefficients below ADD over all labelled fibres. -/
def taggedPhysicalModuli
    (T : Finset (ℕ × ℕ)) (Q : (ℕ × ℕ) → Finset ℕ)
    (modulus : (ℕ × ℕ) → ℕ → ℕ) : Finset ℕ :=
  T.biUnion (fun t => (Q t).image (modulus t))

/-- Signed integer pushforward, retaining all occurrences when distinct
original labels/quotients produce the same physical modulus. -/
def taggedPhysicalIntegerRho
    (T : Finset (ℕ × ℕ)) (Q : (ℕ × ℕ) → Finset ℕ)
    (modulus : (ℕ × ℕ) → ℕ → ℕ)
    (coeff : (ℕ × ℕ) → ℕ → ℤ) (d : ℕ) : ℤ :=
  ∑ t ∈ T, ∑ q ∈ Q t,
    if modulus t q = d then coeff t q else 0

theorem tagged_physical_mem
    (T : Finset (ℕ × ℕ)) (Q : (ℕ × ℕ) → Finset ℕ)
    (modulus : (ℕ × ℕ) → ℕ → ℕ)
    {t : ℕ × ℕ} (ht : t ∈ T) {q : ℕ} (hq : q ∈ Q t) :
    modulus t q ∈ taggedPhysicalModuli T Q modulus := by
  classical
  exact Finset.mem_biUnion.mpr
    ⟨t, ht, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩

/-- There are no coefficient atoms outside the genuinely generated
physical moduli. This does not assert that all supported atoms are nonzero:
different original labelled occurrences may cancel. -/
theorem tagged_physical_integer_rho_zero_off_support
    (T : Finset (ℕ × ℕ)) (Q : (ℕ × ℕ) → Finset ℕ)
    (modulus : (ℕ × ℕ) → ℕ → ℕ)
    (coeff : (ℕ × ℕ) → ℕ → ℤ) (d : ℕ)
    (hd : d ∉ taggedPhysicalModuli T Q modulus) :
    taggedPhysicalIntegerRho T Q modulus coeff d = 0 := by
  classical
  unfold taggedPhysicalIntegerRho
  apply Finset.sum_eq_zero
  intro t ht
  apply Finset.sum_eq_zero
  intro q hq
  have hm : modulus t q ∈ taggedPhysicalModuli T Q modulus :=
    tagged_physical_mem T Q modulus ht hq
  have hne : modulus t q ≠ d := by
    intro h
    exact hd (h ▸ hm)
  simp [hne]

/-- Pure finite reindexing: the SINGLE integer coefficient of each
physical d gives exactly the original signed labelled sum, even with
noninjective t,q -> d. No sign or positivity hypothesis on coeff or F. -/
theorem tagged_physical_pushforward_identity
    (T : Finset (ℕ × ℕ)) (Q : (ℕ × ℕ) → Finset ℕ)
    (modulus : (ℕ × ℕ) → ℕ → ℕ)
    (coeff : (ℕ × ℕ) → ℕ → ℤ) (F : ℕ → ℝ) :
    (∑ d ∈ taggedPhysicalModuli T Q modulus,
       (taggedPhysicalIntegerRho T Q modulus coeff d : ℝ) * F d) =
      ∑ t ∈ T, ∑ q ∈ Q t, (coeff t q : ℝ) * F (modulus t q) := by
  classical
  let D := taggedPhysicalModuli T Q modulus
  have hcast (d : ℕ) :
      (taggedPhysicalIntegerRho T Q modulus coeff d : ℝ) =
        ∑ t ∈ T, ∑ q ∈ Q t,
          if modulus t q = d then (coeff t q : ℝ) else 0 := by
    simp [taggedPhysicalIntegerRho]
  have hsingle (t : ℕ × ℕ) (ht : t ∈ T)
      (q : ℕ) (hq : q ∈ Q t) :
      (∑ d ∈ D,
        (if modulus t q = d then (coeff t q : ℝ) else 0) * F d) =
        (coeff t q : ℝ) * F (modulus t q) := by
    have hm : modulus t q ∈ D :=
      tagged_physical_mem T Q modulus ht hq
    have hsum :
        (∑ d ∈ D,
          (if modulus t q = d then (coeff t q : ℝ) else 0) * F d) =
          (if modulus t q = modulus t q then
            (coeff t q : ℝ) else 0) * F (modulus t q) := by
      apply Finset.sum_eq_single (modulus t q)
      · intro d hd hne
        have hneq : modulus t q ≠ d := Ne.symm hne
        simp [hneq]
      · intro hnot
        exact False.elim (hnot hm)
    simpa using hsum
  change (∑ d ∈ D,
    (taggedPhysicalIntegerRho T Q modulus coeff d : ℝ) * F d) = _
  calc
    _ = ∑ d ∈ D, ∑ t ∈ T, ∑ q ∈ Q t,
          (if modulus t q = d then (coeff t q : ℝ) else 0) * F d := by
          simp only [hcast, Finset.sum_mul]
    _ = ∑ t ∈ T, ∑ q ∈ Q t, ∑ d ∈ D,
          (if modulus t q = d then (coeff t q : ℝ) else 0) * F d := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.sum_comm]
    _ = ∑ t ∈ T, ∑ q ∈ Q t, (coeff t q : ℝ) * F (modulus t q) := by
          apply Finset.sum_congr rfl
          intro t ht
          apply Finset.sum_congr rfl
          intro q hq
          exact hsingle t ht q hq

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

end
end ImbalancedChen.P3ActualU6PhysicalRhoPushforward
