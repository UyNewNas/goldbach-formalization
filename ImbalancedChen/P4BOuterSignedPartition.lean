import ImbalancedChen.ActualUpperCountingInputs

/-!
# P4B exact signed atom partition of an outer source

SOURCE-ONLY / YELLOW / UNCOMPILED, 2026-10-24.

Each atom retains one complete signed physical modulus sum with the same
rho. The sole triangle inequality is over the finite atom family, after
the exact source-linearity and double-sum exchange. In particular, the
analytic supplier below controls signed atom errors; it does not control
an absolute sum over physical moduli. This bridges the literal primitive
input of P4BActualOuterUpperAssembly without asserting any P3 supplier.
-/

namespace ImbalancedChen.P4B

noncomputable section

open scoped BigOperators
open Filter Topology

/-- Exact finite Fubini after the existing primitive-discrepancy linearity.
The coefficient stays signed and is the same function in every atom. -/
theorem outer_primitive_signed_sum_atoms {ι : Type*}
    (I : Finset ι) (S Q : Finset ℕ) (W : ι → ℕ → ℝ)
    (N : ℕ) (rho : ℕ → ℝ) :
    (∑ d ∈ Q, rho d *
      finitePrimitiveDiscrepancy S (fun m => ∑ i ∈ I, W i m) N d) =
        ∑ i ∈ I, ∑ d ∈ Q,
          rho d * finitePrimitiveDiscrepancy S (W i) N d := by
  classical
  simp_rw [finitePrimitiveDiscrepancy_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Equality of weights only on the common carrier suffices. Atoms may
overlap, take either sign, and have arbitrary finite cardinality. -/
theorem outer_primitive_signed_partition {ι : Type*}
    (I : Finset ι) (S Q : Finset ℕ) (weight : ℕ → ℝ)
    (W : ι → ℕ → ℝ) (N : ℕ) (rho : ℕ → ℝ)
    (hpartition : ∀ m ∈ S, weight m = ∑ i ∈ I, W i m) :
    (∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy S weight N d) =
      ∑ i ∈ I, ∑ d ∈ Q,
        rho d * finitePrimitiveDiscrepancy S (W i) N d := by
  classical
  calc
    _ = ∑ d ∈ Q, rho d *
        finitePrimitiveDiscrepancy S (fun m => ∑ i ∈ I, W i m) N d := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [finitePrimitiveDiscrepancy_congr S weight
        (fun m => ∑ i ∈ I, W i m) N d hpartition]
    _ = _ := outer_primitive_signed_sum_atoms I S Q W N rho

/-- The triangle inequality is over whole signed atoms. There is no
absolute value of rho and no absolute-modulus progression supplier. -/
theorem abs_outer_primitive_signed_partition_le {ι : Type*}
    (I : Finset ι) (S Q : Finset ℕ) (weight : ℕ → ℝ)
    (W : ι → ℕ → ℝ) (N : ℕ) (rho : ℕ → ℝ)
    (hpartition : ∀ m ∈ S, weight m = ∑ i ∈ I, W i m) :
    |∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy S weight N d| ≤
      ∑ i ∈ I, |∑ d ∈ Q,
        rho d * finitePrimitiveDiscrepancy S (W i) N d| := by
  classical
  rw [outer_primitive_signed_partition I S Q weight W N rho hpartition]
  exact Finset.abs_sum_le_sum_abs _ _

/-- A signed P3 estimate for each complete atom pays the outer primitive
error by the sum of its atom budgets. All modulus cancellation is retained. -/
theorem outer_primitive_signed_partition_paid {ι : Type*}
    (I : Finset ι) (S Q : Finset ℕ) (weight : ℕ → ℝ)
    (W : ι → ℕ → ℝ) (N : ℕ) (rho : ℕ → ℝ)
    (budget : ι → ℝ) (E : ℝ)
    (hpartition : ∀ m ∈ S, weight m = ∑ i ∈ I, W i m)
    (hatom : ∀ i ∈ I,
      |∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy S (W i) N d| ≤ budget i)
    (hpaid : (∑ i ∈ I, budget i) ≤ E) :
    |∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy S weight N d| ≤ E := by
  exact (abs_outer_primitive_signed_partition_le
    I S Q weight W N rho hpartition).trans
      ((Finset.sum_le_sum hatom).trans hpaid)

/-- Literal attached-upper specialization. The physical modulus carrier,
retention policy, real cutoffs and signed coefficient agree in every atom. -/
theorem actual_attached_outer_primitive_signed_partition_paid {ι : Type*}
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (N : ℕ) (I : Finset ι) (S : Finset ℕ) (weight : ℕ → ℝ)
    (W : ι → ℕ → ℝ) (budget : ι → ℝ) (E : ℝ)
    (hpartition : ∀ m ∈ S, weight m = ∑ i ∈ I, W i m)
    (hatom : ∀ i ∈ I,
      |∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
        attachedUpperCoefficient nu r epsilon retain cap N d *
          finitePrimitiveDiscrepancy S (W i) N d| ≤ budget i)
    (hpaid : (∑ i ∈ I, budget i) ≤ E) :
    |∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
      attachedUpperCoefficient nu r epsilon retain cap N d *
        finitePrimitiveDiscrepancy S weight N d| ≤ E := by
  exact outer_primitive_signed_partition_paid I S
    (attachedUpperModuli nu r epsilon retain cap N) weight W N
    (attachedUpperCoefficient nu r epsilon retain cap N)
    budget E hpartition hatom hpaid

/-- Eventual atom suppliers give exactly the hprimitive input of
P4BActualOuterUpperAssembly. A common eventual threshold covers every atom
at the given delta and target; the finite atom family may depend on both.
Licensing and uniformity of any analytic supplier remain caller obligations. -/
theorem eventually_actual_attached_outer_primitive_signed_partition_paid {ι : Type*}
    (nu r : ℝ) (epsilon : ℝ → ℝ)
    (retain : ℝ → ℕ → List ℕ → Bool) (cap : ℝ → ℕ → ℕ)
    (I : ℝ → ℕ → Finset ι) (S : ℝ → ℕ → Finset ℕ)
    (weight : ℝ → ℕ → ℕ → ℝ) (W : ℝ → ℕ → ι → ℕ → ℝ)
    (budget : ℝ → ℕ → ι → ℝ)
    (hpartition : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      ∀ m ∈ S delta N,
        weight delta N m = ∑ i ∈ I delta N, W delta N i m)
    (hatom : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      ∀ i ∈ I delta N,
        |∑ d ∈ attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N,
          attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N d *
            finitePrimitiveDiscrepancy (S delta N) (W delta N i) N d| ≤
          budget delta N i)
    (hpaid : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      (∑ i ∈ I delta N, budget delta N i) ≤ delta * singularNormalization N) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |∑ d ∈ attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N,
        attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N d *
          finitePrimitiveDiscrepancy (S delta N) (weight delta N) N d| ≤
        delta * singularNormalization N := by
  intro delta hdelta
  filter_upwards [hpartition delta hdelta, hatom delta hdelta, hpaid delta hdelta]
    with N hpartitionN hatomN hpaidN
  intro hEven
  exact actual_attached_outer_primitive_signed_partition_paid
    nu r (epsilon delta) (retain delta) (cap delta) N (I delta N) (S delta N)
    (weight delta N) (W delta N) (budget delta N)
    (delta * singularNormalization N)
    (hpartitionN hEven) (hatomN hEven) (hpaidN hEven)

end

end ImbalancedChen.P4B
