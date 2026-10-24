import ImbalancedChen.P4BLogSavingBudget
import ImbalancedChen.P4BOuterSignedPartition

/-!
# Polylogarithmically many complete signed atoms pay the actual primitive error

SOURCE ONLY / YELLOW / UNCOMPILED (2026-10-24).

The imports are future normal module imports for source-only companions.
The atom estimate is uniform after one supplied natural P3 threshold,
before the target-dependent atom is selected. Each absolute value encloses
the whole signed physical modulus sum with the same rho. Only the outer
atom sum uses the triangle inequality. No P3 atom estimate is proved here.

At each fixed precision, C, D, k, A and the P3 threshold are fixed before
N grows. A logarithmic atom count D*(log N)^k is paid when A >= k+3.
The final theorem returns the exact attached-coefficient hprimitive input
of P4BActualOuterUpperAssembly, without asking for that input as a premise.
-/

namespace ImbalancedChen.P4B

noncomputable section

open scoped BigOperators
open Filter Topology

/-- Finite cardinality accounting after each complete signed atom has
been estimated. No absolute value is introduced inside an atom. -/
theorem polylog_atom_abs_sum_le {ι : Type*}
    (I : Finset ι) (error : ι → ℝ) (N : ℕ) (hN : 2 ≤ N)
    (C D : ℝ) (hC : 0 ≤ C) (k A : ℕ)
    (hatom : ∀ i ∈ I,
      |error i| ≤ C * (N : ℝ) / (Real.log (N : ℝ)) ^ A)
    (hcard : (I.card : ℝ) ≤ D * (Real.log (N : ℝ)) ^ k) :
    (∑ i ∈ I, |error i|) ≤
      (D * C) * (N : ℝ) * (Real.log (N : ℝ)) ^ k /
        (Real.log (N : ℝ)) ^ A := by
  classical
  have hNreal : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) := (Real.log_pos hNreal).le
  have hbudget : 0 ≤ C * (N : ℝ) / (Real.log (N : ℝ)) ^ A :=
    div_nonneg (mul_nonneg hC (Nat.cast_nonneg N)) (pow_nonneg hlog A)
  calc
    (∑ i ∈ I, |error i|) ≤
        ∑ _i ∈ I, C * (N : ℝ) / (Real.log (N : ℝ)) ^ A :=
      Finset.sum_le_sum hatom
    _ = (I.card : ℝ) *
        (C * (N : ℝ) / (Real.log (N : ℝ)) ^ A) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (D * (Real.log (N : ℝ)) ^ k) *
        (C * (N : ℝ) / (Real.log (N : ℝ)) ^ A) :=
      mul_le_mul_of_nonneg_right hcard hbudget
    _ = (D * C) * (N : ℝ) * (Real.log (N : ℝ)) ^ k /
        (Real.log (N : ℝ)) ^ A := by ring

/-- One threshold includes the uniform P3 threshold, the atom-count
estimate, the carrierwise partition, the normalization payment and N >= 2.
The atom family, carrier, weights, physical moduli and signed coefficient
may depend on N. The constants and exponents are fixed beforehand. -/
theorem exists_polylog_signed_partition_payment_threshold {ι : Type*}
    (I : ℕ → Finset ι) (S Q : ℕ → Finset ℕ)
    (weight : ℕ → ℕ → ℝ) (W : ℕ → ι → ℕ → ℝ)
    (rho : ℕ → ℕ → ℝ)
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (k A NP3 : ℕ) (hA : k + 3 ≤ A)
    (hatom : ∀ N : ℕ, NP3 ≤ N → Even N → ∀ i ∈ I N,
      |∑ d ∈ Q N, rho N d *
        finitePrimitiveDiscrepancy (S N) (W N i) N d| ≤
          C * (N : ℝ) / (Real.log (N : ℝ)) ^ A)
    (hcard : ∀ᶠ N : ℕ in atTop, Even N →
      ((I N).card : ℝ) ≤ D * (Real.log (N : ℝ)) ^ k)
    (hpartition : ∀ᶠ N : ℕ in atTop, Even N →
      ∀ m ∈ S N, weight N m = ∑ i ∈ I N, W N i m)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ NP3 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      (∑ i ∈ I N, |∑ d ∈ Q N, rho N d *
        finitePrimitiveDiscrepancy (S N) (W N i) N d|) ≤
          eta * singularNormalization N ∧
      |∑ d ∈ Q N, rho N d *
        finitePrimitiveDiscrepancy (S N) (weight N) N d| ≤
          eta * singularNormalization N := by
  classical
  have hlogPaid := eventually_logPower_atoms_le_singularNormalization
    (D * C) (mul_nonneg hD hC) k A hA eta heta
  have hpaid : ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧ NP3 ≤ N ∧ (Even N →
        (∑ i ∈ I N, |∑ d ∈ Q N, rho N d *
          finitePrimitiveDiscrepancy (S N) (W N i) N d|) ≤
            eta * singularNormalization N ∧
        |∑ d ∈ Q N, rho N d *
          finitePrimitiveDiscrepancy (S N) (weight N) N d| ≤
            eta * singularNormalization N) := by
    filter_upwards [hlogPaid, hcard, hpartition, eventually_ge_atTop NP3]
      with N hlogN hcardN hpartitionN hNP3
    refine ⟨hlogN.1, hNP3, ?_⟩
    intro hEven
    have hsum :
        (∑ i ∈ I N, |∑ d ∈ Q N, rho N d *
          finitePrimitiveDiscrepancy (S N) (W N i) N d|) ≤
            eta * singularNormalization N :=
      (polylog_atom_abs_sum_le (I N)
        (fun i => ∑ d ∈ Q N, rho N d *
          finitePrimitiveDiscrepancy (S N) (W N i) N d)
        N hlogN.1 C D hC k A (hatom N hNP3 hEven) (hcardN hEven)).trans hlogN.2
    exact ⟨hsum,
      (abs_outer_primitive_signed_partition_le
        (I N) (S N) (Q N) (weight N) (W N) N (rho N)
        (hpartitionN hEven)).trans hsum⟩
  obtain ⟨M, hM⟩ := eventually_atTop.mp hpaid
  have h0 := hM (max M 2) (le_max_left _ _)
  refine ⟨max M 2, h0.1, h0.2.1, ?_⟩
  intro N hN hEven
  exact (hM N (le_trans (le_max_left _ _) hN)).2.2 hEven

/-- Exact hprimitive supplier for the literal attached upper coefficient.
The same Q and rho occur in every whole atom and in the full primitive
error. At fixed delta, the P3 threshold precedes both N and i membership;
there is no inference from separate nonuniform eventual estimates per i. -/
theorem eventually_actual_attached_outer_primitive_of_polylog_atoms {ι : Type*}
    (nu r : ℝ) (epsilon : ℝ → ℝ)
    (retain : ℝ → ℕ → List ℕ → Bool) (cap : ℝ → ℕ → ℕ)
    (I : ℝ → ℕ → Finset ι) (S : ℝ → ℕ → Finset ℕ)
    (weight : ℝ → ℕ → ℕ → ℝ) (W : ℝ → ℕ → ι → ℕ → ℝ)
    (C D : ℝ → ℝ) (k A NP3 : ℝ → ℕ)
    (hconstants : ∀ delta : ℝ, 0 < delta →
      0 ≤ C delta ∧ 0 ≤ D delta ∧ k delta + 3 ≤ A delta)
    (hatom : ∀ delta : ℝ, 0 < delta →
      ∀ N : ℕ, NP3 delta ≤ N → Even N → ∀ i ∈ I delta N,
        |∑ d ∈ attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N,
          attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N d *
            finitePrimitiveDiscrepancy (S delta N) (W delta N i) N d| ≤
          C delta * (N : ℝ) / (Real.log (N : ℝ)) ^ (A delta))
    (hcard : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      ((I delta N).card : ℝ) ≤ D delta * (Real.log (N : ℝ)) ^ (k delta))
    (hpartition : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      ∀ m ∈ S delta N,
        weight delta N m = ∑ i ∈ I delta N, W delta N i m) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |∑ d ∈ attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N,
        attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N d *
          finitePrimitiveDiscrepancy (S delta N) (weight delta N) N d| ≤
        delta * singularNormalization N := by
  intro delta hdelta
  obtain ⟨hC, hD, hA⟩ := hconstants delta hdelta
  obtain ⟨N0, _hN02, _hNP3, hpaid⟩ :=
    exists_polylog_signed_partition_payment_threshold
      (I delta) (S delta)
      (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta))
      (weight delta) (W delta)
      (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta))
      (C delta) (D delta) hC hD (k delta) (A delta) (NP3 delta) hA
      (hatom delta hdelta) (hcard delta hdelta) (hpartition delta hdelta) delta hdelta
  filter_upwards [eventually_ge_atTop N0] with N hN
  intro hEven
  exact (hpaid N hN hEven).2

end

end ImbalancedChen.P4B
