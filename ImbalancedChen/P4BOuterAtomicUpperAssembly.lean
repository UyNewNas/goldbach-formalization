import ImbalancedChen.P4BActualOuterUpperAssembly
import ImbalancedChen.P4BOuterSignedPartition

/-!
# P4B actual outer upper count from complete signed atom budgets

SOURCE-ONLY / YELLOW / UNCOMPILED, 2026-10-24.

These are future normal module imports for the two source-only companion
drafts. No module adoption or kernel validation is asserted here.

The outer primitive input is proved from a carrierwise finite atom
decomposition and signed atom budgets, then passed to the positive-outer
upper assembly. Each atom retains its complete physical modulus sum with
the literal attached coefficient. The P3 atom estimates, their total
budget, the outer geometry and surplus, the P4A density estimate and the
outer coprime estimate remain explicit external inputs. In particular,
neither the assembled primitive estimate nor the final upper count is a
hypothesis of this theorem.
-/

namespace ImbalancedChen.P4B

noncomputable section

open scoped BigOperators
open Filter Topology

/-- Conditional actual upper assembly with primitive error discharged
by complete signed atoms. The original signed outer coprime input is
retained; zero-correction suppliers may discharge it separately. -/
theorem eventually_RealB_le_of_actual_outer_atomic_inputs {ι : Type*}
    {b kappa nu r : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hkappa : 0 < kappa)
    (hnu : 0 < nu) (hr : 0 < r) (hsieve : nu * r < 1)
    (epsilon : ℝ → ℝ) (retain : ℝ → ℕ → List ℕ → Bool)
    (cap : ℝ → ℕ → ℕ)
    (S : ℝ → ℕ → Finset ℕ) (weight : ℝ → ℕ → ℕ → ℝ)
    (I : ℝ → ℕ → Finset ι) (W : ℝ → ℕ → ι → ℕ → ℝ)
    (budget : ℝ → ℕ → ι → ℝ)
    (hepsilon : ∀ delta : ℝ, 0 < delta →
      0 < epsilon delta ∧ epsilon delta ≤ 1 ∧ (epsilon delta) ^ 2 ≤ r)
    (hcover : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (nu * r) ≤ (cap delta N : ℝ))
    (hgeometry : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      (∀ m ∈ S delta N, m ≤ N) ∧
      realHalfProductSource b N (manuscriptHalfProductCutoff kappa N) ⊆ S delta N ∧
      (∀ m ∈ S delta N,
        (if m ∈ realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)
          then (1 : ℝ) else 0) ≤ weight delta N m))
    (hsurplus : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      finiteSourceMass (S delta N) (weight delta N) ≤
        ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) +
          delta * ((N : ℝ) / Real.log (N : ℝ)))
    (hdensity : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      physicalDensitySum
        (attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N)
        (attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N) ≤
          (currentK + delta) * (singularSeries N / Real.log (N : ℝ)))
    (hcoprime : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |∑ d ∈ attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N,
        attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N d *
          ((finiteCoprimeMass (S delta N) (weight delta N) d -
              finiteSourceMass (S delta N) (weight delta N)) / (Nat.totient d : ℝ))| ≤
        delta * singularNormalization N)
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
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ N : ℕ in atTop, Even N →
      (RealB b N : ℝ) ≤
        (currentK * Real.log (1 / b) + tolerance) * singularNormalization N := by
  have hprimitive : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N →
      |∑ d ∈ attachedUpperModuli nu r (epsilon delta) (retain delta) (cap delta) N,
        attachedUpperCoefficient nu r (epsilon delta) (retain delta) (cap delta) N d *
          finitePrimitiveDiscrepancy (S delta N) (weight delta N) N d| ≤
        delta * singularNormalization N :=
    eventually_actual_attached_outer_primitive_signed_partition_paid
      nu r epsilon retain cap I S weight W budget hpartition hatom hpaid
  exact eventually_RealB_le_of_actual_outer_primitive_inputs
    hb hb1 hkappa hnu hr hsieve epsilon retain cap S weight
    hepsilon hcover hgeometry hsurplus hdensity hcoprime hprimitive

end

end ImbalancedChen.P4B
