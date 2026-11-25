import ImbalancedChen.P2FiniteMarkedGamma5EulerWordBudget
import Mathlib.Algebra.Order.Floor.Semiring

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

Finite natural-number support of the existing Gamma5 physical profile,
in the original Family interface's Fin coordinates. The same coordinate
permutation and the same physical profile are used without modification.

Nonzero weight makes every natural coordinate positive. Each coordinate
therefore divides a positive complete product and is at most that product.
The accepted complete-product gate puts every coordinate in one finite
integer box. No primality condition is needed for this argument; the
prime support required by Family.finitePrimeSupport is a subset.

Repeated coordinate values and empty old or tail blocks are retained.
Zero coordinates vanish by the original positive floor, while coordinates
equal to one are not removed by a new arithmetic filter. This file neither
admits an actual marked Family nor pays its collar or PP distribution.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5IntegerSupport

noncomputable section
open Finset Real Set
open P2FiniteMarkedGamma5PhysicalExtension
open P2FiniteMarkedGamma5EulerWordBudget
open scoped Classical BigOperators

/-- The accepted slot permutation preserves the complete product,
including every repeated old, fresh and tail coordinate. -/
theorem physicalProduct_finToPhysical {k r : ℕ}
    (v : Fin (k + (2 + r)) → ℝ) :
    physicalProduct (finToPhysical k r v) = ∏ i, v i := by
  change (∏ i : Slot k r, v (slotEquiv k r i)) = ∏ i, v i
  exact (slotEquiv k r).prod_comp v

/-- The original real support bounds in exactly the coordinates used by
Family. These are consequences of the profile, not new support inputs. -/
theorem finPhysicalProfile_nonzero_support {k r : ℕ} {logQ N width b : ℝ}
    {v : Fin (k + (2 + r)) → ℝ} (hb : 0 < b) (hN : 0 < N)
    (hw : 0 < width) (hne : finPhysicalProfile logQ N width b v ≠ 0) :
    (∀ i, b / 2 < v i) ∧ (∏ i, v i) < exp width * N := by
  refine ⟨?_, ?_⟩
  · intro i
    have h := physicalProfile_nonzero_lower hb hne ((slotEquiv k r).symm i)
    simpa only [finToPhysical_apply, Equiv.apply_symm_apply] using h
  · have h := physicalProfile_nonzero_product_lt hb hN hw hne
    simpa only [physicalProduct_finToPhysical] using h

/-- Natural coordinates on nonzero support are positive, without any
prime assumption and without a lower bound such as b >= 2. -/
theorem finPhysicalProfile_integer_pos {k r : ℕ} {logQ N width b : ℝ}
    {u : Fin (k + (2 + r)) → ℕ} (hb : 0 < b)
    (hne : finPhysicalProfile logQ N width b (fun i => (u i : ℝ)) ≠ 0)
    (i : Fin (k + (2 + r))) : 0 < u i := by
  have h := physicalProfile_nonzero_lower hb hne ((slotEquiv k r).symm i)
  have hslot : b / 2 < (u i : ℝ) := by
    simpa only [finToPhysical_apply, Equiv.apply_symm_apply] using h
  exact Nat.cast_pos.mp ((half_pos hb).trans hslot)

/-- The complete natural product has the same cap as the original
physical product. No collapsed product image replaces the labelled tuple. -/
theorem finPhysicalProfile_integer_product_lt {k r : ℕ} {logQ N width b : ℝ}
    {u : Fin (k + (2 + r)) → ℕ} (hb : 0 < b) (hN : 0 < N)
    (hw : 0 < width)
    (hne : finPhysicalProfile logQ N width b (fun i => (u i : ℝ)) ≠ 0) :
    ((∏ i, u i : ℕ) : ℝ) < exp width * N := by
  simpa only [Nat.cast_prod] using
    (finPhysicalProfile_nonzero_support hb hN hw hne).2

/-- One finite integer box contains the entire natural support. Its
upper endpoint is independent of logQ, b and the number of slots. -/
theorem finPhysicalProfile_integer_box {k r : ℕ} {logQ N width b : ℝ}
    {u : Fin (k + (2 + r)) → ℕ} (hb : 0 < b) (hN : 0 < N)
    (hw : 0 < width)
    (hne : finPhysicalProfile logQ N width b (fun i => (u i : ℝ)) ≠ 0) :
    ∀ i, 1 ≤ u i ∧ u i ≤ ⌊exp width * N⌋₊ := by
  have hu : ∀ i, 0 < u i := finPhysicalProfile_integer_pos hb hne
  have hp : 0 < ∏ i, u i := prod_pos (fun i _ => hu i)
  have hcap : (∏ i, u i) ≤ ⌊exp width * N⌋₊ :=
    Nat.le_floor (finPhysicalProfile_integer_product_lt hb hN hw hne).le
  intro i
  exact ⟨hu i, (Nat.le_of_dvd hp (dvd_prod_of_mem u (mem_univ i))).trans hcap⟩

/-- Finite support on all natural-number tuples, including composite
coordinates. The full tuple remains the index, so multiplicity is intact. -/
theorem finite_integer_support (k r : ℕ) (logQ : ℝ) {N width b : ℝ}
    (hb : 0 < b) (hN : 0 < N) (hw : 0 < width) :
    Set.Finite {u : Fin (k + (2 + r)) → ℕ |
      finPhysicalProfile logQ N width b (fun i => (u i : ℝ)) ≠ 0} := by
  have hbox : Set.Finite ((Set.univ : Set (Fin (k + (2 + r)))).pi
      (fun _ => Set.Iic ⌊exp width * N⌋₊)) :=
    Set.Finite.pi (fun _ => Set.finite_Iic _)
  apply hbox.subset
  intro u hu i _
  exact (finPhysicalProfile_integer_box hb hN hw hu i).2

/-- The prime-support condition of the existing Family interface follows
from the stronger integer-support theorem, using the identical weight. -/
theorem finite_prime_support (k r : ℕ) (logQ : ℝ) {N width b : ℝ}
    (hb : 0 < b) (hN : 0 < N) (hw : 0 < width) :
    Set.Finite {u : Fin (k + (2 + r)) → ℕ |
      (∀ i, (u i).Prime) ∧
        finPhysicalProfile logQ N width b (fun i => (u i : ℝ)) ≠ 0} :=
  (finite_integer_support k r logQ hb hN hw).subset (fun _ hu => hu.2)

end
end ImbalancedChen.P2FiniteMarkedGamma5IntegerSupport
