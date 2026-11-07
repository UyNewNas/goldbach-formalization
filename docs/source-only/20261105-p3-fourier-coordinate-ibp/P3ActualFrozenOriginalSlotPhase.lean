import ImbalancedChen.ActualFrozenSelectedPairAssignment
import ImbalancedChen.P3PhysicalOriginalW

/-!
P3.6: the GENUINE selected-pair allocation of ORIGINAL SLOT IDENTITIES
separates each logarithmic Fourier character into three physical modes.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED; manuscript pin
9731290e8f53cffda44129906cde6a965eaa869b, completion §4 (F).

The allocation is exactly actualFrozenSelectedPairAssignment, computed
from original upper endpoints, not the values of the primes. This file
retains original slot identifiers (Fin n), even when several actual prime
values or fine labels coincide. In particular it never transports a
position-sensitive character through a mere label-word permutation.

It establishes the algebraic phase separation for the actual slot words;
it does NOT establish Fourier inversion of W_T, its integrability or a
continuous L1 bound, the actual PP atom dictionary or an arithmetic bound.
The phase here uses the positive 2*pi Fourier-INVERSE sign. Identification
with Mathlib's Fourier inverse character is a separate obligation.
-/

namespace ImbalancedChen.P3ActualFrozenOriginalSlotPhase
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3PhysicalOriginalW

/-- Real log-chart phase attached to an ORIGINAL numbered slot. -/
def originalSlotPhase {n : ℕ} (eta : Fin n → ℝ)
    (z : Point n) (i : Fin n) : ℂ :=
  ((2 * Real.pi * eta i * z i : ℝ) : ℂ) * Complex.I

/-- The single full-original-vector Fourier-inverse character. -/
def originalSlotCharacter {n : ℕ} (eta : Fin n → ℝ)
    (z : Point n) : ℂ :=
  Complex.exp (∑ i : Fin n, originalSlotPhase eta z i)

/-- A character restricted to slots assigned to the j-th genuine
selected-pair group; no individual input value enters the allocation. -/
def originalFrozenGroupCharacter {n : ℕ}
    (group : Fin n → Fin 3) (eta : Fin n → ℝ)
    (z : Point n) (j : Fin 3) : ℂ :=
  Complex.exp (∑ i : Fin n,
    if group i = j then originalSlotPhase eta z i else 0)

/-- The same character expressed directly on a physical list of ORIGINAL
slot identities, not a list of untagged prime values. -/
def physicalWordCharacter {n : ℕ} (word : List (Fin n))
    (eta : Fin n → ℝ) (z : Point n) : ℂ :=
  Complex.exp (∑ i ∈ word.toFinset, originalSlotPhase eta z i)

/-- Elementary finite exponential factorization, including the empty set. -/
theorem exp_sum_eq_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℂ) :
    Complex.exp (∑ i ∈ s, f i) =
      ∏ i ∈ s, Complex.exp (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp [hi, Complex.exp_add, ih]

/-- A literal three-way allocation partitions the full Fourier character.
No hypothesis of phase separation is introduced: it follows from the
unique group index attached to each original slot. -/
theorem original_character_factors {n : ℕ}
    (group : Fin n → Fin 3) (eta : Fin n → ℝ)
    (z : Point n) :
    originalSlotCharacter eta z =
      ∏ j : Fin 3, originalFrozenGroupCharacter group eta z j := by
  classical
  have hg (j : Fin 3) :
      originalFrozenGroupCharacter group eta z j =
        ∏ i : Fin n,
          if group i = j then Complex.exp (originalSlotPhase eta z i) else 1 := by
    unfold originalFrozenGroupCharacter
    rw [exp_sum_eq_prod]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases h : group i = j <;> simp [h]
  unfold originalSlotCharacter
  calc
    Complex.exp (∑ i : Fin n, originalSlotPhase eta z i) =
        ∏ i : Fin n, Complex.exp (originalSlotPhase eta z i) := by
          exact exp_sum_eq_prod Finset.univ _
    _ = ∏ i : Fin n, ∏ j : Fin 3,
          if group i = j then Complex.exp (originalSlotPhase eta z i) else 1 := by
            apply Finset.prod_congr rfl
            intro i hi
            simp
    _ = ∏ j : Fin 3, ∏ i : Fin n,
          if group i = j then Complex.exp (originalSlotPhase eta z i) else 1 :=
            Finset.prod_comm
    _ = ∏ j : Fin 3, originalFrozenGroupCharacter group eta z j := by
          apply Finset.prod_congr rfl
          intro j hj
          exact (hg j).symm

/-- Each group character uses only its OWN original coordinates, even
when physical values coincide. This is the needed positional dependence
statement for the subsequent gamma weights. -/
theorem group_character_congr_on_slots {n : ℕ}
    (group : Fin n → Fin 3) (eta : Fin n → ℝ)
    (z z' : Point n) (j : Fin 3)
    (h : ∀ i, group i = j → z i = z' i) :
    originalFrozenGroupCharacter group eta z j =
      originalFrozenGroupCharacter group eta z' j := by
  unfold originalFrozenGroupCharacter
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hj : group i = j
  · simp [hj, originalSlotPhase, h i hj]
  · simp [hj]

/-- Instantiate the partition with the ACTUAL endpoint-frozen policy.
The slot group is derived by the fixed library, not supplied as an
abstract three-way partition or chosen after seeing a prime tuple. -/
theorem actual_frozen_original_slot_phase_factors {n : ℕ}
    (D A : ℝ) (yz : Bool) (upper : Fin n → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (eta : Fin n → ℝ) (z : Point n) :
    originalSlotCharacter eta z =
      ∏ j : Fin 3,
        originalFrozenGroupCharacter
          (actualFrozenSelectedPairAssignment D A yz upper p tail) eta z j := by
  exact original_character_factors
    (actualFrozenSelectedPairAssignment D A yz upper p tail) eta z

/-- The exact physical frozen group-word character agrees with the
character selected by its ORIGINAL slot-identity assignment. Distinctness
and coverage concern slot IDs, not their prime values or fine labels. -/
theorem actual_frozen_original_phase_from_words {n : ℕ}
    (D A : ℝ) (yz : Bool) (upper : Fin n → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (hnodup : (p 0 :: p 1 :: p 2 :: tail).Nodup)
    (hcover : ∀ i, i ∈ p 0 :: p 1 :: p 2 :: tail)
    (eta : Fin n → ℝ) (z : Point n) :
    let slots := actualFrozenSelectedPairSlots D A yz upper p tail
    originalSlotCharacter eta z =
      physicalWordCharacter slots.1 eta z *
        (physicalWordCharacter slots.2.1 eta z *
          physicalWordCharacter slots.2.2 eta z) := by
  dsimp only
  let slots := actualFrozenSelectedPairSlots D A yz upper p tail
  let g := actualFrozenSelectedPairAssignment D A yz upper p tail
  have hword (j : Fin 3) (word : List (Fin n))
      (hmem : ∀ i, g i = j ↔ i ∈ word) :
      originalFrozenGroupCharacter g eta z j = physicalWordCharacter word eta z := by
    unfold originalFrozenGroupCharacter physicalWordCharacter
    congr 1
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        List.mem_toFinset]
      exact hmem i
    · intro i hi
      rfl
  have h0 := hword 0 slots.1 (fun i =>
    (actualFrozenSelectedPairAssignment_fibres D A yz upper p tail hnodup hcover i).1)
  have h1 := hword 1 slots.2.1 (fun i =>
    (actualFrozenSelectedPairAssignment_fibres D A yz upper p tail hnodup hcover i).2.1)
  have h2 := hword 2 slots.2.2 (fun i =>
    (actualFrozenSelectedPairAssignment_fibres D A yz upper p tail hnodup hcover i).2.2)
  have hthree (f : Fin 3 → ℂ) :
      (∏ j : Fin 3, f j) = f 0 * (f 1 * f 2) := by
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    simp [mul_assoc]
  calc
    originalSlotCharacter eta z =
        ∏ j : Fin 3, originalFrozenGroupCharacter g eta z j :=
          original_character_factors g eta z
    _ = originalFrozenGroupCharacter g eta z 0 *
        (originalFrozenGroupCharacter g eta z 1 *
          originalFrozenGroupCharacter g eta z 2) := hthree _
    _ = physicalWordCharacter slots.1 eta z *
          (physicalWordCharacter slots.2.1 eta z *
            physicalWordCharacter slots.2.2 eta z) := by
        rw [h0, h1, h2]

/-- Specialize the exact original-slot identity to the actual physical
logarithmic HB chart. This is a single Fourier mode, not a claim that
the geometric W_T is already a finite separated sum. -/
theorem actual_frozen_physical_log_phase {n : ℕ}
    (D A : ℝ) (yz : Bool) (upper : Fin n → ℕ)
    (p : Fin 3 → Fin n) (tail : List (Fin n))
    (hnodup : (p 0 :: p 1 :: p 2 :: tail).Nodup)
    (hcover : ∀ i, i ∈ p 0 :: p 1 :: p 2 :: tail)
    (eta U values : Fin n → ℝ) :
    let slots := actualFrozenSelectedPairSlots D A yz upper p tail
    originalSlotCharacter eta (slotLog U values) =
      physicalWordCharacter slots.1 eta (slotLog U values) *
        (physicalWordCharacter slots.2.1 eta (slotLog U values) *
          physicalWordCharacter slots.2.2 eta (slotLog U values)) := by
  exact actual_frozen_original_phase_from_words
    D A yz upper p tail hnodup hcover eta (slotLog U values)

end
end ImbalancedChen.P3ActualFrozenOriginalSlotPhase
