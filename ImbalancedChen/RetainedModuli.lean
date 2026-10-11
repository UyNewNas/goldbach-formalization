import ImbalancedChen.FirstExitTree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Natural-number support of the retained first-exit tree

This file turns the selected-prime product of a retained leaf into a
natural-number modulus support and a literal integer coefficient

`lambda(d) = mu(d)` on that support and `0` off it.

The construction deliberately stops short of replacing the enumerated leaf
`List.sum` by a `Finset.sum`: product injectivity on leaf *values* does not by
itself prove that the recursive leaf list has no duplicate occurrences.  That
separate `Nodup` obligation must be closed before a sum reindex can discard
list multiplicities.
-/

namespace ImbalancedChen

noncomputable section

/-- Natural moduli represented by retained terminal branches. -/
def oddFirstExitRetainedModuli
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ) (universe : List ℕ) :
    Finset ℕ :=
  ((oddFirstExitRetainedLeaves retainOdd h universe).map
    fun leaf => leaf.selected.prod).toFinset

/-- A modulus is retained exactly when it is the selected-prime product of
some retained leaf.  This is a support statement, not yet a sum reindex. -/
@[simp] theorem mem_oddFirstExitRetainedModuli
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ) (universe : List ℕ) (d : ℕ) :
    d ∈ oddFirstExitRetainedModuli retainOdd h universe ↔
      ∃ leaf ∈ oddFirstExitRetainedLeaves retainOdd h universe,
        leaf.selected.prod = d := by
  simp [oddFirstExitRetainedModuli]

/-- The modulus of every retained leaf belongs to the natural support. -/
theorem selectedProd_mem_oddFirstExitRetainedModuli
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ) (universe : List ℕ)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd h universe) :
    leaf.selected.prod ∈
      oddFirstExitRetainedModuli retainOdd h universe := by
  exact mem_oddFirstExitRetainedModuli.mpr ⟨leaf, hleaf, rfl⟩

/-- The empty retained branch keeps the unit modulus in the support. -/
theorem one_mem_oddFirstExitRetainedModuli
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ) (universe : List ℕ) :
    1 ∈ oddFirstExitRetainedModuli retainOdd h universe := by
  refine mem_oddFirstExitRetainedModuli.mpr ⟨
    ({ selected := [], positive := true, mass := 1 } : FirstExitLeaf ℕ),
    oddFirstExitRetainedLeaves_unit_mem retainOdd h universe, ?_⟩
  simp

/-- In a duplicate-free prime universe, every supported modulus has one
unique retained leaf as a value.  This does not yet assert that the source
leaf list contains that value with only one occurrence. -/
theorem existsUnique_retainedLeaf_of_mem_oddFirstExitRetainedModuli
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (universe : List ℕ) (huniverse : universe.Nodup)
    (hprime : ∀ p ∈ universe, Nat.Prime p) (d : ℕ)
    (hd : d ∈ oddFirstExitRetainedModuli retainOdd h universe) :
    ∃! leaf : FirstExitLeaf ℕ,
      leaf ∈ oddFirstExitRetainedLeaves retainOdd h universe ∧
        leaf.selected.prod = d := by
  rcases mem_oddFirstExitRetainedModuli.mp hd with
    ⟨leaf, hleaf, hprod⟩
  refine ⟨leaf, ⟨hleaf, hprod⟩, ?_⟩
  intro leaf' hleaf'
  exact oddFirstExitRetainedLeaves_eq_of_selected_prod_eq
    retainOdd h universe huniverse hprime leaf' leaf hleaf'.1 hleaf
      (hleaf'.2.trans hprod.symm)

/-- Every supported modulus in a duplicate-free prime universe is
squarefree. -/
theorem mem_oddFirstExitRetainedModuli_squarefree
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (universe : List ℕ) (huniverse : universe.Nodup)
    (hprime : ∀ p ∈ universe, Nat.Prime p) (d : ℕ)
    (hd : d ∈ oddFirstExitRetainedModuli retainOdd h universe) :
    Squarefree d := by
  rcases mem_oddFirstExitRetainedModuli.mp hd with
    ⟨leaf, hleaf, hprod⟩
  rw [← hprod]
  exact mem_oddFirstExitRetainedLeaves_selectedProd_squarefree
    retainOdd h universe huniverse hprime leaf hleaf

/-- The integer coefficient attached to a natural modulus: Möbius on the
retained support and zero outside it. -/
def oddFirstExitRetainedCoefficient
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (universe : List ℕ) (d : ℕ) : ℤ :=
  if d ∈ oddFirstExitRetainedModuli retainOdd h universe then
    ArithmeticFunction.moebius d
  else 0

@[simp] theorem oddFirstExitRetainedCoefficient_eq_zero_of_not_mem
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (universe : List ℕ) (d : ℕ)
    (hd : d ∉ oddFirstExitRetainedModuli retainOdd h universe) :
    oddFirstExitRetainedCoefficient retainOdd h universe d = 0 := by
  simp [oddFirstExitRetainedCoefficient, hd]

/-- The retained unit modulus has coefficient `mu(1) = 1`. -/
@[simp] theorem oddFirstExitRetainedCoefficient_one
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ) (universe : List ℕ) :
    oddFirstExitRetainedCoefficient retainOdd h universe 1 = 1 := by
  simp [oddFirstExitRetainedCoefficient,
    one_mem_oddFirstExitRetainedModuli]

/-- Lookup at the modulus of an actual retained leaf returns its Möbius
coefficient. -/
theorem oddFirstExitRetainedCoefficient_selectedProd
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ) (universe : List ℕ)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd h universe) :
    oddFirstExitRetainedCoefficient retainOdd h universe
      leaf.selected.prod = ArithmeticFunction.moebius leaf.selected.prod := by
  simp [oddFirstExitRetainedCoefficient,
    selectedProd_mem_oddFirstExitRetainedModuli
      retainOdd h universe leaf hleaf]

/-- On a retained branch of a duplicate-free prime universe, the leaf value
is the looked-up integer coefficient times the local weights over the
modulus's actual prime-factor finset. -/
theorem mem_oddFirstExitRetainedLeaves_value_eq_coefficient_mul_primeFactors
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (universe : List ℕ) (huniverse : universe.Nodup)
    (hprime : ∀ p ∈ universe, Nat.Prime p)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd h universe) :
    leaf.value =
      (oddFirstExitRetainedCoefficient retainOdd h universe
        leaf.selected.prod : ℝ) *
        leaf.selected.prod.primeFactors.prod h := by
  have hnodup : leaf.selected.Nodup :=
    mem_oddFirstExitRetainedLeaves_selected_nodup
      retainOdd h universe huniverse leaf hleaf
  have hweights : leaf.selected.prod.primeFactors.prod h =
      (leaf.selected.map h).prod := by
    rw [mem_oddFirstExitRetainedLeaves_primeFactors_selectedProd
      retainOdd h universe huniverse hprime leaf hleaf]
    exact List.prod_toFinset h hnodup
  calc
    leaf.value =
        (ArithmeticFunction.moebius leaf.selected.prod : ℝ) *
          (leaf.selected.map h).prod :=
      mem_oddFirstExitRetainedLeaves_value_eq_moebius_mul_selected_prod
        retainOdd h universe huniverse hprime leaf hleaf
    _ =
        (oddFirstExitRetainedCoefficient retainOdd h universe
          leaf.selected.prod : ℝ) *
          leaf.selected.prod.primeFactors.prod h := by
      rw [oddFirstExitRetainedCoefficient_selectedProd
        retainOdd h universe leaf hleaf, hweights]

end

end ImbalancedChen
