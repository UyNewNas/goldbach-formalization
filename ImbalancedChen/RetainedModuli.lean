import ImbalancedChen.FirstExitTree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Natural-number support of the retained first-exit tree

This file turns the selected-prime product of a retained leaf into a
natural-number modulus support and a literal integer coefficient

`lambda(d) = mu(d)` on that support and `0` off it.

The recursive leaf enumeration is proved duplicate-free in
`FirstExitTree.lean`.  Together with product injectivity, this permits the
literal leaf `List.sum` to be reindexed as a `Finset.sum` without discarding
or inventing multiplicities.
-/

namespace ImbalancedChen

noncomputable section

/-- Natural moduli represented by retained terminal branches. -/
def oddFirstExitRetainedModuli
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ) (carrier : List ℕ) :
    Finset ℕ :=
  ((oddFirstExitRetainedLeaves retainOdd h carrier).map
    fun leaf => leaf.selected.prod).toFinset

/-- A modulus is retained exactly when it is the selected-prime product of
some retained leaf. -/
@[simp] theorem mem_oddFirstExitRetainedModuli
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ) (carrier : List ℕ) (d : ℕ) :
    d ∈ oddFirstExitRetainedModuli retainOdd h carrier ↔
      ∃ leaf ∈ oddFirstExitRetainedLeaves retainOdd h carrier,
        leaf.selected.prod = d := by
  simp [oddFirstExitRetainedModuli]

/-- The modulus of every retained leaf belongs to the natural support. -/
theorem selectedProd_mem_oddFirstExitRetainedModuli
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ) (carrier : List ℕ)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd h carrier) :
    leaf.selected.prod ∈
      oddFirstExitRetainedModuli retainOdd h carrier := by
  exact (mem_oddFirstExitRetainedModuli retainOdd h carrier _).2
    ⟨leaf, hleaf, rfl⟩

/-- The empty retained branch keeps the unit modulus in the support. -/
theorem one_mem_oddFirstExitRetainedModuli
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ) (carrier : List ℕ) :
    1 ∈ oddFirstExitRetainedModuli retainOdd h carrier := by
  refine (mem_oddFirstExitRetainedModuli retainOdd h carrier 1).2 ⟨
    ({ selected := [], positive := true, mass := 1 } : FirstExitLeaf ℕ),
    oddFirstExitRetainedLeaves_unit_mem retainOdd h carrier, ?_⟩
  simp

/-- In a duplicate-free prime carrier, every supported modulus has one
unique retained leaf as a value. -/
theorem existsUnique_retainedLeaf_of_mem_oddFirstExitRetainedModuli
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (huniverse : carrier.Nodup)
    (hprime : ∀ p ∈ carrier, Nat.Prime p) (d : ℕ)
    (hd : d ∈ oddFirstExitRetainedModuli retainOdd h carrier) :
    ∃! leaf : FirstExitLeaf ℕ,
      leaf ∈ oddFirstExitRetainedLeaves retainOdd h carrier ∧
        leaf.selected.prod = d := by
  rcases (mem_oddFirstExitRetainedModuli retainOdd h carrier d).1 hd with
    ⟨leaf, hleaf, hprod⟩
  refine ⟨leaf, ⟨hleaf, hprod⟩, ?_⟩
  intro leaf' hleaf'
  exact oddFirstExitRetainedLeaves_eq_of_selected_prod_eq
    retainOdd h carrier huniverse hprime leaf' leaf hleaf'.1 hleaf
      (hleaf'.2.trans hprod.symm)

/-- Every supported modulus in a duplicate-free prime carrier is
squarefree. -/
theorem mem_oddFirstExitRetainedModuli_squarefree
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (huniverse : carrier.Nodup)
    (hprime : ∀ p ∈ carrier, Nat.Prime p) (d : ℕ)
    (hd : d ∈ oddFirstExitRetainedModuli retainOdd h carrier) :
    Squarefree d := by
  rcases (mem_oddFirstExitRetainedModuli retainOdd h carrier d).1 hd with
    ⟨leaf, hleaf, hprod⟩
  rw [← hprod]
  exact mem_oddFirstExitRetainedLeaves_selectedProd_squarefree
    retainOdd h carrier huniverse hprime leaf hleaf

/-- The integer coefficient attached to a natural modulus: Möbius on the
retained support and zero outside it. -/
def oddFirstExitRetainedCoefficient
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (d : ℕ) : ℤ :=
  if d ∈ oddFirstExitRetainedModuli retainOdd h carrier then
    ArithmeticFunction.moebius d
  else 0

@[simp] theorem oddFirstExitRetainedCoefficient_eq_zero_of_not_mem
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (d : ℕ)
    (hd : d ∉ oddFirstExitRetainedModuli retainOdd h carrier) :
    oddFirstExitRetainedCoefficient retainOdd h carrier d = 0 := by
  simp [oddFirstExitRetainedCoefficient, hd]

/-- The retained unit modulus has coefficient `mu(1) = 1`. -/
@[simp] theorem oddFirstExitRetainedCoefficient_one
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ) (carrier : List ℕ) :
    oddFirstExitRetainedCoefficient retainOdd h carrier 1 = 1 := by
  rw [oddFirstExitRetainedCoefficient,
    if_pos (one_mem_oddFirstExitRetainedModuli retainOdd h carrier)]
  simp

/-- Lookup at the modulus of an actual retained leaf returns its Möbius
coefficient. -/
theorem oddFirstExitRetainedCoefficient_selectedProd
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ) (carrier : List ℕ)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd h carrier) :
    oddFirstExitRetainedCoefficient retainOdd h carrier
      leaf.selected.prod = ArithmeticFunction.moebius leaf.selected.prod := by
  simp [oddFirstExitRetainedCoefficient,
    selectedProd_mem_oddFirstExitRetainedModuli
      retainOdd h carrier leaf hleaf]

/-- On a retained branch of a duplicate-free prime carrier, the leaf value
is the looked-up integer coefficient times the local weights over the
modulus's actual prime-factor finset. -/
theorem mem_oddFirstExitRetainedLeaves_value_eq_coefficient_mul_primeFactors
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (huniverse : carrier.Nodup)
    (hprime : ∀ p ∈ carrier, Nat.Prime p)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd h carrier) :
    leaf.value =
      (oddFirstExitRetainedCoefficient retainOdd h carrier
        leaf.selected.prod : ℝ) *
        leaf.selected.prod.primeFactors.prod h := by
  have hnodup : leaf.selected.Nodup :=
    mem_oddFirstExitRetainedLeaves_selected_nodup
      retainOdd h carrier huniverse leaf hleaf
  have hweights : leaf.selected.prod.primeFactors.prod h =
      (leaf.selected.map h).prod := by
    rw [mem_oddFirstExitRetainedLeaves_primeFactors_selectedProd
      retainOdd h carrier huniverse hprime leaf hleaf]
    exact List.prod_toFinset h hnodup
  calc
    leaf.value =
        (ArithmeticFunction.moebius leaf.selected.prod : ℝ) *
          (leaf.selected.map h).prod :=
      mem_oddFirstExitRetainedLeaves_value_eq_moebius_mul_selected_prod
        retainOdd h carrier huniverse hprime leaf hleaf
    _ =
        (oddFirstExitRetainedCoefficient retainOdd h carrier
          leaf.selected.prod : ℝ) *
          leaf.selected.prod.primeFactors.prod h := by
      rw [oddFirstExitRetainedCoefficient_selectedProd
        retainOdd h carrier leaf hleaf, hweights]

/-- The list of natural moduli attached to the actual retained leaves is
duplicate-free.  This combines source-list `Nodup` with injectivity of the
selected-prime product on member leaves. -/
theorem oddFirstExitRetainedLeaves_selectedProd_map_nodup
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (huniverse : carrier.Nodup)
    (hprime : ∀ p ∈ carrier, Nat.Prime p) :
    ((oddFirstExitRetainedLeaves retainOdd h carrier).map
      fun leaf => leaf.selected.prod).Nodup := by
  refine (List.nodup_map_iff_inj_on
    (oddFirstExitRetainedLeaves_nodup
      retainOdd h carrier huniverse)).2 ?_
  intro leaf₁ hleaf₁ leaf₂ hleaf₂ hprod
  exact oddFirstExitRetainedLeaves_eq_of_selected_prod_eq
    retainOdd h carrier huniverse hprime leaf₁ leaf₂
    hleaf₁ hleaf₂ hprod

/-- Exact multiplicity-preserving modulus reindex of the retained branch
sum.  The right side is over the natural support once, with the actual
Möbius coefficient and local weights indexed by `d.primeFactors`. -/
theorem oddFirstExitRetainedLeaves_sum_eq_retainedModuli_sum
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (huniverse : carrier.Nodup)
    (hprime : ∀ p ∈ carrier, Nat.Prime p) :
    ((oddFirstExitRetainedLeaves retainOdd h carrier).map
      FirstExitLeaf.value).sum =
      ∑ d ∈ oddFirstExitRetainedModuli retainOdd h carrier,
        (oddFirstExitRetainedCoefficient retainOdd h carrier d : ℝ) *
          d.primeFactors.prod h := by
  let modulus : FirstExitLeaf ℕ → ℕ := fun leaf => leaf.selected.prod
  let weight : ℕ → ℝ := fun d =>
    (oddFirstExitRetainedCoefficient retainOdd h carrier d : ℝ) *
      d.primeFactors.prod h
  have hvalues :
      (oddFirstExitRetainedLeaves retainOdd h carrier).map
          FirstExitLeaf.value =
        ((oddFirstExitRetainedLeaves retainOdd h carrier).map modulus).map
          weight := by
    rw [List.map_map]
    apply List.map_congr_left
    intro leaf hleaf
    change leaf.value = weight (modulus leaf)
    exact mem_oddFirstExitRetainedLeaves_value_eq_coefficient_mul_primeFactors
      retainOdd h carrier huniverse hprime leaf hleaf
  rw [hvalues]
  change
    (((oddFirstExitRetainedLeaves retainOdd h carrier).map modulus).map
      weight).sum =
      ((oddFirstExitRetainedLeaves retainOdd h carrier).map modulus).toFinset.sum
        weight
  exact (List.sum_toFinset weight
    (oddFirstExitRetainedLeaves_selectedProd_map_nodup
      retainOdd h carrier huniverse hprime)).symm

end

end ImbalancedChen
