import ImbalancedChen.FixedRoughCoefficients
import ImbalancedChen.FirstExitPresieveProjection

/-!
# Fixed modulus coefficients for an arbitrary first-exit policy

All topology and product-injectivity statements here retain the exact leaves
of the supplied policy. No parity of the exits is assumed. The support is
fixed using unit local weights before any arithmetic test is evaluated.
The same support and its literal Mobius coefficient reindex every local
weight evaluation of that tree, without introducing multiplicities.
-/

namespace ImbalancedChen

noncomputable section

open scoped List

/-- Retained root leaves, with no restriction on the retention policy. -/
def firstExitRootLeaves {α : Type*} (retained : Bool → List α → Bool)
    (h : α → ℝ) (carrier : List α) : List (FirstExitLeaf α) :=
  firstExitRetainedLeaves retained h [] true 1 carrier

theorem firstExitRootLeaves_nodup {α : Type*} (retained : Bool → List α → Bool)
    (h : α → ℝ) (carrier : List α) (hcarrier : carrier.Nodup) :
    (firstExitRootLeaves retained h carrier).Nodup := by
  exact firstExitRetainedLeaves_nodup retained h [] carrier true 1 (by simpa using hcarrier)

theorem mem_firstExitRootLeaves_mass_eq_selected_prod
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (carrier : List α) (leaf : FirstExitLeaf α)
    (hleaf : leaf ∈ firstExitRootLeaves retained h carrier) :
    leaf.mass = (leaf.selected.map h).prod := by
  exact firstExitRetainedLeaves_mass_eq_selected_prod
    retained h [] carrier true 1 (by simp) leaf hleaf

theorem mem_firstExitRootLeaves_positive_eq_evenListLength
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (carrier : List α) (leaf : FirstExitLeaf α)
    (hleaf : leaf ∈ firstExitRootLeaves retained h carrier) :
    leaf.positive = evenListLength leaf.selected := by
  exact firstExitRetainedLeaves_positive_eq_evenListLength
    retained h [] carrier true 1 (by simp [evenListLength])
      leaf hleaf

theorem mem_firstExitRootLeaves_selected_reverse_sublist
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (carrier : List α) (leaf : FirstExitLeaf α)
    (hleaf : leaf ∈ firstExitRootLeaves retained h carrier) :
    leaf.selected.reverse <+ carrier := by
  simpa [firstExitRootLeaves] using
    firstExitRetainedLeaves_selected_reverse_sublist
      retained h [] carrier true 1 leaf hleaf

theorem mem_firstExitRootLeaves_selected_nodup
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (carrier : List α) (huniverse : carrier.Nodup)
    (leaf : FirstExitLeaf α)
    (hleaf : leaf ∈ firstExitRootLeaves retained h carrier) :
    leaf.selected.Nodup := by
  have hreverse : leaf.selected.reverse.Nodup :=
    huniverse.sublist
      (mem_firstExitRootLeaves_selected_reverse_sublist
        retained h carrier leaf hleaf)
  simpa using hreverse

theorem mem_firstExitRootLeaves_selected_prime
    (retained : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (hprime : ∀ p ∈ carrier, Nat.Prime p)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRootLeaves retained h carrier) :
    ∀ p ∈ leaf.selected, Nat.Prime p := by
  intro p hp
  have hsub : leaf.selected.reverse <+ carrier :=
    mem_firstExitRootLeaves_selected_reverse_sublist
      retained h carrier leaf hleaf
  apply hprime p
  apply hsub.subset
  simpa using hp

theorem mem_firstExitRootLeaves_primeFactors_selectedProd
    (retained : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (huniverse : carrier.Nodup)
    (hprime : ∀ p ∈ carrier, Nat.Prime p)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRootLeaves retained h carrier) :
    leaf.selected.prod.primeFactors = leaf.selected.toFinset := by
  have hnodup : leaf.selected.Nodup :=
    mem_firstExitRootLeaves_selected_nodup
      retained h carrier huniverse leaf hleaf
  have hprod :
      (∏ p ∈ leaf.selected.toFinset, p) = leaf.selected.prod := by
    simpa using List.prod_toFinset (fun p : ℕ => p) hnodup
  rw [← hprod]
  exact Nat.primeFactors_prod fun p hp =>
    mem_firstExitRootLeaves_selected_prime
      retained h carrier hprime leaf hleaf p (List.mem_toFinset.mp hp)

theorem mem_firstExitRootLeaves_selectedProd_squarefree
    (retained : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (huniverse : carrier.Nodup)
    (hprime : ∀ p ∈ carrier, Nat.Prime p)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRootLeaves retained h carrier) :
    Squarefree leaf.selected.prod := by
  exact list_prod_squarefree_of_nodup_primes leaf.selected
    (mem_firstExitRootLeaves_selected_nodup
      retained h carrier huniverse leaf hleaf)
    (mem_firstExitRootLeaves_selected_prime
      retained h carrier hprime leaf hleaf)

theorem mem_firstExitRootLeaves_moebius_selectedProd
    (retained : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (huniverse : carrier.Nodup)
    (hprime : ∀ p ∈ carrier, Nat.Prime p)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRootLeaves retained h carrier) :
    ArithmeticFunction.moebius leaf.selected.prod =
      (-1 : ℤ) ^ leaf.selected.length := by
  exact moebius_list_prod_eq_negOnePow_length leaf.selected
    (mem_firstExitRootLeaves_selected_nodup
      retained h carrier huniverse leaf hleaf)
    (mem_firstExitRootLeaves_selected_prime
      retained h carrier hprime leaf hleaf)

theorem firstExitRootLeaves_selected_eq_of_prod_eq
    (retained : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (huniverse : carrier.Nodup)
    (hprime : ∀ p ∈ carrier, Nat.Prime p)
    (leaf₁ leaf₂ : FirstExitLeaf ℕ)
    (hleaf₁ : leaf₁ ∈ firstExitRootLeaves retained h carrier)
    (hleaf₂ : leaf₂ ∈ firstExitRootLeaves retained h carrier)
    (hprod : leaf₁.selected.prod = leaf₂.selected.prod) :
    leaf₁.selected = leaf₂.selected := by
  have hsub₁ : leaf₁.selected.reverse <+ carrier :=
    mem_firstExitRootLeaves_selected_reverse_sublist
      retained h carrier leaf₁ hleaf₁
  have hsub₂ : leaf₂.selected.reverse <+ carrier :=
    mem_firstExitRootLeaves_selected_reverse_sublist
      retained h carrier leaf₂ hleaf₂
  have hprime₁ : ∀ p ∈ leaf₁.selected.reverse, _root_.Prime p := by
    intro p hp
    exact Nat.prime_iff.mp (hprime p (hsub₁.subset hp))
  have hprime₂ : ∀ p ∈ leaf₂.selected.reverse, _root_.Prime p := by
    intro p hp
    exact Nat.prime_iff.mp (hprime p (hsub₂.subset hp))
  have hprodReverse :
      leaf₁.selected.reverse.prod = leaf₂.selected.reverse.prod := by
    simpa only [List.prod_reverse] using hprod
  have hperm : leaf₁.selected.reverse ~ leaf₂.selected.reverse :=
    perm_of_prod_eq_prod hprodReverse hprime₁ hprime₂
  have hreverseEq : leaf₁.selected.reverse = leaf₂.selected.reverse :=
    (huniverse.perm_iff_eq_of_sublist hsub₁ hsub₂).1 hperm
  exact List.reverse_injective hreverseEq

theorem firstExitRootLeaves_eq_of_selected_prod_eq
    (retained : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (huniverse : carrier.Nodup)
    (hprime : ∀ p ∈ carrier, Nat.Prime p)
    (leaf₁ leaf₂ : FirstExitLeaf ℕ)
    (hleaf₁ : leaf₁ ∈ firstExitRootLeaves retained h carrier)
    (hleaf₂ : leaf₂ ∈ firstExitRootLeaves retained h carrier)
    (hprod : leaf₁.selected.prod = leaf₂.selected.prod) :
    leaf₁ = leaf₂ := by
  have hselected : leaf₁.selected = leaf₂.selected :=
    firstExitRootLeaves_selected_eq_of_prod_eq
      retained h carrier huniverse hprime leaf₁ leaf₂ hleaf₁ hleaf₂ hprod
  have hpositive : leaf₁.positive = leaf₂.positive := by
    rw [mem_firstExitRootLeaves_positive_eq_evenListLength
        retained h carrier leaf₁ hleaf₁,
      mem_firstExitRootLeaves_positive_eq_evenListLength
        retained h carrier leaf₂ hleaf₂,
      hselected]
  have hmass : leaf₁.mass = leaf₂.mass := by
    rw [mem_firstExitRootLeaves_mass_eq_selected_prod
        retained h carrier leaf₁ hleaf₁,
      mem_firstExitRootLeaves_mass_eq_selected_prod
        retained h carrier leaf₂ hleaf₂,
      hselected]
  exact FirstExitLeaf.ext hselected hpositive hmass

theorem firstExitRootLeaves_selectedProd_injOn
    (retained : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (huniverse : carrier.Nodup)
    (hprime : ∀ p ∈ carrier, Nat.Prime p) :
    Set.InjOn (fun leaf : FirstExitLeaf ℕ => leaf.selected.prod)
      {leaf | leaf ∈ firstExitRootLeaves retained h carrier} := by
  intro leaf₁ hleaf₁ leaf₂ hleaf₂ hprod
  exact firstExitRootLeaves_eq_of_selected_prod_eq
    retained h carrier huniverse hprime leaf₁ leaf₂ hleaf₁ hleaf₂ hprod

theorem mem_firstExitRootLeaves_value_eq_signed_selected_prod
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (carrier : List α) (leaf : FirstExitLeaf α)
    (hleaf : leaf ∈ firstExitRootLeaves retained h carrier) :
    leaf.value = signedTreeCoefficient (evenListLength leaf.selected)
      (leaf.selected.map h).prod := by
  unfold FirstExitLeaf.value
  rw [mem_firstExitRootLeaves_positive_eq_evenListLength
      retained h carrier leaf hleaf,
    mem_firstExitRootLeaves_mass_eq_selected_prod
      retained h carrier leaf hleaf]

theorem mem_firstExitRootLeaves_value_eq_moebius_mul_selected_prod
    (retained : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (huniverse : carrier.Nodup)
    (hprime : ∀ p ∈ carrier, Nat.Prime p)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRootLeaves retained h carrier) :
    leaf.value =
      (ArithmeticFunction.moebius leaf.selected.prod : ℝ) *
        (leaf.selected.map h).prod := by
  calc
    leaf.value = signedTreeCoefficient (evenListLength leaf.selected)
        (leaf.selected.map h).prod :=
      mem_firstExitRootLeaves_value_eq_signed_selected_prod
        retained h carrier leaf hleaf
    _ = (-1 : ℝ) ^ leaf.selected.length *
        (leaf.selected.map h).prod :=
      signedTreeCoefficient_evenListLength_eq_negOnePow
        leaf.selected (leaf.selected.map h).prod
    _ = (ArithmeticFunction.moebius leaf.selected.prod : ℝ) *
        (leaf.selected.map h).prod := by
      rw [mem_firstExitRootLeaves_moebius_selectedProd
        retained h carrier huniverse hprime leaf hleaf]
      simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- The chosen natural support is fixed before the local weights are tested. -/
def firstExitRetainedModuli (retained : Bool → List ℕ → Bool)
    (carrier : List ℕ) : Finset ℕ :=
  ((firstExitRootLeaves retained (fun _ => 1) carrier).map
    fun leaf => leaf.selected.prod).toFinset

/-- The same selected products occur for any local weights. -/
theorem firstExitRetainedModuli_eq (retained : Bool → List ℕ → Bool)
    (h : ℕ → ℝ) (carrier : List ℕ) :
    firstExitRetainedModuli retained carrier =
      ((firstExitRootLeaves retained h carrier).map
        fun leaf => leaf.selected.prod).toFinset := by
  have htop := congrArg (fun xs : List (List ℕ) => (xs.map List.prod).toFinset)
    (firstExitRetainedLeaves_selected_independent retained (fun _ => 1) h
      [] carrier true 1 1)
  simpa only [List.map_map, Function.comp_def, firstExitRetainedModuli,
    firstExitRootLeaves] using htop

@[simp] theorem mem_firstExitRetainedModuli
    (retained : Bool → List ℕ → Bool) (carrier : List ℕ) (d : ℕ) :
    d ∈ firstExitRetainedModuli retained carrier ↔
      ∃ leaf ∈ firstExitRootLeaves retained (fun _ => 1) carrier,
        leaf.selected.prod = d := by
  simp [firstExitRetainedModuli]

theorem firstExitRetainedModuli_squarefree
    (retained : Bool → List ℕ → Bool) (carrier : List ℕ)
    (hnodup : carrier.Nodup) (hprime : ∀ p ∈ carrier, Nat.Prime p)
    {d : ℕ} (hd : d ∈ firstExitRetainedModuli retained carrier) : Squarefree d := by
  rcases (mem_firstExitRetainedModuli retained carrier d).mp hd with ⟨leaf, hleaf, rfl⟩
  exact mem_firstExitRootLeaves_selectedProd_squarefree retained (fun _ => 1)
    carrier hnodup hprime leaf hleaf

theorem firstExitRetainedModuli_primeFactors_mem
    (retained : Bool → List ℕ → Bool) (carrier : List ℕ)
    (hnodup : carrier.Nodup) (hprime : ∀ p ∈ carrier, Nat.Prime p)
    {d p : ℕ} (hd : d ∈ firstExitRetainedModuli retained carrier)
    (hp : p ∈ d.primeFactors) : p ∈ carrier := by
  rcases (mem_firstExitRetainedModuli retained carrier d).mp hd with ⟨leaf, hleaf, rfl⟩
  rw [mem_firstExitRootLeaves_primeFactors_selectedProd retained (fun _ => 1)
    carrier hnodup hprime leaf hleaf] at hp
  exact (mem_firstExitRootLeaves_selected_reverse_sublist retained (fun _ => 1)
    carrier leaf hleaf).subset (by simpa using List.mem_toFinset.mp hp)

/-- Mobius on the fixed retained support, and zero outside it. -/
def firstExitRetainedCoefficient (retained : Bool → List ℕ → Bool)
    (carrier : List ℕ) (d : ℕ) : ℤ :=
  if d ∈ firstExitRetainedModuli retained carrier then ArithmeticFunction.moebius d else 0

theorem firstExitRetainedCoefficient_abs_le_one
    (retained : Bool → List ℕ → Bool) (carrier : List ℕ) (d : ℕ) :
    |firstExitRetainedCoefficient retained carrier d| ≤ 1 := by
  unfold firstExitRetainedCoefficient
  split
  · exact ArithmeticFunction.abs_moebius_le_one
  · norm_num

/-- Root products are duplicate-free even for an arbitrary causal policy. -/
theorem firstExitRootLeaves_selectedProd_map_nodup
    (retained : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (hnodup : carrier.Nodup) (hprime : ∀ p ∈ carrier, Nat.Prime p) :
    ((firstExitRootLeaves retained h carrier).map fun leaf => leaf.selected.prod).Nodup := by
  refine (List.nodup_map_iff_inj_on (firstExitRootLeaves_nodup retained h carrier hnodup)).2 ?_
  intro leaf₁ hleaf₁ leaf₂ hleaf₂ hprod
  exact firstExitRootLeaves_eq_of_selected_prod_eq
    retained h carrier hnodup hprime leaf₁ leaf₂ hleaf₁ hleaf₂ hprod

/-- The literal tree polynomial is exactly a sum over the fixed natural
moduli. The product injection proves that no leaf multiplicity is lost. -/
theorem firstExitRetainedPolynomial_eq_retainedModuli_sum
    (retained : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (carrier : List ℕ) (hnodup : carrier.Nodup) (hprime : ∀ p ∈ carrier, Nat.Prime p) :
    firstExitRetainedPolynomial retained h [] true 1 carrier =
      ∑ d ∈ firstExitRetainedModuli retained carrier,
        (firstExitRetainedCoefficient retained carrier d : ℝ) *
          d.primeFactors.prod h := by
  rw [firstExitRetainedPolynomial_eq_leaves_sum]
  let leaves := firstExitRootLeaves retained h carrier
  let weight : ℕ → ℝ := fun d =>
    (firstExitRetainedCoefficient retained carrier d : ℝ) * d.primeFactors.prod h
  have hvalues : leaves.map FirstExitLeaf.value =
      (leaves.map (fun leaf => leaf.selected.prod)).map weight := by
    rw [List.map_map]
    apply List.map_congr_left
    intro leaf hleaf
    have hselected := mem_firstExitRootLeaves_selected_nodup retained h carrier
      hnodup leaf hleaf
    have hweights : leaf.selected.prod.primeFactors.prod h = (leaf.selected.map h).prod := by
      rw [mem_firstExitRootLeaves_primeFactors_selectedProd
        retained h carrier hnodup hprime leaf hleaf]
      exact List.prod_toFinset h hselected
    have hmem : leaf.selected.prod ∈ firstExitRetainedModuli retained carrier := by
      rw [firstExitRetainedModuli_eq retained h carrier]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨leaf, hleaf, rfl⟩)
    change leaf.value = (firstExitRetainedCoefficient retained carrier leaf.selected.prod : ℝ) *
      leaf.selected.prod.primeFactors.prod h
    rw [firstExitRetainedCoefficient, if_pos hmem, hweights]
    exact mem_firstExitRootLeaves_value_eq_moebius_mul_selected_prod
      retained h carrier hnodup hprime leaf hleaf
  change (leaves.map FirstExitLeaf.value).sum = _
  rw [hvalues, firstExitRetainedModuli_eq retained h carrier]
  exact (List.sum_toFinset weight
    (firstExitRootLeaves_selectedProd_map_nodup retained h carrier hnodup hprime)).symm

end

end ImbalancedChen
