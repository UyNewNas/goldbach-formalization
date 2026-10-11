import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.Prime
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Ring

/-!
# Finite odd-first-exit identity

The physical upper weight in the current manuscript begins with a finite
tree.  Every even-rank prefix is retained, while an odd-rank prefix may be
the first rejected prefix.  Divisors below a first exit remain unrestricted;
their alternating sum is the residual Euler product.

This file proves that algebra for an arbitrary finite ordered universe and an
arbitrary odd-rank retention policy.  It does not identify the policy with
the manuscript's causal boxes, estimate its density, or attach the
small-prime fundamental-lemma weights.

The Boolean `positive` records the sign of the coefficient of the already
selected prefix: `true` is even rank and `false` is odd rank.  The remaining
list is processed from larger to smaller labels.  Thus when a new odd prefix
is rejected, the unprocessed list is exactly the set of smaller labels in
the residual Euler product.
-/

namespace ImbalancedChen

noncomputable section

/-- A nonnegative mass with the alternating sign of the selected prefix. -/
def signedTreeCoefficient (positive : Bool) (mass : ℝ) : ℝ :=
  if positive then mass else -mass

@[simp] theorem signedTreeCoefficient_true (mass : ℝ) :
    signedTreeCoefficient true mass = mass := rfl

@[simp] theorem signedTreeCoefficient_false (mass : ℝ) :
    signedTreeCoefficient false mass = -mass := rfl

/-- Selecting one more label flips the Möbius sign and multiplies the mass
by that label's local weight. -/
theorem signedTreeCoefficient_not_mul
    (positive : Bool) (mass weight : ℝ) :
    signedTreeCoefficient (!positive) (mass * weight) =
      -signedTreeCoefficient positive mass * weight := by
  cases positive <;> simp [signedTreeCoefficient] <;> ring

/-- Sum of all retained extensions of one already-retained prefix.

`retained newSign newPrefix = true` means that the selected branch remains
inside the tree.  If it is false, that branch contributes no retained
coefficient and becomes a first exit. -/
def firstExitRetainedPolynomial {α : Type*}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (prefix : List α) (positive : Bool) (mass : ℝ) : List α → ℝ
  | [] => signedTreeCoefficient positive mass
  | p :: ps =>
      firstExitRetainedPolynomial retained h prefix positive mass ps +
        if retained (!positive) (p :: prefix) = true then
          firstExitRetainedPolynomial retained h (p :: prefix) (!positive)
            (mass * h p) ps
        else 0

/-- The signed correction contributed by all first exits below a retained
prefix.  At an exit, all later smaller labels are free, hence the product of
`1 - h` over the unprocessed tail. -/
def firstExitCorrection {α : Type*}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (prefix : List α) (positive : Bool) (mass : ℝ) : List α → ℝ
  | [] => 0
  | p :: ps =>
      firstExitCorrection retained h prefix positive mass ps +
        if retained (!positive) (p :: prefix) = true then
          firstExitCorrection retained h (p :: prefix) (!positive)
            (mass * h p) ps
        else
          -signedTreeCoefficient (!positive) (mass * h p) *
            (ps.map fun q => 1 - h q).prod

/-- Exact finite product-plus-first-exit identity, before imposing that first
exits have odd rank. -/
theorem firstExitRetainedPolynomial_eq_product_add_correction
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (prefix remaining : List α) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial retained h prefix positive mass remaining =
      signedTreeCoefficient positive mass *
          (remaining.map fun p => 1 - h p).prod +
        firstExitCorrection retained h prefix positive mass remaining := by
  induction remaining generalizing prefix positive mass with
  | nil => simp [firstExitRetainedPolynomial, firstExitCorrection]
  | cons p ps ih =>
      simp only [firstExitRetainedPolynomial, firstExitCorrection,
        List.map_cons, List.prod_cons]
      by_cases hr : retained (!positive) (p :: prefix) = true
      · rw [if_pos hr, ih, ih, signedTreeCoefficient_not_mul]
        ring
      · rw [if_neg hr, ih, signedTreeCoefficient_not_mul]
        ring

/-- One retained terminal branch of the finite tree.  `selected` records the
chosen labels, `positive` records the alternating sign, and `mass` is the
product accumulated along that branch.  These are data, not proof fields. -/
structure FirstExitLeaf (α : Type*) where
  selected : List α
  positive : Bool
  mass : ℝ

/-- The signed value contributed by one terminal retained branch. -/
def FirstExitLeaf.value {α : Type*} (leaf : FirstExitLeaf α) : ℝ :=
  signedTreeCoefficient leaf.positive leaf.mass

/-- Explicit enumeration of all terminal retained branches.  The skip branch
is always present; the select branch is followed exactly when its new prefix
is retained. -/
def firstExitRetainedLeaves {α : Type*}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (prefix : List α) (positive : Bool) (mass : ℝ) :
    List α → List (FirstExitLeaf α)
  | [] => [{ selected := prefix, positive := positive, mass := mass }]
  | p :: ps =>
      firstExitRetainedLeaves retained h prefix positive mass ps ++
        if retained (!positive) (p :: prefix) = true then
          firstExitRetainedLeaves retained h (p :: prefix) (!positive)
            (mass * h p) ps
        else []

/-- Skipping every remaining label always produces the incoming branch as a
terminal leaf.  In particular, the root tree always contains its empty
selection, even when the universe itself is empty. -/
theorem firstExitRetainedLeaves_skipAll_mem
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (prefix remaining : List α) (positive : Bool) (mass : ℝ) :
    ({ selected := prefix, positive := positive, mass := mass } :
        FirstExitLeaf α) ∈
      firstExitRetainedLeaves retained h prefix positive mass remaining := by
  induction remaining generalizing prefix positive mass with
  | nil => simp [firstExitRetainedLeaves]
  | cons p ps ih =>
      rw [firstExitRetainedLeaves]
      exact List.mem_append_left _ (ih prefix positive mass)

/-- The recursive retained polynomial is exactly the sum of its explicitly
enumerated retained terminal branches. -/
theorem firstExitRetainedPolynomial_eq_leaves_sum
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (prefix remaining : List α) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial retained h prefix positive mass remaining =
      ((firstExitRetainedLeaves retained h prefix positive mass remaining).map
        FirstExitLeaf.value).sum := by
  induction remaining generalizing prefix positive mass with
  | nil => simp [firstExitRetainedPolynomial, firstExitRetainedLeaves,
      FirstExitLeaf.value]
  | cons p ps ih =>
      by_cases hr : retained (!positive) (p :: prefix) = true
      · simp [firstExitRetainedPolynomial, firstExitRetainedLeaves, hr, ih]
      · simp [firstExitRetainedPolynomial, firstExitRetainedLeaves, hr, ih]

/-- If the incoming mass is the product of the already selected labels, the
recorded mass of every enumerated leaf is the product of its selected labels.
This is the invariant needed for the later prime-product reindexing. -/
theorem firstExitRetainedLeaves_mass_eq_selected_prod
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (prefix remaining : List α) (positive : Bool) (mass : ℝ)
    (hmass : mass = (prefix.map h).prod) :
    ∀ leaf ∈ firstExitRetainedLeaves retained h prefix positive mass remaining,
      leaf.mass = (leaf.selected.map h).prod := by
  induction remaining generalizing prefix positive mass with
  | nil =>
      intro leaf hleaf
      simp [firstExitRetainedLeaves] at hleaf
      subst leaf
      exact hmass
  | cons p ps ih =>
      intro leaf hleaf
      by_cases hr : retained (!positive) (p :: prefix) = true
      · rw [firstExitRetainedLeaves, if_pos hr, List.mem_append] at hleaf
        rcases hleaf with hskip | hselect
        · exact ih prefix positive mass hmass leaf hskip
        · have hmass' : mass * h p = ((p :: prefix).map h).prod := by
            simp [hmass, mul_comm]
          exact ih (p :: prefix) (!positive) (mass * h p) hmass' leaf hselect
      · rw [firstExitRetainedLeaves, if_neg hr, List.append_nil] at hleaf
        exact ih prefix positive mass hmass leaf hleaf

/-- Boolean parity of a list length: `true` means even. -/
def evenListLength {α : Type*} : List α → Bool
  | [] => true
  | _ :: xs => !evenListLength xs

/-- The Boolean parity sign is the usual algebraic factor `(-1)^length`. -/
theorem signedTreeCoefficient_evenListLength_eq_negOnePow
    {α : Type*} (xs : List α) (mass : ℝ) :
    signedTreeCoefficient (evenListLength xs) mass =
      (-1 : ℝ) ^ xs.length * mass := by
  induction xs with
  | nil => simp [evenListLength]
  | cons x xs ih =>
      calc
        signedTreeCoefficient (evenListLength (x :: xs)) mass =
            -signedTreeCoefficient (evenListLength xs) mass := by
              simpa [evenListLength] using
                signedTreeCoefficient_not_mul (evenListLength xs) mass 1
        _ = -((-1 : ℝ) ^ xs.length * mass) := by rw [ih]
        _ = (-1 : ℝ) ^ (x :: xs).length * mass := by
              simp [pow_succ]

/-- The sign bit stored in every leaf agrees with the parity of the number of
selected labels, provided it agrees at the incoming prefix. -/
theorem firstExitRetainedLeaves_positive_eq_evenListLength
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (prefix remaining : List α) (positive : Bool) (mass : ℝ)
    (hpositive : positive = evenListLength prefix) :
    ∀ leaf ∈ firstExitRetainedLeaves retained h prefix positive mass remaining,
      leaf.positive = evenListLength leaf.selected := by
  induction remaining generalizing prefix positive mass with
  | nil =>
      intro leaf hleaf
      simp [firstExitRetainedLeaves] at hleaf
      subst leaf
      exact hpositive
  | cons p ps ih =>
      intro leaf hleaf
      by_cases hr : retained (!positive) (p :: prefix) = true
      · rw [firstExitRetainedLeaves, if_pos hr, List.mem_append] at hleaf
        rcases hleaf with hskip | hselect
        · exact ih prefix positive mass hpositive leaf hskip
        · have hpositive' : !positive = evenListLength (p :: prefix) := by
            simp [evenListLength, hpositive]
          exact ih (p :: prefix) (!positive) (mass * h p)
            hpositive' leaf hselect
      · rw [firstExitRetainedLeaves, if_neg hr, List.append_nil] at hleaf
        exact ih prefix positive mass hpositive leaf hleaf

/-- Every selected list is accumulated in reverse processing order.  Reversing
it therefore gives a sublist of the labels that were already selected followed
by the labels still available at the current node. -/
theorem firstExitRetainedLeaves_selected_reverse_sublist
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (prefix remaining : List α) (positive : Bool) (mass : ℝ) :
    ∀ leaf ∈ firstExitRetainedLeaves retained h prefix positive mass remaining,
      leaf.selected.reverse <+ prefix.reverse ++ remaining := by
  induction remaining generalizing prefix positive mass with
  | nil =>
      intro leaf hleaf
      simp [firstExitRetainedLeaves] at hleaf
      subst leaf
      simp
  | cons p ps ih =>
      intro leaf hleaf
      by_cases hr : retained (!positive) (p :: prefix) = true
      · rw [firstExitRetainedLeaves, if_pos hr, List.mem_append] at hleaf
        rcases hleaf with hskip | hselect
        · exact (ih prefix positive mass leaf hskip).trans
            ((List.Sublist.refl _).append (List.sublist_cons_self p ps))
        · simpa [List.reverse_cons, List.append_assoc] using
            ih (p :: prefix) (!positive) (mass * h p) leaf hselect
      · rw [firstExitRetainedLeaves, if_neg hr, List.append_nil] at hleaf
        exact (ih prefix positive mass leaf hleaf).trans
          ((List.Sublist.refl _).append (List.sublist_cons_self p ps))

/-- A retention policy with no even-rank exit.  At odd rank `retainOdd`
decides whether the branch continues; at even rank it always continues. -/
def oddFirstExitPolicy {α : Type*}
    (retainOdd : List α → Bool) (positive : Bool) (prefix : List α) : Bool :=
  positive || retainOdd prefix

@[simp] theorem oddFirstExitPolicy_even {α : Type*}
    (retainOdd : List α → Bool) (prefix : List α) :
    oddFirstExitPolicy retainOdd true prefix = true := by
  simp [oddFirstExitPolicy]

/-- The retained polynomial of an odd-first-exit tree, starting at its root. -/
def oddFirstExitRetainedPolynomial {α : Type*}
    (retainOdd : List α → Bool) (h : α → ℝ) (universe : List α) : ℝ :=
  firstExitRetainedPolynomial (oddFirstExitPolicy retainOdd) h [] true 1 universe

/-- Explicit retained terminal branches of an odd-first-exit tree. -/
def oddFirstExitRetainedLeaves {α : Type*}
    (retainOdd : List α → Bool) (h : α → ℝ) (universe : List α) :
    List (FirstExitLeaf α) :=
  firstExitRetainedLeaves (oddFirstExitPolicy retainOdd) h [] true 1 universe

/-- The empty branch is always present.  It is the unit modulus `d = 1`,
with positive sign and coefficient one. -/
theorem oddFirstExitRetainedLeaves_unit_mem
    {α : Type*} (retainOdd : List α → Bool) (h : α → ℝ)
    (universe : List α) :
    ({ selected := [], positive := true, mass := 1 } : FirstExitLeaf α) ∈
      oddFirstExitRetainedLeaves retainOdd h universe := by
  exact firstExitRetainedLeaves_skipAll_mem
    (oddFirstExitPolicy retainOdd) h [] universe true 1

/-- The empty retained branch contributes exactly the unit term. -/
@[simp] theorem oddFirstExitUnitLeaf_value {α : Type*} :
    FirstExitLeaf.value
        ({ selected := [], positive := true, mass := 1 } : FirstExitLeaf α) = 1 := by
  rfl

/-- The root retained polynomial is a literal finite sum over the enumerated
terminal retained branches. -/
theorem oddFirstExitRetainedPolynomial_eq_leaves_sum
    {α : Type*} (retainOdd : List α → Bool) (h : α → ℝ)
    (universe : List α) :
    oddFirstExitRetainedPolynomial retainOdd h universe =
      ((oddFirstExitRetainedLeaves retainOdd h universe).map
        FirstExitLeaf.value).sum := by
  exact firstExitRetainedPolynomial_eq_leaves_sum
    (oddFirstExitPolicy retainOdd) h [] universe true 1

/-- Every root leaf records exactly the product of the local weights at its
selected labels. -/
theorem mem_oddFirstExitRetainedLeaves_mass_eq_selected_prod
    {α : Type*} (retainOdd : List α → Bool) (h : α → ℝ)
    (universe : List α) (leaf : FirstExitLeaf α)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd h universe) :
    leaf.mass = (leaf.selected.map h).prod := by
  exact firstExitRetainedLeaves_mass_eq_selected_prod
    (oddFirstExitPolicy retainOdd) h [] universe true 1 (by simp) leaf hleaf

/-- At the root, every retained branch carries exactly the parity sign of its
selected list. -/
theorem mem_oddFirstExitRetainedLeaves_positive_eq_evenListLength
    {α : Type*} (retainOdd : List α → Bool) (h : α → ℝ)
    (universe : List α) (leaf : FirstExitLeaf α)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd h universe) :
    leaf.positive = evenListLength leaf.selected := by
  exact firstExitRetainedLeaves_positive_eq_evenListLength
    (oddFirstExitPolicy retainOdd) h [] universe true 1 (by simp [evenListLength])
      leaf hleaf

/-- At the root, reversing a leaf's accumulated selected list gives a sublist
of the original ordered universe. -/
theorem mem_oddFirstExitRetainedLeaves_selected_reverse_sublist
    {α : Type*} (retainOdd : List α → Bool) (h : α → ℝ)
    (universe : List α) (leaf : FirstExitLeaf α)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd h universe) :
    leaf.selected.reverse <+ universe := by
  simpa [oddFirstExitRetainedLeaves] using
    firstExitRetainedLeaves_selected_reverse_sublist
      (oddFirstExitPolicy retainOdd) h [] universe true 1 leaf hleaf

/-- A root leaf selects each universe label at most once. -/
theorem mem_oddFirstExitRetainedLeaves_selected_nodup
    {α : Type*} (retainOdd : List α → Bool) (h : α → ℝ)
    (universe : List α) (huniverse : universe.Nodup)
    (leaf : FirstExitLeaf α)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd h universe) :
    leaf.selected.Nodup := by
  have hreverse : leaf.selected.reverse.Nodup :=
    huniverse.sublist
      (mem_oddFirstExitRetainedLeaves_selected_reverse_sublist
        retainOdd h universe leaf hleaf)
  simpa using hreverse

/-- Every selected label of a retained root branch inherits primality from
the common universe. -/
theorem mem_oddFirstExitRetainedLeaves_selected_prime
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (universe : List ℕ) (hprime : ∀ p ∈ universe, Nat.Prime p)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd h universe) :
    ∀ p ∈ leaf.selected, Nat.Prime p := by
  intro p hp
  have hsub : leaf.selected.reverse <+ universe :=
    mem_oddFirstExitRetainedLeaves_selected_reverse_sublist
      retainOdd h universe leaf hleaf
  apply hprime p
  apply hsub.subset
  simpa using hp

/-- A duplicate-free list of prime natural numbers has squarefree product. -/
theorem list_prod_squarefree_of_nodup_primes
    (xs : List ℕ) (hnodup : xs.Nodup)
    (hprime : ∀ p ∈ xs, Nat.Prime p) :
    Squarefree xs.prod := by
  have hprod : xs.toFinset.prod (fun p : ℕ => p) = xs.prod := by
    simpa using List.prod_toFinset (fun p : ℕ => p) hnodup
  rw [← hprod]
  refine Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => ?_) (fun p hp => ?_)
  · simp only [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes
      (hprime p (List.mem_toFinset.mp hp))
      (hprime q (List.mem_toFinset.mp hq))).mpr hpq
  · exact (hprime p (List.mem_toFinset.mp hp)).squarefree

/-- The prime-factor set of a retained branch product is exactly the Finset
of its selected labels.  This is the carrier inverse needed by the later
filtered modulus reindexing. -/
theorem mem_oddFirstExitRetainedLeaves_primeFactors_selectedProd
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (universe : List ℕ) (huniverse : universe.Nodup)
    (hprime : ∀ p ∈ universe, Nat.Prime p)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd h universe) :
    leaf.selected.prod.primeFactors = leaf.selected.toFinset := by
  have hnodup : leaf.selected.Nodup :=
    mem_oddFirstExitRetainedLeaves_selected_nodup
      retainOdd h universe huniverse leaf hleaf
  have hprod :
      (∏ p ∈ leaf.selected.toFinset, p) = leaf.selected.prod := by
    simpa using List.prod_toFinset (fun p : ℕ => p) hnodup
  rw [← hprod]
  exact Nat.primeFactors_prod fun p hp =>
    mem_oddFirstExitRetainedLeaves_selected_prime
      retainOdd h universe hprime leaf hleaf p (List.mem_toFinset.mp hp)

/-- Counting prime factors with multiplicity recovers the length of a list
whose entries are all prime.  Repetitions are allowed in this auxiliary
lemma; the squarefree application below supplies `Nodup` separately. -/
theorem cardFactors_list_prod_eq_length_of_primes
    (xs : List ℕ) (hprime : ∀ p ∈ xs, Nat.Prime p) :
    ArithmeticFunction.cardFactors xs.prod = xs.length := by
  have hprod0 : xs.prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hzero
    exact (hprime 0 hzero).ne_zero rfl
  have hcard := ArithmeticFunction.cardFactors_multiset_prod
    (s := (xs : Multiset ℕ)) (by
      simpa only [Multiset.prod_coe] using hprod0)
  rw [Multiset.prod_coe] at hcard
  have hmap :
      Multiset.map ArithmeticFunction.cardFactors (xs : Multiset ℕ) =
        Multiset.map (fun _ : ℕ => 1) (xs : Multiset ℕ) := by
    exact Multiset.map_congr rfl fun p hp =>
      ArithmeticFunction.cardFactors_apply_prime
        (hprime p (by simpa using hp))
  rw [hcard, hmap]
  simp

/-- For a duplicate-free prime list, the Möbius value of its product is the
alternating sign determined by the list length. -/
theorem moebius_list_prod_eq_negOnePow_length
    (xs : List ℕ) (hnodup : xs.Nodup)
    (hprime : ∀ p ∈ xs, Nat.Prime p) :
    ArithmeticFunction.moebius xs.prod = (-1 : ℤ) ^ xs.length := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree
      (list_prod_squarefree_of_nodup_primes xs hnodup hprime),
    cardFactors_list_prod_eq_length_of_primes xs hprime]

/-- Every retained branch in a duplicate-free prime universe has squarefree
selected product. -/
theorem mem_oddFirstExitRetainedLeaves_selectedProd_squarefree
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (universe : List ℕ) (huniverse : universe.Nodup)
    (hprime : ∀ p ∈ universe, Nat.Prime p)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd h universe) :
    Squarefree leaf.selected.prod := by
  exact list_prod_squarefree_of_nodup_primes leaf.selected
    (mem_oddFirstExitRetainedLeaves_selected_nodup
      retainOdd h universe huniverse leaf hleaf)
    (mem_oddFirstExitRetainedLeaves_selected_prime
      retainOdd h universe hprime leaf hleaf)

/-- The Möbius value of a retained branch product is exactly its stored
alternating parity sign, before casting to the real-valued polynomial. -/
theorem mem_oddFirstExitRetainedLeaves_moebius_selectedProd
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (universe : List ℕ) (huniverse : universe.Nodup)
    (hprime : ∀ p ∈ universe, Nat.Prime p)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd h universe) :
    ArithmeticFunction.moebius leaf.selected.prod =
      (-1 : ℤ) ^ leaf.selected.length := by
  exact moebius_list_prod_eq_negOnePow_length leaf.selected
    (mem_oddFirstExitRetainedLeaves_selected_nodup
      retainOdd h universe huniverse leaf hleaf)
    (mem_oddFirstExitRetainedLeaves_selected_prime
      retainOdd h universe hprime leaf hleaf)

/-- Two retained root branches in a duplicate-free prime universe with the
same product select exactly the same labels. -/
theorem oddFirstExitRetainedLeaves_selected_eq_of_prod_eq
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (universe : List ℕ) (huniverse : universe.Nodup)
    (hprime : ∀ p ∈ universe, Nat.Prime p)
    (leaf₁ leaf₂ : FirstExitLeaf ℕ)
    (hleaf₁ : leaf₁ ∈ oddFirstExitRetainedLeaves retainOdd h universe)
    (hleaf₂ : leaf₂ ∈ oddFirstExitRetainedLeaves retainOdd h universe)
    (hprod : leaf₁.selected.prod = leaf₂.selected.prod) :
    leaf₁.selected = leaf₂.selected := by
  have hsub₁ : leaf₁.selected.reverse <+ universe :=
    mem_oddFirstExitRetainedLeaves_selected_reverse_sublist
      retainOdd h universe leaf₁ hleaf₁
  have hsub₂ : leaf₂.selected.reverse <+ universe :=
    mem_oddFirstExitRetainedLeaves_selected_reverse_sublist
      retainOdd h universe leaf₂ hleaf₂
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

/-- On retained root leaves of a duplicate-free prime universe, the selected
prime product determines the entire leaf. -/
theorem oddFirstExitRetainedLeaves_eq_of_selected_prod_eq
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (universe : List ℕ) (huniverse : universe.Nodup)
    (hprime : ∀ p ∈ universe, Nat.Prime p)
    (leaf₁ leaf₂ : FirstExitLeaf ℕ)
    (hleaf₁ : leaf₁ ∈ oddFirstExitRetainedLeaves retainOdd h universe)
    (hleaf₂ : leaf₂ ∈ oddFirstExitRetainedLeaves retainOdd h universe)
    (hprod : leaf₁.selected.prod = leaf₂.selected.prod) :
    leaf₁ = leaf₂ := by
  have hselected : leaf₁.selected = leaf₂.selected :=
    oddFirstExitRetainedLeaves_selected_eq_of_prod_eq
      retainOdd h universe huniverse hprime leaf₁ leaf₂ hleaf₁ hleaf₂ hprod
  have hpositive : leaf₁.positive = leaf₂.positive := by
    rw [mem_oddFirstExitRetainedLeaves_positive_eq_evenListLength
        retainOdd h universe leaf₁ hleaf₁,
      mem_oddFirstExitRetainedLeaves_positive_eq_evenListLength
        retainOdd h universe leaf₂ hleaf₂,
      hselected]
  have hmass : leaf₁.mass = leaf₂.mass := by
    rw [mem_oddFirstExitRetainedLeaves_mass_eq_selected_prod
        retainOdd h universe leaf₁ hleaf₁,
      mem_oddFirstExitRetainedLeaves_mass_eq_selected_prod
        retainOdd h universe leaf₂ hleaf₂,
      hselected]
  exact FirstExitLeaf.ext hselected hpositive hmass

/-- The selected-prime product is injective on the actual retained root
leaves.  This is the finite uniqueness input for reindexing the leaf sum by a
single natural modulus. -/
theorem oddFirstExitRetainedLeaves_selectedProd_injOn
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (universe : List ℕ) (huniverse : universe.Nodup)
    (hprime : ∀ p ∈ universe, Nat.Prime p) :
    Set.InjOn (fun leaf : FirstExitLeaf ℕ => leaf.selected.prod)
      {leaf | leaf ∈ oddFirstExitRetainedLeaves retainOdd h universe} := by
  intro leaf₁ hleaf₁ leaf₂ hleaf₂ hprod
  exact oddFirstExitRetainedLeaves_eq_of_selected_prod_eq
    retainOdd h universe huniverse hprime leaf₁ leaf₂ hleaf₁ hleaf₂ hprod

/-- The value of every root leaf is its selected-label product with exactly
the alternating sign determined by the selected-list parity. -/
theorem mem_oddFirstExitRetainedLeaves_value_eq_signed_selected_prod
    {α : Type*} (retainOdd : List α → Bool) (h : α → ℝ)
    (universe : List α) (leaf : FirstExitLeaf α)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd h universe) :
    leaf.value = signedTreeCoefficient (evenListLength leaf.selected)
      (leaf.selected.map h).prod := by
  unfold FirstExitLeaf.value
  rw [mem_oddFirstExitRetainedLeaves_positive_eq_evenListLength
      retainOdd h universe leaf hleaf,
    mem_oddFirstExitRetainedLeaves_mass_eq_selected_prod
      retainOdd h universe leaf hleaf]

/-- On an actual retained branch, the real coefficient is the Möbius value
of the selected squarefree prime product times its local-weight product. -/
theorem mem_oddFirstExitRetainedLeaves_value_eq_moebius_mul_selected_prod
    (retainOdd : List ℕ → Bool) (h : ℕ → ℝ)
    (universe : List ℕ) (huniverse : universe.Nodup)
    (hprime : ∀ p ∈ universe, Nat.Prime p)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ oddFirstExitRetainedLeaves retainOdd h universe) :
    leaf.value =
      (ArithmeticFunction.moebius leaf.selected.prod : ℝ) *
        (leaf.selected.map h).prod := by
  calc
    leaf.value = signedTreeCoefficient (evenListLength leaf.selected)
        (leaf.selected.map h).prod :=
      mem_oddFirstExitRetainedLeaves_value_eq_signed_selected_prod
        retainOdd h universe leaf hleaf
    _ = (-1 : ℝ) ^ leaf.selected.length *
        (leaf.selected.map h).prod :=
      signedTreeCoefficient_evenListLength_eq_negOnePow
        leaf.selected (leaf.selected.map h).prod
    _ = (ArithmeticFunction.moebius leaf.selected.prod : ℝ) *
        (leaf.selected.map h).prod := by
      rw [mem_oddFirstExitRetainedLeaves_moebius_selectedProd
        retainOdd h universe huniverse hprime leaf hleaf]
      simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- The sum of the residual Euler products at all odd first exits. -/
def oddFirstExitCorrection {α : Type*}
    (retainOdd : List α → Bool) (h : α → ℝ) (universe : List α) : ℝ :=
  firstExitCorrection (oddFirstExitPolicy retainOdd) h [] true 1 universe

/-- The manuscript's finite identity in its root form: retained Möbius
polynomial equals the complete Euler product plus the odd-first-exit sum. -/
theorem oddFirstExitRetainedPolynomial_eq_product_add_exits
    {α : Type*} (retainOdd : List α → Bool) (h : α → ℝ)
    (universe : List α) :
    oddFirstExitRetainedPolynomial retainOdd h universe =
      (universe.map fun p => 1 - h p).prod +
        oddFirstExitCorrection retainOdd h universe := by
  simpa [oddFirstExitRetainedPolynomial, oddFirstExitCorrection] using
    firstExitRetainedPolynomial_eq_product_add_correction
      (oddFirstExitPolicy retainOdd) h [] universe true 1

/-- Fully explicit branch-sum form of the manuscript identity. -/
theorem oddFirstExitRetainedLeaves_sum_eq_product_add_exits
    {α : Type*} (retainOdd : List α → Bool) (h : α → ℝ)
    (universe : List α) :
    ((oddFirstExitRetainedLeaves retainOdd h universe).map
        FirstExitLeaf.value).sum =
      (universe.map fun p => 1 - h p).prod +
        oddFirstExitCorrection retainOdd h universe := by
  rw [← oddFirstExitRetainedPolynomial_eq_leaves_sum]
  exact oddFirstExitRetainedPolynomial_eq_product_add_exits
    retainOdd h universe

/-- A product of nonnegative factors indexed by a list is nonnegative. -/
theorem list_prod_nonneg_of_mem {α : Type*} (f : α → ℝ) (xs : List α)
    (hf : ∀ x ∈ xs, 0 ≤ f x) : 0 ≤ (xs.map f).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.prod_cons]
      exact mul_nonneg (hf x (by simp))
        (ih fun y hy => hf y (by simp [hy]))

/-- Every first-exit correction is nonnegative when local weights lie in
`[0,1]` and even-rank prefixes are retained. -/
theorem firstExitCorrection_nonneg_of_even_retained
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (prefix remaining : List α) (positive : Bool) (mass : ℝ)
    (heven : ∀ pre, retained true pre = true)
    (hmass : 0 ≤ mass)
    (hh : ∀ p ∈ remaining, 0 ≤ h p ∧ h p ≤ 1) :
    0 ≤ firstExitCorrection retained h prefix positive mass remaining := by
  induction remaining generalizing prefix positive mass with
  | nil => simp [firstExitCorrection]
  | cons p ps ih =>
      have hp : 0 ≤ h p ∧ h p ≤ 1 := hh p (by simp)
      have hps : ∀ q ∈ ps, 0 ≤ h q ∧ h q ≤ 1 := by
        intro q hq
        exact hh q (by simp [hq])
      have hleft :
          0 ≤ firstExitCorrection retained h prefix positive mass ps :=
        ih prefix positive mass hmass hps
      have hright :
          0 ≤ firstExitCorrection retained h (p :: prefix) (!positive)
            (mass * h p) ps :=
        ih (p :: prefix) (!positive) (mass * h p)
          (mul_nonneg hmass hp.1) hps
      have hprod : 0 ≤ (ps.map fun q => 1 - h q).prod :=
        list_prod_nonneg_of_mem (fun q => 1 - h q) ps
          (fun q hq => sub_nonneg.mpr (hps q hq).2)
      simp only [firstExitCorrection]
      by_cases hr : retained (!positive) (p :: prefix) = true
      · rw [if_pos hr]
        exact add_nonneg hleft hright
      · rw [if_neg hr]
        cases positive with
        | false =>
            exact False.elim (hr (heven (p :: prefix)))
        | true =>
            simpa [signedTreeCoefficient] using
              add_nonneg hleft (mul_nonneg (mul_nonneg hmass hp.1) hprod)

/-- Odd first exits give a nonnegative residual sum. -/
theorem oddFirstExitCorrection_nonneg
    {α : Type*} (retainOdd : List α → Bool) (h : α → ℝ)
    (universe : List α)
    (hh : ∀ p ∈ universe, 0 ≤ h p ∧ h p ≤ 1) :
    0 ≤ oddFirstExitCorrection retainOdd h universe := by
  unfold oddFirstExitCorrection
  exact firstExitCorrection_nonneg_of_even_retained
    (oddFirstExitPolicy retainOdd) h [] universe true 1
    (fun pre => oddFirstExitPolicy_even retainOdd pre) zero_le_one hh

/-- Consequently the retained tree polynomial majorizes the complete Euler
product for every choice of local weights in `[0,1]`. -/
theorem product_le_oddFirstExitRetainedPolynomial
    {α : Type*} (retainOdd : List α → Bool) (h : α → ℝ)
    (universe : List α)
    (hh : ∀ p ∈ universe, 0 ≤ h p ∧ h p ≤ 1) :
    (universe.map fun p => 1 - h p).prod ≤
      oddFirstExitRetainedPolynomial retainOdd h universe := by
  rw [oddFirstExitRetainedPolynomial_eq_product_add_exits]
  exact le_add_of_nonneg_right
    (oddFirstExitCorrection_nonneg retainOdd h universe hh)

/-- Literal divisibility indicator on every integer, including zero and
negative integers. -/
def integerDivisorIndicator (n : ℤ) (p : ℕ) : ℝ :=
  if (p : ℤ) ∣ n then 1 else 0

/-- The complete finite roughness indicator written as an Euler product. -/
def finiteIntegerRoughIndicator (universe : List ℕ) (n : ℤ) : ℝ :=
  (universe.map fun p => 1 - integerDivisorIndicator n p).prod

/-- The Euler product is literally the `0`/`1` indicator that no member of
the finite universe divides `n`.  No positivity hypothesis on `n` is used. -/
theorem finiteIntegerRoughIndicator_eq_indicator
    (universe : List ℕ) (n : ℤ) :
    finiteIntegerRoughIndicator universe n =
      if ∀ p ∈ universe, ¬(p : ℤ) ∣ n then 1 else 0 := by
  induction universe with
  | nil => simp [finiteIntegerRoughIndicator]
  | cons p ps ih =>
      rw [finiteIntegerRoughIndicator, List.map_cons, List.prod_cons]
      change (1 - integerDivisorIndicator n p) *
          finiteIntegerRoughIndicator ps n = _
      rw [ih]
      by_cases hp : (p : ℤ) ∣ n <;>
        simp [integerDivisorIndicator, hp]

/-- Equivalent proposition-level characterization of the finite roughness
indicator. -/
theorem finiteIntegerRoughIndicator_eq_one_iff
    (universe : List ℕ) (n : ℤ) :
    finiteIntegerRoughIndicator universe n = 1 ↔
      ∀ p ∈ universe, ¬(p : ℤ) ∣ n := by
  rw [finiteIntegerRoughIndicator_eq_indicator]
  by_cases hrough : ∀ p ∈ universe, ¬(p : ℤ) ∣ n <;> simp [hrough]

/-- Taking `h(p)=1_{p∣n}` gives the manuscript's pointwise rough-indicator
majorant for every integer `n`, without excluding `0` or negative inputs. -/
theorem finiteIntegerRoughIndicator_le_oddFirstExitRetainedPolynomial
    (retainOdd : List ℕ → Bool) (universe : List ℕ) (n : ℤ) :
    finiteIntegerRoughIndicator universe n ≤
      oddFirstExitRetainedPolynomial retainOdd
        (integerDivisorIndicator n) universe := by
  apply product_le_oddFirstExitRetainedPolynomial
  intro p hp
  by_cases hpn : (p : ℤ) ∣ n <;>
    simp [integerDivisorIndicator, hpn]

/-- The pointwise majorant with the roughness indicator displayed explicitly,
matching the manuscript's statement for every integer. -/
theorem integerRoughIndicator_le_oddFirstExitRetainedPolynomial
    (retainOdd : List ℕ → Bool) (universe : List ℕ) (n : ℤ) :
    (if ∀ p ∈ universe, ¬(p : ℤ) ∣ n then 1 else 0 : ℝ) ≤
      oddFirstExitRetainedPolynomial retainOdd
        (integerDivisorIndicator n) universe := by
  rw [← finiteIntegerRoughIndicator_eq_indicator]
  exact finiteIntegerRoughIndicator_le_oddFirstExitRetainedPolynomial
    retainOdd universe n

end

end ImbalancedChen
