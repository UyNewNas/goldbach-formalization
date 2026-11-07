import ImbalancedChen.P5OriginalH3Cell00PhysicalBoxBinding
import ImbalancedChen.RetainedModuli
import ImbalancedChen.SmallRoughAttachment
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The local H3 contribution is a restriction of the ACTUAL small/rough rho.
A local q is defined by its small factor and a retained rough root leaf
whose own eighth ancestor belongs to the previously proved H3 box.
Cutoff-separated factorization and retained-prime-product injectivity prove
that this small-factor/leaf pair is unique. Thus local rho equals global
rho on this exact q-image and zero outside it, with no multiplicity factor.

The rough leaves are those of oddFirstExitPolicy retainOdd, precisely as
fixedRoughSupport and actualSmallRoughRho are defined. No unproved equality
with an arbitrary Bool-valued policy is used. The final specialization
sets retainOdd to physicalPolicy ... false, the exact physicalRho lookup.
This finite identity does not construct the global causal cap supplier.
-/

namespace ImbalancedChen.P5OriginalH3LocalPhysicalQFibre

noncomputable section
open scoped Classical BigOperators
open P5OriginalAdoptedEighthPhysicalMasks
open P5OriginalH3Cell00StrictOldPlanes
open P5OriginalH3Cell00PhysicalBoxBinding

abbrev Pair := ℕ × FirstExitLeaf ℕ

def eighthAncestor (leaf : FirstExitLeaf ℕ) : List ℕ :=
  rosserAncestor 8 leaf.selected

/-- Local selection is a property of this very leaf's causal ancestor,
not an unrelated history conjoined with a global modulus assertion. -/
def H3Leaf (N : ℕ) (lambda3 lambda6 : List ℕ → ℝ)
    (leaf : FirstExitLeaf ℕ) : Prop :=
  let pre := eighthAncestor leaf
  8 ≤ leaf.selected.length ∧
  InBox (primeHistoryLogCoordinates (N : ℝ) 8 pre) ∧
  (567 / 1000 : ℝ) ≤ lambda3 (rosserAncestor 3 pre) ∧
  (596 / 1000 : ℝ) ≤ lambda6 (rosserAncestor 6 pre) ∧
  lambda3 (rosserAncestor 3 pre) ≤ lambda6 (rosserAncestor 6 pre) ∧
  lambda6 (rosserAncestor 6 pre) ≤
    oldComparison slot (primeHistoryLogCoordinates (N : ℝ) 8 pre)

/-- The unit-weight root leaves used by the literal physical coefficient. -/
def localLeaves (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) : Finset (FirstExitLeaf ℕ) :=
  ((oddFirstExitRetainedLeaves retainOdd (fun _ => 1)
    (roughPrimeUniverse N cap w z)).toFinset).filter (H3Leaf N lambda3 lambda6)

@[simp] theorem mem_localLeaves
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) (leaf : FirstExitLeaf ℕ) :
    leaf ∈ localLeaves retainOdd N cap w z lambda3 lambda6 ↔
      leaf ∈ oddFirstExitRetainedLeaves retainOdd (fun _ => 1)
        (roughPrimeUniverse N cap w z) ∧ H3Leaf N lambda3 lambda6 leaf := by
  simp [localLeaves]

/-- Local rough products retain the original root leaf's arithmetic sign. -/
def localRough (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) : Finset ℕ :=
  (localLeaves retainOdd N cap w z lambda3 lambda6).image
    (fun leaf => leaf.selected.prod)

theorem localRough_subset_fixed
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) :
    localRough retainOdd N cap w z lambda3 lambda6 ⊆
      fixedRoughSupport retainOdd N cap w z := by
  intro d hd
  rcases Finset.mem_image.mp hd with ⟨leaf, hleaf, rfl⟩
  exact selectedProd_mem_oddFirstExitRetainedModuli retainOdd (fun _ => 1)
    (roughPrimeUniverse N cap w z) leaf ((mem_localLeaves _ _ _ _ _ _ _ _).mp hleaf).1

def localPairs (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) : Finset Pair :=
  actualSmallRosserSupport N cap w ×ˢ localLeaves retainOdd N cap w z lambda3 lambda6

def pairModulus (x : Pair) : ℕ := x.1 * x.2.selected.prod

def localModuli (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) : Finset ℕ :=
  (localPairs retainOdd N cap w z lambda3 lambda6).image pairModulus

def atom (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (x : Pair) : ℝ :=
  smallRoughPairCoefficient (fixedRoughCoefficient retainOdd N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)
    (x.1, x.2.selected.prod)

/-- This is an actual local coefficient, indexed by the local leaf's q. -/
def localRho (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) : ℕ → ℝ :=
  smallRoughRho (actualSmallRosserSupport N cap w)
    (localRough retainOdd N cap w z lambda3 lambda6)
    (fixedRoughCoefficient retainOdd N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)

private theorem local_leaf_fixed_mem
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) {leaf : FirstExitLeaf ℕ}
    (hl : leaf ∈ localLeaves retainOdd N cap w z lambda3 lambda6) :
    leaf.selected.prod ∈ fixedRoughSupport retainOdd N cap w z := by
  apply localRough_subset_fixed retainOdd N cap w z lambda3 lambda6
  exact Finset.mem_image.mpr ⟨leaf, hl, rfl⟩

/-- The physical q determines both the small factor AND the complete
retained rough leaf, including its own eighth ancestor. -/
theorem pairModulus_injOn
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) :
    Set.InjOn pairModulus (localPairs retainOdd N cap w z lambda3 lambda6) := by
  intro x hx y hy hq
  rcases Finset.mem_product.mp hx with ⟨hxs, hxl⟩
  rcases Finset.mem_product.mp hy with ⟨hys, hyl⟩
  have hxr := local_leaf_fixed_mem retainOdd N cap w z lambda3 lambda6 hxl
  have hyr := local_leaf_fixed_mem retainOdd N cap w z lambda3 lambda6 hyl
  have hab : (x.1, x.2.selected.prod) = (y.1, y.2.selected.prod) :=
    smallRough_factorization_unique
      (actualSmallRosserSupport_smallPrimeSupportedAt N cap w hxs)
      (fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hxr)
      (actualSmallRosserSupport_smallPrimeSupportedAt N cap w hys)
      (fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hyr) hq
  have ha : x.1 = y.1 := congrArg Prod.fst hab
  have hd : x.2.selected.prod = y.2.selected.prod := congrArg Prod.snd hab
  have hleaf : x.2 = y.2 :=
    oddFirstExitRetainedLeaves_eq_of_selected_prod_eq retainOdd (fun _ => 1)
      (roughPrimeUniverse N cap w z) (roughPrimeUniverse_nodup N cap w z)
      (fun _ hp => mem_roughPrimeUniverse_prime hp) x.2 y.2
      ((mem_localLeaves _ _ _ _ _ _ _ _).mp hxl).1
      ((mem_localLeaves _ _ _ _ _ _ _ _).mp hyl).1 hd
  exact Prod.ext ha hleaf

/-- The leaf image is exactly the natural-number small/local-rough
carrier, rather than merely a subset of the global support. -/
theorem localModuli_eq_smallRoughModuli
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) :
    localModuli retainOdd N cap w z lambda3 lambda6 =
      smallRoughModuli (actualSmallRosserSupport N cap w)
        (localRough retainOdd N cap w z lambda3 lambda6) := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨x, hx, rfl⟩
    rcases Finset.mem_product.mp hx with ⟨ha, hl⟩
    exact Finset.mem_image.mpr ⟨(x.1, x.2.selected.prod),
      Finset.mem_product.mpr ⟨ha, Finset.mem_image.mpr ⟨x.2, hl, rfl⟩⟩, rfl⟩
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨⟨a, d⟩, had, hq⟩
    rcases Finset.mem_product.mp had with ⟨ha, hd⟩
    rcases Finset.mem_image.mp hd with ⟨leaf, hl, hprod⟩
    apply Finset.mem_image.mpr
    refine ⟨(a, leaf), Finset.mem_product.mpr ⟨ha, hl⟩, ?_⟩
    change a * leaf.selected.prod = q
    rw [hprod]
    exact hq

theorem localRho_pairModulus
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) (x : Pair)
    (hx : x ∈ localPairs retainOdd N cap w z lambda3 lambda6) :
    localRho retainOdd N cap w z L lambda3 lambda6 (pairModulus x) =
      atom retainOdd N cap w z L x := by
  rcases Finset.mem_product.mp hx with ⟨ha, hl⟩
  exact smallRoughRho_mul
    (fun _ hs => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hs)
    (fun _ hr => fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z
      (localRough_subset_fixed retainOdd N cap w z lambda3 lambda6 hr))
    (fixedRoughCoefficient retainOdd N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)
    ha (Finset.mem_image.mpr ⟨x.2, hl, rfl⟩)

theorem globalRho_pairModulus
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) (x : Pair)
    (hx : x ∈ localPairs retainOdd N cap w z lambda3 lambda6) :
    actualSmallRoughRho retainOdd N cap w z L (pairModulus x) =
      atom retainOdd N cap w z L x := by
  rcases Finset.mem_product.mp hx with ⟨ha, hl⟩
  exact smallRoughRho_mul
    (fun _ hs => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hs)
    (fun _ hr => fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hr)
    (fixedRoughCoefficient retainOdd N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)
    ha (local_leaf_fixed_mem retainOdd N cap w z lambda3 lambda6 hl)

/-- The sign and the small beta choice are those of this same retained
leaf. In particular a negative leaf uses betaMinus, without a new sign
hypothesis or an independent local coefficient. -/
theorem atom_eq_signed_leaf_beta
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) (x : Pair)
    (hx : x ∈ localPairs retainOdd N cap w z lambda3 lambda6) :
    atom retainOdd N cap w z L x =
      signedTreeCoefficient x.2.positive 1 *
        (if x.2.positive then actualSmallRosserPlus N cap w L x.1
         else actualSmallRosserMinus N cap w L x.1) := by
  have hl := ((mem_localLeaves _ _ _ _ _ _ _ _).mp
    (Finset.mem_product.mp hx).2).1
  have hm : x.2.mass = 1 := by
    simpa using mem_oddFirstExitRetainedLeaves_mass_eq_selected_prod retainOdd
      (fun _ => 1) (roughPrimeUniverse N cap w z) x.2 hl
  have hc : fixedRoughCoefficient retainOdd N cap w z x.2.selected.prod =
      x.2.value := by
    have hv := mem_oddFirstExitRetainedLeaves_value_eq_coefficient_mul_primeFactors
      retainOdd (fun _ => 1) (roughPrimeUniverse N cap w z)
      (roughPrimeUniverse_nodup N cap w z)
      (fun _ hp => mem_roughPrimeUniverse_prime hp) x.2 hl
    simpa [fixedRoughCoefficient] using hv.symm
  unfold atom smallRoughPairCoefficient signAttachedCoefficient
  rw [hc]
  cases hp : x.2.positive <;>
    simp [FirstExitLeaf.value, signedTreeCoefficient, hp, hm]

/-- Exact localization of the actual signed coefficient. It is neither
an unrelated q nor a separately assumed coefficient identity. -/
theorem localRho_eq_masked_global
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) (q : ℕ) :
    localRho retainOdd N cap w z L lambda3 lambda6 q =
      if q ∈ localModuli retainOdd N cap w z lambda3 lambda6 then
        actualSmallRoughRho retainOdd N cap w z L q else 0 := by
  by_cases hq : q ∈ localModuli retainOdd N cap w z lambda3 lambda6
  · rcases Finset.mem_image.mp hq with ⟨x, hx, hprod⟩
    rw [if_pos hq, ← hprod, localRho_pairModulus retainOdd N cap w z L
      lambda3 lambda6 x hx, globalRho_pairModulus retainOdd N cap w z L
      lambda3 lambda6 x hx]
  · rw [if_neg hq]
    exact smallRoughRho_eq_zero_of_not_mem _ _ _ _ _
      (by simpa only [← localModuli_eq_smallRoughModuli] using hq)

/-- Any arithmetic test, including a signed AP count minus its exact
coprime mean, is reindexed by the unique local small-factor/leaf pair. -/
theorem local_signed_test_eq_pairs
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) (F : ℕ → ℝ) :
    (∑ q ∈ localModuli retainOdd N cap w z lambda3 lambda6,
      localRho retainOdd N cap w z L lambda3 lambda6 q * F q) =
    ∑ x ∈ localPairs retainOdd N cap w z lambda3 lambda6,
      atom retainOdd N cap w z L x * F (pairModulus x) := by
  unfold localModuli
  rw [Finset.sum_image (pairModulus_injOn retainOdd N cap w z lambda3 lambda6)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [localRho_pairModulus retainOdd N cap w z L lambda3 lambda6 x hx]

/-- An active local pair uses the original strict small-prime level. -/
theorem active_pair_small_lt_level
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (x : Pair)
    (hx : atom retainOdd N cap w z L x ≠ 0) : (x.1 : ℝ) < L := by
  unfold atom smallRoughPairCoefficient signAttachedCoefficient at hx
  have hb := (mul_ne_zero_iff.mp hx).2
  by_cases hc : 0 ≤ fixedRoughCoefficient retainOdd N cap w z x.2.selected.prod
  · rw [if_pos hc] at hb
    exact (actualSmallRosserPlus_active hb).2.1
  · rw [if_neg hc] at hb
    exact (actualSmallRosserMinus_active hb).2.1

/-- The active physical modulus determines a unique local root leaf and
therefore a unique ancestor carrying the H3 mask and raised exponent. -/
theorem active_q_unique_local_fibre
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) (q : ℕ)
    (hq : localRho retainOdd N cap w z L lambda3 lambda6 q ≠ 0) :
    ∃! x : Pair,
      x ∈ localPairs retainOdd N cap w z lambda3 lambda6 ∧
      pairModulus x = q ∧ (x.1 : ℝ) < L ∧
      actualSmallRoughRho retainOdd N cap w z L q = atom retainOdd N cap w z L x ∧
      ∃ h : adoptedGuard (N : ℝ) lambda3 lambda6 (eighthAncestor x.2),
        selectedMask (Classical.choose h) = mask138 ∧
        raisedExponent (N : ℝ) lambda3 lambda6 (eighthAncestor x.2) =
          newCap slot (primeHistoryLogCoordinates (N : ℝ) 8 (eighthAncestor x.2)) := by
  have hmem : q ∈ localModuli retainOdd N cap w z lambda3 lambda6 := by
    by_contra hn
    rw [localRho_eq_masked_global retainOdd N cap w z L lambda3 lambda6 q,
      if_neg hn] at hq
    exact hq rfl
  rcases Finset.mem_image.mp hmem with ⟨x, hx, hprod⟩
  have ha : atom retainOdd N cap w z L x ≠ 0 := by
    rw [← localRho_pairModulus retainOdd N cap w z L lambda3 lambda6 x hx, hprod]
    exact hq
  have hleaf := ((mem_localLeaves _ _ _ _ _ _ _ _).mp
    (Finset.mem_product.mp hx).2).2
  rcases hleaf with ⟨hlen, hbox, hthird, hcurrent, hmono, hupper⟩
  obtain ⟨hg, hmask, hcap, _⟩ := actual_h3_guard_and_choice
    (N : ℝ) lambda3 lambda6 (eighthAncestor x.2)
    hbox hthird hcurrent hmono hupper
  refine ⟨x, ⟨hx, hprod, active_pair_small_lt_level retainOdd N cap w z L x ha,
    ?_, hg, hmask, hcap⟩, ?_⟩
  · rw [← hprod]
    exact globalRho_pairModulus retainOdd N cap w z L lambda3 lambda6 x hx
  · intro y hy
    exact pairModulus_injOn retainOdd N cap w z lambda3 lambda6 hy.1 hx
      (hy.2.1.trans hprod.symm)

/-- Final specialization uses exactly the corrected-parent physicalRho,
without replacing its oddified root topology by an unproved full policy. -/
theorem physical_h3_local_rho
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z L : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) (q : ℕ) :
    let retainOdd := (P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega
      (N : ℝ) lambda3 lambda6) false
    localRho retainOdd N cap w z L lambda3 lambda6 q =
      if q ∈ localModuli retainOdd N cap w z lambda3 lambda6 then
        P5OriginalPhaseBPhysicalBinding.physicalRho e chi m omega N cap
          w z L lambda3 lambda6 q else 0 := by
  dsimp only
  exact localRho_eq_masked_global _ N cap w z L lambda3 lambda6 q

end
end ImbalancedChen.P5OriginalH3LocalPhysicalQFibre
