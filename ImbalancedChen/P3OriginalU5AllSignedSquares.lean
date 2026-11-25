import ImbalancedChen.P3OriginalU5AllSourceSquares
import ImbalancedChen.P3OriginalU5FreshFifthSquareSupplier

/-!
# Every actual U5 source to complete signed square support

SOURCE ONLY / UNCOMPILED / NO KERNEL ACCEPTANCE.

The original nonzero native rho supplies its own actual factor witness.
All short/inherited/fresh cases use the preceding all-source square
supplier. The already proved carrier facts and signed-small extension
are reused; neither the rough-tail nor the small-factor proof is repeated.

The complete word is supported at the SAME last source's once-buffered
auxiliary cover. This does not change its coefficient, density, physical
common Q, or replace a factorization parameter by the carrier bound .599.
No full (F), W adoption, three-factor reconstruction or PP is asserted.

Compatibility: public-receiver-helpers.patch exposes the four old PairRange
helpers used by the imported all-source module. The adjacent
public-native-carrier-helpers.patch only makes original_word_data and
integer_gates_mono public in the frozen fresh-fifth source; proof bodies
remain byte for byte unchanged. Neither patch is applied by this snapshot.
-/

namespace ImbalancedChen.P3OriginalU5AllSignedSquares

noncomputable section
open scoped Classical List
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairRootRoughProducer P2OriginalSelectedPairNativeData
open P2OriginalPairSourceReceiver
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalSelectedIntegerPrefixSquares
open P2OriginalSelectedNativeSmallExtension
open P2OriginalSelectedFifthRoughBudget (original_U5_small_head)
open P3OriginalU5AllSourceSquares
open P5OriginalU5CausalFinite
open P5OriginalU5PlateauPrimeBV (fullModulus)

/-- The root keeps its original level; a fresh row keeps its original
    affine source and code. Only the second support buffer is paid. -/
def sourceCover (R : PairRange) {mesh : ℕ} (buffer : ℚ)
    (N : ℕ) (t : ℕ × ℕ) : Origin mesh → ℝ
  | .root => rootLevel false N t - (buffer : ℝ)
  | .row _ code branch _ => (rowCap R code buffer branch : ℝ)

theorem source_cover_identity (R : PairRange) {mesh : ℕ} (buffer : ℚ)
    (N : ℕ) (t : ℕ × ℕ) (source : Origin mesh) :
    originCap R (2 * buffer) (rootSeed false buffer N t) source + (buffer : ℝ) =
      sourceCover R buffer N t source := by
  cases source with
  | root => simp only [originCap, sourceCover, rootSeed]; ring
  | row rank code branch p =>
      simp only [originCap, sourceCover, rowCap, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]
      ring

structure SignedSupply (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (epsilon : ℝ) (N : ℕ) (t : ℕ × ℕ) (k s : ℕ)
    (chosen : List ℕ) (source : Origin mesh) (slots : List (ℕ × Bool)) : Prop where
  rough : IntegerSupply R bank (2 * buffer) (rootSeed false buffer N t)
    N t chosen source slots
  full : IntegerSquareGates N (sourceCover R buffer N t source) 1
    ((appendUnselected slots s.primeFactorsList.reverse).map Prod.fst)
  selected : IntegerSquareGates N (sourceCover R buffer N t source)
    (selectedPrimes (appendUnselected slots s.primeFactorsList.reverse)).prod
    (remainingPrimes (appendUnselected slots s.primeFactorsList.reverse))
  mask_preserved : selectedPrimes (appendUnselected slots s.primeFactorsList.reverse) =
    selectedPrimes (originSlots t source)
  canonical : (appendUnselected slots s.primeFactorsList.reverse).map Prod.fst =
    (fullModulus t k).primeFactorsList.reverse
  same_rho : rho N epsilon (selectedPolicy R bank buffer false N t) k =
    P5CausalRhoFactorization.coefficient (selectedPolicy R bank buffer false N t)
      N (Nat.ceil (cutoff N)) (smallCutoff N epsilon) (cutoff N) (smallLevel N epsilon)
      (s, chosen.prod)

private theorem attach_original_small
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : 0 ≤ buffer)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1/8)
    (hgrid : (R.epsilon : ℝ) ≤ attachmentNu * epsilon ^ 2)
    (halloc : attachmentNu * epsilon ≤ (buffer : ℝ))
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    {k s : ℕ} (hk : rho N epsilon (selectedPolicy R bank buffer false N t) k ≠ 0)
    (hs : s ∈ actualSmallRosserSupport N (Nat.ceil (cutoff N)) (smallCutoff N epsilon))
    (chosen : List ℕ) (hkprod : k = s * chosen.prod)
    (hsub : chosen <+ roughPrimeUniverse N (Nat.ceil (cutoff N))
      (smallCutoff N epsilon) (cutoff N))
    (haccept : (actualTrace R bank (2 * buffer) (rootSeed false buffer N t)
      N t chosen).accepted = true)
    (source : Origin mesh) (slots : List (ℕ × Bool))
    (rough : IntegerSupply R bank (2 * buffer) (rootSeed false buffer N t)
      N t chosen source slots) :
    SignedSupply R bank buffer epsilon N t k s chosen source slots := by
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hd := P3OriginalU5FreshFifthSquareSupplier.original_word_data
    R epsilon hepsilon hepsilon8 hgrid hN ht hsub
  have hr : chosen.prod ∈ fixedEvenRoughSupport (selectedPolicy R bank buffer false N t)
      N (Nat.ceil (cutoff N)) (smallCutoff N epsilon) (cutoff N) := by
    apply (pair_policy_support_iff
      (pairPlan R bank (2 * buffer) (rootSeed false buffer N t))
      (R.epsilon : ℝ) (ceiling : ℝ) (rootSeed false buffer N t)
      N (Nat.ceil (cutoff N)) t (smallCutoff N epsilon) (cutoff N) _).mpr
    exact ⟨chosen, hsub, haccept, rfl⟩
  have hpairs : (s, chosen.prod) ∈ P5CausalRhoFactorization.pairs
      (selectedPolicy R bank buffer false N t) N (Nat.ceil (cutoff N))
      (smallCutoff N epsilon) (cutoff N) := Finset.mem_product.mpr ⟨hs, hr⟩
  have hvalue := P5CausalRhoFactorization.rho_at_pair
    (selectedPolicy R bank buffer false N t) N (Nat.ceil (cutoff N))
    (smallCutoff N epsilon) (cutoff N) (smallLevel N epsilon) hpairs
  have hactive : (s, chosen.prod) ∈ P5CausalRhoFactorization.activePairs
      (selectedPolicy R bank buffer false N t) N (Nat.ceil (cutoff N))
      (smallCutoff N epsilon) (cutoff N) (smallLevel N epsilon) := by
    apply Finset.mem_filter.mpr
    refine ⟨hpairs, ?_⟩
    rw [← hvalue, ← hkprod]
    exact hk
  have hprod : (slots.map Prod.fst).prod = (t.1 * t.2) * chosen.prod := by
    rw [rough.values]
    simp only [List.prod_cons]
    ac_rfl
  have hprime : ∀ p ∈ slots.map Prod.fst, 1 < p := by
    intro p hp
    rw [rough.values] at hp
    exact (hd.1 p hp).one_lt
  have hne : slots.map Prod.fst ≠ [] := by rw [rough.values]; simp
  have hBr := integerSquareGates_product_lt (slots.map Prod.fst)
    (by decide : 0 < (1 : ℕ)) hprime hne rough.full
  simp only [Nat.one_mul] at hBr
  have hL := P2OriginalPairBufferedRootProvenance.fifth_native_small_level_budget
    hNr epsilon buffer halloc
  have hcover : (actualTrace R bank (2 * buffer) (rootSeed false buffer N t)
      N t chosen).cap + (buffer : ℝ) = sourceCover R buffer N t source := by
    rw [rough.cap]
    exact source_cover_identity R buffer N t source
  have hbudget : ((slots.map Prod.fst).prod : ℝ) * smallLevel N epsilon <
      (N : ℝ) ^ sourceCover R buffer N t source := by
    calc
      _ ≤ ((slots.map Prod.fst).prod : ℝ) * (N : ℝ) ^ (buffer : ℝ) :=
        mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg _)
      _ < (N : ℝ) ^ (actualTrace R bank (2 * buffer) (rootSeed false buffer N t)
          N t chosen).cap * (N : ℝ) ^ (buffer : ℝ) :=
        mul_lt_mul_of_pos_right hBr (Real.rpow_pos_of_pos (zero_lt_one.trans hNr) _)
      _ = _ := by rw [← Real.rpow_add (zero_lt_one.trans hNr), hcover]
  have hlevels : (actualTrace R bank (2 * buffer) (rootSeed false buffer N t)
      N t chosen).cap ≤ sourceCover R buffer N t source := by
    have hbR : 0 ≤ (buffer : ℝ) := by exact_mod_cast hb
    linarith [hcover]
  have hfull := P3OriginalU5FreshFifthSquareSupplier.integer_gates_mono
    hNr hlevels _ rough.full
  have hselected := P3OriginalU5FreshFifthSquareSupplier.integer_gates_mono
    hNr hlevels _ rough.selected
  have hsmall := actual_signed_small_extension
    (selectedPolicy R bank buffer false N t) N (Nat.ceil (cutoff N)) (t.1 * t.2)
    (smallCutoff N epsilon) (cutoff N) (smallLevel N epsilon)
    (sourceCover R buffer N t source)
    hactive (original_U5_small_head hNr hepsilon.le hepsilon8.le)
    slots hprod
    (by rw [rough.values]; exact hd.1)
    (by rw [rough.values]; exact hd.2.1)
    (by rw [rough.values]; exact hd.2.2.1)
    hfull hselected (by rw [← hprod]; exact hbudget.le)
  refine ⟨rough, hsmall.1, hsmall.2.1, ?_, ?_, ?_⟩
  · exact hsmall.2.2.1.trans
      (provenance_mask R bank (2 * buffer) (rootSeed false buffer N t) N t rough.provenance)
  · have heq : ((t.1 * t.2) * chosen.prod) * s = fullModulus t k := by
      rw [hkprod]
      simp only [fullModulus, P5OriginalU5PlateauPrimeBV.markedProduct]
      ac_rfl
    simpa only [heq] using hsmall.2.2.2.1
  · rw [hkprod]
    exact hsmall.2.2.2.2

/-- The literal native U5 rho now supplies its complete canonical word's
    full and selected-complement square lists on EVERY actual source case.
    The only allocations are original scalar precision/buffer inequalities;
    no incoming square, cap identity, small budget or fresh branch is assumed. -/
theorem native_U5_nonzero_all_signed_squares
    (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (buffer : ℚ) (hb : 0 ≤ buffer) (hb' : buffer ≤ 1/1000)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1/8)
    (hgrid : (R.epsilon : ℝ) ≤ attachmentNu * epsilon ^ 2)
    (halloc : attachmentNu * epsilon ≤ (buffer : ℝ))
    {N : ℕ} (hN : 2 ≤ N) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) {k : ℕ}
    (hk : rho N epsilon (selectedPolicy R bank buffer false N t) k ≠ 0) :
    ∃ s ∈ actualSmallRosserSupport N (Nat.ceil (cutoff N)) (smallCutoff N epsilon),
      ∃ chosen : List ℕ,
        chosen <+ roughPrimeUniverse N (Nat.ceil (cutoff N))
          (smallCutoff N epsilon) (cutoff N) ∧ k = s * chosen.prod ∧
        (actualTrace R bank (2 * buffer) (rootSeed false buffer N t) N t chosen).accepted = true ∧
        ∃ source slots, SignedSupply R bank buffer epsilon N t k s chosen source slots := by
  obtain ⟨s, hs, chosen, hsub, hkprod, haccept, source, slots, rough⟩ :=
    native_U5_nonzero_all_source_squares R bank buffer hb' epsilon hgrid hN ht hk
  exact ⟨s, hs, chosen, hsub, hkprod, haccept, source, slots,
    attach_original_small R bank buffer hb epsilon hepsilon hepsilon8 hgrid halloc
      hN ht hk hs chosen hkprod hsub haccept source slots rough⟩

end
end ImbalancedChen.P3OriginalU5AllSignedSquares
