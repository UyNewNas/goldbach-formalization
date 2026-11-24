import ImbalancedChen.P1OriginalFinalPolicyStructure
import ImbalancedChen.P4AOriginalFiniteFallbackRankReads
import ImbalancedChen.P2LowerCanonicalRetainedTrace

set_option autoImplicit false

/-!
RECONSTRUCTED P1 OUTPUT / SOURCE ONLY / NOT COMPILED OR KERNEL ACCEPTED.

This is a new thin export, not a recovered copy of the unavailable earlier
file. No earlier source hash or formal-verification credit is asserted.

The existing canonical-word theorem and finite rank-reading program are
applied only to a modulus in the actual rough carrier. A physical modulus
is first decomposed into its small and rough factors; ancestor assertions
then concern the rough factor. The physical modulus itself is never silently
treated as an all-rough prime word. The omega-to-zero policy transport uses
the actual lower bound on every prime in the ancestor. All selectors, caps,
stage indices, polarities and the literal final policy are preserved.
-/

namespace ImbalancedChen.P1OriginalFinalPolicyAncestorReads

noncomputable section
open scoped Classical List
open P4AOriginalFiniteAll22RawLedger (finalPolicy)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalNewFifthUnion (data)
open P4AFallbackCanonicalBanks (bank)
open P4AUpperTaggedParityCompiler («universe»)
open P4AOrderedThirdRectangleRate (index position)
open P4AOrderedThirdRankReads (admit)
open P4AOriginalFiniteFallbackPrograms (code)
open P4AFull87ActualAffineDeletion (coords)

/-- The canonical decreasing word is an actual subword of the rough universe. -/
theorem actual_rough_word (N cap : ℕ) (w z : ℝ) (x : ℕ)
    (hx : x ∈ «universe» N cap w z) :
    x.primeFactorsList.reverse <+ roughPrimeUniverse N cap w z ∧
      x.primeFactorsList.reverse.prod = x :=
  P2LowerCanonicalRetainedTrace.canonical_subword_of_universe N cap w z hx

/-- Every prime in an actual rough ancestor retains the original lower cutoff. -/
theorem rough_ancestor_lower (N cap : ℕ) (w z : ℝ) (x : ℕ)
    (hx : x ∈ «universe» N cap w z) (k : ℕ) :
    ∀ p ∈ rosserAncestor k x.primeFactorsList, w ≤ (p : ℝ) := by
  have hs := (actual_rough_word N cap w z x hx).1
  intro p hp
  have hp' : p ∈ x.primeFactorsList := List.mem_of_mem_drop hp
  have hp'' : p ∈ x.primeFactorsList.reverse := List.mem_reverse.mpr hp'
  exact mem_roughPrimeUniverse_lower (hs.subset hp'')

/-- The physical carrier is decomposed before any ancestor is read. -/
theorem physical_modulus_factors (N : ℕ) (omega : ℝ) (v : ℕ)
    (hv : v ∈ moduli N ((N : ℝ) ^ omega)) :
    ∃ s x : ℕ, s ∈ actualSmallRosserSupport N N ((N : ℝ) ^ omega) ∧
      x ∈ «universe» N N ((N : ℝ) ^ omega) (cutoff N) ∧ v = s * x := by
  obtain ⟨⟨s, x⟩, hsx, hprod⟩ := Finset.mem_image.mp hv
  obtain ⟨hs, hx⟩ := Finset.mem_product.mp hsx
  exact ⟨s, x, hs, hx, hprod.symm⟩

/-- Small/rough decomposition is unique on this same physical carrier. -/
theorem physical_modulus_factors_unique (N : ℕ) (omega : ℝ) {s x s' x' : ℕ}
    (hs : s ∈ actualSmallRosserSupport N N ((N : ℝ) ^ omega))
    (hx : x ∈ «universe» N N ((N : ℝ) ^ omega) (cutoff N))
    (hs' : s' ∈ actualSmallRosserSupport N N ((N : ℝ) ^ omega))
    (hx' : x' ∈ «universe» N N ((N : ℝ) ^ omega) (cutoff N))
    (h : s * x = s' * x') : s = s' ∧ x = x' :=
  P4AUpperTaggedBetaAttachment.product_unique N N ((N : ℝ) ^ omega) (cutoff N)
    hs hx hs' hx' h

/-- Runtime-cut transport is restricted to an ancestor in the actual rough word. -/
theorem final_policy_cut_on_ancestor (m r n : ℕ) (e : ℚ) (q : ℕ)
    (a omega : ℝ) (N : ℕ) (hN : 1 ≤ N) (homega : 0 ≤ omega)
    (x : ℕ) (hx : x ∈ «universe» N N ((N : ℝ) ^ omega) (cutoff N)) (k : ℕ) :
    finalPolicy m r n e q a omega N false (rosserAncestor k x.primeFactorsList) =
      finalPolicy m r n e q a 0 N false (rosserAncestor k x.primeFactorsList) :=
  P4AOriginalFiniteFallbackPolicy.policy_cut (bank m) (width r) n (data e q a)
    hN homega (rosserAncestor k x.primeFactorsList)
    (rough_ancestor_lower N N ((N : ℝ) ^ omega) (cutoff N) x hx k)

/-- The literal final policy reads the existing finite program at its actual ancestor. -/
theorem final_policy_reads_actual_ancestor (m r n : ℕ) (e : ℚ) (q : ℕ)
    (a omega : ℝ) (N : ℕ) (hN : 1 < N) (homega : 0 ≤ omega)
    (x : ℕ) (hx : x ∈ «universe» N N ((N : ℝ) ^ omega) (cutoff N))
    (k : ℕ) (hk : k ≤ x.primeFactorsList.length) (ho : polarityAfter true k = false) :
    index (position k) + 1 ≤ k ∧
      finalPolicy m r n e q a omega N false (rosserAncestor k x.primeFactorsList) =
        admit N ((code (bank m) (width r) n (data e q a) (position k)).eval
          (coords N _ x.primeFactorsList.reverse)) (rosserAncestor k x.primeFactorsList) := by
  obtain ⟨hindex, hread⟩ := P4AOriginalFiniteFallbackRankReads.read
    (bank m) (width r) (width_pos r) n (data e q a) N N hN
    ((N : ℝ) ^ omega) (cutoff N) x hx k hk ho
  refine ⟨hindex, ?_⟩
  exact (final_policy_cut_on_ancestor m r n e q a omega N hN.le homega x hx k).trans hread

/-- A physical carrier element is split into its small and rough factors;
the same ancestor-read theorem is then applied only to its rough factor. -/
theorem physical_modulus_ancestor_reads (m r n : ℕ) (e : ℚ) (q : ℕ)
    (a omega : ℝ) (N : ℕ) (hN : 1 < N) (homega : 0 ≤ omega)
    (v : ℕ) (hv : v ∈ moduli N ((N : ℝ) ^ omega)) :
    ∃ s x : ℕ, s ∈ actualSmallRosserSupport N N ((N : ℝ) ^ omega) ∧
      x ∈ «universe» N N ((N : ℝ) ^ omega) (cutoff N) ∧ v = s * x ∧
      ∀ k : ℕ, k ≤ x.primeFactorsList.length → polarityAfter true k = false →
        index (position k) + 1 ≤ k ∧
          finalPolicy m r n e q a omega N false (rosserAncestor k x.primeFactorsList) =
            admit N ((code (bank m) (width r) n (data e q a) (position k)).eval
              (coords N _ x.primeFactorsList.reverse)) (rosserAncestor k x.primeFactorsList) := by
  obtain ⟨s, x, hs, hx, hprod⟩ := physical_modulus_factors N omega v hv
  refine ⟨s, x, hs, hx, hprod, ?_⟩
  intro k hk ho
  exact final_policy_reads_actual_ancestor m r n e q a omega N hN homega x hx k hk ho

end
end ImbalancedChen.P1OriginalFinalPolicyAncestorReads
