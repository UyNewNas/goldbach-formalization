import ImbalancedChen.P4AOriginalFiniteAll22RawLedger
import ImbalancedChen.P4AOriginalFiniteFallbackRankReads
import ImbalancedChen.P4AOriginalFiniteFallbackCanonical
import ImbalancedChen.P4AUpperTaggedBetaAttachment
import ImbalancedChen.P2LowerCanonicalRetainedTrace
import ImbalancedChen.RoughPrimeUniverse

/-!
Static continuation of the final-policy structure exports.
UNCOMPILED: no kernel or publication status is asserted.

The runtime-cutoff policy is transported only on actual rough words.
The zero-cutoff program is not identified with it on arbitrary words.
Canonical table licenses are attached to their actual table hits; the
last two test identities specify when those hits are the actual high
branch's second/third continuation caps.
-/
namespace ImbalancedChen.P1OriginalFinalPolicyAncestorReads

noncomputable section
open scoped Classical
open P4AOriginalFiniteAll22RawLedger (finalPolicy)
open P4AOriginalFiniteFallbackPolicy (F rho point high upper policy dispatch secondLevel level choose)
open P4AOriginalFiniteFallbackBank (read)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87RawChronology (cutoff)
open P4AUpperTaggedParityCompiler (universe)
open P4AOrderedThirdRectangleRate (index position)
open P4AOriginalFiniteFallbackPrograms (code)
open P4AOrderedThirdRankReads (admit)
open P4AFull87ActualAffineDeletion (coords)
open P5OriginalAboveMuThirdLowerPhysicalCoefficient
  (SecondRegion ThirdRegion secondMask thirdMask)

/-- Every prime of a canonical ancestor inherits the actual carrier's
rough lower bound.  No retained-support premise is needed. -/
theorem canonical_rough_ancestor_lower (N cap : ℕ) (w z : ℝ) (x k : ℕ)
    (hx : x ∈ universe N cap w z) :
    ∀ p ∈ rosserAncestor k x.primeFactorsList, w ≤ (p : ℝ) := by
  have hs := (P2LowerCanonicalRetainedTrace.canonical_subword_of_universe N cap w z hx).1
  intro p hp
  have hpf : p ∈ x.primeFactorsList := (List.drop_sublist _ _).subset hp
  have hrev : p ∈ x.primeFactorsList.reverse := List.mem_reverse.mpr hpf
  exact mem_roughPrimeUniverse_lower (hs.subset hrev)

/-- A nonzero physical modulus has an actual rough factor in the
carrier used below.  Its full small-times-rough modulus need not itself
be a rough word. -/
theorem final_nonzero_rho_rough_factor (m trim n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (tau L : ℝ) (v : ℕ)
    (hv : rho (bank m) trim n e q a omega N tau L v ≠ 0) :
    ∃ s x : ℕ, s ∈ actualSmallRosserSupport N N ((N : ℝ) ^ omega) ∧
      x ∈ universe N N ((N : ℝ) ^ omega) (cutoff N) ∧ v = s * x := by
  classical
  have hm : v ∈ P4AUpperTaggedBetaAttachment.support N N ((N : ℝ) ^ omega) (cutoff N) := by
    by_contra hnot
    apply hv
    change smallRoughRho _ _ _ _ _ v = 0
    exact smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hnot
  obtain ⟨⟨s, x⟩, hpair, hprod⟩ := Finset.mem_image.mp hm
  obtain ⟨hs, hx⟩ := Finset.mem_product.mp hpair
  exact ⟨s, x, hs, hx, hprod.symm⟩

/-- Runtime cutoff transport is local to this actual rough ancestor. -/
theorem final_rough_ancestor_cut (m trim n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (hN : 1 ≤ N) (homega : 0 ≤ omega) (x k : ℕ)
    (hx : x ∈ universe N N ((N : ℝ) ^ omega) (cutoff N)) :
    F (bank m) (width trim) n (data e q a) omega N
        (rosserAncestor k x.primeFactorsList) =
      F (bank m) (width trim) n (data e q a) 0 N
        (rosserAncestor k x.primeFactorsList) :=
  P4AOriginalFiniteFallbackPolicy.policy_cut
    (bank m) (width trim) n (data e q a) hN homega
    (rosserAncestor k x.primeFactorsList)
    (canonical_rough_ancestor_lower N N ((N : ℝ) ^ omega) (cutoff N) x k hx)

/-- Actual odd-rank admission reads the same word's canonical program
after the justified rough-word transport.  The program index, not an
extra later prime, determines which prefix is read. -/
theorem final_rough_ancestor_read (m trim n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (hN : 1 < N) (homega : 0 ≤ omega) (x k : ℕ)
    (hx : x ∈ universe N N ((N : ℝ) ^ omega) (cutoff N))
    (hk : k ≤ x.primeFactorsList.length) (ho : polarityAfter true k = false) :
    index (position k) + 1 ≤ k ∧
      F (bank m) (width trim) n (data e q a) omega N
          (rosserAncestor k x.primeFactorsList) =
        admit N
          ((code (bank m) (width trim) n (data e q a) (position k)).eval
            (coords N (index (position k) + 1) x.primeFactorsList.reverse))
          (rosserAncestor k x.primeFactorsList) := by
  obtain ⟨hi, hread⟩ :=
    P4AOriginalFiniteFallbackRankReads.read
      (bank m) (width trim) (width_pos trim) n (data e q a) N N hN
      ((N : ℝ) ^ omega) (cutoff N) x hx k hk ho
  refine ⟨hi, ?_⟩
  calc
    F (bank m) (width trim) n (data e q a) omega N
        (rosserAncestor k x.primeFactorsList) =
        F (bank m) (width trim) n (data e q a) 0 N
          (rosserAncestor k x.primeFactorsList) :=
      final_rough_ancestor_cut m trim n e q a omega N hN.le homega x k hx
    _ = _ := hread

/-- A selected second cap satisfies the original full and complementary
square bounds at the actual two-coordinate ancestor. -/
theorem final_second_hit_license (m N : ℕ) (pre : List ℕ) (c : ℚ)
    (hhit : read m (bank m).second (point (N : ℝ) 2 pre) = some c) :
    let t := point (N : ℝ) 2 pre
    SecondRegion (t 0) (t 1) ∧ 3 * t 0 < VariableEnvelope.v (t 0) ∧
      VariableEnvelope.v (t 0) < c ∧ (c : ℝ) < 299 / 500 ∧
      (1 / 2 : ℝ) < c ∧ (∀ i, prefixSquareExpr t i < c) ∧
      (∀ i ∉ secondMask, selectedSquareExpr secondMask t i < c) ∧
      (c : ℝ) < VariableEnvelope.v (t 1) :=
  P4AOriginalFiniteFallbackCanonical.selected_second hhit

/-- A selected third cap retains the earlier cubes and has the original
full and complementary square bounds at the actual third ancestor. -/
theorem final_third_hit_license (m N : ℕ) (pre : List ℕ) (c : ℚ)
    (hhit : read m (bank m).third (point (N : ℝ) 3 pre) = some c) :
    let t := point (N : ℝ) 3 pre
    ThirdRegion (t 0) (t 1) (t 2) ∧ 3 * t 0 < VariableEnvelope.v (t 0) ∧
      t 0 + t 1 + 3 * t 2 < VariableEnvelope.v (t 0) ∧
      VariableEnvelope.v (t 0) < c ∧ (c : ℝ) < 299 / 500 ∧
      (1 / 2 : ℝ) < c ∧ (∀ i, prefixSquareExpr t i < c) ∧
      (∀ i ∉ thirdMask, selectedSquareExpr thirdMask t i < c) ∧
      (c : ℝ) < VariableEnvelope.v (t 1 + t 2) :=
  P4AOriginalFiniteFallbackCanonical.selected_third hhit

/-- On the high branch the second-table hit is the actual rank-three
test level, not only a detached geometric license. -/
theorem final_second_hit_test (m trim n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (pre : List ℕ) (c : ℚ) (hlen : pre.length = 3)
    (hhigh : high (N : ℝ) pre)
    (hhit : read m (bank m).second (point (N : ℝ) 2 pre) = some c) :
    finalPolicy m trim n e q a omega N false pre =
      decide (ordinaryRosserPrefixAdmissible false ((N : ℝ) ^ (c : ℝ)) pre) := by
  have hlevel : secondLevel (bank m) (data e q a) omega (N : ℝ) pre = (c : ℝ) := by
    simp only [secondLevel, hhit, choose]
  calc
    finalPolicy m trim n e q a omega N false pre =
        upper (bank m) (data e q a) omega (N : ℝ) false pre := by
      simp only [finalPolicy, policy, dispatch, if_pos hhigh]
    _ = decide (ordinaryRosserPrefixAdmissible false
        ((N : ℝ) ^ secondLevel (bank m) (data e q a) omega (N : ℝ) pre) pre) :=
      P4AOriginalFiniteFallbackPolicy.rank_three (bank m) (data e q a) omega (N : ℝ) pre hlen
    _ = _ := by rw [hlevel]

/-- After rank three a high-branch third-table hit supplies the actual
frozen continuation level of that same word. -/
theorem final_third_hit_test (m trim n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (pre : List ℕ) (c : ℚ) (hlen : 3 < pre.length)
    (hhigh : high (N : ℝ) pre)
    (hhit : read m (bank m).third (point (N : ℝ) 3 pre) = some c) :
    finalPolicy m trim n e q a omega N false pre =
      decide (ordinaryRosserPrefixAdmissible false ((N : ℝ) ^ (c : ℝ)) pre) := by
  have hlevel :=
    P4AOriginalFiniteFallbackPolicy.third_hit
      (bank m) (data e q a) omega (N : ℝ) pre hlen hhit
  have hnot : ¬pre.length ≤ 2 := by omega
  change policy (bank m) (width trim) n (data e q a) omega (N : ℝ) false pre = _
  rw [policy, dispatch, if_pos hhigh, upper, if_neg hnot, hlevel]
  rfl

/-- On the actual low branch the original whole ordered 4/5/6/8 tree is
retained literally; this is not a global old-policy identity. -/
theorem final_lower_history (m trim n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    (N : ℕ) (positive : Bool) (pre : List ℕ)
    (hlow : point (N : ℝ) 1 pre 0 ≤ VariableEnvelope.mu) :
    finalPolicy m trim n e q a omega N positive pre =
      P4AOriginalOrderedThirdFullPolicy.policy (width trim) n (data e q a)
        omega (N : ℝ) positive pre :=
  P4AOriginalFiniteFallbackPolicy.lower_history
    (bank m) (width trim) n (data e q a) omega (N : ℝ) positive pre hlow

end
end ImbalancedChen.P1OriginalFinalPolicyAncestorReads
