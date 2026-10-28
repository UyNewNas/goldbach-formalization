import ImbalancedChen.P2W1ActualCanonicalPrimeWord

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This module binds the independent arithmetic family to the actual D
integer singleton-source paths. The masks on the two sides have separate
definitions: recursive admittedChildPredicate versus the frozen physical
history exporter. Their equality is the D source-path theorem, using the
real root/full/selected tests and immutable incoming cap. No ParentTests
conclusion, arbitrary exporter, PP estimate or positive-K licence is an
input. Pair routes and the eleven Upsilon root cover are not supplied here.
-/
namespace ImbalancedChen.P2W1ActualPrefixFamilyBinding
noncomputable section
open scoped Classical BigOperators
open P2W1UnsiftedPrimeProductSource
open P2W1ActualCanonicalPrimeWord
open P2EnhancedW1OrderedPositiveTripleWord
open P2Selected430ActualW1SourceCoverage
open P2Selected430CausalOccurrenceExporter
open P2EnhancedLowerPhysicalNode
open P2EnhancedLowerPrimeChildCarriers (parentWindow)
open P2PhysicalFrozenPrefixHistory
open P2PhysicalIncomingPrefixCells (CapPlan)

theorem actual_prefix_count_exact {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q chi lo hi : ℝ) (n : PhysicalNode) (old : List ℕ)
    (seedCap sigma : ℝ) (E : ℕ → ℕ → Prop) (es : List (IntegerStep N))
    (i : Fin 7) (j : Fin 10)
    (hroot : rootGate depth lo hi n)
    (hs : IntegerState N Q (start plan lo hi seedCap n) old)
    (hw : parentWindow N Q old chi)
    (hsource : SourceSteps plan N Q lo hi (start plan lo hi seedCap n) old es) :
    sigma * (∑ ell ∈ Finset.range (N+1),
      ((positiveTripleWords N ell Q (finishWord old es) i j
        (sourceReceiver plan N Q lo hi (start plan lo hi seedCap n) old E es)).card : ℝ)) =
    p5z_labelledPrimeMass
      (arithmeticLabels N Q (oldWord (input Q n old seedCap E es)) i j)
      (product (oldWord (input Q n old seedCap E es)))
      (frozenWeight N (oldWord (input Q n old seedCap E es))
        (computedFrozenMask plan N lo hi (input Q n old seedCap E es)) sigma) N := by
  have ha0 : (start plan lo hi seedCap n).accepted=true := by
    change decide (rootGate depth lo hi n) = true
    exact decide_eq_true hroot
  have hsound := source_steps_sound plan N Q chi lo hi _ old es ha0
    hroot.2.2.1 hroot.2.2.2 hs hw hsource
  have hw' := hsound.2.2.2.2.1
  rw [← actual_source_mask_eq plan N Q chi lo hi n old seedCap E es hroot hs hw hsource,
    input_word]
  exact actual_switched_count_eq_labelledPrimeMass _ sigma hw'.2.1

/-- Complete prime slots are derived from the integer old-word alignment
along the real causal path, rather than assumed for an abstract family. -/
theorem actual_prefix_word_primes {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q chi lo hi : ℝ) (n : PhysicalNode) (old : List ℕ)
    (seedCap : ℝ) (es : List (IntegerStep N))
    (hroot : rootGate depth lo hi n)
    (hs : IntegerState N Q (start plan lo hi seedCap n) old)
    (hw : parentWindow N Q old chi)
    (hsource : SourceSteps plan N Q lo hi (start plan lo hi seedCap n) old es)
    {i : Fin 7} {j : Fin 10} {a : Label}
    (ha : a ∈ arithmeticLabels N Q (finishWord old es) i j) :
    ∀ p ∈ primeWord (finishWord old es) a, Nat.Prime p := by
  have ha0 : (start plan lo hi seedCap n).accepted=true := by
    change decide (rootGate depth lo hi n) = true
    exact decide_eq_true hroot
  have hsound := source_steps_sound plan N Q chi lo hi _ old es ha0
    hroot.2.2.1 hroot.2.2.2 hs hw hsource
  have hs' := hsound.2.2.2.1
  exact primeWord_primes hs'.primes (Finset.mem_filter.mp ha).2

end
end ImbalancedChen.P2W1ActualPrefixFamilyBinding
