import ImbalancedChen.P2EnhancedW1FixedPowerLabelMultiplicity
import ImbalancedChen.P2PhysicalFrozenPrefixHistory
import ImbalancedChen.P2EnhancedLowerPrimeChildGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

One original integer-prime W1 singleton child is realized by the
deterministic one-step finite physical graph. The coordinate is exactly
`physicalPrime N p.val`; the graph code is `canonicalProgram` with
`StepShape.w1Singleton i j`, not an assumed hRealized. The true
`singleChildren (.w1 i j)` domain and accepted `History.step` supply
the local graph gates. The same old Q, word, original E B ell predicate,
old parent carrier, exact B*p child carrier and sigma(B) survive.

The actual `History.step.accepted=true` is an input from the frozen
constructor, not a manufactured admission theorem. Establishing it
for all primes in the original positive switched multiset, and binding
their triple source word, remains open.

Original: manuscript-body.tex 790--817, 819--875;
same-new-level-double-sieve-route.tex 93--105, 147--165.
-/

namespace ImbalancedChen.P2EnhancedW1IntegerPrimeGraphStep

noncomputable section
open Set Finset
open scoped Classical BigOperators
open P2EnhancedLowerPhysicalNode
open P2EnhancedLowerPhysicalTransition (StepShape LocalDomain OneGate
  normalized perform)
open P2EnhancedLowerFinitePhysicalGraph (TypedNode Program Coordinates
  Member canonicalProgram canonicalProgram_member LocalPath realize)
open P2EnhancedLowerPrimeChildCarriers (SingleRule parentWindow
  singleChildren mem_singleChildren physicalPrime relativePrime)
open P2EnhancedLowerPrimeChildGeometry (physicalLevel parentWindow_logs
  relativePrime_physical)
open P2EnhancedW1RepeatedLabelClassification
  (physical_level_eq_parent_residual)
open P2EnhancedW1R2ActualCarrierBranch (w1HistoryChild
  admittedChildPredicate singleton_child_computed_history)
open P2PhysicalFrozenPrefixHistory (History step stepGate step_accepted_iff
  admitted_step_gates)
open P2PhysicalIncomingPrefixCells (CapPlan)
open P2LargerSActualPositiveCounts (historyCarrier)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P5OriginalActionMassBound (W1Target W1Anchor W1Domain)
open P5OriginalFeedbackDomains (singletonProfile)

/-- The deterministic graph coordinate of this exact integer prime. -/
def primeCoordinate (N p : ℕ) : Coordinates 1 :=
  fun _ _ => physicalPrime N p

/-- The graph action label is fixed by the original W1 target/anchor,
while the physical cell is computed from the integer prime coordinate. -/
def primeActionCode (lo hi : ℝ) (mesh N : ℕ)
    (i : Fin 7) (j : Fin 10) (p : ℕ) : Program mesh 1 :=
  canonicalProgram lo hi mesh (fun _ => StepShape.w1Singleton i j)
    (primeCoordinate N p)

@[simp] theorem primeActionCode_shape (lo hi : ℝ) (mesh N : ℕ)
    (i : Fin 7) (j : Fin 10) (p : ℕ) :
    (primeActionCode lo hi mesh N i j p 0).1 =
      StepShape.w1Singleton i j := rfl

@[simp] theorem primeCoordinate_literal (N p : ℕ) :
    (primeCoordinate N p 0) 0 = physicalPrime N p := rfl

/-- An actually admitted original W1 integer singleton is a graph
member with its prime coordinate and its true frozen step child. The
extra argument/ceiling comparisons are exactly the selected W1 action
query at the parent; they are not graph-soundness assumptions. -/
theorem accepted_integer_W1_prime_realizes_graph
    {depth mesh N ell : ℕ} {Q chi lo hi : ℝ}
    {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {sigma : ℕ → ℝ}
    {p : Fin (N+1)} (plan : CapPlan depth mesh) (H : History)
    (hp : p ∈ singleChildren (.w1 i j) N Q old chi)
    (hprime : ∀ r ∈ old, r.Prime)
    (hword : word H.node = old.map (physicalPrime N))
    (htotal : H.node.total = Real.log Q / Real.log (N : ℝ))
    (hargument : H.node.argument ≤ W1Target i)
    (hanchorCeiling : residual H.node / W1Target i ≤ H.node.ceiling)
    (haccepted : (w1HistoryChild plan lo hi H N Q old j p.val).accepted=true)
    (hell : ell ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)))
    (hdiv : p.val ∣ (N-ell)/old.prod) :
    Member lo hi 1 ⟨true,H.node⟩
      (primeActionCode lo hi mesh N i j p.val)
      (primeCoordinate N p.val) ∧
    (primeActionCode lo hi mesh N i j p.val 0).1 =
      StepShape.w1Singleton i j ∧
    (primeCoordinate N p.val 0) 0 = physicalPrime N p.val ∧
    (realize 1 ⟨true,H.node⟩
      (primeActionCode lo hi mesh N i j p.val)
      (primeCoordinate N p.val)).physical =
        (w1HistoryChild plan lo hi H N Q old j p.val).node ∧
    word (w1HistoryChild plan lo hi H N Q old j p.val).node =
      old.map (physicalPrime N) ++ [physicalPrime N p.val] ∧
    (w1HistoryChild plan lo hi H N Q old j p.val).node.total =
      Real.log Q / Real.log (N : ℝ) ∧
    fullGates (w1HistoryChild plan lo hi H N Q old j p.val).node ∧
    selectedGates (w1HistoryChild plan lo hi H N Q old j p.val).node ∧
    p.val.Coprime (old.prod*N) ∧
    ell ∈ historyCarrier N (old.prod*p.val)
      (admittedChildPredicate E old.prod
        (w1HistoryChild plan lo hi H N Q old j p.val))
      (cutoff Q old.prod (W1Anchor j)) ∧
    sigma old.prod * (if ell ∈ historyCarrier N (old.prod*p.val)
      (admittedChildPredicate E old.prod
        (w1HistoryChild plan lo hi H N Q old j p.val))
      (cutoff Q old.prod (W1Anchor j)) then (1 : ℝ) else 0) =
      sigma old.prod := by
  have hdata := mem_singleChildren.mp hp
  have hw : parentWindow N Q old chi := hdata.2.1
  have hres : residual H.node = physicalLevel N Q old :=
    (physical_level_eq_parent_residual hw hprime hword htotal).symm
  have hlevelPos : 0 < physicalLevel N Q old := (parentWindow_logs hw).2.2
  have hresPos : 0 < residual H.node := by rw [hres]; exact hlevelPos
  have hnorm : normalized H.node (primeCoordinate N p.val 0) 0 =
      relativePrime Q old p.val := by
    change physicalPrime N p.val / residual H.node =
      relativePrime Q old p.val
    rw [hres]
    apply (div_eq_iff hlevelPos.ne').2
    simpa only [mul_comm] using (relativePrime_physical hw (p:=p.val)).symm
  have hstepAccepted :
      (step plan lo hi H (physicalPrime N p.val)
        (W1Anchor j*(1-relativePrime Q old p.val))).accepted=true := haccepted
  have hgate := ((step_accepted_iff plan lo hi H
    (physicalPrime N p.val)
    (W1Anchor j*(1-relativePrime Q old p.val))).mp hstepAccepted).2
  obtain ⟨_,hbox,hxPos,hxCeil,hxSquare,_,_,_⟩ := hgate
  have hdomain : relativePrime Q old p.val ∈ W1Domain i j :=
    hdata.2.2.1
  have hlocal : LocalDomain H.node (.w1Singleton i j)
      (primeCoordinate N p.val 0) := by
    refine ⟨hresPos,⟨hxPos,hxCeil.le,hxSquare⟩,?_,
      hargument,hanchorCeiling⟩
    simpa only [hnorm] using hdomain
  have hpath : LocalPath lo hi 1 ⟨true,H.node⟩
      (fun _ => StepShape.w1Singleton i j)
      (primeCoordinate N p.val) := by
    exact ⟨hbox,hbox,by simp [P2EnhancedLowerFinitePhysicalGraph.incomingAllowed],
      hlocal,trivial⟩
  have hmember : Member lo hi 1 ⟨true,H.node⟩
      (primeActionCode lo hi mesh N i j p.val)
      (primeCoordinate N p.val) := by
    exact canonicalProgram_member _ _ _ hpath
  have hrealize :
      (realize 1 ⟨true,H.node⟩
        (primeActionCode lo hi mesh N i j p.val)
        (primeCoordinate N p.val)).physical =
      (w1HistoryChild plan lo hi H N Q old j p.val).node := by
    change appendOne H.node (physicalPrime N p.val)
      (singletonProfile (W1Anchor j)
        (normalized H.node (primeCoordinate N p.val 0) 0)) =
      appendOne H.node (physicalPrime N p.val)
        (W1Anchor j*(1-relativePrime Q old p.val))
    rw [hnorm]
    rfl
  have hchild := singleton_child_computed_history plan H hell hdiv haccepted
  have hhistoryGates := admitted_step_gates plan lo hi H
    (physicalPrime N p.val)
    (W1Anchor j*(1-relativePrime Q old p.val)) hstepAccepted
  have hchildWord : word (w1HistoryChild plan lo hi H N Q old j p.val).node =
      old.map (physicalPrime N) ++ [physicalPrime N p.val] := by
    change word (appendOne H.node (physicalPrime N p.val)
      (W1Anchor j*(1-relativePrime Q old p.val))) = _
    rw [word_appendOne,hword]
  have hchildTotal : (w1HistoryChild plan lo hi H N Q old j p.val).node.total =
      Real.log Q / Real.log (N : ℝ) := by
    change H.node.total = _
    exact htotal
  have hcop : p.val.Coprime (old.prod*N) := by
    simpa only [mul_comm] using hdata.1.2
  refine ⟨hmember,rfl,rfl,hrealize,hchildWord,hchildTotal,?_,?_,hcop,
    hchild,?_⟩
  · exact hhistoryGates.1
  · exact hhistoryGates.2.1
  · simp [hchild]

end
end ImbalancedChen.P2EnhancedW1IntegerPrimeGraphStep
