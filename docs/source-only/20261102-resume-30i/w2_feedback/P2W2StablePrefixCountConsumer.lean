import ImbalancedChen.P2AllW2ImmutableCountRecursion

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Attach the actual joint all106-action recursion to positive marked counts
and the independently defined recursive stable-prefix prime source. The
original root receiver E old.prod is immutable. Equal products never merge
path labels. The admitted singleton-source coverage is exactly F's, not a
new claim of all eleven roots or a complete pair/retain compiler.
-/
namespace ImbalancedChen.P2W2StablePrefixCountConsumer

noncomputable section
open Finset Set Wu2008DoubleSieve
open scoped Classical BigOperators
open P2FrozenReceiverCountActions
open P2ActualMarkedCountState (Query CountState)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2W2PhysicalChildFeedback (W2Bound)
open P5OriginalActionMassBound (originalW2At)
open P2EnhancedLowerPhysicalNode
open P2PhysicalFrozenPrefixHistory
open P2PhysicalIncomingPrefixCells (CapPlan)
open P2EnhancedLowerPrimeChildCarriers (parentWindow physicalPrime)
open P2Selected430ActualW1SourceCoverage
open P2StablePrefixActualCountState

abbrev physicalIterate := P2AllW2ImmutableCountRecursion.iterate

def markedState {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop)
    (bank : List Query) (rounds : ℕ) : CountState :=
  ⟨fun s => ∑ a∈L, sigma a*(physicalIterate N Q (E a) bank rounds).upper
      (B a) (cutoff Q (B a) s.val),
   fun s => ∑ a∈L, sigma a*(physicalIterate N Q (E a) bank rounds).lower
      (B a) (cutoff Q (B a) s.val)⟩

theorem markedState_encloses {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop)
    (bank : List Query) (rounds : ℕ) (s : Query)
    (hB : ∀a∈L,0<B a) (hsigma : ∀a∈L,0≤sigma a)
    (hR : ∀a∈L,1<Q/(B a:ℝ)) :
    (markedState N Q L B sigma E bank rounds).lower s ≤ markedPhi N Q L B sigma E s.val ∧
      markedPhi N Q L B sigma E s.val ≤ (markedState N Q L B sigma E bank rounds).upper s := by
  have hc (a : ι) (ha : a∈L) := P2AllW2ImmutableCountRecursion.iterate_encloses
    N Q (E a) bank rounds (B a) (cutoff Q (B a) s.val)
    (P2AllW1SameQRawCountInduction.cutoff_query (hB a ha) (hR a ha) s.property.1)
  constructor
  · exact sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hc a ha).1 (hsigma a ha))
  · exact sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hc a ha).2 (hsigma a ha))

/-- A count consumer, not just the assertion that an action list exists.
The new marked upper bound lies below each old-generation W2 candidate. -/
theorem all36_marked_transition {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop)
    (bank : List Query) (rounds : ℕ) (j : Fin 36)
    (hB : ∀a∈L,0<B a) (hsigma : ∀a∈L,0≤sigma a)
    (hR : ∀a∈L,1<Q/(B a:ℝ)) :
    markedPhi N Q L B sigma E (originalW2At j).s ≤
      (markedState N Q L B sigma E bank (rounds+1)).upper
        (P2AllW2SameQRawCountAction.target j) ∧
    (markedState N Q L B sigma E bank (rounds+1)).upper
        (P2AllW2SameQRawCountAction.target j) ≤
      ∑ a∈L, sigma a*W2Bound N Q (E a) (physicalIterate N Q (E a) bank rounds) (B a) j := by
  refine ⟨(markedState_encloses N Q L B sigma E bank (rounds+1)
    (P2AllW2SameQRawCountAction.target j) hB hsigma hR).2,?_⟩
  exact sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left
    (P2AllW2ImmutableCountRecursion.iterate_upper_le_each_W2 N Q (E a) bank rounds (B a) j)
    (hsigma a ha))

def pathState {depth mesh : ℕ} (plan : CapPlan depth mesh) (N : ℕ)
    (Q lo hi seedCap : ℝ) (n : PhysicalNode) (old : List ℕ)
    (E : ℕ → ℕ → Prop) (raw : Finset (List (IntegerStep N)))
    (sigma : List (IntegerStep N) → ℝ) (bank : List Query) (rounds : ℕ) : CountState :=
  markedState N Q (admittedPaths plan N Q lo hi seedCap n old raw)
    (pathProduct old) sigma (fun _ => E old.prod) bank rounds

/-- Exact actual-source caller. Only primitive root geometry, source-path
membership and positive sigma are supplied; the count bound is proved by
the joint W1/W2/Buchstab recursion from arithmetic Rosser initial data. -/
theorem pathState_actual_recursivePhi {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q chi lo hi seedCap : ℝ) (n : PhysicalNode) (old : List ℕ)
    (E : ℕ → ℕ → Prop) (raw : Finset (List (IntegerStep N)))
    (sigma : List (IntegerStep N) → ℝ) (bank : List Query) (rounds : ℕ) (s : Query)
    (hword : word n=old.map (physicalPrime N))
    (htotal : n.total=Real.log Q/Real.log (N:ℝ))
    (hprimes : ∀p∈old,p.Prime) (hw : parentWindow N Q old chi)
    (hsigma : ∀es∈admittedPaths plan N Q lo hi seedCap n old raw,0≤sigma es) :
    (pathState plan N Q lo hi seedCap n old E raw sigma bank rounds).lower s ≤
      recursivePhi plan N Q lo hi seedCap n old E raw sigma s.val ∧
    recursivePhi plan N Q lo hi seedCap n old E raw sigma s.val ≤
      (pathState plan N Q lo hi seedCap n old E raw sigma bank rounds).upper s := by
  have hg (es : List (IntegerStep N))
      (hes : es∈admittedPaths plan N Q lo hi seedCap n old raw) :=
    admittedPath_product_level plan N Q chi lo hi seedCap n old raw hword htotal hprimes hw hes
  have hc := markedState_encloses N Q
    (admittedPaths plan N Q lo hi seedCap n old raw)
    (pathProduct old) sigma (fun _ => E old.prod) bank rounds s
    (fun es hes => (hg es hes).1) hsigma (fun es hes => (hg es hes).2)
  rw [←recursivePhi_eq_markedPhi plan N Q chi lo hi seedCap n old E raw sigma s.val
    hword htotal hprimes hw] at hc
  exact hc

/-- Each original W2 action is applied at the independently defined
recursive source itself, with all child/complement/raw costs visible. -/
theorem recursivePhi_le_each_W2 {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q chi lo hi seedCap : ℝ) (n : PhysicalNode) (old : List ℕ)
    (E : ℕ → ℕ → Prop) (raw : Finset (List (IntegerStep N)))
    (sigma : List (IntegerStep N) → ℝ) (bank : List Query) (rounds : ℕ) (j : Fin 36)
    (hword : word n=old.map (physicalPrime N))
    (htotal : n.total=Real.log Q/Real.log (N:ℝ))
    (hprimes : ∀p∈old,p.Prime) (hw : parentWindow N Q old chi)
    (hsigma : ∀es∈admittedPaths plan N Q lo hi seedCap n old raw,0≤sigma es) :
    recursivePhi plan N Q lo hi seedCap n old E raw sigma (originalW2At j).s ≤
      ∑ es∈admittedPaths plan N Q lo hi seedCap n old raw,
        sigma es*W2Bound N Q (E old.prod)
          (physicalIterate N Q (E old.prod) bank rounds) (pathProduct old es) j := by
  have hg (es : List (IntegerStep N))
      (hes : es∈admittedPaths plan N Q lo hi seedCap n old raw) :=
    admittedPath_product_level plan N Q chi lo hi seedCap n old raw hword htotal hprimes hw hes
  have hc := all36_marked_transition N Q
    (admittedPaths plan N Q lo hi seedCap n old raw)
    (pathProduct old) sigma (fun _ => E old.prod) bank rounds j
    (fun es hes => (hg es hes).1) hsigma (fun es hes => (hg es hes).2)
  rw [recursivePhi_eq_markedPhi plan N Q chi lo hi seedCap n old E raw sigma
    (originalW2At j).s hword htotal hprimes hw]
  exact hc.1.trans hc.2

end
end ImbalancedChen.P2W2StablePrefixCountConsumer
