import ImbalancedChen.P2ActualMarkedCountState
import ImbalancedChen.P2Selected430ActualW1SourceCoverage

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The finite labels here are actual integer source paths. Retention is
computed from the original incoming-cap history constructor and the
production singleChildren BH/W1/W2 membership tests. Every retained path
has derived final admission, full/selected gates, unchanged Q, original
prime word and positive residual. Its recursively frozen receiver is
proved equal to the original root receiver, at the same actual prime
label. This binds the independently defined recursive source count to
the frozen-receiver count state; no final count/Sound licence is input.

An arbitrary supplied finite source-path set and CapPlan are not claimed
to cover the original eleven roots or pair paths. Nor is the Rosser
initial enclosure the adopted positive seed or an H248 table state.
-/
namespace ImbalancedChen.P2StablePrefixActualCountState

noncomputable section
open Finset Set
open scoped Classical BigOperators
open Wu2008DoubleSieve
open P2FrozenReceiverCountActions
open P2ActualMarkedCountState
open P2EnhancedLowerPhysicalNode
open P2PhysicalFrozenPrefixHistory
open P2PhysicalIncomingPrefixCells (CapPlan)
open P2EnhancedLowerPrimeChildCarriers (parentWindow parentProduct residualLevel physicalPrime)
open P2EnhancedLowerPrimeChildGeometry (parentWindow_logs)
open P2Selected430ActualW1SourceCoverage

def admittedPaths {depth mesh : ℕ} (plan : CapPlan depth mesh) (N : ℕ)
    (Q lo hi seedCap : ℝ) (n : PhysicalNode) (old : List ℕ)
    (raw : Finset (List (IntegerStep N))) : Finset (List (IntegerStep N)) :=
  raw.filter (fun es => (start plan lo hi seedCap n).accepted=true ∧
    SourceSteps plan N Q lo hi (start plan lo hi seedCap n) old es)

def pathProduct {N : ℕ} (old : List ℕ) (es : List (IntegerStep N)) : ℕ :=
  (finishWord old es).prod

def recursiveCarrier {depth mesh : ℕ} (plan : CapPlan depth mesh) (N : ℕ)
    (Q lo hi seedCap : ℝ) (n : PhysicalNode) (old : List ℕ)
    (E : ℕ → ℕ → Prop) (es : List (IntegerStep N)) (s : ℝ) : Finset ℕ :=
  (sieveCarrier N (pathProduct old es) (pathProduct old es*N)
    (P2EnhancedTwentyOneSameQWeighted.cutoff Q (pathProduct old es) s)).filter
      (sourceReceiver plan N Q lo hi (start plan lo hi seedCap n) old E es (pathProduct old es))

def recursivePhi {depth mesh : ℕ} (plan : CapPlan depth mesh) (N : ℕ)
    (Q lo hi seedCap : ℝ) (n : PhysicalNode) (old : List ℕ)
    (E : ℕ → ℕ → Prop) (raw : Finset (List (IntegerStep N)))
    (sigma : List (IntegerStep N) → ℝ) (s : ℝ) : ℝ :=
  ∑ es∈admittedPaths plan N Q lo hi seedCap n old raw,
    sigma es*((recursiveCarrier plan N Q lo hi seedCap n old E es s).card:ℝ)

/-- Actual retained integer source membership discharges the final
history admission and gates. No ParentTests/accepted output is assumed. -/
theorem admittedPath_data {depth mesh : ℕ} (plan : CapPlan depth mesh) (N : ℕ)
    (Q chi lo hi seedCap : ℝ) (n : PhysicalNode) (old : List ℕ)
    (raw : Finset (List (IntegerStep N))) {es : List (IntegerStep N)}
    (hword : word n=old.map (physicalPrime N))
    (htotal : n.total=Real.log Q/Real.log (N:ℝ))
    (hprimes : ∀p∈old,p.Prime) (hw : parentWindow N Q old chi)
    (hes : es∈admittedPaths plan N Q lo hi seedCap n old raw) :
    (finishHistory plan N Q lo hi (start plan lo hi seedCap n) old es).accepted=true ∧
    fullGates (finishHistory plan N Q lo hi (start plan lo hi seedCap n) old es).node ∧
    selectedGates (finishHistory plan N Q lo hi (start plan lo hi seedCap n) old es).node ∧
    IntegerState N Q (finishHistory plan N Q lo hi (start plan lo hi seedCap n) old es)
      (finishWord old es) ∧
    parentWindow N Q (finishWord old es) chi ∧
    residual n/(2:ℝ)^es.length≤
      residual (finishHistory plan N Q lo hi (start plan lo hi seedCap n) old es).node := by
  have hd := (mem_filter.mp hes).2
  have hroot : rootGate depth lo hi n := by
    have ha := hd.1
    change decide (rootGate depth lo hi n)=true at ha
    exact of_decide_eq_true ha
  have hs : IntegerState N Q (start plan lo hi seedCap n) old :=
    ⟨hword,htotal,hprimes⟩
  exact source_steps_sound plan N Q chi lo hi (start plan lo hi seedCap n) old es
    hd.1 hroot.2.2.1 hroot.2.2.2 hs hw hd.2

theorem admittedPath_product_level {depth mesh : ℕ} (plan : CapPlan depth mesh) (N : ℕ)
    (Q chi lo hi seedCap : ℝ) (n : PhysicalNode) (old : List ℕ)
    (raw : Finset (List (IntegerStep N))) {es : List (IntegerStep N)}
    (hword : word n=old.map (physicalPrime N))
    (htotal : n.total=Real.log Q/Real.log (N:ℝ))
    (hprimes : ∀p∈old,p.Prime) (hw : parentWindow N Q old chi)
    (hes : es∈admittedPaths plan N Q lo hi seedCap n old raw) :
    0<pathProduct old es ∧ 1<Q/(pathProduct old es:ℝ) := by
  obtain ⟨_,_,_,_,hfinal,_⟩ :=
    admittedPath_data plan N Q chi lo hi seedCap n old raw hword htotal hprimes hw hes
  refine ⟨hfinal.2.1,?_⟩
  simpa only [residualLevel,parentProduct,pathProduct] using (parentWindow_logs hfinal).2.1

/-- The original root receiver is retained at every actual prime label;
the proof uses the independently constructed integer source path. -/
theorem recursiveCarrier_eq_root_frozen {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q chi lo hi seedCap : ℝ) (n : PhysicalNode) (old : List ℕ)
    (E : ℕ → ℕ → Prop) (raw : Finset (List (IntegerStep N)))
    {es : List (IntegerStep N)} (s : ℝ)
    (hword : word n=old.map (physicalPrime N))
    (htotal : n.total=Real.log Q/Real.log (N:ℝ))
    (hprimes : ∀p∈old,p.Prime) (hw : parentWindow N Q old chi)
    (hes : es∈admittedPaths plan N Q lo hi seedCap n old raw) :
    recursiveCarrier plan N Q lo hi seedCap n old E es s =
      frozenCarrier N (pathProduct old es) (E old.prod)
        (P2EnhancedTwentyOneSameQWeighted.cutoff Q (pathProduct old es) s) := by
  have hd := (mem_filter.mp hes).2
  have hroot : rootGate depth lo hi n := by
    have ha := hd.1
    change decide (rootGate depth lo hi n)=true at ha
    exact of_decide_eq_true ha
  have hs : IntegerState N Q (start plan lo hi seedCap n) old :=
    ⟨hword,htotal,hprimes⟩
  have hreceiver (ell : ℕ) := sourceReceiver_root plan N Q chi lo hi
    (start plan lo hi seedCap n) old E es hd.1 hroot.2.2.1 hroot.2.2.2 hs hw hd.2
    (pathProduct old es) ell
  unfold recursiveCarrier frozenCarrier
  rw [(source_double_sieve_carriers N (pathProduct old es) _).1]
  ext ell
  simp only [mem_filter]
  exact and_congr_right (fun _ => hreceiver ell)

/-- An equality of independently defined actual counts. Equal prefix
products do not merge path labels, receiver tests or sigma multiplicities. -/
theorem recursivePhi_eq_markedPhi {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q chi lo hi seedCap : ℝ) (n : PhysicalNode) (old : List ℕ)
    (E : ℕ → ℕ → Prop) (raw : Finset (List (IntegerStep N)))
    (sigma : List (IntegerStep N) → ℝ) (s : ℝ)
    (hword : word n=old.map (physicalPrime N))
    (htotal : n.total=Real.log Q/Real.log (N:ℝ))
    (hprimes : ∀p∈old,p.Prime) (hw : parentWindow N Q old chi) :
    recursivePhi plan N Q lo hi seedCap n old E raw sigma s =
      markedPhi N Q (admittedPaths plan N Q lo hi seedCap n old raw)
        (pathProduct old) sigma (fun _ => E old.prod) s := by
  unfold recursivePhi markedPhi
  apply sum_congr rfl
  intro es hes
  rw [recursiveCarrier_eq_root_frozen plan N Q chi lo hi seedCap n old E raw s
    hword htotal hprimes hw hes]
  simp only [frozenCount,Int.cast_natCast]

def pathState {depth mesh : ℕ} (plan : CapPlan depth mesh) (N : ℕ)
    (Q lo hi seedCap : ℝ) (n : PhysicalNode) (old : List ℕ)
    (E : ℕ → ℕ → Prop) (raw : Finset (List (IntegerStep N)))
    (sigma : List (IntegerStep N) → ℝ) (bank : List Query) (rounds : ℕ) : CountState :=
  iterate N Q (admittedPaths plan N Q lo hi seedCap n old raw)
    (pathProduct old) sigma (fun _ => E old.prod) bank rounds

/-- A real stable-prefix count enclosure, obtained from arithmetic
initial data and immutable-old ordinary actions; no seed/Sound count
bound is an input. Root prime/physical-state and source membership gates
are exactly the independent primitive constructor conditions. -/
theorem pathState_actual_count_enclosure {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q chi lo hi seedCap : ℝ) (n : PhysicalNode) (old : List ℕ)
    (E : ℕ → ℕ → Prop) (raw : Finset (List (IntegerStep N)))
    (sigma : List (IntegerStep N) → ℝ) (bank : List Query) (rounds : ℕ) (s : Query)
    (hword : word n=old.map (physicalPrime N))
    (htotal : n.total=Real.log Q/Real.log (N:ℝ))
    (hprimes : ∀p∈old,p.Prime) (hw : parentWindow N Q old chi)
    (hsigma : ∀es∈admittedPaths plan N Q lo hi seedCap n old raw,0≤sigma es) :
    (pathState plan N Q lo hi seedCap n old E raw sigma bank rounds).lower s≤
      recursivePhi plan N Q lo hi seedCap n old E raw sigma s.val ∧
    recursivePhi plan N Q lo hi seedCap n old E raw sigma s.val≤
      (pathState plan N Q lo hi seedCap n old E raw sigma bank rounds).upper s := by
  have hg (es : List (IntegerStep N))
      (hes : es∈admittedPaths plan N Q lo hi seedCap n old raw) :=
    admittedPath_product_level plan N Q chi lo hi seedCap n old raw hword htotal hprimes hw hes
  have hc := iterate_actual_count_enclosure N Q
    (admittedPaths plan N Q lo hi seedCap n old raw)
    (pathProduct old) sigma (fun _ => E old.prod) bank
    (fun es hes => (hg es hes).1) hsigma (fun es hes => (hg es hes).2) rounds s
  rw [←recursivePhi_eq_markedPhi plan N Q chi lo hi seedCap n old E raw sigma s.val
    hword htotal hprimes hw] at hc
  exact hc

end
end ImbalancedChen.P2StablePrefixActualCountState
