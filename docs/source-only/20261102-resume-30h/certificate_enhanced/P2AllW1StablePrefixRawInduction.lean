import ImbalancedChen.P2AllW1SameQRawCountInduction
import ImbalancedChen.P2StablePrefixActualCountState

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Attach the real all70 raw-count induction to original positive marked
families and to F's independently defined recursive stable-prefix prime
source. Labels with equal products are never merged. The physical root
receiver stays fixed through all subsequent arithmetic actions.

The resulting H/h are finite arithmetic defects, possibly negative and
dependent on N,Q,E. They are not the adopted uniform seed/table. Original
all-root/pair/retained coverage and analytic action licences remain open.
-/
namespace ImbalancedChen.P2AllW1StablePrefixRawInduction

noncomputable section
open Finset Set Wu2008DoubleSieve
open scoped Classical BigOperators
open P2FrozenReceiverCountActions
open P2ActualMarkedCountState (Query CountState markedTheta markedTheta_pos upperDefect lowerDefect)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedActualBuchstabTransfer (childWindow)
open P2AllW1FrozenReceiverFiniteAction (markedRawPositive original_W1_parameters)
open P5OriginalActionMassBound (W1Target W1Anchor)
open P2EnhancedLowerPhysicalNode
open P2PhysicalFrozenPrefixHistory
open P2PhysicalIncomingPrefixCells (CapPlan)
open P2EnhancedLowerPrimeChildCarriers (parentWindow physicalPrime)
open P2Selected430ActualW1SourceCoverage
open P2StablePrefixActualCountState

abbrev physicalIterate := P2AllW1SameQRawCountInduction.iterate

def markedState {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop)
    (bank : List Query) (rounds : ℕ) : CountState :=
  ⟨fun s => ∑ a∈L,sigma a*(physicalIterate N Q (E a) bank rounds).upper
      (B a) (cutoff Q (B a) s.val),
   fun s => ∑ a∈L,sigma a*(physicalIterate N Q (E a) bank rounds).lower
      (B a) (cutoff Q (B a) s.val)⟩

theorem markedState_encloses {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop)
    (bank : List Query) (rounds : ℕ) (s : Query)
    (hB : ∀a∈L,0<B a) (hsigma : ∀a∈L,0≤sigma a)
    (hR : ∀a∈L,1<Q/(B a:ℝ)) :
    (markedState N Q L B sigma E bank rounds).lower s≤markedPhi N Q L B sigma E s.val ∧
    markedPhi N Q L B sigma E s.val≤(markedState N Q L B sigma E bank rounds).upper s := by
  have hc (a : ι) (ha : a∈L) := P2AllW1SameQRawCountInduction.iterate_encloses
    N Q (E a) bank rounds (B a) (cutoff Q (B a) s.val)
    (P2AllW1SameQRawCountInduction.cutoff_query (hB a ha) (hR a ha) s.property.1)
  constructor
  · exact sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hc a ha).1 (hsigma a ha))
  · exact sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left (hc a ha).2 (hsigma a ha))

def W1TargetQuery (i : Fin 7) : Query :=
  ⟨W1Target i,by
    have hp := original_W1_parameters i (0:Fin 10)
    constructor <;> linarith [hp.1,hp.2.1,hp.2.2]⟩

def W1AnchorQuery (j : Fin 10) : Query :=
  ⟨W1Anchor j,by
    have hp := original_W1_parameters (0:Fin 7) j
    constructor <;> linarith [hp.1,hp.2.1,hp.2.2]⟩

/-- This is the actual old-generation lower CHILD sum. The old state's
receiver E a and the inherited physical anchor cutoff are unchanged. -/
def markedOldW1Children {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop)
    (bank : List Query) (rounds : ℕ) (i : Fin 7) (j : Fin 10) : ℝ :=
  ∑ a∈L,sigma a*∑ q∈childWindow N (B a) Q (W1Target i) (W1Anchor j),
    (physicalIterate N Q (E a) bank rounds).lower (B a*q) (cutoff Q (B a) (W1Anchor j))

/-- The true all70 old-to-new marked transition, with its complete raw
positive count. No old H/h count assertion is an input. -/
theorem all70_marked_raw_transition {ι : Type*} (N : ℕ) (Q : ℝ) (L : Finset ι)
    (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop)
    (bank : List Query) (rounds : ℕ) (i : Fin 7) (j : Fin 10)
    (hB : ∀a∈L,0<B a) (hsigma : ∀a∈L,0≤sigma a)
    (hR : ∀a∈L,1<Q/(B a:ℝ)) :
    markedPhi N Q L B sigma E (W1Target i)≤
      (markedState N Q L B sigma E bank (rounds+1)).upper (W1TargetQuery i) ∧
    (markedState N Q L B sigma E bank (rounds+1)).upper (W1TargetQuery i)≤
      (markedState N Q L B sigma E bank rounds).upper (W1AnchorQuery j)-
        markedOldW1Children N Q L B sigma E bank rounds i j/2+
        markedRawPositive N Q L B sigma E i j/2 := by
  refine ⟨(markedState_encloses N Q L B sigma E bank (rounds+1)
    (W1TargetQuery i) hB hsigma hR).2,?_⟩
  have h := sum_le_sum (fun a ha => mul_le_mul_of_nonneg_left
    (P2AllW1SameQRawCountInduction.iterate_upper_le_each_W1 N Q (E a) bank rounds (B a) i j)
    (hsigma a ha))
  simpa only [markedState,W1TargetQuery,W1AnchorQuery,markedOldW1Children,
    markedRawPositive,physicalIterate,mul_add,mul_sub,mul_div_assoc,sum_add_distrib,
    sum_sub_distrib,sum_div] using h

/-- The same true original Theta, without treating H as an ordinary
rho density or asserting the positive adopted H248 values. -/
theorem markedState_actual_defects {ι : Type*} {N : ℕ} (hN : 4≤N)
    (Q : ℝ) (L : Finset ι) (B : ι → ℕ) (sigma : ι → ℝ) (E : ι → ℕ → Prop)
    (bank : List Query) (rounds : ℕ) (s : Query)
    (hB : ∀a∈L,0<B a) (hsigma : ∀a∈L,0≤sigma a)
    (hR : ∀a∈L,1<Q/(B a:ℝ)) (hpositive : ∃a∈L,0<sigma a) :
    wuLowerCoefficient s.val+
        lowerDefect N Q L B sigma (markedState N Q L B sigma E bank rounds) s≤
      markedPhi N Q L B sigma E s.val/markedTheta N Q L B sigma ∧
    markedPhi N Q L B sigma E s.val/markedTheta N Q L B sigma≤
      wuUpperCoefficient s.val-
        upperDefect N Q L B sigma (markedState N Q L B sigma E bank rounds) s := by
  have ht := (markedTheta_pos hN Q L B sigma hB hsigma hR hpositive).le
  have hc := markedState_encloses N Q L B sigma E bank rounds s hB hsigma hR
  constructor
  · have h := div_le_div_of_nonneg_right hc.1 ht
    dsimp [lowerDefect]
    linarith
  · have h := div_le_div_of_nonneg_right hc.2 ht
    dsimp [upperDefect]
    linarith

def pathRawState {depth mesh : ℕ} (plan : CapPlan depth mesh) (N : ℕ)
    (Q lo hi seedCap : ℝ) (n : PhysicalNode) (old : List ℕ)
    (E : ℕ → ℕ → Prop) (raw : Finset (List (IntegerStep N)))
    (sigma : List (IntegerStep N) → ℝ) (bank : List Query) (rounds : ℕ) : CountState :=
  markedState N Q (admittedPaths plan N Q lo hi seedCap n old raw)
    (pathProduct old) sigma (fun _ => E old.prod) bank rounds

/-- Bind the stronger induction to F's independent actual recursive
prime carrier. The available path coverage remains exactly F's coverage. -/
theorem pathRawState_actual_count_enclosure {depth mesh : ℕ} (plan : CapPlan depth mesh)
    (N : ℕ) (Q chi lo hi seedCap : ℝ) (n : PhysicalNode) (old : List ℕ)
    (E : ℕ → ℕ → Prop) (raw : Finset (List (IntegerStep N)))
    (sigma : List (IntegerStep N) → ℝ) (bank : List Query) (rounds : ℕ) (s : Query)
    (hword : word n=old.map (physicalPrime N))
    (htotal : n.total=Real.log Q/Real.log (N:ℝ))
    (hprimes : ∀p∈old,p.Prime) (hw : parentWindow N Q old chi)
    (hsigma : ∀es∈admittedPaths plan N Q lo hi seedCap n old raw,0≤sigma es) :
    (pathRawState plan N Q lo hi seedCap n old E raw sigma bank rounds).lower s≤
      recursivePhi plan N Q lo hi seedCap n old E raw sigma s.val ∧
    recursivePhi plan N Q lo hi seedCap n old E raw sigma s.val≤
      (pathRawState plan N Q lo hi seedCap n old E raw sigma bank rounds).upper s := by
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

end
end ImbalancedChen.P2AllW1StablePrefixRawInduction
