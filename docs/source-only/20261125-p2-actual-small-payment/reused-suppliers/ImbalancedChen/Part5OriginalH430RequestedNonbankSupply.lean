import ImbalancedChen.Part5OriginalH430RequestedLevelBankSupply
import ImbalancedChen.Part5OriginalBuchstabRowMass
import ImbalancedChen.Part5OriginalH430OwnedBuchstabLower

/-!
Manuscript-local missing NON-BANK branch of the literal selected-request
recursion. SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The selected retention reads its specified cell at generation g; neither an
old scalar owner nor an equality between new/old scalar lookup is assumed.
Both Buchstab polarities retain their full strict prime carrier, the actual
parent ceiling and previous-generation arrays. The original integer suffix
is NOT identified with the arithmetic prime sum; those are compared, not
silently equated, by the subsequent count induction.
-/
namespace ImbalancedChen.Part5OriginalH430RequestedNonbankSupply

noncomputable section
open Set
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter P5OriginalFeedbackTableKernels
open P5OriginalActionMassBound
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open Part5OriginalH430PrimeChildAdmission
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430BuchstabArithmeticRows
open Part5OriginalBuchstabImmutable430Budget Part5OriginalBuchstabRowMass
open Part5OriginalH430DecisionProvenance Part5OriginalH430OwnedBuchstabLower
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedAdmission Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedBankRows
open Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430BuchstabPhysicalBudget
open Part5OriginalUpsilon5CausalDictionary (floorValue)

/-- Read the original strict prime set, with no reoptimized query or
ceiling. This is a LIST: each prime component survives as one occurrence. -/
def buchstabEdges (N : ℕ) (Q : ℝ) (r : Request) : List (Edge N) :=
  (singleChildren (.buchstab r.node.upper r.node.physical.argument)
    N Q r.old r.node.physical.ceiling).toList.map (.buchstab r.node.upper)

theorem children_eq_retained {N g : ℕ} {Q : ℝ} {r : Request} {i : Fin 200}
    (hs : Selected g r i .retained) : children N Q g r = [.retained i] := by
  simp only [children,hs.1,hs.2,branchEdges]

theorem children_eq_buchstab {N g : ℕ} {Q : ℝ} {r : Request} {i : Fin 200}
    (hs : Selected g r i .buchstab) : children N Q g r = buchstabEdges N Q r := by
  simp only [children,hs.1,hs.2,branchEdges,buchstabEdges]

/-- The retained outcome is the OLD specified cell's value, even when a
scalar closed-min owner changes between g and g+1. -/
theorem requested_retained_value {g : ℕ} {r : Request} {i : Fin 200}
    (hs : Selected g r i .retained) :
    requestValue (iterate (g+1)) r = floorValue (iterate g r.node.upper) i := by
  simpa only [choiceValue, floorValue] using selected_value hs

theorem requested_retained_children_value {N g : ℕ} {Q : ℝ} {r : Request}
    {i : Fin 200} (hs : Selected g r i .retained) :
    edgeValue Q (iterate g) r (children N Q g r) =
      thetaAtom N Q (parentProduct r.old)*floorValue (iterate g r.node.upper) i := by
  rw [children_eq_retained hs]
  exact retained_edgeValue N Q (iterate g) r i

/-- A selected Buchstab request reads exactly the ORIGINAL previous
integer suffix. This is not a prime-to-integral count comparison. -/
theorem requested_buchstab_value {g : ℕ} {r : Request} {i : Fin 200}
    (hs : Selected g r i .buchstab) :
    requestValue (iterate (g+1)) r =
      (buchstabValue (iterate g) r.node.upper i : ℝ)/(2:ℝ)^80 := by
  simpa only [choiceValue] using selected_value hs

private theorem list_sum_finset {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (s.toList.map f).sum = ∑ i ∈ s, f i := by
  change (s.val.toList.map f).sum = (s.val.map f).sum
  exact Multiset.sum_map_toList _ _

private theorem buchstab_edge_coords (N : ℕ) (up : Bool) (q : Fin (N+1)) :
    edgeCoordinates (.buchstab up q) = singleCoordinates N q.val := by
  funext j
  fin_cases j <;> simp [edgeCoordinates,edgePrimes,singleCoordinates,physicalPrime]

/-- A singleton coefficient is the original Buchstab arithmetic atom,
not a new abstract row. It has multiplier ONE, no 1/2 or 1/5. -/
private theorem buchstab_edge_coefficient {N : ℕ} {Q : ℝ} {r : Request}
    (hr : Coherent N Q r) (q : Fin (N+1))
    (hq : q ∈ singleChildren (.buchstab r.node.upper r.node.physical.argument)
      N Q r.old r.node.physical.ceiling) (b : RowAtom) :
    coefficient Q r (.buchstab r.node.upper q) b =
      match b with
      | .inl a => if r.node.upper then 0 else
          pointAtom (thetaAtom N Q (parentProduct r.old*q.val)) false
            (buchstabArgument Q r.old q.val) a
      | .inr a => if r.node.upper then
          pointAtom (thetaAtom N Q (parentProduct r.old*q.val)) true
            (buchstabArgument Q r.old q.val) a else 0 := by
  have harg := actual_buchstab_argument (coherent_window hr)
    (mem_singleChildren.mp hq).1.1 (coherent_residual hr)
  have hcoords := buchstab_edge_coords N r.node.upper q
  have hquery : (nextRequest r (.buchstab r.node.upper q)).node.physical.argument =
      buchstabArgument Q r.old q.val := by
    change (perform r.node.physical (edgeShape (.buchstab r.node.upper q))
      (edgeCoordinates (.buchstab r.node.upper q))).argument = _
    rw [hcoords]
    cases hu : r.node.upper <;>
      simpa only [edgeShape,perform] using harg
  have hword : parentProduct (nextRequest r (.buchstab r.node.upper q)).old =
      parentProduct r.old*q.val := by
    simp [nextRequest,edgeShape,edgePrimes,appendedWord,parentProduct,
      List.prod_append]
  cases hu : r.node.upper <;> cases b with
  | inl a =>
      simp [coefficient,edgeWeight,requestAtom,nextRequest,edgeMode,edgeShape,
        advance,childUpper,hu,hquery,hword,pointAtom]
  | inr a =>
      simp [coefficient,edgeWeight,requestAtom,nextRequest,edgeMode,edgeShape,
        advance,childUpper,hu,hquery,hword,pointAtom]

/-- Exact 802-atom arithmetic row, including the true parent ceiling and
both polarities. No scalar-vs-cell selection shortcut is involved. -/
theorem buchstab_edgeRow_eq {N : ℕ} {Q : ℝ} {r : Request}
    (hr : Coherent N Q r) (b : RowAtom) :
    edgeRow Q r (buchstabEdges N Q r) b =
      strictRow r.node.upper N Q r.node.physical.ceiling r.old r.node.physical b := by
  change ((buchstabEdges N Q r).map (fun e => coefficient Q r e b)).sum = _
  simp only [buchstabEdges,List.map_map,Function.comp_def]
  rw [list_sum_finset]
  calc
    _ = ∑ q ∈ singleChildren (.buchstab r.node.upper r.node.physical.argument)
          N Q r.old r.node.physical.ceiling,
          match b with
          | .inl a => if r.node.upper then 0 else
              pointAtom (thetaAtom N Q (parentProduct r.old*q.val)) false
                (buchstabArgument Q r.old q.val) a
          | .inr a => if r.node.upper then
              pointAtom (thetaAtom N Q (parentProduct r.old*q.val)) true
                (buchstabArgument Q r.old q.val) a else 0 := by
        apply Finset.sum_congr rfl
        intro q hq
        exact buchstab_edge_coefficient hr q hq b
    _ = _ := by
        cases hu : r.node.upper <;> cases b <;>
          simp [strictRow,rowFrom,hu]

/-- The generated selected branch, not the whole union of offers, has
exactly the original strict Buchstab row. -/
theorem requested_buchstab_row_eq {N g : ℕ} {Q : ℝ} {r : Request}
    {i : Fin 200} (hr : Coherent N Q r)
    (hs : Selected g r i .buchstab) (b : RowAtom) :
    edgeRow Q r (children N Q g r) b =
      strictRow r.node.upper N Q r.node.physical.ceiling r.old r.node.physical b := by
  rw [children_eq_buchstab hs]
  exact buchstab_edgeRow_eq hr b

/-- The owner was resolved at g+1; the original previous-generation
strict prime sum is the ACTUAL child value at generation g. -/
theorem requested_buchstab_children_value {N g : ℕ} {Q : ℝ} {r : Request}
    {i : Fin 200} (hr : Coherent N Q r) (hs : Selected g r i .buchstab) :
    edgeValue Q (iterate g) r (children N Q g r) =
      ∑ q ∈ singleChildren (.buchstab r.node.upper r.node.physical.argument)
        N Q r.old r.node.physical.ceiling,
        thetaAtom N Q (parentProduct r.old*q.val) *
          tableFunction r.node.upper
            (if r.node.upper then iterate g false else iterate g true)
            (buchstabArgument Q r.old q.val) := by
  rw [← edgeRow_value]
  simp_rw [requested_buchstab_row_eq hr hs]
  simpa using
    (strictRow_value r.node.upper N Q r.node.physical.ceiling r.old
      r.node.physical (iterate g true) (iterate g false))

/-- Derived from the actual selected cell, including lower s=2. -/
theorem requested_buchstab_guard {N : ℕ} {Q : ℝ} {r : Request}
    {g : ℕ} {i : Fin 200} (hr : Coherent N Q r)
    (hs : Selected g r i .buchstab) :
    directionGuard r.node.upper r.node.physical := by
  have htwo := selected_buchstab_guard hr.read_valid hs
  cases hu : r.node.upper with
  | false => simpa only [directionGuard,hu] using htwo
  | true => trivial

/-- One common eventual threshold for either genuinely selected
Buchstab request (specified cell or closed scalar owner), all g<430.
This remains an arithmetic FEEDBACK row result, not a count licence. -/
theorem uniform_requested_buchstab_local {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ Q : ℝ, ∀ r : Request,
      ∀ g : Fin 430, ∀ i : Fin 200,
      Coherent N Q r → Selected g.val r i .buchstab →
      frozenResidualFloor ≤ physicalLevel N Q r.old →
      (∑ b : RowAtom,
        |edgeRow Q r (children N Q g.val r) b -
          thetaAtom N Q (parentProduct r.old)*integralRow r.node.upper r.node.physical b| *
          |oldAtomValue (precedingH g) (precedingh g) b|) ≤
            epsilon*thetaAtom N Q (parentProduct r.old) ∧
      (∀ b, 0 ≤ edgeRow Q r (children N Q g.val r) b) ∧
      (∑ b : RowAtom, edgeRow Q r (children N Q g.val r) b) ≤
        5*thetaAtom N Q (parentProduct r.old) := by
  obtain ⟨Te,hTe⟩ := immutable430_uniform_buchstab_rows
    frozenResidualFloor_pos he
  obtain ⟨Tm,hTm⟩ := uniform_strictRow_mass frozenResidualFloor_pos
  refine ⟨max 4 (max Te Tm),le_max_left _ _,?_⟩
  intro N hN Q r g i hr hs hfloor
  have hw := coherent_window hr
  have hL := coherent_residual hr
  have hg := requested_buchstab_guard hr hs
  have harg : 1 ≤ r.node.physical.argument :=
    (by norm_num : (1:ℝ) ≤ 2).trans (selected_buchstab_guard hr.read_valid hs)
  have he' := hTe N (by omega) Q ({()} : Finset Unit)
    (fun _ => r.old) (fun _ => r.node.physical)
    (fun _ => r.node.physical.ceiling) (fun _ => (1:ℝ))
    (fun _ => r.node.upper) (fun _ => g)
    (fun _ _ => hw) (fun _ _ => hL) (fun _ _ => rfl)
    (fun _ _ => harg) (fun _ _ => hg)
    (fun _ _ => zero_le_one) (fun _ _ => hfloor)
  have herr : strictAbsoluteError r.node.upper N Q r.node.physical.ceiling r.old
      r.node.physical (precedingH g) (precedingh g) ≤
      epsilon*thetaAtom N Q (parentProduct r.old) := by
    simpa only [parentTheta,Finset.sum_singleton,one_mul] using he'
  have hm := hTm N (by omega) Q r.node.physical.ceiling r.old r.node.physical
    r.node.upper hw hL rfl harg hg hfloor
  simp_rw [requested_buchstab_row_eq hr hs]
  exact ⟨herr,hm.1,hm.2⟩

/-- Signed applied errors are DOWNSTREAM of coefficientwise absolute
control. This theorem never uses cancellation to prove the stronger bound. -/
theorem requested_buchstab_applied_le {N : ℕ} {Q : ℝ} {r : Request}
    {g : Fin 430} {i : Fin 200} (hr : Coherent N Q r)
    (hs : Selected g.val r i .buchstab) :
    |edgeValue Q (iterate g.val) r (children N Q g.val r) -
      thetaAtom N Q (parentProduct r.old) *
        idealProfile r.node.upper r.node.physical (precedingH g) (precedingh g)| ≤
      strictAbsoluteError r.node.upper N Q r.node.physical.ceiling r.old
        r.node.physical (precedingH g) (precedingh g) := by
  have hg := requested_buchstab_guard hr hs
  rw [← edgeRow_value]
  simp_rw [requested_buchstab_row_eq hr hs]
  rw [← integralRow_value hg,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_assoc,← sub_mul,abs_mul]

end
end ImbalancedChen.Part5OriginalH430RequestedNonbankSupply
