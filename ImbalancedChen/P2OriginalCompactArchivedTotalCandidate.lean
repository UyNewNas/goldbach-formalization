import ImbalancedChen.P2OriginalCompactQ80CacheEncloser
import ImbalancedChen.P2OriginalCompactConcreteLoop
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.TreeMap.Raw.WF

/-!
Finite source candidate for the original archived whole upper equality.

The public statement retains the original source-computed fixedUpper and
historical compact integer. A private balanced table is computed from the
unchanged nodeUpdate recurrence and proved to have exactly the same total
lookup as the original source table. Generic formula equalities transport
the computed fixed term back to the original public expression.

No saved first-integral, tail, table, or charge-list output is used as an
evaluator. This module performs no adaptive run; the separate historical
endpoint candidate must still establish the actual two-million-split total.
The closed kernel proof and its independent replay require their original
acceptance gates. Runtime observations are diagnostic evidence only.
-/
namespace ImbalancedChen.P2OriginalCompactArchivedTotalCandidateSourceOnly

open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80CacheEncloserSourceOnly

namespace KernelTableProof

open Certificates.P2HistoricQ80DefectLookup
open Certificates.P2HistoricI80DivisionSoundness
open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80CacheEncloserSourceOnly

universe u

private abbrev NodeMap (α : Type u) := Std.TreeMap.Raw Nat α

private def mapSpecification {α : Type u} (initial : α)
    (update : Nat → (Nat → α) → α) : Nat → (Nat → α) :=
  Nat.rec (motive := fun _ => Nat → α) (fun _ => initial)
    (fun n old i => if i = n + 1 then update (n + 1) old else old i)

private def mapRead {α : Type u} (initial : α) (nodes : NodeMap α) (i : Nat) : α :=
  nodes.getD i initial

private def mapStep {α : Type u} (initial : α)
    (update : Nat → (Nat → α) → α) (next : Nat) (nodes : NodeMap α) : NodeMap α :=
  nodes.insert next (update next (mapRead initial nodes))

private def mapBuildFrom {α : Type u} (initial : α)
    (update : Nat → (Nat → α) → α) : Nat → Nat → NodeMap α → NodeMap α
  | 0, _, nodes => nodes
  | remaining + 1, next, nodes =>
      mapBuildFrom initial update remaining (next + 1)
        (mapStep initial update next nodes)

private def Represents {α : Type u} (initial : α)
    (update : Nat → (Nat → α) → α) (completed : Nat) (nodes : NodeMap α) : Prop :=
  nodes.WF ∧ mapRead initial nodes = mapSpecification initial update completed

private theorem empty_represents {α : Type u} (initial : α)
    (update : Nat → (Nat → α) → α) :
    Represents initial update 0 (∅ : NodeMap α) := by
  refine ⟨Std.TreeMap.Raw.WF.emptyc, ?_⟩
  funext i
  change (∅ : NodeMap α).getD i initial = initial
  exact Std.TreeMap.Raw.getD_emptyc

private theorem mapRead_step {α : Type u} (initial : α)
    (update : Nat → (Nat → α) → α) (next : Nat)
    (nodes : NodeMap α) (hw : nodes.WF) :
    mapRead initial (mapStep initial update next nodes) =
      fun i => if i = next then update next (mapRead initial nodes)
        else mapRead initial nodes i := by
  funext i
  have hcmp : compare next i = Ordering.eq ↔ i = next :=
    Nat.compare_eq_eq.trans eq_comm
  simpa only [mapRead, mapStep, hcmp] using
    (Std.TreeMap.Raw.getD_insert (t := nodes) hw (k := next) (a := i)
      (v := update next (mapRead initial nodes)) (fallback := initial))

private theorem mapStep_represents {α : Type u} (initial : α)
    (update : Nat → (Nat → α) → α) (n : Nat)
    (nodes : NodeMap α) (h : Represents initial update n nodes) :
    Represents initial update (n + 1) (mapStep initial update (n + 1) nodes) := by
  constructor
  · exact h.1.insert
  · rw [mapRead_step initial update (n + 1) nodes h.1, h.2]
    rfl

private theorem mapBuildFrom_represents {α : Type u} (initial : α)
    (update : Nat → (Nat → α) → α) (remaining n : Nat)
    (nodes : NodeMap α) (h : Represents initial update n nodes) :
    Represents initial update (n + remaining)
      (mapBuildFrom initial update remaining (n + 1) nodes) := by
  induction remaining generalizing n nodes with
  | zero => simpa only [mapBuildFrom, Nat.add_zero] using h
  | succ remaining ih =>
      rw [show n + (remaining + 1) = (n + 1) + remaining by omega]
      exact ih (n + 1) (mapStep initial update (n + 1) nodes)
        (mapStep_represents initial update n nodes h)

private theorem mapBuildFrom_empty_lookup {α : Type u} (initial : α)
    (update : Nat → (Nat → α) → α) (count : Nat) :
    mapRead initial (mapBuildFrom initial update count 1 ∅) =
      mapSpecification initial update count := by
  have h := mapBuildFrom_represents initial update count 0 ∅
    (empty_represents initial update)
  simpa only [Nat.zero_add] using h.2

private theorem mapBuildFrom_original_lookup (g count : Nat) :
    mapRead initialNode (mapBuildFrom initialNode (nodeUpdate g) count 1 ∅) =
      sourceState g count := by
  simpa only [mapSpecification, sourceState] using
    mapBuildFrom_empty_lookup initialNode (nodeUpdate g) count

private abbrev kernelTable : NodeMap Node :=
  mapBuildFrom initialNode (nodeUpdate 16384) (12 * 16384) 1 ∅

private theorem kernelTable_lookup : mapRead initialNode kernelTable = sourceTable :=
  mapBuildFrom_original_lookup 16384 (12 * 16384)

private def d10OfReader (read : Nat → Node) : ℤ :=
  up ((read (10 * 16384)).hh - (read (10 * 16384)).ll) (10 : ℤ)

private def tailIntervalOfD10 (d : ℤ) : I80 :=
  let d0 := I80.raw d
  let ell := logI (rho/cutoff)
  let poly := (ell.mul ell).add ((I80.point 2).mul ell) |>.add (I80.point 2)
  historicalDiv
    (((((I80.point 2).mul d0).mul (I80.point (10^2))).mul
      (I80.point cutoff)).mul poly)
    (I80.point ((rho-cutoff)^2))

private def fixedUpperOfD10 (d : ℤ) : ℚ :=
  4/theta + ((firstBounds.upper+(tailIntervalOfD10 d).hi : ℤ) : ℚ)/(scale : ℚ)

private theorem fixedUpperWith_factor :
    fixedUpperWith =
      fun nodes => fixedUpperOfD10 (d10OfReader (lookup nodes)) := by
  funext nodes
  rfl

private theorem original_fixed_eq_kernel :
    fastFixedUpper =
      fixedUpperOfD10 (d10OfReader (mapRead initialNode kernelTable)) :=
  (congrFun fixedUpperWith_factor tableArray).trans
    (congrArg fixedUpperOfD10
      (congrArg d10OfReader (tableArray_lookup.trans kernelTable_lookup.symm)))

end KernelTableProof

/-- Original archived whole upper endpoint, distinct from the stop target. -/
def archivedOriginalUpper : ℚ :=
  1230679674488580033396846301 / 180734410032387061618573312

set_option maxRecDepth 0 in
set_option maxHeartbeats 0 in
/-- Closed source equality candidate. The private table refinement and
generic formula transport preserve the original computation; the remaining
closed equality is checked by the kernel, without numerical substitutes. -/
theorem cached_fixed_plus_original_compact_eq_archived_candidate :
    fastFixedUpper +
        (P2OriginalCompactConcreteLoopSourceOnly.historicalUpper : ℚ) / (scale : ℚ) =
      archivedOriginalUpper := by
  rw [KernelTableProof.original_fixed_eq_kernel]
  decide +kernel

/-- Symbolic exact cache transport; neither table implementation is reduced
to prove this transfer. The closed finite equality remains a dependency. -/
theorem original_fixed_plus_original_compact_eq_archived_candidate :
    fixedUpper +
        (P2OriginalCompactConcreteLoopSourceOnly.historicalUpper : ℚ) / (scale : ℚ) =
      archivedOriginalUpper := by
  rw [← fastFixedUpper_eq]
  exact cached_fixed_plus_original_compact_eq_archived_candidate

end ImbalancedChen.P2OriginalCompactArchivedTotalCandidateSourceOnly

