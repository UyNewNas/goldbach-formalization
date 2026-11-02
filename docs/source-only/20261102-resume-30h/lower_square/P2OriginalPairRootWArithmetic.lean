import ImbalancedChen.P2OriginalPairBufferedRootProvenance
import ImbalancedChen.ActualSelectedSubproductParameters

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The ORIGINAL pair-root max is inspected before any continuation policy.
Its W term is B(a), a fixed rough ceiling, not a fictitious selected
product. Ties with either tent are assigned to the tent. The original
U6 piecewise domain excludes this strict root-W branch; this does not
exclude later W improvements in U6. A genuine U5 root-W gap pays all
three initialization exponents, including BOTH critical upper bounds.
-/
namespace ImbalancedChen.P2OriginalPairRootWArithmetic
noncomputable section
open scoped Classical BigOperators
open P2LowerCapPlanIntegerRetention P2PhysicalIncomingPrefixCells
open P2OriginalPairRootRoughProducer P2OriginalSelectedPairNativeData
open P2OriginalPairBufferedRootProvenance
open P2OriginalLowerWholeBoxBranchSelect

def cutoff : ℝ := 417/5000
def W : ℝ := VariableEnvelope.B cutoff

/-- Independent raw-root branch decision, with both tent ties retained. -/
def rootWChosen (sixth : Bool) (u t : ℝ) : Bool :=
  decide ((sixth=false ∨ t<VariableEnvelope.mu) ∧
    VariableEnvelope.v t<W ∧ VariableEnvelope.v (t+u)<W)

/-- The W source reads the retained ROUGH CEILING at position three. -/
def sourcePoint (u t : ℝ) : Fin 5 → ℝ := ![t,u,cutoff,0,0]

theorem source_form (u t : ℝ) :
    (SourceForm.wSlot 2).affine.eval (sourcePoint u t)=W ∧
      (SourceForm.wSlot 2).supportMask=∅ := by
  constructor
  · norm_num [SourceForm.affine,P2OriginalLowerAffineTieSelector.AffineBranch.eval,
      sourcePoint,W,VariableEnvelope.B,VariableEnvelope.cap,cutoff,Fin.sum_univ_succ]
  · rfl

/-- No candidate policy appears in this identity for the ORIGINAL level. -/
theorem chosen_original_root (sixth : Bool) (N : ℕ) (p : ℕ×ℕ)
    (hW : rootWChosen sixth (coordinate N p.1) (coordinate N p.2)=true) :
    rootLevel sixth N p=W := by
  have hh : (sixth=false ∨ coordinate N p.2<VariableEnvelope.mu) ∧
      VariableEnvelope.v (coordinate N p.2)<W ∧
      VariableEnvelope.v (coordinate N p.2+coordinate N p.1)<W :=
    of_decide_eq_true hW
  cases sixth with
  | false =>
      change max (VariableEnvelope.v (coordinate N p.2))
        (max (VariableEnvelope.v (coordinate N p.2+coordinate N p.1)) W)=W
      rw [max_eq_right hh.2.2.le,max_eq_right hh.2.1.le]
  | true =>
      have ht : coordinate N p.2<VariableEnvelope.mu := hh.1.resolve_left (by decide)
      change P5U6CausalLevelGeometry.physicalLevel _ _=W
      rw [P5U6CausalLevelGeometry.physicalLevel,if_pos ht]
      change max (VariableEnvelope.v (coordinate N p.2))
        (max (VariableEnvelope.v (coordinate N p.2+coordinate N p.1)) W)=W
      rw [max_eq_right hh.2.2.le,max_eq_right hh.2.1.le]

/-- The actual L6 rectangle cannot choose this ROOT W term. Later
    W sources are a different obligation and are not excluded. -/
theorem sixth_root_W_absent {eta : ℝ} {x : Fin 2 → ℝ}
    (hx : x∈currentChenUpsilon6LogDomain eta) :
    rootWChosen true (x 0) (x 1)=false := by
  by_cases hw : rootWChosen true (x 0) (x 1)=true
  · have hh : (true=false ∨ x 1<VariableEnvelope.mu) ∧
        VariableEnvelope.v (x 1)<W ∧ VariableEnvelope.v (x 1+x 0)<W :=
      of_decide_eq_true hw
    have ht : x 1<VariableEnvelope.mu := hh.1.resolve_left (by decide)
    have hht := (mem_currentChenUpsilon6LogRectangle.mp hx.1).2.2.1
    have hv := hh.2.1
    rw [VariableEnvelope.v_eq_A ht.le] at hv
    norm_num [VariableEnvelope.A,W,VariableEnvelope.B,VariableEnvelope.cap,
      cutoff] at hv
    norm_num [P5U6CausalLevelGeometry.h] at hht
    linarith
  · cases hh : rootWChosen true (x 0) (x 1) with
    | false => rfl
    | true => exact (hw hh).elim

def theta (buffer : ℝ) : ℝ := W-buffer/2
def delta (buffer : ℝ) : ℝ := buffer/4

/-- Numerical margin at the real original W-root crop. The input is a
    gap in the original max, not any factor or critical-interval licence.
    The second critical bound keeps the moving residue exponent 1+3kappa. -/
theorem root_W_exponents {u t buffer kappa : ℝ}
    (htriangle : (![u,t] : Fin 2 → ℝ)∈Part5OriginalUpsilon5CausalDictionary.triangle)
    (hb : 0<buffer) (hbhi : buffer≤1/1000)
    (hgap : VariableEnvelope.A t+2*buffer≤W) (hk : kappa≤buffer) :
    (1/2:ℝ)<theta buffer ∧ theta buffer≤153/256 ∧
      t≤2*theta buffer-1-buffer ∧
      2*u≤1-theta buffer-2*delta buffer ∧
      (1/3:ℝ)≤1-theta buffer-2*delta buffer ∧
      cutoff+(2*theta buffer-1)+buffer/4≤
        actualSelectedSubproductUpper (1+3*kappa) (theta buffer) ∧
      theta buffer-2*delta buffer=W-buffer := by
  obtain ⟨hu,hut,ht⟩ := Part5OriginalUpsilon5CausalDictionary.mem_triangle.mp htriangle
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at hu hut ht
  dsimp [Part5OriginalUpsilon5CausalDictionary.a,
    Part5OriginalUpsilon5CausalDictionary.h] at hu ht
  dsimp [theta,delta,W,VariableEnvelope.B,VariableEnvelope.cap,
    VariableEnvelope.A,cutoff] at hgap ⊢
  refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith,?_,by ring⟩
  unfold actualSelectedSubproductUpper
  apply le_min <;> linarith

/-- The primitive historical condition says that each actually read
    plan decision inherits. It does not assert any final cap or gate. -/
def Inherits {depth mesh : ℕ} (P : CapPlan depth mesh) (a b : ℝ) :
    P2LowerCapPlanIntegerRetention.Trace → List ℝ → Prop
  | _, [] => True
  | H, x::xs => (∃ argument, planChoice P a b (H.word++[x])=.inherit argument) ∧
      Inherits P a b (step P a b H x) xs

theorem inherited_run_cap {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (H : P2LowerCapPlanIntegerRetention.Trace) (xs : List ℝ)
    (hh : Inherits P a b H xs) : (run P a b H xs).cap=H.cap := by
  induction xs generalizing H with
  | nil => rfl
  | cons x xs ih =>
      obtain ⟨⟨argument,hchoice⟩,hrest⟩ := hh
      change (run P a b (step P a b H x) xs).cap=H.cap
      rw [ih _ hrest]
      change (planChoice P a b (H.word++[x])).freeze H.cap=H.cap
      rw [hchoice]
      rfl

/-- The unchanged original double buffer, once buffer and auxiliary
    W parameter are related by algebra; no original.policy replacement. -/
theorem inherited_original_W_level {depth mesh : ℕ} (P : CapPlan depth mesh)
    (a b : ℝ) (sixth : Bool) (buffer : ℚ) (N : ℕ) (p : ℕ×ℕ) (xs : List ℝ)
    (hW : rootWChosen sixth (coordinate N p.1) (coordinate N p.2)=true)
    (hh : Inherits P a b (pairRoot N p (rootSeed sixth buffer N p)) xs) :
    (run P a b (pairRoot N p (rootSeed sixth buffer N p)) xs).cap+(buffer:ℝ)=
      theta buffer-2*delta buffer := by
  rw [inherited_run_cap P a b _ _ hh]
  change rootSeed sixth buffer N p+(buffer:ℝ)=_
  rw [rootSeed,chosen_original_root sixth N p hW]
  dsimp [theta,delta]
  ring

end
end ImbalancedChen.P2OriginalPairRootWArithmetic
