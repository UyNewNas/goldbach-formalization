import ImbalancedChen.P2FiniteMarkedGamma5SelectedWallCatalogue

namespace ImbalancedChen.P2FiniteMarkedGamma5SelectedNativeStrips
noncomputable section
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalH430NativeQueryPaths Part5OriginalH430PhysicalRoots
open Part5OriginalH430FrozenRootRefinement Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430MemberGateRows
open P2FiniteMarkedGamma5FixedNativeItinerary P2FiniteMarkedGamma5RealSelectedPrefix
open P2FiniteMarkedGamma5SelectedQueryRows P2FiniteMarkedGamma5SelectedWallCatalogue
open Set

abbrev Form (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  ℝ × (E →L[ℝ] ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ev (x : E) : Form E →ₗ[ℝ] ℝ where
  toFun r := r.1+r.2 x
  map_add' r s := by simp <;> ring
  map_smul' c r := by simp [mul_add]

def const (c : ℝ) : Form E := (c,0)
@[simp] theorem ev_const (x : E) (c : ℝ) : ev x (const c) = c := by simp [ev,const]

variable {d : ℕ} (sh : Fin d → StepShape)
abbrev Space := NativeSlot sh → ℝ

def coordinate (i : NativeSlot sh) : Form (Space sh) :=
  (0,ContinuousLinearMap.proj i)

@[simp] theorem ev_coordinate (x : Space sh) (i : NativeSlot sh) :
    ev x (coordinate sh i) = x i := by simp [ev,coordinate]

def symbol (i : Fin d) (j : Fin 2) : Form (Space sh) :=
  if h : j.val < arity (sh i) then coordinate sh (.inr ⟨i,⟨j.val,h⟩⟩) else const 0

@[simp] theorem ev_symbol (x : Space sh) (i : Fin d) (j : Fin 2) :
    ev x (symbol sh i j)=nativeCoordinates sh x i j := by
  by_cases h : j.val < arity (sh i) <;> simp [symbol,nativeCoordinates,h]

def nativeRows (a : Fin d → ReadLabel) : List (SymbolicRow (Form (Space sh))) :=
  List.ofFn fun i => (a i,sh i,symbol sh i 0,symbol sh i 1)

private theorem rows_eval (a : Fin d → ReadLabel) (x : Space sh) :
    (nativeRows sh a).map (atRow (ev x)) =
      List.ofFn fun i => (a i,sh i,nativeCoordinates sh x i) := by
  rw [nativeRows,List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply,atRow,ev_symbol,Prod.mk.injEq,true_and]
  funext j
  fin_cases j <;> rfl

def start (nu : ℝ) (clamped : Bool) : Chart (Form (Space sh)) :=
  let x := coordinate sh (.inl ())
  let L := const nu-x
  ⟨const nu,L,x,if clamped then L else const a,if clamped then 2 else 1⟩

def wallList (a : Fin d → ReadLabel) (nu : ℝ) (clamped : Bool) : List (Form (Space sh)) :=
  catalogue (const 1) (start sh nu clamped) (nativeRows sh a)

/-- These two tests describe the original frozen-level and clamp strata.
For the original root code the level equality is frozenLevel_eq_of_code. -/
def chartAt (n : ℕ) (k : Root) (tau nu : ℝ) (clamped : Bool) (v : Space sh) : Prop :=
  let x := v (.inl ())
  frozenLevel n (sourceRoot k tau x).physical.total = nu ∧ 0 < nu-x ∧
    (if clamped then nu-x ≤ 2*a else 2*a < nu-x)

private theorem start_fits (n : ℕ) (k : Root) (tau nu : ℝ) (b : Bool) (v : Space sh)
    (h : chartAt sh n k tau nu b v) :
    (start sh nu b).fits (ev v) (frozenRoot n k tau (v (.inl ()))).physical := by
  let p := (frozenRoot n k tau (v (.inl ()))).physical
  obtain ⟨hs,hL,hb⟩ := h
  have ht : p.total=nu := hs
  have hl : residual p=nu-v (.inl ()) := (frozenRoot_residual n k tau (v (.inl ()))).trans (by rw [hs])
  have hc : p.ceiling=v (.inl ()) := rfl
  change (start sh nu b).fits (ev v) p
  have hLp : 0 < residual p := by simpa only [hl] using hL
  obtain hp | hp := frozen_root_chart n k tau (v (.inl ())) hLp (by norm_num [a])
  · cases b
    · exact False.elim (not_lt_of_ge (by simpa only [hl] using hp.1) hb)
    · simpa [Chart.fits,start,ht,hl,hc] using
        (show p.total=nu ∧ residual p=nu-v (.inl ()) ∧ p.ceiling=v (.inl ()) ∧
          0<residual p ∧ represents p 2 (residual p) from ⟨ht,hl,hc,hLp,hp.2⟩)
  · cases b
    · simpa [Chart.fits,start,ht,hl,hc] using
        (show p.total=nu ∧ residual p=nu-v (.inl ()) ∧ p.ceiling=v (.inl ()) ∧
          0<residual p ∧ represents p 1 a from ⟨ht,hl,hc,hLp,hp.2⟩)
    · exact False.elim (not_lt_of_ge hb (by simpa only [hl] using hp.1))

theorem proper_crossing {x y : E} (r : Form E) (h : ¬ agree (ev x) (ev y) r) :
    r.2 ≠ 0 ∧ |r.1+r.2 x| ≤ ‖r.2‖ * ‖x-y‖ := by
  classical
  have he : ev x r ≠ ev y r := by
    intro hval
    exact h (by simp [agree,hval])
  have hlin : r.2 ≠ 0 := by
    intro hz
    exact he (by simp [ev,hz])
  have hstrip : |ev x r| ≤ |ev x r-ev y r| := by
    by_cases hp : 0 < ev x r ↔ 0 < ev y r
    · have hn : ¬ (0 ≤ ev x r ↔ 0 ≤ ev y r) := fun hn => h ⟨hp,hn⟩
      have hs := (changed_row_strip (weakRow 1 0 0) (L := ev x r) (M := ev y r)
        (s := 0) (t := 0) (by simpa [weakRow,GateRow.value,GateRow.accepts] using hn)).2
      simpa [weakRow,GateRow.value] using hs
    · have hs := (changed_row_strip (strictRow 1 0 0) (L := ev x r) (M := ev y r)
        (s := 0) (t := 0) (by simpa [strictRow,GateRow.value,GateRow.accepts] using hp)).2
      simpa [strictRow,GateRow.value] using hs
  refine ⟨hlin,hstrip.trans ?_⟩
  have heq : ev x r-ev y r = r.2 (x-y) := by simp [ev] <;> ring
  rw [heq,← Real.norm_eq_abs]
  exact r.2.le_opNorm _

/-- Two points of a mixed atlas box in the same original root and clamp
stratum hit a proper affine strip from the fixed finite native catalogue.
No norm bound on a structural equality is charged. -/
theorem changed_selected_native_strip (n : ℕ) (k : Root) (tau nu : ℝ)
    (a : Fin d → ReadLabel) (b : Bool) (x y : Space sh)
    (hx : chartAt sh n k tau nu b x) (hy : chartAt sh n k tau nu b y)
    (h : ¬ (x ∈ selected n k tau sh a ↔ y ∈ selected n k tau sh a)) :
    ∃ r ∈ wallList sh a nu b, r.2 ≠ 0 ∧ |r.1+r.2 x| ≤ ‖r.2‖*‖x-y‖ := by
  classical
  by_contra hn
  apply h
  have hs : ∀ r ∈ wallList sh a nu b, agree (ev x) (ev y) r := by
    intro r hr
    by_contra hd
    exact hn ⟨r,hr,proper_crossing r hd⟩
  apply and_congr_right
  intro _
  have hw := walk_agrees (const 1) (start sh nu b) (nativeRows sh a)
    (ev x) (ev y) _ _ .scalar 430 (start_fits sh n k tau nu b x hx)
    (start_fits sh n k tau nu b y hy) rfl (ev_const x 1) (ev_const y 1) hs
  simpa only [rows_eval] using hw

end
end ImbalancedChen.P2FiniteMarkedGamma5SelectedNativeStrips
