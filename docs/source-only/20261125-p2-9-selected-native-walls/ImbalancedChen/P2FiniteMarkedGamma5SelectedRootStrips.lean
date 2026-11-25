import ImbalancedChen.P2FiniteMarkedGamma5SelectedNativeStrips

namespace ImbalancedChen.P2FiniteMarkedGamma5SelectedRootStrips
noncomputable section
open Set
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open P2PhysicalIncomingPrefixCells Part5UpperTables Part5UpperTables.OriginalU34
open Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430NativeQueryPaths P2FiniteMarkedGamma5FixedNativeItinerary
open P2FiniteMarkedGamma5RealSelectedPrefix P2FiniteMarkedGamma5SelectedWallCatalogue
open P2FiniteMarkedGamma5SelectedNativeStrips

/-- Includes every possible frozen lower endpoint and the singleton at 1.
Repeated endpoints may remain in this list. -/
def endpoints : ℕ → List ℝ
  | 0 => [1] ++ List.ofFn (fun j : Fin 2 => logPrimeMeshPoint 0 1 0 j.val)
  | n+1 => endpoints n ++ List.ofFn (fun j : Fin (n+3) => logPrimeMeshPoint 0 1 (n+1) j.val)

private theorem one_mem (n : ℕ) : (1:ℝ) ∈ endpoints n := by
  induction n with
  | zero => simp [endpoints]
  | succ n ih => exact List.mem_append_left _ ih

private theorem mesh_mem {m n j : ℕ} (hm : m≤n) (hj : j≤m+1) :
    logPrimeMeshPoint 0 1 m j ∈ endpoints n := by
  induction n with
  | zero =>
    have h : m=0 := by omega
    subst m
    apply List.mem_append_right
    exact List.mem_ofFn.mpr ⟨⟨j,by omega⟩,rfl⟩
  | succ n ih =>
    by_cases h : m=n+1
    · subst m
      apply List.mem_append_right
      exact List.mem_ofFn.mpr ⟨⟨j,by omega⟩,rfl⟩
    · exact List.mem_append_left _ (ih (by omega))

private theorem raw_mem (n : ℕ) (v : ℝ) : rawLower n v ∈ endpoints n := by
  unfold rawLower
  cases exponentCode 0 1 n v with
  | none => exact one_mem _
  | some j => exact mesh_mem (le_refl _) (by omega)

theorem frozen_mem (n : ℕ) (v : ℝ) : frozenLevel n v ∈ endpoints n := by
  induction n with
  | zero => exact raw_mem 0 v
  | succ n ih =>
    by_cases h : frozenLevel n v ≤ rawLower (n+1) v
    · simpa only [frozenLevel,max_eq_right h] using raw_mem (n+1) v
    · rw [frozenLevel,max_eq_left (le_of_not_ge h)]
      exact List.mem_append_left _ ih

/-- A root-code transition can only change one of these comparisons.
It includes weak lower and strict upper endpoints of every original cell. -/
private theorem codes_equal {n : ℕ} {v w : ℝ} (hv : v ∈ Icc (0:ℝ) 1)
    (hw : w ∈ Icc (0:ℝ) 1)
    (h : ∀ c ∈ endpoints n, (c≤v ↔ c≤w) ∧ (c<v ↔ c<w)) :
    rootCode n v=rootCode n w := by
  funext i
  change exponentCode 0 1 i.val v = exponentCode 0 1 i.val w
  symm
  apply exponentCode_eq_of_cell (by norm_num) hw
  have hh := exponentCode_membership (m:=i.val) hv
  cases he : exponentCode 0 1 i.val v with
  | none =>
    have heq : v=1 := by simpa [he,exponentCell] using hh
    have h1 : 1≤w := (h 1 (one_mem n)).1.mp heq.ge
    exact le_antisymm hw.2 h1
  | some j =>
    have hv' : logPrimeMeshPoint 0 1 i.val j.val ≤ v ∧
        v < logPrimeMeshPoint 0 1 i.val (j.val+1) := by simpa [he,exponentCell] using hh
    refine ⟨(h _ (mesh_mem (by omega : i.val≤n) (by omega : j.val≤i.val+1))).1.mp hv'.1,?_⟩
    exact lt_of_not_ge (fun hn => hv'.2.not_ge
      ((h _ (mesh_mem (by omega : i.val≤n) (by omega : j.val+1≤i.val+1))).1.mpr hn))

variable {d : ℕ} (sh : Fin d → StepShape)

private def X : Form (Space sh) := coordinate sh (.inl ())
private def armA : Form (Space sh) := (1/2:ℝ) • (const 1+X sh)
private def armC : Form (Space sh) := const (57/64)-(3/2:ℝ) • X sh

private theorem arms (x : Space sh) :
    ev x (armA sh)=VariableEnvelope.A (x (.inl ())) ∧
    ev x (armC sh)=VariableEnvelope.C (x (.inl ())) := by
  simp [armA,armC,X,VariableEnvelope.A,VariableEnvelope.C,smul_eq_mul] <;> ring

def walls (n : ℕ) (a : Fin d → ReadLabel) : List (Form (Space sh)) :=
  (X sh-const tailCutoff) :: (endpoints n).flatMap fun v =>
    [armA sh-const v,armC sh-const v,const (v-2*Part5OriginalUpsilon5CausalDictionary.a)-X sh] ++
      wallList sh a v true ++ wallList sh a v false

private theorem main_total (x : ℝ) :
    x+mainResidual x=min (VariableEnvelope.A x) (VariableEnvelope.C x) := by
  simp [mainResidual,VariableEnvelope.v_eq_min] <;> ring

private theorem tail_total (tau x : ℝ) : x+(tailResidual x-tau)=1/2-tau := by
  unfold tailResidual
  ring

/-- Preserve the complete original root code under agreement on the existing
finite root walls. This also fixes each code-selected atlas component. -/
theorem rootCode_eq_of_agree (n : ℕ) (k : Root) (tau : ℝ) (xs ys : Space sh)
    (a : Fin d → ReadLabel) (ht : 0≤tau) (ht' : tau≤1/12)
    (hx : xs (.inl ()) ∈ rootBand k) (hy : ys (.inl ()) ∈ rootBand k)
    (hs : ∀ r ∈ walls sh n a, agree (ev xs) (ev ys) r) :
    rootCode n (sourceRoot k tau (xs (.inl ()))).physical.total =
      rootCode n (sourceRoot k tau (ys (.inl ()))).physical.total := by
  let x := xs (.inl ())
  let y := ys (.inl ())
  have hc : (x<tailCutoff ↔ y<tailCutoff) := by
    have H := (hs (X sh-const tailCutoff) (by simp [walls])).2
    simpa [X,x,y,sub_nonneg,not_le] using not_congr H
  have hmain (c : ℝ) (hm : c ∈ endpoints n) :
      (c ≤ x+mainResidual x ↔ c ≤ y+mainResidual y) ∧
      (c < x+mainResidual x ↔ c < y+mainResidual y) := by
    have ha := hs (armA sh-const c) (by
      apply List.mem_cons_of_mem
      exact List.mem_flatMap.mpr ⟨c,hm,by simp⟩)
    have hb := hs (armC sh-const c) (by
      apply List.mem_cons_of_mem
      exact List.mem_flatMap.mpr ⟨c,hm,by simp⟩)
    simp only [agree,map_sub,ev_const,(arms sh xs).1,(arms sh ys).1,
      (arms sh xs).2,(arms sh ys).2,sub_nonneg,sub_pos] at ha hb
    simp only [main_total]
    exact ⟨by simpa only [le_min_iff] using and_congr ha.2 hb.2,
      by simpa only [lt_min_iff] using and_congr ha.1 hb.1⟩
  apply codes_equal (root_total_bounds ht ht' hx) (root_total_bounds ht ht' hy)
  intro c hm
  cases k with
  | U4 => exact hmain c hm
  | U3 =>
    let v (t : ℝ) := t + (if t<tailCutoff then mainResidual t else tailResidual t-tau)
    change (c≤v x ↔ c≤v y) ∧ (c<v x ↔ c<v y)
    by_cases he : x<tailCutoff
    · simpa only [v,if_pos he,if_pos (hc.mp he)] using hmain c hm
    · simp only [v,if_neg he,if_neg (mt hc.mpr he),tail_total,iff_self,and_self]

private theorem same_level (n : ℕ) (k : Root) (tau : ℝ) (xs ys : Space sh)
    (a : Fin d → ReadLabel) (ht : 0≤tau) (ht' : tau≤1/12)
    (hx : xs (.inl ()) ∈ rootBand k) (hy : ys (.inl ()) ∈ rootBand k)
    (hs : ∀ r ∈ walls sh n a, agree (ev xs) (ev ys) r) :
    frozenLevel n (sourceRoot k tau (xs (.inl ()))).physical.total =
      frozenLevel n (sourceRoot k tau (ys (.inl ()))).physical.total := by
  apply frozenLevel_eq_of_code
  exact rootCode_eq_of_agree sh n k tau xs ys a ht ht' hx hy hs

/-- The list precedes the target, both points and the finite-tail loss.
On the original root band, variation of the complete selected predicate
has a proper affine witness in the original native slots. -/
theorem changed_full_root_strip (n : ℕ) (k : Root) (tau : ℝ)
    (a : Fin d → ReadLabel) (x y : Space sh)
    (ht : 0≤tau) (ht' : tau≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hx : x (.inl ()) ∈ rootBand k) (hy : y (.inl ()) ∈ rootBand k)
    (change : ¬ (x ∈ selected n k tau sh a ↔ y ∈ selected n k tau sh a)) :
    ∃ r ∈ walls sh n a, r.2 ≠ 0 ∧ |r.1+r.2 x| ≤ ‖r.2‖*‖x-y‖ := by
  classical
  by_contra h
  have hs : ∀ r ∈ walls sh n a, agree (ev x) (ev y) r := by
    intro r hr
    by_contra hn'
    exact h ⟨r,hr,proper_crossing r hn'⟩
  let nu := frozenLevel n (sourceRoot k tau (x (.inl ()))).physical.total
  have hm : nu ∈ endpoints n := frozen_mem _ _
  have hnu := same_level sh n k tau x y a ht ht' hx hy hs
  have hpos (u : Space sh) (hb : u (.inl ()) ∈ rootBand k) :
      0 < frozenLevel n (sourceRoot k tau (u (.inl ()))).physical.total-u (.inl ()) := by
    have H := (frozenRoot_residual_bounds ht ht' hb hn).1
    rw [frozenRoot_residual] at H
    linarith
  have hcl : (nu-x (.inl ())≤2*Part5OriginalUpsilon5CausalDictionary.a ↔
      nu-y (.inl ())≤2*Part5OriginalUpsilon5CausalDictionary.a) := by
    have H := (hs (const (nu-2*Part5OriginalUpsilon5CausalDictionary.a)-X sh) (by
      apply List.mem_cons_of_mem
      exact List.mem_flatMap.mpr ⟨nu,hm,by simp⟩)).1
    simp only [map_sub,ev_const,X,ev_coordinate,sub_pos] at H
    constructor <;> intro hc <;> by_contra hn'
    · have := H.mpr (by linarith : y (.inl ()) < nu-2*Part5OriginalUpsilon5CausalDictionary.a)
      linarith
    · have := H.mp (by linarith : x (.inl ()) < nu-2*Part5OriginalUpsilon5CausalDictionary.a)
      linarith
  let b := decide (nu-x (.inl ())≤2*Part5OriginalUpsilon5CausalDictionary.a)
  have hx' : chartAt sh n k tau nu b x := by
    refine ⟨rfl,hpos x hx,?_⟩
    by_cases he : nu-x (.inl ())≤2*Part5OriginalUpsilon5CausalDictionary.a
    · simpa [b,he] using he
    · simpa [b,he] using lt_of_not_ge he
  have hy' : chartAt sh n k tau nu b y := by
    refine ⟨hnu.symm,by simpa only [nu,hnu] using hpos y hy,?_⟩
    by_cases he : nu-x (.inl ())≤2*Part5OriginalUpsilon5CausalDictionary.a
    · simpa [b,he] using hcl.mp he
    · simpa [b,he] using lt_of_not_ge (mt hcl.mpr he)
  obtain ⟨r,hr,hnr,hsr⟩ := changed_selected_native_strip sh n k tau nu a b x y hx' hy' change
  apply h
  exact ⟨r,List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨nu,hm,by cases b <;> simp_all⟩),hnr,hsr⟩

def bandSelected (n : ℕ) (k : Root) (tau : ℝ) (labels : Fin d → ReadLabel) :
    Set (Space sh) := {x | x (.inl ()) ∈ rootBand k ∧ x ∈ selected n k tau sh labels}

def fullWalls (n : ℕ) (k : Root) (labels : Fin d → ReadLabel) : List (Form (Space sh)) :=
  (X sh-const a) :: (const (match k with | .U3 => 1/3 | .U4 => 59/250)-X sh) ::
    walls sh n labels

theorem changed_band_selected_strip (n : ℕ) (k : Root) (tau : ℝ)
    (labels : Fin d → ReadLabel) (x y : Space sh)
    (ht : 0≤tau) (ht' : tau≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (H : ¬ (x ∈ bandSelected sh n k tau labels ↔ y ∈ bandSelected sh n k tau labels)) :
    ∃ r ∈ fullWalls sh n k labels, r.2 ≠ 0 ∧ |r.1+r.2 x| ≤ ‖r.2‖*‖x-y‖ := by
  classical
  by_contra hall
  have hs : ∀ r ∈ fullWalls sh n k labels, agree (ev x) (ev y) r := by
    intro r hr
    by_contra h
    exact hall ⟨r,hr,proper_crossing r h⟩
  have hb : x (.inl ()) ∈ rootBand k ↔ y (.inl ()) ∈ rootBand k := by
    cases k <;> simp only [rootBand,mem_Icc]
    all_goals
      apply and_congr
      · simpa [X,sub_nonneg] using (hs (X sh-const a) (by simp [fullWalls])).2
      · simpa [X,sub_nonneg] using (hs _ (List.mem_cons_of_mem _ List.mem_cons_self)).2
  by_cases hx : x (.inl ()) ∈ rootBand k
  · have hy := hb.mp hx
    have hsel : ¬ (x ∈ selected n k tau sh labels ↔ y ∈ selected n k tau sh labels) := by
      simpa [bandSelected,hx,hy] using H
    obtain ⟨r,hr,hne,hm⟩ := changed_full_root_strip sh n k tau labels x y ht ht' hn hx hy hsel
    exact hall ⟨r,by simp [fullWalls,hr],hne,hm⟩
  · exact H (by simp [bandSelected,hx,mt hb.mpr hx])

end
end ImbalancedChen.P2FiniteMarkedGamma5SelectedRootStrips
