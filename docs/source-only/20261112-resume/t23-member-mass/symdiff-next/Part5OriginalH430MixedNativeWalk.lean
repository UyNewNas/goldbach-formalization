import ImbalancedChen.Part5OriginalH430MixedGateStability

namespace ImbalancedChen.Part5OriginalH430MixedNativeWalk
noncomputable section
open Set MeasureTheory Filter Topology Function
open scoped Classical
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalH430NativeQueryPaths Part5OriginalH430FullMemberStrips
open Part5OriginalH430FullMemberMeasurable Part5OriginalH430FrozenPerturbation
open Part5OriginalH430DescendantLimits Part5OriginalH430PhysicalRoots
open Part5OriginalH430FreshAxis Part5OriginalH430MixedGateStability Part5OriginalH430InheritedMemberL1
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem active_sign {G : Chart ι → Prop} {p : Chart ι → TypedNode}
    {f : ℕ → Chart ι → TypedNode} (st : State G p f) (q : FeedbackQuery)
    (sl : Fin (arity q.shape) → ι) (hinj : Injective sl)
    (hind : ∀ j x, p (update x (sl j) 0) = p x) (c : ℝ) :
    ∀ᵐ x : Chart ι, (G x ∧ LocalDomain (p x).physical q.shape (point q.shape sl x)) →
      ∀ᶠ n : ℕ in atTop, Compares
        (perform (f n x).physical q.shape (point q.shape sl x)).argument
        (perform (p x).physical q.shape (point q.shape sl x)).argument c := by
  by_cases hc : 1 ≤ c
  · filter_upwards [active_avoids st.measurable q sl hinj hind hc] with x hx
    rintro ⟨hg,hd⟩
    have hpos : 0 < point q.shape sl x 0 := by
      cases q with
      | buchstabLower _ => exact hd.2.2.1.1
      | _ => exact hd.2.1.1
    exact cmp_of_ne (perform_argument_tendsto (st.level x hg) (st.query x hg)
      (st.pos x hg) _ _) (hx (st.pos x hg) hpos)
  · apply Eventually.of_forall
    rintro x ⟨hg,hd⟩
    have hb := (perform_argument_bounds (st.arg x hg) hd).1
    exact cmp_of_ne (perform_argument_tendsto (st.level x hg) (st.query x hg)
      (st.pos x hg) _ _) ((lt_of_not_ge hc).trans_le hb).ne'

theorem advance_state {G : Chart ι → Prop} {p : Chart ι → TypedNode}
    {f : ℕ → Chart ι → TypedNode} (st : State G p f) (s : StepShape)
    (sl : Fin (arity s) → ι) (hinj : Injective sl)
    (hind : ∀ j x, p (update x (sl j) 0) = p x) :
    State (fun x => G x ∧ LocalDomain (p x).physical s (point s sl x))
      (fun x => advance (p x) s (point s sl x))
      (fun n x => advance (f n x) s (point s sl x)) := by
  refine ⟨perform_stateMeasurable st.measurable (point_measurable s sl) s,
    fun x h => perform_residual_pos h.2,?_,fun x h => perform_argument_bounds (st.arg x h.1) h.2,
    fun x h => perform_residual_tendsto (st.level x h.1) _ _,
    fun x h => perform_argument_tendsto (st.level x h.1) (st.query x h.1) (st.pos x h.1) _ _,
    ?_,fun x n => perform_ceiling_eq (st.ceiling x n) _ _,
    fun x n => advance_upper_eq (st.upper x n) _ _,?_⟩
  · intro x h
    exact Part5OriginalH430DescendantLimits.perform_ceiling_pos (st.capPos x h.1) h.2
  · intro x h n
    have hle := st.below x h.1 n
    change residual (perform (f n x).physical s (point s sl x)) ≤ residual (perform (p x).physical s (point s sl x))
    cases s <;> simp only [perform,residual_appendOne,residual_appendPair] <;>
      first | exact hle | linarith only [hle]
  · intro c
    cases s with
    | retain => exact (st.sign c).mono (fun x h hg => h hg.1)
    | transport _ | w1Fixed _ _ | w2Fixed _ _ =>
      exact .of_forall (fun _ _ => .of_forall (fun _ => ⟨Iff.rfl,Iff.rfl⟩))
    | buchstabUpper => exact active_sign st (.buchstabUpper 0) sl hinj hind c
    | buchstabLower => exact active_sign st (.buchstabLower 0) sl hinj hind c
    | w1Singleton i j => exact active_sign st (.w1 i j) sl hinj hind c
    | w2Singleton j k => exact active_sign st (.w2Singleton j k) sl hinj hind c
    | w2Pair j k => exact active_sign st (.w2Pair j k) sl hinj hind c

private theorem atom_sign {G : Chart ι → Prop} {p : Chart ι → TypedNode}
    {f : ℕ → Chart ι → TypedNode} (st : State G p f) (lo : Bool) (b : FloorAtom) :
    ∀ᵐ x : Chart ι, G x → ∀ᶠ n : ℕ in atTop,
      ((f n x).physical.argument ∈ tableAtomSet lo b ↔ (p x).physical.argument ∈ tableAtomSet lo b) := by
  let c : ℝ := if lo then 2 else 1
  cases b with
  | inl i =>
    filter_upwards [st.sign c,st.sign 5,st.sign (floorGrid i.val),st.sign (floorGrid (i.val+1))]
      with x h1 h2 h3 h4
    intro hg
    filter_upwards [h1 hg,h2 hg,h3 hg,h4 hg] with n h1 h2 h3 h4
    have l := not_congr h3.1
    have r := not_congr h4.2
    simp only [not_le] at l r
    cases lo <;> simpa only [c,tableAtomSet,floorAtomSet,upperAtomSet,if_true,if_false,
      Bool.false_eq_true,mem_inter_iff,mem_Icc,mem_Ioo] using
      (and_congr (and_congr h1.2 h2.1) (and_congr l r))
  | inr j =>
    filter_upwards [st.sign c,st.sign 5,st.sign (floorGrid j.val)] with x h1 h2 h3
    intro hg
    filter_upwards [h1 hg,h2 hg,h3 hg] with n h1 h2 h3
    have e := and_congr h3.1 h3.2
    rw [← le_antisymm_iff,← le_antisymm_iff] at e
    cases lo <;> simpa only [c,tableAtomSet,floorAtomSet,upperAtomSet,if_true,if_false,
      Bool.false_eq_true,mem_inter_iff,mem_Icc,mem_singleton_iff] using and_congr (and_congr h1.2 h2.1) e

abbrev Slots {d : ℕ} (s : Fin d → StepShape) := (i : Fin d) × Fin (arity (s i))

def zOf {d : ℕ} (s : Fin d → StepShape) (sl : Slots s → ι) (x : Chart ι) : Coordinates d :=
  fun i => point (s i) (fun j => sl ⟨i,j⟩) x

private theorem first_ne_next {d : ℕ} {s : Fin (d+1) → StepShape} (sl : Slots s → ι)
    (hi : Injective sl) (j : Fin (arity (s 0))) (t : Slots (tail s)) :
    sl ⟨0,j⟩ ≠ sl ⟨t.1.succ,t.2⟩ := by
  intro he
  have h := congrArg (fun v : Slots s => v.1.val) (hi he)
  change 0 = t.1.val+1 at h
  omega

/-- Fixed original shape, every original cell and incoming type at
every step, arbitrary coordinate-dependent program cells shared by the
two paths. On a failed ideal gate the frozen path eventually stops at
that gate; on an admitted gate the child induction carries its actual
state. The argument never assumes either complete Member. -/
theorem walk {G : Chart ι → Prop} {p : Chart ι → TypedNode} {f : ℕ → Chart ι → TypedNode}
    {lo hi : ℝ} {mesh d : ℕ} (st : State G p f) (s : Fin d → StepShape)
    (sl : Slots s → ι) (hinj : Injective sl) (hind : ∀ j x, p (update x (sl j) 0) = p x)
    (code : Chart ι → Program mesh d) (hshape : ∀ x i, (code x i).1 = s i)
    (pol : Bool) (atom : FloorAtom) :
    ∀ᵐ x : Chart ι, G x → ∀ᶠ n : ℕ in atTop,
      (QueryMember lo hi (f n x) (code x) (zOf s sl x) pol atom ↔
       QueryMember lo hi (p x) (code x) (zOf s sl x) pol atom) := by
  induction d generalizing G p f with
  | zero => simpa only [QueryMember,Member,realize,true_and] using atom_sign st pol atom
  | succ d ih =>
    let a := s 0
    let head := fun j : Fin (arity a) => sl ⟨0,j⟩
    let tailSl := fun t : Slots (tail s) => sl ⟨t.1.succ,t.2⟩
    let next := fun x => advance (p x) a (point a head x)
    let ff := fun n x => advance (f n x) a (point a head x)
    let H := fun x => G x ∧ LocalDomain (p x).physical a (point a head x)
    have hhi : Injective head := fun _ _ h =>
      Fin.ext (congrArg (fun v : Slots s => v.2.val) (hinj h))
    have hti : Injective tailSl := by
      rintro ⟨i,j⟩ ⟨i',j'⟩ he
      have h := hinj he
      have hh := congrArg (fun v : Slots s => v.1.val) h
      change i.val+1 = i'.val+1 at hh
      have hi : i = i' := Fin.ext (by omega)
      subst i'
      have hj : j = j' := Fin.ext (congrArg (fun v : Slots s => v.2.val) h)
      subst j'
      rfl
    have hphead (j) (x) : p (update x (head j) 0) = p x := hind ⟨0,j⟩ x
    have hn : State H next ff := advance_state st a head hhi hphead
    have hskip (t) (x) : next (update x (tailSl t) 0) = next x := by
      dsimp only [next]
      rw [hind ⟨t.1.succ,t.2⟩,point_independent (fun j => first_ne_next sl hinj j t)]
    have nextStable := ih hn (tail s) tailSl hti hskip (fun x => tail (code x)) (fun x i => hshape x i.succ)
    have off := ae_off st.measurable a head hhi hphead
    filter_upwards [nextStable,off,st.sign (parentTest a)] with x htail hx hs
    intro hg
    have hf := local_stable a (point a head x) (st.pos x hg) (st.capPos x hg) (st.arg x hg).1
      (st.level x hg) (st.query x hg) (st.below x hg) (st.ceiling x) (hs hg) hx
    by_cases had : LocalDomain (p x).physical a (point a head x)
    · filter_upwards [hf,htail ⟨hg,had⟩] with n hlocal hrest
      have hfrozen := hlocal.mpr had
      change (QueryMember lo hi (ff n x) (tail (code x)) (tail (zOf s sl x)) pol atom ↔
        QueryMember lo hi (next x) (tail (code x)) (tail (zOf s sl x)) pol atom) at hrest
      simp only [QueryMember] at hrest
      simp only [QueryMember,Member,realize,hshape,st.upper x n]
      change ((_ ∧ _ ∧ LocalDomain (f n x).physical a (point a head x) ∧ _) ∧ _) ↔
        ((_ ∧ _ ∧ LocalDomain (p x).physical a (point a head x) ∧ _) ∧ _)
      dsimp only [ff,next] at hrest
      change (_ ∧ _ ↔ _ ∧ _) at hrest
      tauto
    · filter_upwards [hf] with n hlocal
      have hfrozen := fun h => had (hlocal.mp h)
      simp only [QueryMember,Member,realize,hshape,st.upper x n]
      change ((_ ∧ _ ∧ LocalDomain (f n x).physical a (point a head x) ∧ _) ∧ _) ↔
        ((_ ∧ _ ∧ LocalDomain (p x).physical a (point a head x) ∧ _) ∧ _)
      tauto

end
end ImbalancedChen.Part5OriginalH430MixedNativeWalk

