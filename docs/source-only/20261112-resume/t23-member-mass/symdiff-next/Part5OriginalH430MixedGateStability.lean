import ImbalancedChen.Part5OriginalH430FreshAxis
import ImbalancedChen.Part5OriginalH430MemberGateRows

namespace ImbalancedChen.Part5OriginalH430MixedGateStability
noncomputable section
open Set MeasureTheory Filter Topology Function
open scoped Classical
open P5OriginalActionMassBound P5OriginalFeedbackDomains P2EnhancedLowerPhysicalNode
open P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalH430NativeQueryPaths Part5OriginalH430MemberGateRows
open Part5OriginalH430FreshAxis Part5OriginalH430InheritedMemberL1 Part5OriginalH430FullMemberMeasurable

def parentTest : StepShape → ℝ
  | .transport i => gridArgument i
  | .w1Fixed i _ | .w1Singleton i _ => W1Target i
  | .w2Fixed j _ | .w2Singleton j _ | .w2Pair j _ => (originalW2At j).s
  | _ => 2

def cuts (s : StepShape) : Finset ℝ :=
  {1/2,1/3,1/6} ∪ match s with
  | .w1Singleton i j => {1/W1Anchor j,1/W1Target i}
  | .w2Singleton j k =>
      let w := originalW2At j
      {a0 w, ![b w,a2 w,a3 w] k}
  | .w2Pair j _ =>
      let w := originalW2At j
      {a0 w,a1 w,a2 w,a3 w}
  | _ => ∅

def Off (shape : StepShape) (p : PhysicalNode) (z : Point) : Prop :=
  (∀ j : Fin 2, j.val < arity shape → ∀ c ∈ cuts shape, z j ≠ c * residual p) ∧
  (0 < arity shape → z 0 ≠ residual p / p.argument) ∧
  (arity shape = 2 → z 1 ≠ residual p - 2*z 0)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every nonstructural local admission row has a fresh transverse
coordinate. The physical pair-square uses the larger coordinate after
the smaller is fixed; the bank endpoints in the smaller coordinate
are integrated in that coordinate itself. -/
theorem ae_off {p : Chart ι → TypedNode} (hp : StateMeasurable (fun x => (p x).physical))
    (s : StepShape) (sl : Fin (arity s) → ι) (hinj : Injective sl)
    (hind : ∀ j x, p (update x (sl j) 0) = p x) :
    ∀ᵐ x : Chart ι, Off s (p x).physical (point s sl x) := by
  have hlin (j : Fin 2) (hj : j.val < arity s) (c : ℝ) :
      ∀ᵐ x : Chart ι, point s sl x j ≠ c*residual (p x).physical := by
    simpa only [point,dif_pos hj] using avoid_graph (sl ⟨j.val,hj⟩) (fun x => c * residual (p x).physical)
      (measurable_const.mul hp.1) (fun x => by rw [hind])
  have hal (j : Fin 2) (c : ↥(cuts s)) :
      ∀ᵐ x : Chart ι, j.val < arity s → point s sl x j ≠ c.val*residual (p x).physical := by
    by_cases hj : j.val < arity s
    · exact (hlin j hj c.val).mono (fun _ h _ => h)
    · exact .of_forall (fun _ h => (hj h).elim)
  have hfirst := Filter.eventually_all.mpr (fun j : Fin 2 =>
    Filter.eventually_all.mpr (hal j))
  have hb : ∀ᵐ x : Chart ι, 0 < arity s →
      point s sl x 0 ≠ residual (p x).physical/(p x).physical.argument := by
    by_cases h : 0 < arity s
    · have h' := avoid_graph (sl ⟨0,h⟩) (fun x => residual (p x).physical / (p x).physical.argument)
        (hp.1.div hp.2.1) (fun x => by rw [hind])
      filter_upwards [h'] with x hx
      intro _
      simpa only [point,Fin.val_zero,dif_pos h] using hx
    · exact .of_forall (fun _ h' => (h h').elim)
  have hpair : ∀ᵐ x : Chart ι, arity s = 2 →
      point s sl x 1 ≠ residual (p x).physical - 2*point s sl x 0 := by
    by_cases h : arity s = 2
    · let i : Fin (arity s) := ⟨0,by omega⟩
      let j : Fin (arity s) := ⟨1,by omega⟩
      have hne : sl i ≠ sl j := fun he =>
        (by decide : (0:ℕ) ≠ 1) (congrArg Fin.val (hinj he))
      have h' := avoid_graph (sl j) (fun x => residual (p x).physical - 2*x (sl i))
        (hp.1.sub (measurable_const.mul (measurable_pi_apply _)))
        (fun x => by rw [hind,update_of_ne hne])
      filter_upwards [h'] with x hx
      intro _
      change (if h1 : 1 < arity s then x (sl ⟨1,h1⟩) else 0) ≠
        residual (p x).physical-2*(if h0 : 0 < arity s then x (sl ⟨0,h0⟩) else 0)
      simpa only [dif_pos (by omega : 1 < arity s),dif_pos (by omega : 0 < arity s)] using hx
    · exact .of_forall (fun _ h' => (h h').elim)
  filter_upwards [hfirst,hb,hpair] with x hx h1 h2
  exact ⟨fun j hj c hc => hx j ⟨c,hc⟩ hj,h1,h2⟩

private theorem all_eventual (rs : List GateRow) {P : ℕ → GateRow → Prop} {Q : GateRow → Prop}
    (h : ∀ r ∈ rs, ∀ᶠ n : ℕ in atTop, P n r ↔ Q r) :
    ∀ᶠ n : ℕ in atTop, (∀ r ∈ rs, P n r) ↔ (∀ r ∈ rs, Q r) := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    filter_upwards [h r (by simp),ih (fun t ht => h t (by simp [ht]))] with n hr ht
    simpa only [List.forall_mem_cons] using and_congr hr ht

/-- The cap row is weak. Downward freezing preserves its ideal
equality, even before a fresh prime has appeared. -/
private theorem cap_stable {l : ℕ → ℝ} {L C : ℝ} (c : ℝ) (hC : 0 < C) (hL : 0 < L)
    (hl : Tendsto l atTop (𝓝 L)) (hle : ∀ n, l n ≤ L) :
    ∀ᶠ n : ℕ in atTop, l n/c ≤ C ↔ L/c ≤ C := by
  by_cases hc : 0 < c
  · by_cases h : L/c ≤ C
    · exact .of_forall (fun n => iff_of_true ((div_le_div_of_nonneg_right (hle n) hc.le).trans h) h)
    · filter_upwards [(hl.div_const c).eventually (eventually_gt_nhds (lt_of_not_ge h))] with n hn
      exact iff_of_false (not_le.mpr hn) h
  · filter_upwards [hl.eventually (eventually_gt_nhds hL)] with n hn
    exact iff_of_true ((div_nonpos_of_nonneg_of_nonpos hn.le (le_of_not_gt hc)).trans hC.le)
      ((div_nonpos_of_nonneg_of_nonpos hL.le (le_of_not_gt hc)).trans hC.le)

theorem local_stable {p : PhysicalNode} {f : ℕ → PhysicalNode} (s : StepShape) (z : Point)
    (hL : 0 < residual p) (hC : 0 < p.ceiling) (harg : 1 ≤ p.argument)
    (hl : Tendsto (fun n => residual (f n)) atTop (𝓝 (residual p)))
    (hq : Tendsto (fun n => (f n).argument) atTop (𝓝 p.argument))
    (hle : ∀ n, residual (f n) ≤ residual p) (hc : ∀ n, (f n).ceiling = p.ceiling)
    (test : ∀ᶠ n : ℕ in atTop, Compares (f n).argument p.argument (parentTest s))
    (off : Off s p z) :
    ∀ᶠ n : ℕ in atTop, LocalDomain (f n) s z ↔ LocalDomain p s z := by
  let L := residual p
  let A := p.argument
  let St := fun r : GateRow => ∀ᶠ n : ℕ in atTop,
    r.accepts (residual (f n)) (f n).argument ↔ r.accepts L A
  have nz (r : GateRow) (hr : r.value L A ≠ 0) : St r := by
    have hlim : Tendsto (fun n => r.value (residual (f n)) (f n).argument) atTop (𝓝 (r.value L A)) :=
      ((hl.const_mul r.level).add (hq.const_mul r.query)).add_const r.constant
    filter_upwards [cmp_of_ne hlim hr] with n hn
    unfold GateRow.accepts
    split_ifs
    · simpa only [not_le] using not_congr hn.1
    · exact hn.2
  have base : St (strictRow 1 0 0) := nz _ (by simpa [GateRow.value,strictRow,L] using hL.ne')
  have fixed (b : Bool) (c : ℝ) : St ⟨b,0,0,c⟩ := .of_forall (fun n => by simp [GateRow.accepts,GateRow.value])
  have upper : St (weakRow 0 (-1) (parentTest s)) := test.mono (fun _ h => by simpa using h.1)
  have lower : St (weakRow 0 1 (-(parentTest s))) := test.mono (fun _ h => by simpa using h.2)
  have cap (c : ℝ) : St (capRow c p.ceiling) := by
    simpa only [St,capRow_iff] using cap_stable c hC hL hl hle
  have xlo (j : Fin 2) (hj : j.val < arity s) (c : ℝ) (hc' : c ∈ cuts s) :
      St (strictRow (-c) 0 (z j)) := by
    apply nz
    intro he
    apply off.1 j hj c hc'
    dsimp [strictRow,GateRow.value,L] at he
    linarith only [he]
  have xhi (j : Fin 2) (hj : j.val < arity s) (c : ℝ) (hc' : c ∈ cuts s) :
      St (strictRow c 0 (-(z j))) := by
    apply nz
    intro he
    apply off.1 j hj c hc'
    dsimp [strictRow,GateRow.value,L] at he
    linarith only [he]
  have square (j : Fin 2) (hj : j.val < arity s) (m : ℝ)
      (hm : m ≠ 0) (hm' : 1/m ∈ cuts s) : St (weakRow 1 0 (-(m*z j))) := by
    apply nz
    intro he
    apply off.1 j hj (1/m) hm'
    dsimp [weakRow,GateRow.value,L] at he
    field_simp [hm]
    linarith only [he,mul_comm m (z j)]
  have sixth (hj : 0 < arity s) : St (weakRow (-1) 0 (6*z 0)) := by
    apply nz
    intro he
    apply off.1 0 hj (1/6) (by simp [cuts])
    dsimp [weakRow,GateRow.value,L] at he
    linarith only [he]
  have move (hj : 0 < arity s) : St (weakRow 1 (-(z 0)) 0) := by
    apply nz
    intro he
    apply off.2.1 hj
    apply (eq_div_iff (by linarith only [harg] : p.argument ≠ 0)).mpr
    dsimp [weakRow,GateRow.value,L,A] at he
    linarith only [he]
  have pairSum (b : Bool) (hj : arity s = 2) : St ⟨b,1,0,-(z 1+2*z 0)⟩ := by
    apply nz
    intro he
    apply off.2.2 hj
    dsimp [GateRow.value,L] at he
    linarith only [he]
  have rows (r : GateRow) (hr : r ∈ localRows p.ceiling s z) : St r := by
    cases s with
    | w2Pair j piece => fin_cases piece
    | _ => skip
    all_goals
      simp only [localRows,oneRows,pairRows,intervalRows,W2singleRows,W2pairRows,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
        List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
      repeat' (have hh : _ ∨ _ := hr; clear hr; rcases hh with hr | hr)
      all_goals subst r
      all_goals first
        | exact base | exact upper | exact lower | exact cap _ | exact fixed _ _
        | exact pairSum _ (by decide) | exact move (by decide) | exact sixth (by decide)
        | exact square _ (by decide) _ (by norm_num) (by simp [cuts])
        | exact xlo _ (by decide) _ (by simp [cuts])
        | exact xhi _ (by decide) _ (by simp [cuts])
  have he := all_eventual (localRows p.ceiling s z) rows
  filter_upwards [he] with n hn
  simpa only [localDomain_iff_rows,hc,AllRows,L,A] using hn

end
end ImbalancedChen.Part5OriginalH430MixedGateStability

