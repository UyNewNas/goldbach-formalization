import ImbalancedChen.Part5OriginalH430ChangedPrefixDescendants

/-! A complete physical Member without a terminal table-atom test. Both
terminal reads can be outside the tables. The geometric and arithmetic
bounds include those exits. The original T23 modules keep the helpers for
their terminal induction private. The same root/step formulas below use
the original public rational-germ, moving-wall and arithmetic estimates. -/
namespace ImbalancedChen.Part5OriginalH430WholeMemberScreen
noncomputable section
open Set MeasureTheory Filter Topology Function
open scoped Classical BigOperators
open Part5OriginalH430FixedPrimeScreen (Fields view rootBand_stable)
open Part5OriginalH430PrimeProgramWord (base)
open Part5OriginalH430NativeMovingDensity
open Part5OriginalH430PrimeRegularGerms Part5OriginalH430SharpPrimeBox
open Part5OriginalH430FullRootAmplitude Part5OriginalH430FullPrimeTheta
open Part5OriginalH430ChangedPrefixDescendants
open Part5OriginalH430RequestedHistory P5OriginalU5FrozenSource (receiver)
open Part5OriginalH430FullMemberMeasurable Part5OriginalH430FrozenPerturbation
open Part5OriginalH430FreshAxis Part5OriginalH430MixedGateStability Part5OriginalH430MixedNativeWalk
open Part5OriginalH430DescendantLimits Part5OriginalH430InheritedMemberL1

open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open P2PhysicalIncomingPrefixCells Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenRootMass Part5OriginalH430FrozenTableRootMass
open Part5OriginalH430FullMemberStrips Part5OriginalH430NativeQueryPaths
open Part5OriginalH430PrimeRegularGerms Part5OriginalH430FixedProgramL1
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables Part5UpperTables.OriginalU34

local macro "germs" : tactic => `(tactic|
  repeat' first
    | assumption | exact pw_const _ | exact st_const _
    | apply Stable.and | apply PW.le | apply PW.lt | apply PW.eq
    | apply PW.min | apply PW.max | apply PW.piece | apply PW.add | apply PW.sub
    | apply PW.div | apply PW.mul | apply PW.neg)

variable {r : ℕ}

private theorem exponent_cell {f : Space r → ℝ} (hf : PW f) (lo hi : ℝ) (m : ℕ) (c : CellCode m) :
    Stable (fun x => f x ∈ exponentCell lo hi m c) := by
  cases c <;> simp only [exponentCell,mem_singleton_iff,mem_Ico] <;> germs

private theorem raw {f : Space r → ℝ} (hf : PW f) (m : ℕ) :
    PW (fun x => rawLower m (f x)) := by
  let S : Finset (Poly r × Poly r) := Finset.univ.image (fun c : CellCode m => (MvPolynomial.C (lowerEndpoint m c),1))
  have hc (c : CellCode m) := exponent_cell hf 0 1 m c
  have hI : Stable (fun x => f x ∈ Ico (0:ℝ) 1) := (PW.le (pw_const 0) hf).and (hf.lt (pw_const 1))
  refine ⟨S,?_⟩
  filter_upwards [Filter.eventually_all.mpr hc,hI] with x hs hI
  let c := exponentCode 0 1 m (f x)
  refine ⟨_,Finset.mem_image_of_mem (fun q : CellCode m => (MvPolynomial.C (lowerEndpoint m q),1)) (Finset.mem_univ c),
    by simp [ev],?_⟩
  filter_upwards [hI,hs c] with y hy hcell
  have he : exponentCode 0 1 m (f y) = c := by
    by_cases hx : f x ∈ Ico (0:ℝ) 1
    · have hqy := hy.mpr hx
      exact exponentCode_eq_of_cell zero_lt_one ⟨hqy.1,hqy.2.le⟩
        (hcell.mpr (exponentCode_membership ⟨hx.1,hx.2.le⟩))
    · simp [c,exponentCode,hx,fun h => hx (hy.mp h)]
  simp [rawLower,he,ev]

private theorem frozen {f : Space r → ℝ} (hf : PW f) (n : ℕ) :
    PW (fun x => frozenLevel n (f x)) := by
  induction n with
  | zero => exact raw hf 0
  | succ n ih => exact ih.max (raw hf _)

private theorem residual_pw (k : Root) (tau : ℝ) {t : Space r → ℝ} (ht : PW t) :
    PW (fun x => sourceResidual k tau (t x)) := by
  cases k <;> simp only [sourceResidual,U3Residual,mainResidual,tailResidual,VariableEnvelope.v,
    VariableEnvelope.A,VariableEnvelope.C] <;> germs

private theorem root_fields (k : Root) (v : Option ℕ) {t : Space r → ℝ} (ht : PW t) :
    Fields (fun x => match v with | none => sourceRoot k 0 (t x)
      | some n => frozenRoot n k (finiteTau n) (t x)) := by
  cases v with
  | none =>
    have hr := residual_pw k 0 ht
    exact ⟨by simpa only [sourceRoot_residual] using hr,
      (pw_const 2).max (hr.div (pw_const a)),ht⟩
  | some n =>
    have hp := ht.add (residual_pw k (finiteTau n) ht)
    have hr := (frozen hp n).sub ht
    exact ⟨hr,(pw_const 2).max (hr.div (pw_const a)),ht⟩

private theorem perform_fields {p : Space r → TypedNode} (hp : Fields p)
    (a : StepShape) {z : Space r → Point} (hz : ∀ i, PW (fun x => z x i)) :
    Fields (fun x => advance (p x) a (z x)) := by
  obtain ⟨hL,hs,hC⟩ := hp
  have h0 := hz 0
  have h1 := hz 1
  have hu (i : Fin 2) := (hz i).div hL
  cases a with
  | retain => exact ⟨hL,hs,hC⟩
  | transport _ | w1Fixed _ _ | w2Fixed _ _ => exact ⟨hL,pw_const _,hC⟩
  | buchstabUpper | buchstabLower =>
    exact ⟨by simpa only [advance,perform,residual_appendOne] using hL.sub h0,
      (hL.div h0).sub (pw_const 1),h0⟩
  | w1Singleton _ _ | w2Singleton _ _ =>
    exact ⟨by simpa only [advance,perform,residual_appendOne] using hL.sub h0,
      (pw_const _).mul ((pw_const 1).sub (hu 0)),h0⟩
  | w2Pair i j =>
    refine ⟨by simpa only [advance,perform,residual_appendPair] using (hL.sub h1).sub h0,?_,h0⟩
    by_cases hj : j.val < 2
    · simpa only [advance,perform,appendPair,pairProfile,if_pos hj,fixedPairProfile,normalized]
        using (pw_const (originalW2At i).s0).mul (((pw_const 1).sub (hu 0)).sub (hu 1))
    · simpa only [advance,perform,appendPair,pairProfile,if_neg hj,movingPairProfile,normalized]
        using (((pw_const 1).sub (hu 0)).sub (hu 1)).div (hu 0)

private theorem fixed_local_stable {p : Space r → TypedNode} (hp : Fields p)
    (a : StepShape) {z : Space r → Point} (hz : ∀ i, PW (fun x => z x i)) :
    Stable (fun x => LocalDomain (p x).physical a (z x)) := by
  obtain ⟨hL,hs,hC⟩ := hp
  have h0 := hz 0
  have h1 := hz 1
  cases a with
  | w2Pair _ j => fin_cases j
  | w2Singleton _ j => fin_cases j
  | _ => skip
  all_goals
    simp only [LocalDomain,OneGate,PairGate,normalized,buchstabArgument,buchstabUpperDomain,
      buchstabLowerDomain,W1Domain,W2SingletonDomain,W2PairDomain,W2Singleton2,W2Singleton3,
      W2Singleton4,W2Pair5,W2Pair6,W2Pair7,W2Pair8,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,mem_setOf_eq,mem_Icc,mem_Ioo,and_true]
    germs

private theorem cell_stable (lo hi : ℝ) {mesh : ℕ} (a : PhysicalCell mesh × PhysicalCell mesh)
    {z : Space r → Point} (hz : ∀ i, PW (fun x => z x i)) :
    Stable (fun x => cellMember lo hi mesh a (z x)) :=
  (((pw_const lo).le (hz 0)).and ((hz 0).le (pw_const hi))).and
    ((((pw_const lo).le (hz 1)).and ((hz 1).le (pw_const hi))).and
      ((exponent_cell (hz 0) lo hi mesh a.1).and (exponent_cell (hz 1) lo hi mesh a.2)))

private theorem bare_regular {d mesh : ℕ} (lo hi : ℝ) {p : Space r → TypedNode} (hp : Fields p)
    {b : Bool} (hb : ∀ x, (p x).upper=b) (code : Program mesh d) {z : Space r → Coordinates d}
    (hz : ∀ i j, PW (fun x => z x i j)) :
    Stable (fun x => Member lo hi d (p x) code (z x)) := by
  induction d generalizing p b with
  | zero => exact st_const True
  | succ d ih =>
    have htail := ih (perform_fields hp (code 0).1 (hz 0))
      (fun x => congrArg (fun u => childUpper u (code 0).1) (hb x)) (tail code)
      (fun i j => hz i.succ j)
    have hcell := cell_stable lo hi (code 0).2 (hz 0)
    have hloc := fixed_local_stable hp (code 0).1 (hz 0)
    filter_upwards [htail,hcell,hloc] with x hx hc hl
    filter_upwards [hx,hc,hl] with y hy hcy hly
    simp only [Member,hb] at hy ⊢
    tauto

def bareSet {mesh d : ℕ} (k : Root) (code : Program mesh d) (v : Option ℕ) :
    Set (NativeSlot (shapes code) → ℝ) := {x |
    Member 0 1 d (base k v (nativeRootCoordinate x)) code (nativeCoordinates (shapes code) x)}

def bareDifference {mesh d : ℕ} (k : Root) (code : Program mesh d) (n : ℕ) :=
  (bareSet k code none \ bareSet k code (some n)) ∪ (bareSet k code (some n) \ bareSet k code none)

def bareScreen {mesh d : ℕ} (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (n : ℕ) : Set (Space r) :=
  view e ⁻¹' (region k (shapes code) ∩ bareDifference k code n)

theorem bare_stable {mesh d : ℕ} (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (v : Option ℕ) :
    Stable (fun x => view e x ∈ bareSet k code v) := by
  have ht := pw_coord (e.symm (.inl ()))
  have hz (i : Fin d) (j : Fin 2) :
      PW (fun x : Space r => nativeCoordinates (shapes code) (view e x) i j) := by
    unfold nativeCoordinates
    split_ifs <;> first | exact pw_coord _ | exact pw_const _
  exact bare_regular 0 1 (root_fields k v ht) (b := true) (fun x => by cases v <;> rfl) code hz

theorem bare_difference_stable {mesh d : ℕ} (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (n : ℕ) :
    Stable (fun x => view e x ∈ bareDifference k code n) := by
  have hI := bare_stable k code e none
  have hS := bare_stable k code e (some n)
  exact (hI.and hS.not).or (hS.and hI.not)

private theorem rootState {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) (k : Root) :
    State (fun x : Chart ι => x j ∈ rootBand k) (fun x => sourceRoot k 0 (x j))
      (fun n x => frozenRoot n k (finiteTau n) (x j)) := by
  have h := sourceRoot_stateMeasurable k 0
  have hcoord := (measurable_pi_apply j : Measurable (fun x : Chart ι => x j))
  let emptyCode : Program 0 0 := Fin.elim0
  let emptyZ : Coordinates 0 := Fin.elim0
  refine ⟨⟨h.1.comp hcoord,h.2.1.comp hcoord,h.2.2.comp hcoord⟩,?_,?_,
    fun _ hx => sourceRoot_argument (by norm_num) (by norm_num) hx,
    fun _ hx => frozenDescendant_residual_tendsto hx emptyCode emptyZ,
    fun _ hx => frozenQuery_tendsto hx,?_,fun _ _ => rfl,fun _ _ => rfl,?_⟩
  · intro x hx
    rw [sourceRoot_residual]
    exact (by norm_num : (0:ℝ)<11/192).trans_le (sourceResidual_bounds (by norm_num) (by norm_num) hx).1
  · intro x hx
    exact (by norm_num [a] : (0:ℝ)<a).trans_le (rootBand_subset k hx).1
  · intro x hx n
    have hl := (rootLoss_bounds (n := n) (finiteTau_pos n).le (finiteTau_le n) hx).1
    rw [← actual_descendant_residual_loss n k (finiteTau n) (x j) emptyCode emptyZ] at hl
    exact sub_nonneg.mp hl
  · intro c
    suffices hsign : ∀ᵐ t : ℝ, t ∈ rootBand k → ∀ᶠ n : ℕ in atTop,
        Compares (frozenQuery n k (finiteTau n) t) (idealQuery k t) c by
      exact (Measure.quasiMeasurePreserving_eval (fun _ : ι => (volume : Measure ℝ)) j).ae hsign
    filter_upwards [volume.ae_ne (1-2*a*c),volume.ae_ne ((57/64-a*c)*2/5),
      volume.ae_ne (1/2-a*c)] with t ha hb hd
    intro ht
    by_cases he : idealQuery k t = 2
    · exact .of_forall (fun n => by
        change Compares (frozenQuery n k (finiteTau n) t) (idealQuery k t) c
        rw [ideal_clamp_preserved (finiteTau_pos n).le (finiteTau_le n) ht he,he]
        exact ⟨Iff.rfl,Iff.rfl⟩)
    · apply cmp_of_ne (frozenQuery_tendsto ht)
      intro hq
      exact (proper_root_fibre he hq).elim ha (fun h' => h'.elim hb hd)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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
private theorem bare_walk {G : Chart ι → Prop} {p : Chart ι → TypedNode} {f : ℕ → Chart ι → TypedNode}
    {lo hi : ℝ} {mesh d : ℕ} (st : State G p f) (s : Fin d → StepShape)
    (sl : Slots s → ι) (hinj : Injective sl) (hind : ∀ j x, p (update x (sl j) 0) = p x)
    (code : Chart ι → Program mesh d) (hshape : ∀ x i, (code x i).1 = s i)
    :
    ∀ᵐ x : Chart ι, G x → ∀ᶠ n : ℕ in atTop,
      (Member lo hi d (f n x) (code x) (zOf s sl x) ↔
       Member lo hi d (p x) (code x) (zOf s sl x)) := by
  induction d generalizing G p f with
  | zero => exact .of_forall (fun _ _ => .of_forall (fun _ => Iff.rfl))
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
      change (Member lo hi d (ff n x) (tail (code x)) (tail (zOf s sl x)) ↔
        Member lo hi d (next x) (tail (code x)) (tail (zOf s sl x))) at hrest
      simp only [Member,hshape,st.upper x n]
      change (_ ∧ _ ∧ LocalDomain (f n x).physical a (point a head x) ∧ _) ↔
        (_ ∧ _ ∧ LocalDomain (p x).physical a (point a head x) ∧ _)
      dsimp only [ff,next] at hrest
      tauto
    · filter_upwards [hf] with n hlocal
      have hfrozen := fun h => had (hlocal.mp h)
      simp only [Member,hshape,st.upper x n]
      change (_ ∧ _ ∧ LocalDomain (f n x).physical a (point a head x) ∧ _) ↔
        (_ ∧ _ ∧ LocalDomain (p x).physical a (point a head x) ∧ _)
      tauto

theorem bare_eventually {mesh d : ℕ} (k : Root) (code : Program mesh d) :
    ∀ᵐ x : NativeSlot (shapes code) → ℝ, nativeRootCoordinate x∈rootBand k →
      ∀ᶠ n : ℕ in atTop, x∈bareSet k code (some n) ↔ x∈bareSet k code none := by
  apply bare_walk (rootState (Sum.inl () : NativeSlot (shapes code)) k) (shapes code)
    (fun i => Sum.inr i) (fun _ _ h => Sum.inr.inj h) _ (fun _=>code) (fun _ _=>rfl)
  intro j x
  change sourceRoot k 0 (update x (.inr j) 0 (.inl ())) = sourceRoot k 0 (x (.inl ()))
  rw [update_of_ne (by simp : (Sum.inl () : NativeSlot (shapes code)) ≠ Sum.inr j)]

theorem bare_measurable {mesh d : ℕ} (k : Root) (code : Program mesh d)
    (v : Option ℕ) : MeasurableSet (bareSet k code v) := by
  let s := shapes code
  have hr : Measurable (nativeRootCoordinate : (NativeSlot s → ℝ) → ℝ) := measurable_pi_apply _
  have hz : Measurable (nativeCoordinates s) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    unfold nativeCoordinates
    split_ifs <;> first | exact measurable_pi_apply _ | exact measurable_const
  cases v with
  | none => exact ((actual_joint_Member_measurable 0 1 0 k 0 code).1).preimage (hr.prodMk hz)
  | some n => exact ((actual_joint_Member_measurable 0 1 n k (finiteTau n) code).2).preimage (hr.prodMk hz)

private theorem bareDifference_measurable {mesh d : ℕ} (k : Root) (code : Program mesh d) (n : ℕ) :
    MeasurableSet (bareDifference k code n) :=
  ((bare_measurable k code none).diff (bare_measurable k code (some n))).union
    ((bare_measurable k code (some n)).diff (bare_measurable k code none))

theorem bare_volume {mesh d : ℕ} (k : Root) (code : Program mesh d) :
    Tendsto (fun n : ℕ => volume.real (region k (shapes code) ∩ bareDifference k code n))
      atTop (𝓝 0) := by
  let s := shapes code
  let B := region k s
  let D := bareDifference k code
  let F (n : ℕ) := (D n).indicator (fun _ => (1:ℝ))
  have hm : MeasurableSet B := measurableSet_Icc.inter
    ((rootBand_measurable k).preimage (measurable_pi_apply (.inl ())))
  have hb : volume B < ⊤ := lt_of_le_of_lt (measure_mono inter_subset_left) isCompact_Icc.measure_lt_top
  have hF (n : ℕ) : Measurable (F n) := measurable_const.indicator (bareDifference_measurable k code _)
  have hbound (n : ℕ) : ∀ᵐ x ∂volume.restrict B, ‖F n x‖ ≤ 1 := by
    apply Eventually.of_forall
    intro x
    by_cases h : x ∈ D n <;> simp [F,h]
  have hlim : ∀ᵐ x ∂volume.restrict B, Tendsto (fun n => F n x) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem hm,
      ae_restrict_of_ae (bare_eventually k code)] with x hx hh
    apply tendsto_const_nhds.congr'
    filter_upwards [hh hx.2] with n hn
    have hout : x ∉ D n := by
      change ¬((x ∈ _ ∧ x ∉ _) ∨ (x ∈ _ ∧ x ∉ _))
      tauto
    simp [F,hout]
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict B) (f := fun _ : NativeSlot s → ℝ => (0:ℝ))
    (fun _ => (1:ℝ)) (fun n => (hF n).aestronglyMeasurable)
    (integrableOn_const hb.ne) hbound hlim
  have he (n : ℕ) : (∫ x in B, F n x) = volume.real (B ∩ D n) := by
    rw [show F n = (D n).indicator (fun _ => (1:ℝ)) from rfl,
      setIntegral_indicator (bareDifference_measurable k code _),setIntegral_const,smul_eq_mul,mul_one]
  simpa only [integral_zero,he] using h

def bareError {mesh d : ℕ} (k : Root) (code : Program mesh d) (n : ℕ) :=
  ∫ x in region k (shapes code), |(bareSet k code none).indicator
    (density mesh k (shapes code) none) x - (bareSet k code (some n)).indicator
    (density mesh k (shapes code) (some n)) x|

/-- Both full physical densities are zero-extended on their own complete
Member, including at a terminal query outside all 401 atoms. -/
theorem bare_L1 {mesh d : ℕ} (hd : d≤440) (k : Root) (code : Program mesh d) :
    Tendsto (bareError k code) atTop (𝓝 0) := by
  let B := region k (shapes code)
  have hB : MeasurableSet B := measurableSet_Icc.inter
    ((rootBand_measurable k).preimage (measurable_pi_apply (.inl ())))
  have hfinite : volume B<⊤ := lt_of_le_of_lt (measure_mono inter_subset_left) isCompact_Icc.measure_lt_top
  have hlim : Tendsto (fun n => rate n*volume.real B+volume.real (B∩bareDifference k code n)*envelope)
      atTop (𝓝 0) := by
    simpa only [zero_mul,add_zero] using (rate_tendsto.mul_const (volume.real B)).add
      ((bare_volume k code).mul_const envelope)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact .of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _))
  · filter_upwards [eventually_fine_mesh] with n hn
    let I := bareSet k code none
    let S := bareSet k code (some n)
    let D := bareDifference k code n
    have hDm := bareDifference_measurable k code n
    have hr : 0≤rate n := by
      unfold rate levelError
      exact div_nonneg (mul_nonneg (div_nonneg (by norm_num) productFloor_pos.le)
        (add_nonneg (finiteTau_pos n).le (meshError_pos n).le)) (mul_self_nonneg _)
    have bound (x : NativeSlot (shapes code) → ℝ) (hx : x∈B) :
        |I.indicator (density mesh k (shapes code) none) x -
         S.indicator (density mesh k (shapes code) (some n)) x| ≤
          rate n + D.indicator (fun _ => envelope) x := by
      have hD : x∈D ↔ (x∈I ∧ x∉S)∨(x∈S ∧ x∉I) := Iff.rfl
      by_cases hi : x∈I <;> by_cases hs : x∈S
      · have hnD : x∉D := by simp only [hD,hi,hs]; tauto
        simpa only [indicator_of_mem hi,indicator_of_mem hs,indicator_of_notMem hnD,add_zero,
          fixed_density k code none x,fixed_density k code (some n) x] using
          (frozen_admitted_density_error hx.2 hd hn hs)
      · have hy := hD.mpr (Or.inl ⟨hi,hs⟩)
        simpa only [indicator_of_mem hi,indicator_of_notMem hs,indicator_of_mem hy,sub_zero,
          fixed_density k code none x] using (ideal_weight_bound hx.2 hd hi).trans (le_add_of_nonneg_left hr)
      · have hy := hD.mpr (Or.inr ⟨hs,hi⟩)
        simpa only [indicator_of_notMem hi,indicator_of_mem hs,indicator_of_mem hy,zero_sub,abs_neg,
          fixed_density k code (some n) x] using
          (frozen_weight_bound hx.2 hd hn hs).trans (le_add_of_nonneg_left hr)
      · have hnD : x∉D := by simp only [hD,hi,hs]; tauto
        simpa only [indicator_of_notMem hi,indicator_of_notMem hs,indicator_of_notMem hnD,sub_zero,
          abs_zero,add_zero] using hr
    have hc : IntegrableOn (fun _ : NativeSlot (shapes code) → ℝ => rate n) B := integrableOn_const hfinite.ne
    have hD : IntegrableOn (D.indicator (fun _ => envelope)) B :=
      (integrableOn_const hfinite.ne : IntegrableOn (fun _ : NativeSlot (shapes code) → ℝ => envelope) B).indicator hDm
    have h := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
      (hc.add hD) ((ae_restrict_mem hB).mono bound)
    rw [integral_add hc hD,setIntegral_indicator hDm] at h
    simpa only [setIntegral_const,smul_eq_mul,mul_comm (volume.real B),Pi.add_apply] using h

theorem bareScreen_regular {r mesh d : ℕ} (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) (n : ℕ) :
    MeasurableSet (bareScreen k code e n) ∧
    Stable (fun x => x ∈ bareScreen k code e n) ∧
    volume (bareScreen k code e n) =
      volume (region k (shapes code) ∩ bareDifference k code n) := by
  have hmI := bare_measurable k code none
  have hmS := bare_measurable k code (some n)
  have hmD : MeasurableSet (bareDifference k code n) := (hmI.diff hmS).union (hmS.diff hmI)
  have hmB : MeasurableSet (region k (shapes code)) := measurableSet_Icc.inter
    ((rootBand_measurable k).preimage (measurable_pi_apply (.inl ())))
  refine ⟨(hmB.inter hmD).preimage (view_preserves e).measurable,?_,
    (view_preserves e).measure_preimage (hmB.inter hmD).nullMeasurableSet⟩
  have hcoord (i : NativeSlot (shapes code)) :=
    ((pw_const 0).le (pw_coord (e.symm i))).and ((pw_coord (e.symm i)).le (pw_const 1))
  have cube : Stable (fun x => view e x ∈ Icc (fun _ => (0:ℝ)) (fun _ => (1:ℝ))) := by
    filter_upwards [Filter.eventually_all.mpr hcoord] with x hx
    filter_upwards [Filter.eventually_all.mpr hx] with y hy
    change ((∀ i, 0 ≤ y (e.symm i)) ∧ (∀ i, y (e.symm i) ≤ 1)) ↔
      ((∀ i, 0 ≤ x (e.symm i)) ∧ (∀ i, x (e.symm i) ≤ 1))
    constructor <;> rintro ⟨hl,hu⟩
    · exact ⟨fun i => ((hy i).mp ⟨hl i,hu i⟩).1,fun i => ((hy i).mp ⟨hl i,hu i⟩).2⟩
    · exact ⟨fun i => ((hy i).mpr ⟨hl i,hu i⟩).1,fun i => ((hy i).mpr ⟨hl i,hu i⟩).2⟩
  exact (cube.and (rootBand_stable k code e)).and (bare_difference_stable k code e n)

theorem bare_primebox {r mesh d : ℕ} (k : Root) (code : Program mesh d)
    (e : Fin r ≃ NativeSlot (shapes code)) {a eps : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (he : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ N : ℕ in atTop, badMass N a (bareScreen k code e n) < eps := by
  let C := (1/a)^r
  have hC : 0 < C := pow_pos (one_div_pos.mpr ha) _
  filter_upwards [(bare_volume k code).eventually (eventually_lt_nhds (div_pos (half_pos he) hC))] with n hv
  have hs := bareScreen_regular k code e n
  have heq := congrArg ENNReal.toReal hs.2.2
  change volume.real (bareScreen k code e n) = _ at heq
  have hB : volume (region k (shapes code)) < ⊤ :=
    lt_of_le_of_lt (measure_mono inter_subset_left) isCompact_Icc.measure_lt_top
  have hf : volume (bareScreen k code e n) < ⊤ := hs.2.2.trans_lt
    (lt_of_le_of_lt (measure_mono inter_subset_left) hB)
  filter_upwards [eventual_sharp_bound ha ha1 hs.1 hs.2.1 hf (half_pos he)] with N hN
  have hsmall := (lt_div_iff₀ hC).mp hv
  change badMass N a _ < C * volume.real _ + eps/2 at hN
  rw [heq,mul_comm C] at hN
  linarith only [hN,hsmall]

/-- Common thresholds for original integer descendants of EVERY geometric
admission change, including an unvalued exterior on either chart. -/
theorem all_bare_changed_prefix_descendants (mesh : ℕ) {eps : ℝ} (he : 0<eps) :
    ∃ T : ℕ, ∀ n≥T, ∃ N₀ : ℕ, ∀ N≥N₀, Even N → ∀ (v : SplitPrograms mesh)
      (k : Root) (m : ℕ) (E : Occurrence N → ℕ → Prop) (f : Occurrence N → ℕ → ℝ),
      (∀ o ell,E o ell → receiver N ell) → (∀ o ell, |f o ell|≤1) →
      descendants N n m k v.2.2 (chronologicalOrder v.2.2)
        (fun p => actualPrimeTupleLog N p∈bareScreen k (prefixCode v.2.2)
          (order (prefixCode v.2.2)) n) E f 0 < eps := by
  have each (v : SplitPrograms mesh) (k : Root) :=
    descendants_of_small_screen he v.2.2 (chronologicalOrder v.2.2) k
      (bareScreen k (prefixCode v.2.2) (order (prefixCode v.2.2)))
      (fun _ he => bare_primebox k (prefixCode v.2.2) (order (prefixCode v.2.2)) bottom_pos bottom_lt_one he)
  apply eventually_atTop.1
  filter_upwards [Filter.eventually_all.mpr (fun v : SplitPrograms mesh => Filter.eventually_all.mpr (each v))] with n hn
  apply eventually_atTop.1
  filter_upwards [Filter.eventually_all.mpr (fun v : SplitPrograms mesh => Filter.eventually_all.mpr (hn v))] with N hN
  exact fun hev v k => hN v k hev

end
end ImbalancedChen.Part5OriginalH430WholeMemberScreen
