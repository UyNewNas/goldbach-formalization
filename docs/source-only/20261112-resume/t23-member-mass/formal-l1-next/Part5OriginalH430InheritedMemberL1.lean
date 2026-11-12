import ImbalancedChen.Part5OriginalH430NativeProperSections
import ImbalancedChen.Part5OriginalH430FullRootAmplitude

/-! Complete fixed Programs with no fresh prime slots. Their native chart
has only its root coordinate. Sets on both sides include every recursive
admission gate and the terminal atom before extending their densities by zero. -/
namespace ImbalancedChen.Part5OriginalH430InheritedMemberL1
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalH430NativeQueryPaths Part5OriginalH430FullMemberStrips
open Part5OriginalH430FullMemberMeasurable Part5OriginalH430DescendantLimits
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenPerturbation Part5OriginalH430PhysicalMassPerturbation
open Part5OriginalH430FrozenRootMass Part5OriginalH430FrozenTableRootMass
open Part5OriginalH430FullRootAmplitude Part5OriginalUpsilon5CausalDictionary
open Part5UpperTables Part5UpperTables.OriginalU34

def Compares (x y c : ℝ) : Prop := (x ≤ c ↔ y ≤ c) ∧ (c ≤ x ↔ c ≤ y)

private theorem compares_self (x c : ℝ) : Compares x x c := ⟨Iff.rfl,Iff.rfl⟩

private theorem root_compares (k : Root) (c : ℝ) :
    ∀ᵐ t ∂volume.restrict (rootBand k), ∀ᶠ n : ℕ in atTop,
      Compares (frozenQuery n k (finiteTau n) t) (idealQuery k t) c := by
  have hne (v : ℝ) : ∀ᵐ t ∂volume.restrict (rootBand k), t ≠ v :=
    ae_restrict_of_ae (by rw [ae_iff]; simp)
  filter_upwards [ae_restrict_mem (rootBand_measurable k), hne (1-2*a*c),
      hne ((57/64-a*c)*2/5), hne (1/2-a*c)] with t ht hA hC hT
  by_cases hc : idealQuery k t = 2
  · exact .of_forall (fun n => by rw [ideal_clamp_preserved (finiteTau_pos n).le
      (finiteTau_le n) ht hc,hc]; exact compares_self _ _)
  · have hd : idealQuery k t ≠ c := fun h =>
      (proper_root_fibre hc h).elim hA (fun h => h.elim hC hT)
    rcases lt_or_gt_of_ne hd with h | h
    · filter_upwards [(frozenQuery_tendsto ht).eventually (eventually_lt_nhds h)] with n hn
      exact ⟨iff_of_true hn.le h.le, iff_of_false (not_le.mpr hn) (not_le.mpr h)⟩
    · filter_upwards [(frozenQuery_tendsto ht).eventually (eventually_gt_nhds h)] with n hn
      exact ⟨iff_of_false (not_le.mpr hn) (not_le.mpr h),iff_of_true hn.le h.le⟩

private theorem caps {L C c : ℝ} {l : ℕ → ℝ} (hc : 0 < c)
    (hl : Tendsto l atTop (𝓝 L)) (hle : ∀ n, l n ≤ L) :
    ∀ᶠ n in atTop, (l n/c ≤ C ↔ L/c ≤ C) := by
  by_cases h : L/c ≤ C
  · exact .of_forall (fun n => iff_of_true ((div_le_div_of_nonneg_right (hle n) hc.le).trans h) h)
  · filter_upwards [(hl.div_const c).eventually (eventually_gt_nhds (lt_of_not_ge h))] with n hn
    exact iff_of_false (not_le.mpr hn) h

private theorem fixedW2_pos (j : Fin 36) (b : Bool) :
    0 < (if b then (originalW2At j).s0 else (originalW2At j).phi1) := by
  have hg := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  have h0 : 0 < a0 (originalW2At j) := (by norm_num : (0:ℝ)<1/5).trans_le hg.1
  cases b
  · exact one_div_pos.mp (h0.trans hg.2.1)
  · exact W2_anchor_positive hg

private def Static {X : Type*} (μ : Filter X) (p : X → TypedNode)
    (f : ℕ → X → TypedNode) : Prop :=
  ∀ᶠ t in μ, 0 < residual (p t).physical ∧
    Tendsto (fun n => residual (f n t).physical) atTop (𝓝 (residual (p t).physical)) ∧
    (∀ n, residual (f n t).physical ≤ residual (p t).physical) ∧
    (∀ n, (f n t).physical.ceiling = (p t).physical.ceiling) ∧
    (∀ n, (f n t).upper = (p t).upper)

private def QueryLaws {X : Type*} (μ : Filter X) (p : X → TypedNode)
    (f : ℕ → X → TypedNode) : Prop :=
  ∀ c : ℝ, ∀ᶠ t in μ, ∀ᶠ n : ℕ in atTop,
    Compares (f n t).physical.argument (p t).physical.argument c

private theorem local_stable {X : Type*} {μ : Filter X} {p : X → TypedNode}
    {f : ℕ → X → TypedNode} (hp : Static μ p f) (hs : QueryLaws μ p f)
    (s : StepShape) (z : Point) (hz : arity s = 0) :
    ∀ᶠ t in μ, ∀ᶠ n : ℕ in atTop,
      (LocalDomain (f n t).physical s z ↔ LocalDomain (p t).physical s z) := by
  cases s with
  | retain =>
    filter_upwards [hp] with t h
    filter_upwards [h.2.1.eventually (eventually_gt_nhds h.1)] with n hn
    simp [LocalDomain,hn,h.1]
  | transport i =>
    filter_upwards [hp,hs (gridArgument i)] with t h hq
    filter_upwards [h.2.1.eventually (eventually_gt_nhds h.1),hq] with n hn hh
    simp only [LocalDomain,hn,h.1,true_and,hh.1]
  | w1Fixed i j =>
    have ha : 0 < W1Anchor j := by
      have h : (0:ℝ) ≤ j.val := Nat.cast_nonneg _
      dsimp [W1Anchor]
      linarith
    filter_upwards [hp,hs (W1Target i)] with t h hq
    filter_upwards [h.2.1.eventually (eventually_gt_nhds h.1),hq,
      caps (C := (p t).physical.ceiling) ha h.2.1 h.2.2.1] with n hn hh hcap
    simp only [LocalDomain,hn,h.1,true_and,hh.1,h.2.2.2.1 n,hcap]
  | w2Fixed j b =>
    filter_upwards [hp,hs (originalW2At j).s] with t h hq
    filter_upwards [h.2.1.eventually (eventually_gt_nhds h.1),hq,
      caps (C := (p t).physical.ceiling) (fixedW2_pos j b) h.2.1 h.2.2.1] with n hn hh hcap
    simp only [LocalDomain,hn,h.1,true_and,hh.1,h.2.2.2.1 n,hcap]
  | _ => simp [arity] at hz

private theorem static_step {X : Type*} {μ : Filter X} {p : X → TypedNode}
    {f : ℕ → X → TypedNode} (hp : Static μ p f) (hs : QueryLaws μ p f)
    (s : StepShape) (z : Point) (hz : arity s = 0) :
    Static μ (fun t => advance (p t) s z) (fun n t => advance (f n t) s z) ∧
    QueryLaws μ (fun t => advance (p t) s z) (fun n t => advance (f n t) s z) := by
  constructor
  · filter_upwards [hp] with t h
    have hu (n : ℕ) := advance_upper_eq (h.2.2.2.2 n) s z
    refine ⟨?_,?_,?_,?_,hu⟩ <;>
      cases s <;> simp [arity] at hz <;>
      first | exact h.1 | exact h.2.1 | exact h.2.2.1 | exact h.2.2.2.1
  · intro c
    cases s with
    | retain => exact hs c
    | transport _ | w1Fixed _ _ | w2Fixed _ _ =>
      exact .of_forall (fun t => .of_forall (fun n => compares_self _ _))
    | _ => simp [arity] at hz

private theorem atom_stable {X : Type*} {μ : Filter X} {p : X → TypedNode}
    {f : ℕ → X → TypedNode} (hs : QueryLaws μ p f) (lower : Bool) (atom : FloorAtom) :
    ∀ᶠ t in μ, ∀ᶠ n : ℕ in atTop,
      ((f n t).physical.argument ∈ tableAtomSet lower atom ↔
        (p t).physical.argument ∈ tableAtomSet lower atom) := by
  let c : ℝ := if lower then 2 else 1
  cases atom with
  | inl i =>
    filter_upwards [hs c,hs 5,hs (floorGrid i.val),hs (floorGrid (i.val+1))]
      with t h1 h2 h3 h4
    filter_upwards [h1,h2,h3,h4] with n h1 h2 h3 h4
    have hlo := not_congr h3.1
    have hhi := not_congr h4.2
    simp only [not_le] at hlo hhi
    cases lower <;> simpa only [tableAtomSet,floorAtomSet,upperAtomSet,if_true,if_false,
      Bool.false_eq_true,Set.mem_inter_iff,Set.mem_Icc,Set.mem_Ioo] using
        (and_congr (and_congr h1.2 h2.1) (and_congr hlo hhi))
  | inr j =>
    filter_upwards [hs c,hs 5,hs (floorGrid j.val)] with t h1 h2 h3
    filter_upwards [h1,h2,h3] with n h1 h2 h3
    have he := and_congr h3.1 h3.2
    rw [← le_antisymm_iff,← le_antisymm_iff] at he
    cases lower <;> simpa only [tableAtomSet,floorAtomSet,upperAtomSet,if_true,if_false,
      Bool.false_eq_true,Set.mem_inter_iff,Set.mem_Icc,Set.mem_singleton_iff] using
        (and_congr (and_congr h1.2 h2.1) he)

private theorem walk {X : Type*} {μ : Filter X} {p : X → TypedNode}
    {f : ℕ → X → TypedNode} (hp : Static μ p f) (hs : QueryLaws μ p f)
    {lo hi : ℝ} {mesh d : ℕ} (code : Program mesh d) (z : Coordinates d)
    (hz : ∀ i, arity (code i).1 = 0) (lower : Bool) (atom : FloorAtom) :
    ∀ᶠ t in μ, ∀ᶠ n : ℕ in atTop,
      (QueryMember lo hi (f n t) code z lower atom ↔ QueryMember lo hi (p t) code z lower atom) := by
  induction d generalizing p f with
  | zero =>
    simpa only [QueryMember,Member,realize,true_and] using atom_stable hs lower atom
  | succ d ih =>
    have hstep := static_step hp hs (code 0).1 (z 0) (hz 0)
    have htail := ih hstep.1 hstep.2 (tail code) (tail z) (fun i => hz i.succ)
    filter_upwards [hp,local_stable hp hs (code 0).1 (z 0) (hz 0),htail] with t h hloc he
    filter_upwards [hloc,he] with n hd hq
    simp only [QueryMember,Member,realize,h.2.2.2.2 n,hd] at hq ⊢
    tauto

theorem inherited_QueryMember_stable {lo hi : ℝ} {mesh d : ℕ} (k : Root)
    (code : Program mesh d) (z : Coordinates d) (hz : ∀ i, arity (code i).1 = 0)
    (lower : Bool) (atom : FloorAtom) :
    ∀ᵐ t ∂volume.restrict (rootBand k), ∀ᶠ n : ℕ in atTop,
      (QueryMember lo hi (frozenRoot n k (finiteTau n) t) code z lower atom ↔
        QueryMember lo hi (sourceRoot k 0 t) code z lower atom) := by
  apply walk _ (root_compares k) code z hz
  filter_upwards [ae_restrict_mem (rootBand_measurable k)] with t ht
  have hlim := frozenDescendant_residual_tendsto ht
    (fun i : Fin 0 => Fin.elim0 i : Program 0 0) (fun i => Fin.elim0 i)
  refine ⟨?_,hlim,?_,fun _ => rfl,fun _ => rfl⟩
  · rw [sourceRoot_residual]
    exact (by norm_num : (0:ℝ)<11/192).trans_le (sourceResidual_bounds (by norm_num) (by norm_num) ht).1
  · intro n
    have h := (rootLoss_bounds (n := n) (finiteTau_pos n).le (finiteTau_le n) ht).1
    have he := actual_descendant_residual_loss n k (finiteTau n) t
      (fun i : Fin 0 => Fin.elim0 i : Program 0 0) (fun i => Fin.elim0 i)
    exact sub_nonneg.mp (he.symm ▸ h)

private theorem weight_unchanged {mesh d : ℕ} (p : TypedNode) (code : Program mesh d)
    (z : Coordinates d) (hz : ∀ i, arity (code i).1 = 0) :
    physicalWeight (realize d p code z).physical = physicalWeight p.physical := by
  induction d generalizing p with
  | zero => rfl
  | succ d ih =>
    change physicalWeight (realize d (advance p (code 0).1 (z 0)) (tail code) (tail z)).physical = _
    rw [ih _ _ _ (fun i => hz i.succ)]
    have h := hz 0
    generalize he : (code 0).1 = s at h ⊢
    cases s <;> simp [arity] at h <;> rfl

def inheritedDensity {mesh d : ℕ} (lo hi : ℝ) (root : ℝ → TypedNode)
    (code : Program mesh d) (z : Coordinates d) (lower : Bool) (atom : FloorAtom) (t : ℝ) : ℝ :=
  ({v | QueryMember lo hi (root v) code z lower atom} : Set ℝ).indicator
    (fun v => physicalWeight (realize d (root v) code z).physical) t

/-- Full L1 for arbitrary lengths and both root bands on the native
chart t ↦ root plus zero fresh letters. No mass/stability input. -/
theorem inherited_full_native_L1 {lo hi : ℝ} {mesh d : ℕ} (k : Root)
    (code : Program mesh d) (z : Coordinates d) (hz : ∀ i, arity (code i).1 = 0)
    (lower : Bool) (atom : FloorAtom) :
    Tendsto (fun n : ℕ => ∫ t in rootBand k,
      |inheritedDensity lo hi (fun t => frozenRoot n k (finiteTau n) t) code z lower atom t -
        inheritedDensity lo hi (sourceRoot k 0) code z lower atom t|) atTop (𝓝 0) := by
  let E (root : ℝ → TypedNode) : Set ℝ := {t | QueryMember lo hi (root t) code z lower atom}
  let D := E (sourceRoot k 0)
  let S (n : ℕ) := E (fun t => frozenRoot n k (finiteTau n) t)
  let W := branchWeight (sourceResidual k 0)
  let V (n : ℕ) := frozenRootWeight n k (finiteTau n)
  have hmD : MeasurableSet D := measurableSet_QueryMember (sourceRoot_stateMeasurable _ _)
    (b := true) (fun _ => rfl) code (fun _ _ => measurable_const) lower atom
  have hmS (n : ℕ) : MeasurableSet (S n) :=
    measurableSet_QueryMember (frozenRoot_stateMeasurable _ _ _)
      (b := true) (fun _ => rfl) code (fun _ _ => measurable_const) lower atom
  let err (n : ℕ) (t : ℝ) := |(S n).indicator (V n) t - D.indicator W t|
  have hW (t : ℝ) : physicalWeight (sourceRoot k 0 t).physical = W t :=
    root_physicalWeight k 0 t
  have hident (n : ℕ) (t : ℝ) :
      |inheritedDensity lo hi (fun t => frozenRoot n k (finiteTau n) t) code z lower atom t -
        inheritedDensity lo hi (sourceRoot k 0) code z lower atom t| = err n t := by
    simp only [inheritedDensity,weight_unchanged _ code z hz,hW]
    rfl
  let good (n : ℕ) := meshError n ≤ 11/384
  let G (n : ℕ) (t : ℝ) := if good n then err n t else 0
  have hmeas (n : ℕ) : AEStronglyMeasurable (G n) (volume.restrict (rootBand k)) := by
    by_cases hn : good n
    · simp only [G, if_pos hn]
      exact (((frozenRootWeight_measurable n k _).aestronglyMeasurable.indicator (hmS n)).sub
        ((sourceWeight_measurable k _).aestronglyMeasurable.indicator hmD)).abs
    · simp only [G, if_neg hn]; exact aestronglyMeasurable_const
  have hb (n : ℕ) : ∀ᵐ t ∂volume.restrict (rootBand k), ‖G n t‖ ≤ 2*weightEnvelope := by
    filter_upwards [ae_restrict_mem (rootBand_measurable k)] with t ht
    have hwi : |W t| ≤ weightEnvelope := weight_bound ((by norm_num : (11/384:ℝ) ≤ 11/192).trans
      (sourceResidual_bounds (by norm_num) (by norm_num) ht).1) (rootBand_subset _ ht).1
    have hpos := (abs_nonneg _).trans hwi
    by_cases hn : good n
    · have hwf : |V n t| ≤ weightEnvelope := by
        change |frozenRootWeight n k (finiteTau n) t| ≤ _
        rw [frozenRootWeight_eq]
        simpa only [mul_comm] using weight_bound
          (frozenRoot_residual_bounds (finiteTau_pos n).le (finiteTau_le n) ht hn).1 (rootBand_subset _ ht).1
      simp only [G,if_pos hn,err,Real.norm_eq_abs,abs_abs]
      apply (abs_sub _ _).trans
      by_cases he : t ∈ S n <;> by_cases hd : t ∈ D <;> simp [he,hd] <;> linarith
    · simp only [G,if_neg hn,norm_zero]; linarith
  have hlim : ∀ᵐ t ∂volume.restrict (rootBand k), Tendsto (fun n => G n t) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem (rootBand_measurable k),
      inherited_QueryMember_stable k code z hz lower atom] with t ht hst
    change ∀ᶠ n : ℕ in atTop, t ∈ S n ↔ t ∈ D at hst
    by_cases hd : t ∈ D
    · have hw : Tendsto (fun n => |V n t-W t|) atTop (𝓝 0) := by
        simpa using ((frozenRootWeight_tendsto ht).sub_const (W t)).abs
      apply hw.congr'
      filter_upwards [eventually_fine_mesh,hst] with n hn he
      simp [G,good,err,hn,he.mpr hd,hd]
    · apply tendsto_const_nhds.congr'
      filter_upwards [hst] with n he
      simp [G,err,hd,fun hs => hd (he.mp hs)]
  have hD := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (rootBand k)) (f := fun _ : ℝ => (0:ℝ))
    (fun _ : ℝ => 2*weightEnvelope) hmeas (integrableOn_const (rootBand_volume_lt_top k).ne) hb hlim
  apply (show Tendsto (fun n => ∫ t in rootBand k, G n t) atTop (𝓝 0) by
    simpa only [integral_zero] using hD).congr'
  filter_upwards [eventually_fine_mesh] with n hn
  apply setIntegral_congr_fun (rootBand_measurable k)
  intro t _
  rw [hident]
  exact if_pos hn

end
end ImbalancedChen.Part5OriginalH430InheritedMemberL1

