import ImbalancedChen.Part5OriginalH430NativePrefixFubini
import ImbalancedChen.Part5OriginalH430InheritedMemberL1

namespace ImbalancedChen.Part5OriginalH430FreshAxis
noncomputable section
open Set MeasureTheory Filter Topology Function
open scoped Classical
open P5OriginalActionMassBound P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph Part5OriginalH430NativeQueryPaths
open Part5OriginalH430FullMemberMeasurable Part5OriginalH430NativeProperSections
open Part5OriginalH430ActiveKnotPullbacks Part5OriginalH430InheritedMemberL1
open Part5OriginalH430DescendantLimits Part5OriginalH430PhysicalRoots

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Chart (ι : Type*) := ι → ℝ

/-- Integrate one genuine coordinate of this same finite product. The
function may depend measurably on all other coordinates, including later
slots. Independence in the pivot slot is an exact update identity. -/
theorem avoid_graph (j : ι) (f : Chart ι → ℝ) (hf : Measurable f)
    (hind : ∀ x : Chart ι, f (update x j 0) = f x) :
    ∀ᵐ x : Chart ι, x j ≠ f x := by
  let A := {i : ι // i ≠ j}
  let B := {i : ι // ¬i ≠ j}
  let b : B := ⟨j,fun h => h rfl⟩
  let fill (u : A → ℝ) : Chart ι := fun i => if hi : i ≠ j then u ⟨i,hi⟩ else 0
  have hm : Measurable fill := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i ≠ j
    · simpa only [fill,dif_pos hi] using (measurable_pi_apply (⟨i,hi⟩ : A) :
        Measurable (fun u : A → ℝ => u ⟨i,hi⟩))
    · simp only [fill,dif_neg hi]; exact measurable_const
  have he : MeasurableSet {z : (A → ℝ) × (B → ℝ) | z.2 b ≠ f (fill z.1)} :=
    (measurableSet_eq_fun ((measurable_pi_apply b).comp measurable_snd)
      ((hf.comp hm).comp measurable_fst)).compl
  have hp : ∀ᵐ z : (A → ℝ) × (B → ℝ), z.2 b ≠ f (fill z.1) := by
    rw [Measure.volume_eq_prod]
    apply (Measure.ae_prod_iff_ae_ae he).mpr
    exact Eventually.of_forall (fun u =>
      (Measure.quasiMeasurePreserving_eval (fun _ : B => (volume : Measure ℝ)) b).ae
        (volume.ae_ne (f (fill u))))
  have h := (volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℝ)
    (fun i => i ≠ j)).quasiMeasurePreserving.ae hp
  filter_upwards [h] with x hx
  change x j ≠ f (fill (fun i => x i.val)) at hx
  have hf' : fill (fun i : A => x i.val) = update x j 0 := by
    funext i
    by_cases hi : i = j
    · subst i; simp [fill]
    · simp [fill,hi,update_of_ne hi]
  rwa [hf',hind] at hx

def point (s : StepShape) (slot : Fin (arity s) → ι) (x : Chart ι) : Point :=
  fun i => if h : i.val < arity s then x (slot ⟨i.val,h⟩) else 0

theorem point_measurable (s : StepShape) (slot : Fin (arity s) → ι) (j : Fin 2) :
    Measurable (fun x : Chart ι => point s slot x j) := by
  unfold point
  split_ifs <;> first | exact measurable_pi_apply _ | exact measurable_const

theorem point_independent {s : StepShape} {slot : Fin (arity s) → ι} {j : ι}
    (h : ∀ i, slot i ≠ j) (x : Chart ι) :
    point s slot (update x j 0) = point s slot x := by
  funext i
  unfold point
  split_ifs with hi
  · simp only [update_of_ne (h ⟨i.val,hi⟩)]
  · rfl

structure State (G : Chart ι → Prop) (p : Chart ι → TypedNode) (f : ℕ → Chart ι → TypedNode) : Prop where
  measurable : StateMeasurable (fun x => (p x).physical)
  pos : ∀ x, G x → 0 < residual (p x).physical
  capPos : ∀ x, G x → 0 < (p x).physical.ceiling
  arg : ∀ x, G x → (p x).physical.argument ∈ Icc (1:ℝ) 6
  level : ∀ x, G x → Tendsto (fun n => residual (f n x).physical) atTop (𝓝 (residual (p x).physical))
  query : ∀ x, G x → Tendsto (fun n => (f n x).physical.argument) atTop (𝓝 (p x).physical.argument)
  below : ∀ x, G x → ∀ n, residual (f n x).physical ≤ residual (p x).physical
  ceiling : ∀ x n, (f n x).physical.ceiling = (p x).physical.ceiling
  upper : ∀ x n, (f n x).upper = (p x).upper
  sign : ∀ c : ℝ, ∀ᵐ x : Chart ι, G x → ∀ᶠ n : ℕ in atTop,
    Compares (f n x).physical.argument (p x).physical.argument c

theorem cmp_of_ne {u : ℕ → ℝ} {a c : ℝ} (hu : Tendsto u atTop (𝓝 a)) (hne : a ≠ c) :
    ∀ᶠ n : ℕ in atTop, Compares (u n) a c := by
  rcases lt_or_gt_of_ne hne with h | h
  · filter_upwards [hu.eventually (eventually_lt_nhds h)] with n hn
    exact ⟨iff_of_true hn.le h.le,iff_of_false (not_le.mpr hn) (not_le.mpr h)⟩
  · filter_upwards [hu.eventually (eventually_gt_nhds h)] with n hn
    exact ⟨iff_of_false (not_le.mpr hn) (not_le.mpr h),iff_of_true hn.le h.le⟩

/-- The direct section intersection used in joint_strip_L1, now inside
the full original ambient slot product, with its pivot explicitly removed. -/
theorem active_avoids {p : Chart ι → TypedNode} (hp : StateMeasurable (fun x => (p x).physical))
    (q : FeedbackQuery) (sl : Fin (arity q.shape) → ι) (hinj : Injective sl)
    (hind : ∀ j x, p (update x (sl j) 0) = p x) {c : ℝ} (hc : 1 ≤ c) :
    ∀ᵐ x : Chart ι, 0 < residual (p x).physical → 0 < point q.shape sl x 0 →
      (perform (p x).physical q.shape (point q.shape sl x)).argument ≠ c := by
  let ix : Fin (arity q.shape) := match q with
    | .w2Pair _ _ => 1
    | .w1 _ _ | .w2Singleton _ _ | .buchstabUpper _ | .buchstabLower _ => 0
  let u := fun x : Chart ι => point q.shape sl x 0
  let small := fun x : Chart ι => match q with | .w2Pair _ _ => u x | _ => 0
  let H := fun x : Chart ι => hit (p x).physical q c (small x)
  have hs : Measurable small := by
    cases q <;> first | exact measurable_const | exact point_measurable _ _ _
  have hm : Measurable H := by
    have hL := hp.1
    cases q with
    | w2Pair i j =>
      by_cases hj : j.val < 2 <;> simp [H,hit,sectionPoint,knotNumerator,pivot,hj] <;> fun_prop
    | _ => simp [H,hit,sectionPoint,knotNumerator,pivot] <;> fun_prop
  have hsmall (x : Chart ι) : small (update x (sl ix) 0) = small x := by
    cases q with
    | w2Pair i j =>
      change update x (sl 1) 0 (sl 0) = x (sl 0)
      rw [update_of_ne (fun h => (by decide : (0 : Fin 2) ≠ 1) (hinj h))]
    | _ => rfl
  have hh := avoid_graph (sl ix) H hm (fun x => by
    dsimp only [H]; rw [hind,hsmall])
  have hpoint (x : Chart ι) : point q.shape sl x = sectionPoint q (small x) (x (sl ix)) := by
    cases q <;> funext j <;> fin_cases j <;> rfl
  filter_upwards [hh] with x hx
  intro hL hz he
  have heq := (query_knot_comparisons hL hz q c).2.2.mp he
  rw [hpoint] at heq
  exact hx ((section_zero_iff _ q hc _ _).mp heq)

end
end ImbalancedChen.Part5OriginalH430FreshAxis

