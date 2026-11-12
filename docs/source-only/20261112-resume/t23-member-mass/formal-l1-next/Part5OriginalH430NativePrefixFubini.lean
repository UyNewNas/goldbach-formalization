import ImbalancedChen.Part5OriginalH430NativeProperSections
import Mathlib.MeasureTheory.Measure.Prod

/-! Proper terminal query walls after an arbitrary genuine native history.
The smaller W2 prime is an independent parameter. The final fresh prime
is integrated with one-dimensional Lebesgue measure. -/
namespace ImbalancedChen.Part5OriginalH430NativePrefixFubini
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators
open P5OriginalActionMassBound P2EnhancedLowerPhysicalNode
open P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalH430NativeQueryPaths Part5OriginalH430ActiveKnotPullbacks
open Part5OriginalH430NativeProperSections Part5OriginalH430FullMemberMeasurable
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement

private theorem measurable_hit {X : Type*} [MeasurableSpace X] {p : X → PhysicalNode}
    {u : X → ℝ} (hl : Measurable (fun x => residual (p x))) (hu : Measurable u)
    (q : FeedbackQuery) (c : ℝ) : Measurable (fun x => hit (p x) q c (u x)) := by
  cases q with
  | w2Pair i j =>
    by_cases hj : j.val < 2 <;> simp [hit,sectionPoint,knotNumerator,pivot,hj] <;> fun_prop
  | _ => simp [hit,sectionPoint,knotNumerator,pivot] <;> fun_prop

theorem joint_active_null {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {p : X → PhysicalNode} {u : X → ℝ}
    (hl : Measurable (fun x => residual (p x))) (hu : Measurable u)
    (q : FeedbackQuery) {c : ℝ} (hc : 1 ≤ c) :
    ∀ᵐ v ∂μ.prod volume,
      knotNumerator (p v.1) (sectionPoint q (u v.1) v.2) c q ≠ 0 := by
  let B := fun t => hit (p t) q c (u t)
  have hm : MeasurableSet {v : X × ℝ | v.2 ≠ B v.1} :=
    (measurableSet_eq_fun measurable_snd ((measurable_hit hl hu q c).comp measurable_fst)).compl
  have hne : ∀ᵐ v ∂μ.prod volume, v.2 ≠ B v.1 :=
    (ae_prod_iff_ae_ae hm).mpr (.of_forall (fun t => volume.ae_ne (B t)))
  exact hne.mono (fun v hv h => hv ((section_zero_iff (p v.1) q hc _ _).mp h))

def jointStrip {X : Type*} (p : X → PhysicalNode) (u : X → ℝ) (q : FeedbackQuery)
    (c : ℝ) (n : ℕ) : Set (X × ℝ) :=
  {v | |knotNumerator (p v.1) (sectionPoint q (u v.1) v.2) c q| ≤ 1/((n:ℝ)+1)}

theorem joint_strip_L1 {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    {p : X → PhysicalNode} {u : X → ℝ}
    (hl : Measurable (fun x => residual (p x))) (hu : Measurable u)
    (q : FeedbackQuery) {c : ℝ} (hc : 1 ≤ c) {f : X × ℝ → ℝ}
    (hf : Integrable f (μ.prod volume)) :
    Tendsto (fun n : ℕ => ∫ v, (jointStrip p u q c n).indicator (fun v => |f v|) v
        ∂(μ.prod volume)) atTop (𝓝 0) := by
  let A := fun v : X × ℝ => knotNumerator (p v.1) (sectionPoint q (u v.1) v.2) c q
  have ha : Measurable A := by
    have he : A = fun v : X × ℝ => (hit (p v.1) q c (u v.1) - v.2) * pivot q c := by
      funext v
      dsimp only [A]
      rw [numerator_section,hit]
      field_simp [(pivot_pos q hc).ne'] <;> ring
    rw [he]
    exact (((measurable_hit hl hu q c).comp measurable_fst).sub measurable_snd).mul_const _
  have hset (n : ℕ) : MeasurableSet (jointStrip p u q c n) := measurableSet_le ha.abs measurable_const
  have hlim : ∀ᵐ v ∂μ.prod volume, Tendsto
      (fun n => (jointStrip p u q c n).indicator (fun w => |f w|) v) atTop (𝓝 0) := by
    filter_upwards [joint_active_null μ hl hu q hc] with v hv
    have hpos : 0 < |A v| := abs_pos.mpr hv
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (eventually_lt_nhds hpos)] with n hn
    exact (indicator_of_notMem (show v ∉ jointStrip p u q c n from not_le.mpr hn) _).symm
  have hbound (n : ℕ) : ∀ᵐ v ∂μ.prod volume,
      ‖(jointStrip p u q c n).indicator (fun w => |f w|) v‖ ≤ |f v| := by
    apply Filter.Eventually.of_forall
    intro v
    by_cases hv : v ∈ jointStrip p u q c n
    · simp [hv]
    · simpa only [indicator_of_notMem hv,norm_zero] using abs_nonneg (f v)
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (μ := μ.prod volume) (f := fun _ : X × ℝ => (0:ℝ)) (fun v => |f v|)
    (fun n => hf.abs.aestronglyMeasurable.indicator (hset n)) hf.abs hbound hlim

/-- Option.none is the original root; some n is its original frozen
root at precision n. The physical parent is realized on its own
canonical native program at the specified coordinates. -/
def nativeParent {d : ℕ} (mesh : ℕ) (k : Root) (tau : ℝ) (prec : Option ℕ)
    (shape : Fin d → StepShape) (x : NativeSlot shape → ℝ) : PhysicalNode :=
  let t := nativeRootCoordinate x
  let root := match prec with
    | none => sourceRoot k 0 t
    | some n => frozenRoot n k tau t
  (realize d root (nativeProgram mesh shape x) (nativeCoordinates shape x)).physical

theorem nativeParent_measurable {d : ℕ} (mesh : ℕ) (k : Root) (tau : ℝ)
    (prec : Option ℕ) (shape : Fin d → StepShape) :
    StateMeasurable (nativeParent mesh k tau prec shape) := by
  let base := fun x : NativeSlot shape → ℝ => match prec with
    | none => sourceRoot k 0 (nativeRootCoordinate x)
    | some n => frozenRoot n k tau (nativeRootCoordinate x)
  have ht : Measurable (nativeRootCoordinate : (NativeSlot shape → ℝ) → ℝ) :=
    measurable_pi_apply (.inl ())
  have hbase : StateMeasurable (fun x => (base x).physical) := by
    cases prec with
    | none =>
      have h := sourceRoot_stateMeasurable k 0
      exact ⟨h.1.comp ht,h.2.1.comp ht,h.2.2.comp ht⟩
    | some n =>
      have h := frozenRoot_stateMeasurable n k tau
      exact ⟨h.1.comp ht,h.2.1.comp ht,h.2.2.comp ht⟩
  have hz (i : Fin d) (j : Fin 2) :
      Measurable (fun x : NativeSlot shape → ℝ => nativeCoordinates shape x i j) := by
    unfold nativeCoordinates
    split_ifs
    · exact measurable_pi_apply _
    · exact measurable_const
  let code := canonicalProgram 0 1 mesh shape (fun _ _ => 0)
  have he : nativeParent mesh k tau prec shape =
      fun x => (realize d (base x) code (nativeCoordinates shape x)).physical := by
    funext x
    exact congrArg TypedNode.physical (realize_eq_of_shapes (base x) _ code _ (fun _ => rfl))
  rw [he]
  exact realize_stateMeasurable hbase code hz

/-- Native coordinates of every preceding step are integrated jointly,
without padded primes. For a singleton choose u constant. In the pair
case the prefix space can be augmented by the independent smaller prime
using joint_strip_L1 and measurable_fst/measurable_snd. -/
theorem actual_prefix_strip_L1 {d : ℕ} (mesh : ℕ) (k : Root) (tau : ℝ)
    (prec : Option ℕ) (shape : Fin d → StepShape)
    {u : (NativeSlot shape → ℝ) → ℝ} (hu : Measurable u) (q : FeedbackQuery)
    {c : ℝ} (hc : 1 ≤ c) {f : (NativeSlot shape → ℝ) × ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun n : ℕ => ∫ v,
      (jointStrip (nativeParent mesh k tau prec shape) u q c n).indicator
        (fun w => |f w|) v) atTop (𝓝 0) := by
  rw [Measure.volume_eq_prod] at hf ⊢
  exact joint_strip_L1 volume (nativeParent_measurable mesh k tau prec shape).1 hu q hc hf

theorem actual_prefix_pair_strip_L1 {d : ℕ} (mesh : ℕ) (k : Root) (tau : ℝ)
    (prec : Option ℕ) (shape : Fin d → StepShape) (j : Fin 36) (s : Fin 4)
    {c : ℝ} (hc : 1 ≤ c) {f : ((NativeSlot shape → ℝ) × ℝ) × ℝ → ℝ}
    (hf : Integrable f) :
    Tendsto (fun n : ℕ => ∫ v,
      (jointStrip (fun y : (NativeSlot shape → ℝ) × ℝ =>
        nativeParent mesh k tau prec shape y.1) Prod.snd (.w2Pair j s) c n).indicator
        (fun w => |f w|) v) atTop (𝓝 0) := by
  rw [Measure.volume_eq_prod] at hf ⊢
  exact joint_strip_L1 volume ((nativeParent_measurable mesh k tau prec shape).1.comp measurable_fst)
    measurable_snd (.w2Pair j s) hc hf

end
end ImbalancedChen.Part5OriginalH430NativePrefixFubini

