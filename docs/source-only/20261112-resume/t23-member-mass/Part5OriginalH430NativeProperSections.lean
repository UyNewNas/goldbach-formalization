import ImbalancedChen.Part5OriginalH430FullMemberMeasurable
import ImbalancedChen.Part5OriginalH430NativeBuchstabMeasure

/-! Disintegration in the last fresh native coordinate. No padded
coordinate is integrated. All original active query constructors, including
the moving D7/D8 denominator and both Buchstab directions, are treated.
The arbitrary integrable density in the last lemma is a test on a single
section, not an assumed mass of a boundary. -/
namespace ImbalancedChen.Part5OriginalH430NativeProperSections
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open Part5OriginalH430NativeQueryPaths Part5OriginalH430ActiveKnotPullbacks

/-- The compact cube for integration comes from the *physical*
coordinates of the admitted path. This tests only the active slots. -/
theorem fresh_coordinate_floor {p : PhysicalNode} {s : StepShape} {z : Point}
    (hd : LocalDomain p s z) {j : Fin 2} (hj : j.val < arity s) :
    residual p / 6 ≤ z j := by
  have frac (x : ℝ) (hx : 1/5 ≤ x / residual p) : residual p/6 ≤ x := by
    have h := (le_div_iff₀ hd.1).mp hx
    linarith only [h,hd.1]
  cases s with
  | retain | transport _ | w1Fixed _ _ | w2Fixed _ _ => simp [arity] at hj
  | buchstabUpper =>
    have hj0 : j = 0 := Fin.ext (by change j.val < 1 at hj; change j.val = 0; omega)
    subst j
    have hw := (buchstabUpperDomain_subset p.argument hd.2.2).2
    change residual p / z 0 - 1 ≤ 5 at hw
    have h := (div_le_iff₀ hd.2.1.1).mp (show residual p / z 0 ≤ 6 by linarith)
    linarith
  | buchstabLower =>
    have hj0 : j = 0 := Fin.ext (by change j.val < 1 at hj; change j.val = 0; omega)
    subst j
    have hw := (buchstabLowerDomain_subset hd.2.1 hd.2.2.2).2
    change residual p / z 0 - 1 ≤ 5 at hw
    have h := (div_le_iff₀ hd.2.2.1.1).mp (show residual p / z 0 ≤ 6 by linarith)
    linarith
  | w1Singleton i i' =>
    have hj0 : j = 0 := Fin.ext (by change j.val < 1 at hj; change j.val = 0; omega)
    subst j
    exact frac _ (W1Domain_subset i i' hd.2.2.1).1
  | w2Singleton i piece =>
    have hj0 : j = 0 := Fin.ext (by change j.val < 1 at hj; change j.val = 0; omega)
    subst j
    exact frac _ (W2SingletonDomain_subset
      (originalRepairedW2Bank_geometry _ (originalW2At_mem i)) piece hd.2.2.1).1
  | w2Pair i piece =>
    exact frac _ ((W2PairDomain_subset
      (originalRepairedW2Bank_geometry _ (originalW2At_mem i)) piece hd.2.2.1).1 j)

/-- Keep the smaller pair-prime coordinate fixed. For each singleton
the free variable is the only active coordinate. -/
def sectionPoint (q : FeedbackQuery) (u x : ℝ) : Point :=
  match q with
  | .w2Pair _ _ => ![u,x]
  | _ => ![x,0]

def pivot : FeedbackQuery → ℝ → ℝ
  | .w1 _ j, _ => W1Anchor j
  | .w2Singleton j _, _ => (originalW2At j).s0
  | .w2Pair j k, _ => if k.val < 2 then (originalW2At j).s0 else 1
  | .buchstabUpper _, c => c+1
  | .buchstabLower _, c => c+1

private theorem pos_s0 (j : Fin 36) : 0 < (originalW2At j).s0 := by
  have h := (originalRepairedW2Bank_geometry _ (originalW2At_mem j)).1
  exact one_div_pos.mp ((by norm_num : (0:ℝ) < 1/5).trans_le h)

theorem pivot_pos (q : FeedbackQuery) {c : ℝ} (hc : 1 ≤ c) : 0 < pivot q c := by
  cases q with
  | w1 i j => dsimp [pivot,W1Anchor]; positivity
  | w2Singleton j k => exact pos_s0 j
  | w2Pair j k =>
    unfold pivot
    split_ifs
    · exact pos_s0 j
    · norm_num
  | buchstabUpper i => change 0 < c+1; linarith
  | buchstabLower i => change 0 < c+1; linarith

theorem numerator_section (p : PhysicalNode) (q : FeedbackQuery) (c u x : ℝ) :
    knotNumerator p (sectionPoint q u x) c q =
      knotNumerator p (sectionPoint q u 0) c q - pivot q c*x := by
  cases q with
  | w1 i j => simp [sectionPoint,knotNumerator,pivot]
  | w2Singleton j k => simp [sectionPoint,knotNumerator,pivot]
  | buchstabUpper i => simp [sectionPoint,knotNumerator,pivot]
  | buchstabLower i => simp [sectionPoint,knotNumerator,pivot]
  | w2Pair j k =>
    by_cases hk : k.val < 2 <;> simp [sectionPoint,knotNumerator,pivot,hk] <;> ring

def hit (p : PhysicalNode) (q : FeedbackQuery) (c u : ℝ) : ℝ :=
  knotNumerator p (sectionPoint q u 0) c q / pivot q c

theorem section_zero_iff (p : PhysicalNode) (q : FeedbackQuery) {c : ℝ}
    (hc : 1 ≤ c) (u x : ℝ) :
    knotNumerator p (sectionPoint q u x) c q = 0 ↔ x = hit p q c u := by
  rw [numerator_section, hit, eq_div_iff (pivot_pos q hc).ne']
  constructor <;> intro h <;> linarith only [h, mul_comm (pivot q c) x]

/-- A zero row on an active coordinate is a single native point even
after arbitrary earlier constraints or extra suffix tests. -/
theorem active_knot_section_null (p : PhysicalNode) (q : FeedbackQuery) {c : ℝ}
    (hc : 1 ≤ c) (u : ℝ) :
    volume {x : ℝ | 0 < residual p ∧ 0 < sectionPoint q u x 0 ∧
      (perform p q.shape (sectionPoint q u x)).argument = c} = 0 := by
  apply measure_mono_null (t := {hit p q c u}) _ (measure_singleton _)
  rintro x ⟨hL,hx,he⟩
  exact (section_zero_iff p q hc u x).mp ((query_knot_comparisons hL hx q c).2.2.mp he)

/-- Full *closed* proper strips, including equality, have vanishing L1
mass on the actual fresh coordinate, with no assumption on the boundary.
The density can include all measurable prefix/suffix selectors. -/
theorem active_strip_integral_tendsto (p : PhysicalNode) (q : FeedbackQuery) {c : ℝ}
    (hc : 1 ≤ c) (u : ℝ) {f : ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun n : ℕ => ∫ x : ℝ,
      ({y : ℝ | |knotNumerator p (sectionPoint q u y) c q| ≤ 1/((n:ℝ)+1)} :
        Set ℝ).indicator (fun y => |f y|) x) atTop (𝓝 0) := by
  let A := fun x : ℝ => knotNumerator p (sectionPoint q u x) c q
  let S := fun n : ℕ => {x : ℝ | |A x| ≤ 1/((n:ℝ)+1)}
  have hA : Measurable A := by
    have hfun : A = fun x : ℝ => knotNumerator p (sectionPoint q u 0) c q - pivot q c*x :=
      funext (numerator_section p q c u)
    rw [hfun]
    exact measurable_const.sub (measurable_const.mul measurable_id)
  have hS (n : ℕ) : MeasurableSet (S n) := measurableSet_le hA.abs measurable_const
  have hz : ∀ᵐ x : ℝ, x ≠ hit p q c u := by
    exact ae_iff.mpr (by simpa only [not_not] using
      (measure_singleton (μ := volume) (hit p q c u)))
  have hlim : ∀ᵐ x : ℝ, Tendsto (fun n : ℕ => (S n).indicator (fun y => |f y|) x)
      atTop (𝓝 0) := by
    filter_upwards [hz] with x hx
    have hpos : 0 < |A x| := abs_pos.mpr (fun h =>
      hx ((section_zero_iff p q hc u x).mp h))
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (eventually_lt_nhds hpos)] with n hn
    exact (indicator_of_notMem (show x ∉ S n from not_le.mpr hn) _).symm
  have hh := tendsto_integral_of_dominated_convergence
    (f := fun _ : ℝ => (0:ℝ)) (fun x : ℝ => |f x|)
    (fun n : ℕ => hf.abs.aestronglyMeasurable.indicator (hS n)) hf.abs
    (fun n => Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ S n
      · simp only [indicator_of_mem hx, Real.norm_eq_abs, abs_abs, le_refl]
      · simpa only [indicator_of_notMem hx,norm_zero] using abs_nonneg (f x))) hlim
  simpa only [integral_zero] using hh

end
end ImbalancedChen.Part5OriginalH430NativeProperSections
