import ImbalancedChen.Part5OriginalH430PhysicalRoots
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Constructed finite simple-function approximations to the actual normalized
W1/W2/Buchstab and U3/U4 query integrals.  All query knots are kept exactly.
Errors are L1/absolute and are selected simultaneously before any N.

This constructs finite simple-function/sign labels.  Explicit measurable-
cell theorems are not exported.  A smooth/rectangular arithmetic realization
at a common frozen Q is a separate, OPEN obligation; this file does not
rename simple-function cells as licensed prime families.
-/

namespace ImbalancedChen.Part5OriginalH430AbsoluteQueries

noncomputable section
open Set MeasureTheory Filter Topology
open scoped BigOperators Classical
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P5OriginalFeedbackTableKernels
open Part5UpperTables Part5UpperTables.OriginalU34
open Part5OriginalUpsilon5CausalDictionary

inductive Primitive where
  | w1 (i : Fin 7) (j : Fin 10)
  | w2Singleton (bank : Fin 36) (piece : Fin 3)
  | w2Pair (bank : Fin 36) (piece : Fin 4)
  | buchstabUpper (cell : Fin 200)
  | buchstabLower (cell : Fin 150)
  | U3main | U3tail | U4
  deriving DecidableEq, Fintype

def Space : Primitive → Type
  | .w2Pair _ _ => Point
  | _ => ℝ

instance (p : Primitive) : MeasurableSpace (Space p) := by
  cases p <;> exact inferInstance
instance (p : Primitive) : MeasureSpace (Space p) := by
  cases p <;> exact inferInstance

structure Data (X : Type*) [MeasureSpace X] where
  domain : Set X
  domain_measurable : MeasurableSet domain
  density : X → ℝ
  density_measurable : Measurable density
  density_integrable : IntegrableOn density domain
  query : X → ℝ
  query_measurable : Measurable query
  lower : Bool

private theorem singleton_integrable {D : Set ℝ} (h : D ⊆ singletonAmbient) :
    IntegrableOn singletonKernel D :=
  (singletonKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc).mono_set h

private theorem pair_integrable {D : Set Point} (h : D ⊆ pairAmbient) :
    IntegrableOn pairKernel D :=
  (pairKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc).mono_set h

private theorem buchstab_integrable {D : Set ℝ} (h : D ⊆ buchstabAmbient) :
    IntegrableOn buchstabKernel D :=
  (buchstabKernel_continuous.continuousOn.integrableOn_compact isCompact_Icc).mono_set h

def upperStart (i : Fin 200) : ℝ := 1 + ((i.val : ℝ) + 1) / 50
def lowerStart (i : Fin 150) : ℝ := 2 + ((i.val : ℝ) + 1) / 50

private theorem lowerStart_ge_two (i : Fin 150) : 2 ≤ lowerStart i := by
  have h : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  dsimp [lowerStart]; linarith

private def rootData (D : Set ℝ) (hD : MeasurableSet D)
    (hsub : D ⊆ coordinateInterval) (r : ℝ → ℝ) (hr : Continuous r)
    (hR : ∀ t ∈ coordinateInterval, (11 / 192 : ℝ) ≤ r t ∧ r t ≤ 1 / 2) : Data ℝ :=
  ⟨D, hD, branchWeight r, by unfold branchWeight; fun_prop,
    (integrableOn_branchWeight hr hR).mono_set hsub,
    rootArgument r, (continuous_const.max (hr.div_const a)).measurable, false⟩

/-- Literal original domains/profiles.  Root-only max-two does not alter
the moving D7/D8 child profiles. -/
def data : (p : Primitive) → Data (Space p)
  | .w1 i j =>
      ⟨W1Domain i j, measurableSet_Ioo, singletonKernel,
        singletonKernel_continuous.measurable, singleton_integrable (W1Domain_subset i j),
        singletonProfile (W1Anchor j), measurable_singletonProfile _, true⟩
  | .w2Singleton k j =>
      ⟨W2SingletonDomain (originalW2At k) j, measurableSet_W2SingletonDomain _ _,
        singletonKernel, singletonKernel_continuous.measurable,
        singleton_integrable (W2SingletonDomain_subset
          (originalRepairedW2Bank_geometry _ (originalW2At_mem k)) j),
        singletonProfile (originalW2At k).s0, measurable_singletonProfile _, true⟩
  | .w2Pair k j =>
      ⟨W2PairDomain (originalW2At k) j, measurableSet_W2PairDomain _ _,
        pairKernel, pairKernel_continuous.measurable,
        pair_integrable (W2PairDomain_subset
          (originalRepairedW2Bank_geometry _ (originalW2At_mem k)) j),
        pairProfile (originalW2At k) j, measurable_pairProfile _ _, false⟩
  | .buchstabUpper i =>
      ⟨buchstabUpperDomain (upperStart i), measurableSet_Icc,
        buchstabKernel, buchstabKernel_continuous.measurable,
        buchstab_integrable (buchstabUpperDomain_subset _), id, measurable_id, true⟩
  | .buchstabLower i =>
      ⟨buchstabLowerDomain (lowerStart i), measurableSet_Icc,
        buchstabKernel, buchstabKernel_continuous.measurable,
        buchstab_integrable (buchstabLowerDomain_subset (lowerStart_ge_two i)),
        id, measurable_id, false⟩
  | .U3main => rootData (Ico a tailCutoff) measurableSet_Ico
      (fun _ hx => ⟨hx.1, hx.2.le.trans (by norm_num [tailCutoff])⟩)
      mainResidual continuous_mainResidual (fun _ hx => mainResidual_bounds hx)
  | .U3tail => rootData (Ico tailCutoff (1 / 3)) measurableSet_Ico
      (fun _ hx => ⟨(by norm_num [a, tailCutoff]).trans hx.1, hx.2.le⟩)
      tailResidual continuous_tailResidual (fun _ hx => tailResidual_bounds hx)
  | .U4 => rootData (Ico a (59 / 250)) measurableSet_Ico
      (fun _ hx => ⟨hx.1, hx.2.le.trans (by norm_num)⟩)
      mainResidual continuous_mainResidual (fun _ hx => mainResidual_bounds hx)

def atomSet (p : Primitive) (b : FloorAtom) : Set (Space p) :=
  (data p).domain ∩ tablePullback (data p).lower (data p).query b

theorem atomSet_measurable (p : Primitive) (b : FloorAtom) :
    MeasurableSet (atomSet p b) :=
  (data p).domain_measurable.inter
    (measurableSet_tablePullback _ (data p).query_measurable b)

def atomDensity (p : Primitive) (b : FloorAtom) : Space p → ℝ :=
  (atomSet p b).indicator (data p).density

theorem atomDensity_measurable (p : Primitive) (b : FloorAtom) :
    Measurable (atomDensity p b) :=
  (data p).density_measurable.indicator (atomSet_measurable p b)

theorem atomDensity_integrable (p : Primitive) (b : FloorAtom) :
    Integrable (atomDensity p b) :=
  ((data p).density_integrable.mono_set inter_subset_left).integrable_indicator
    (atomSet_measurable p b)

/-- Exact knot atoms include the adjacent-cell minimum; no seam is
declared null after a query has been composed with a root/child profile. -/
theorem actual_query_integral (p : Primitive) (nums : Fin 200 → ℤ) :
    (∫ x in (data p).domain,
      weightedTable (data p).lower nums (data p).query (data p).density x) =
      ∑ b : FloorAtom, floorAtomValue nums b * ∫ x, atomDensity p b x := by
  rw [weightedTable_integral_atom_sum _ _ (data p).query_measurable
    (data p).domain_measurable (data p).density_integrable]
  apply Finset.sum_congr rfl
  intro b _
  rw [atomDensity, integral_indicator (atomSet_measurable p b)]
  rfl

def queryApprox (p : Primitive) (b : FloorAtom) (n : ℕ) : Space p →ₛ ℝ :=
  SimpleFunc.approxOn (atomDensity p b) (atomDensity_measurable p b) univ 0 (mem_univ _) n

def queryError (p : Primitive) (b : FloorAtom) (n : ℕ) : ℝ :=
  ∫ x, ‖queryApprox p b n x - atomDensity p b x‖

theorem queryError_tendsto (p : Primitive) (b : FloorAtom) :
    Tendsto (queryError p b) atTop (𝓝 0) := by
  have hb (n : ℕ) (x : Space p) :
      ‖queryApprox p b n x - atomDensity p b x‖ ≤ ‖atomDensity p b x‖ := by
    have h := SimpleFunc.nnnorm_approxOn_le (atomDensity_measurable p b)
      (s := (univ : Set ℝ)) (y₀ := (0 : ℝ)) (mem_univ _) x n
    exact_mod_cast (by simpa [queryApprox] using h)
  have h := tendsto_integral_of_dominated_convergence
    (f := fun _ : Space p => (0 : ℝ))
    (fun x => ‖atomDensity p b x‖)
    (fun n => (((queryApprox p b n).measurable.sub
      (atomDensity_measurable p b)).norm).aestronglyMeasurable)
    (atomDensity_integrable p b).norm
    (fun n => Filter.Eventually.of_forall (fun x => by
      simpa only [norm_norm] using hb n x))
    (Filter.Eventually.of_forall (fun x => by
      have ht := SimpleFunc.tendsto_approxOn (atomDensity_measurable p b)
        (s := (univ : Set ℝ)) (y₀ := (0 : ℝ)) (mem_univ _)
        (x := x) (by simp)
      simpa [queryApprox] using (ht.sub tendsto_const_nhds).norm))
  simpa [queryError] using h

def atomNormMass (p : Primitive) (b : FloorAtom) : ℝ := ∫ x, ‖atomDensity p b x‖

theorem queryError_bounds (p : Primitive) (b : FloorAtom) (n : ℕ) :
    0 ≤ queryError p b n ∧ queryError p b n ≤ atomNormMass p b := by
  have hb (x : Space p) :
      ‖queryApprox p b n x - atomDensity p b x‖ ≤ ‖atomDensity p b x‖ := by
    have h := SimpleFunc.nnnorm_approxOn_le (atomDensity_measurable p b)
      (s := (univ : Set ℝ)) (y₀ := (0 : ℝ)) (mem_univ _) x n
    exact_mod_cast (by simpa [queryApprox] using h)
  have hi : Integrable (fun x => ‖queryApprox p b n x - atomDensity p b x‖) :=
    (atomDensity_integrable p b).norm.mono'
      (((queryApprox p b n).measurable.sub (atomDensity_measurable p b)).norm).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by simpa only [norm_norm] using hb x))
  exact ⟨integral_nonneg (fun _ => norm_nonneg _),
    integral_mono hi (atomDensity_integrable p b).norm hb⟩

/-- Zero-mass cells are paid absolutely.  This conclusion has no
division by the atom's mass and remains valid for every finite stage. -/
theorem queryError_zero_mass {p : Primitive} {b : FloorAtom}
    (hzero : atomNormMass p b = 0) (n : ℕ) : queryError p b n = 0 := by
  exact le_antisymm ((queryError_bounds p b n).2.trans_eq hzero)
    (queryError_bounds p b n).1

/-- A zero value remains exactly zero in every approximant.  In
particular no division by a cell mass occurs at any stage. -/
theorem queryApprox_zero {p : Primitive} {b : FloorAtom} {x : Space p}
    (hx : atomDensity p b x = 0) (n : ℕ) : queryApprox p b n x = 0 := by
  have h := SimpleFunc.nnnorm_approxOn_le (atomDensity_measurable p b)
    (s := (univ : Set ℝ)) (y₀ := (0 : ℝ)) (mem_univ _) x n
  simpa [queryApprox, hx] using h

/-- The puncture is essential: an identical branch or the max-two
clamp belongs to the equality stratum and is NEVER discarded. -/
def puncturedTube {X : Type*} (f : X → ℝ) (n : ℕ) : Set X :=
  {x | 0 < |f x| ∧ |f x| ≤ 1 / ((n : ℝ) + 1)}

theorem puncturedTube_measurable {X : Type*} [MeasurableSpace X]
    {f : X → ℝ} (hf : Measurable f) (n : ℕ) : MeasurableSet (puncturedTube f n) :=
  (measurableSet_lt measurable_const hf.abs).inter
    (measurableSet_le hf.abs measurable_const)

theorem puncturedTube_eventually_absent {X : Type*} (f : X → ℝ) (x : X) :
    ∀ᶠ n : ℕ in atTop, x ∉ puncturedTube f n := by
  by_cases hx : f x = 0
  · exact Filter.Eventually.of_forall (fun n => by simp [puncturedTube, hx])
  · have hp : 0 < |f x| := abs_pos.mpr hx
    filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (eventually_lt_nhds hp)] with n hn
    exact fun h => (not_lt_of_ge h.2) hn

def queryWall (p : Primitive) (j : Fin 201) (x : Space p) : ℝ :=
  (data p).query x - floorGrid j.val

def wallError (p : Primitive) (b : FloorAtom) (j : Fin 201) (n : ℕ) : ℝ :=
  ∫ x, (puncturedTube (queryWall p j) n).indicator
    (fun x => ‖atomDensity p b x‖) x

theorem wallError_tendsto (p : Primitive) (b : FloorAtom) (j : Fin 201) :
    Tendsto (wallError p b j) atTop (𝓝 0) := by
  have hm (n : ℕ) := puncturedTube_measurable
    ((data p).query_measurable.sub measurable_const) n
  have h := tendsto_integral_of_dominated_convergence
    (f := fun _ : Space p => (0 : ℝ))
    (fun x => ‖atomDensity p b x‖)
    (fun n => ((atomDensity_measurable p b).norm.indicator (hm n)).aestronglyMeasurable)
    (atomDensity_integrable p b).norm
    (fun n => Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ puncturedTube (queryWall p j) n
      · simp [indicator_of_mem hx]
      · simp [indicator_of_notMem hx]))
    (Filter.Eventually.of_forall (fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [puncturedTube_eventually_absent (queryWall p j) x] with n hn
      simp [indicator_of_notMem hn]))
  simpa [wallError] using h

/-- Actual all-action/all-root finite query set; the 441 generation
labels are separate occurrences, not summed alternatives. -/
abbrev QueryIndex := Fin 441 × Primitive × FloorAtom
abbrev WallIndex := QueryIndex × Fin 201

theorem exists_one_absolute_query_stage {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ n : ℕ,
      (∀ q : QueryIndex, queryError q.2.1 q.2.2 n < epsilon) ∧
      (∀ w : WallIndex, wallError w.1.2.1 w.1.2.2 w.2 n < epsilon) := by
  have hq : ∀ q : QueryIndex, ∀ᶠ n : ℕ in atTop,
      queryError q.2.1 q.2.2 n < epsilon := fun q =>
    (queryError_tendsto q.2.1 q.2.2).eventually (eventually_lt_nhds he)
  have hw : ∀ w : WallIndex, ∀ᶠ n : ℕ in atTop,
      wallError w.1.2.1 w.1.2.2 w.2 n < epsilon := fun w =>
    (wallError_tendsto w.1.2.1 w.1.2.2 w.2).eventually (eventually_lt_nhds he)
  exact ((Filter.eventually_all.mpr hq).and (Filter.eventually_all.mpr hw)).exists

instance approxRangeFintype (p : Primitive) (b : FloorAtom) (n : ℕ) :
    Fintype (Set.range (queryApprox p b n)) := (queryApprox p b n).finite_range.fintype

/-- All earlier simple partitions and all exact atom decisions are
remembered.  Consequently this is one nested refinement, not separately
chosen partitions whose intersections have not been accounted for. -/
abbrev CommonCode (p : Primitive) (n : ℕ) :=
  ((k : Fin (n + 1)) → (b : FloorAtom) → Set.range (queryApprox p b k.val)) ×
    (FloorAtom → Bool)

def commonCode (p : Primitive) (n : ℕ) (x : Space p) : CommonCode p n :=
  ⟨fun k b => ⟨queryApprox p b k.val x, ⟨x, rfl⟩⟩,
    fun b => decide (x ∈ atomSet p b)⟩

def commonCell (p : Primitive) (n : ℕ) (c : CommonCode p n) : Set (Space p) :=
  {x | commonCode p n x = c}

theorem commonCode_finite (p : Primitive) (n : ℕ) :
    (Set.range (commonCode p n)).Finite := Set.finite_range _

theorem commonCell_covers (p : Primitive) (n : ℕ) (x : Space p) :
    x ∈ commonCell p n (commonCode p n x) := rfl

theorem commonCell_disjoint {p : Primitive} {n : ℕ} {c d : CommonCode p n}
    (h : c ≠ d) : Disjoint (commonCell p n c) (commonCell p n d) := by
  apply Set.disjoint_left.mpr
  intro x hc hd
  exact h (hc.symm.trans hd)

def restrictCode (p : Primitive) {m n : ℕ} (h : m ≤ n)
    (c : CommonCode p n) : CommonCode p m :=
  ⟨fun k b => c.1 ⟨k.val, lt_of_lt_of_le k.isLt (Nat.succ_le_succ h)⟩ b, c.2⟩

theorem commonCell_refines (p : Primitive) {m n : ℕ} (h : m ≤ n)
    (c : CommonCode p n) : commonCell p n c ⊆ commonCell p m (restrictCode p h c) := by
  intro x hx
  change commonCode p m x = restrictCode p h c
  rw [← hx]
  rfl

theorem commonCell_query_exact {p : Primitive} {n : ℕ} {c : CommonCode p n}
    {x y : Space p} (hx : x ∈ commonCell p n c) (hy : y ∈ commonCell p n c)
    (b : FloorAtom) : (x ∈ atomSet p b ↔ y ∈ atomSet p b) := by
  have h := congrFun (congrArg Prod.snd (hx.trans hy.symm)) b
  simpa [commonCode] using h

theorem commonCell_approx_constant {p : Primitive} {n : ℕ} {c : CommonCode p n}
    {x y : Space p} (hx : x ∈ commonCell p n c) (hy : y ∈ commonCell p n c)
    (b : FloorAtom) : queryApprox p b n x = queryApprox p b n y := by
  have h := congrFun (congrFun (congrArg Prod.fst (hx.trans hy.symm)) ⟨n, by omega⟩) b
  exact congrArg Subtype.val h

/-- Concrete local accuracy is selected inside the actual root reserve.
This is a query-approximation theorem, not an assertion that the source
action bases already have a signed AP/table licence. -/
theorem exists_common_stage_inside_root_reserve {reserve : ℝ} (hr : 0 < reserve) :
    ∃ delta : ℝ, 0 < delta ∧
      (7 / 2 : ℝ) * (delta * (((12 : ℝ)^441 - 1) / 11)) < reserve ∧
      ∃ n : ℕ,
        (∀ q : QueryIndex, queryError q.2.1 q.2.2 n < delta) ∧
        (∀ w : WallIndex, wallError w.1.2.1 w.1.2.2 w.2 n < delta) := by
  obtain ⟨delta, hd, _, hbudget⟩ :=
    P5RenewalFiniteError.exists_local_reserve reserve 1 hr (by norm_num)
  exact ⟨delta, hd, hbudget, exists_one_absolute_query_stage hd⟩

end
end ImbalancedChen.Part5OriginalH430AbsoluteQueries
