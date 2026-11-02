import ImbalancedChen.Part5OriginalH430FrozenRootRefinement

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual finite affine gate walls, together with all201 query knots, for
the original106 actions and U3/U4 roots.  Identically-zero wall functions
are retained.  Punctured wall losses tend to zero in absolute integral
units; no positive-mass normalization or wall-nullity premise is used.
-/

namespace ImbalancedChen.Part5OriginalH430GeometricWalls

noncomputable section
open Set MeasureTheory Filter Topology
open scoped BigOperators Classical
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open Part5UpperTables Part5UpperTables.OriginalU34
open Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430AbsoluteQueries

/-- All original gate equations are present.  Additional harmless walls
only refine the partition.  Zero padding means a retained identity stratum.
For D7/D8 the query is still the moving quotient, handled by queryWall. -/
def geometricWall : (p : Primitive) → Fin 12 → Space p → ℝ
  | .w1 i j, k, u =>
      ![u - 1 / W1Anchor j, 1 / W1Target i - u, u, 1 - u,
        1 - 2*u, 0, 0, 0, 0, 0, 0, 0] k
  | .w2Singleton j _, k, u =>
      ![u - a0 (originalW2At j), b (originalW2At j) - u,
        a1 (originalW2At j) - u, a2 (originalW2At j) - u,
        a3 (originalW2At j) - u, u, 1 - u, 1 - 2*u, 0, 0, 0, 0] k
  | .w2Pair j _, k, x =>
      ![x 0 - a0 (originalW2At j), x 1 - x 0,
        a1 (originalW2At j) - x 0, a2 (originalW2At j) - x 0,
        a3 (originalW2At j) - x 0, a1 (originalW2At j) - x 1,
        a2 (originalW2At j) - x 1, a3 (originalW2At j) - x 1,
        1 - 2*x 1, 1 - x 1 - 2*x 0, x 0, 1 - x 0 - x 1] k
  | .buchstabUpper i, k, w =>
      ![w - max 2 (upperStart i - 1), 5 - w, w, w - 1,
        0, 0, 0, 0, 0, 0, 0, 0] k
  | .buchstabLower i, k, w =>
      ![w - (lowerStart i - 1), 5 - w, w, w - 1,
        0, 0, 0, 0, 0, 0, 0, 0] k
  | .U3main, k, t =>
      ![t - a, tailCutoff - t, t, mainResidual t,
        VariableEnvelope.A t - VariableEnvelope.C t,
        mainResidual t - 2*a, 1/3-t, 0, 0, 0, 0, 0] k
  | .U3tail, k, t =>
      ![t - tailCutoff, 1/3-t, t, tailResidual t,
        tailResidual t - 2*a, t - clampStart, 0, 0, 0, 0, 0, 0] k
  | .U4, k, t =>
      ![t - a, 59/250-t, t, mainResidual t,
        VariableEnvelope.A t - VariableEnvelope.C t,
        mainResidual t - 2*a, 0, 0, 0, 0, 0, 0] k

theorem geometricWall_measurable (p : Primitive) (j : Fin 12) :
    Measurable (geometricWall p j) := by
  cases p <;> fin_cases j <;>
    dsimp [geometricWall, mainResidual, tailResidual,
      VariableEnvelope.v, VariableEnvelope.A, VariableEnvelope.C] <;> fun_prop

abbrev Wall := Fin 12 ⊕ Fin 201
def wall (p : Primitive) : Wall → Space p → ℝ
  | .inl j => geometricWall p j
  | .inr j => queryWall p j

theorem wall_measurable (p : Primitive) (j : Wall) : Measurable (wall p j) := by
  cases j with
  | inl j => exact geometricWall_measurable p j
  | inr j => exact (data p).query_measurable.sub measurable_const

def absoluteWallError (p : Primitive) (b : FloorAtom) (j : Wall) (n : ℕ) : ℝ :=
  ∫ x, (puncturedTube (wall p j) n).indicator (fun x => ‖atomDensity p b x‖) x

theorem absoluteWallError_tendsto (p : Primitive) (b : FloorAtom) (j : Wall) :
    Tendsto (absoluteWallError p b j) atTop (𝓝 0) := by
  have hm (n : ℕ) := puncturedTube_measurable (wall_measurable p j) n
  have h := tendsto_integral_of_dominated_convergence
    (f := fun _ : Space p => (0 : ℝ))
    (fun x => ‖atomDensity p b x‖)
    (fun n => ((atomDensity_measurable p b).norm.indicator (hm n)).aestronglyMeasurable)
    (atomDensity_integrable p b).norm
    (fun n => Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ puncturedTube (wall p j) n
      · simp [indicator_of_mem hx]
      · simp [indicator_of_notMem hx]))
    (Filter.Eventually.of_forall (fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [puncturedTube_eventually_absent (wall p j) x] with n hn
      simp [indicator_of_notMem hn]))
  simpa [absoluteWallError] using h

inductive Sign where
  | negative | zero | positive
  deriving DecidableEq, Fintype

def sign (v : ℝ) : Sign := if v < 0 then .negative else if v = 0 then .zero else .positive

theorem sign_zero_iff (v : ℝ) : sign v = .zero ↔ v = 0 := by
  unfold sign
  split_ifs <;> simp_all

abbrev FullCode (p : Primitive) (n : ℕ) := CommonCode p n ×
  (Wall → Sign) × ((j : Fin (n+1)) → Wall → Bool)

def fullCode (p : Primitive) (n : ℕ) (x : Space p) : FullCode p n :=
  ⟨commonCode p n x, fun j => sign (wall p j x),
    fun m j => decide (x ∈ puncturedTube (wall p j) m.val)⟩

def fullCell (p : Primitive) (n : ℕ) (c : FullCode p n) : Set (Space p) :=
  {x | fullCode p n x = c}

theorem fullCode_finite (p : Primitive) (n : ℕ) :
    (Set.range (fullCode p n)).Finite := Set.finite_range _

def restrictFullCode (p : Primitive) {m n : ℕ} (h : m ≤ n)
    (c : FullCode p n) : FullCode p m :=
  ⟨restrictCode p h c.1, c.2.1,
    fun j => c.2.2 ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_succ h)⟩⟩

theorem fullCell_refines (p : Primitive) {m n : ℕ} (h : m ≤ n) (c : FullCode p n) :
    fullCell p n c ⊆ fullCell p m (restrictFullCode p h c) := by
  intro x hx
  change fullCode p m x = restrictFullCode p h c
  rw [← hx]
  rfl

theorem fullCell_covers (p : Primitive) (n : ℕ) (x : Space p) :
    x ∈ fullCell p n (fullCode p n x) := rfl

theorem fullCell_keeps_equality {p : Primitive} {n : ℕ} {c : FullCode p n}
    {x y : Space p} (hx : x ∈ fullCell p n c) (hy : y ∈ fullCell p n c)
    (j : Wall) : wall p j x = 0 ↔ wall p j y = 0 := by
  have hs := congrFun (congrArg (fun z : FullCode p n => z.2.1) (hx.trans hy.symm)) j
  change sign (wall p j x) = sign (wall p j y) at hs
  rw [← sign_zero_iff, ← sign_zero_iff, hs]

abbrev AllWallIndex := QueryIndex × Wall

/-- All local errors are summed, not merely bounded separately by the
same reserve.  The finite indices include all441 generation occurrences. -/
def totalAbsoluteError (n : ℕ) : ℝ :=
  (∑ q : QueryIndex, queryError q.2.1 q.2.2 n) +
    ∑ w : AllWallIndex, absoluteWallError w.1.2.1 w.1.2.2 w.2 n

theorem totalAbsoluteError_tendsto : Tendsto totalAbsoluteError atTop (𝓝 0) := by
  have hq := tendsto_finset_sum (Finset.univ : Finset QueryIndex)
    (fun q _ => queryError_tendsto q.2.1 q.2.2)
  have hw := tendsto_finset_sum (Finset.univ : Finset AllWallIndex)
    (fun w _ => absoluteWallError_tendsto w.1.2.1 w.1.2.2 w.2)
  simpa [totalAbsoluteError] using hq.add hw

theorem exists_one_total_absolute_stage {reserve : ℝ} (hr : 0 < reserve) :
    ∃ delta : ℝ, 0 < delta ∧
      (7 / 2 : ℝ) * (delta * (((12 : ℝ)^441 - 1) / 11)) < reserve ∧
      ∃ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 11 / 384 ∧ totalAbsoluteError n < delta := by
  obtain ⟨delta, hd, _, hbudget⟩ :=
    P5RenewalFiniteError.exists_local_reserve reserve 1 hr (by norm_num)
  have herror := totalAbsoluteError_tendsto.eventually (eventually_lt_nhds hd)
  have hmesh : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ 11 / 384 :=
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 11 / 384))).mono (fun _ h => h.le)
  obtain ⟨n, hn⟩ := (hmesh.and herror).exists
  exact ⟨delta, hd, hbudget, n, hn⟩

/-- The common n is selected after delta and before N.  Every primitive,
query atom, proper wall, identity wall and generation label is finite.
The independent root Q mesh can be refined to the same cumulative n. -/
theorem exists_one_nested_absolute_stage {reserve : ℝ} (hr : 0 < reserve) :
    ∃ delta : ℝ, 0 < delta ∧
      (7 / 2 : ℝ) * (delta * (((12 : ℝ)^441 - 1) / 11)) < reserve ∧
      ∃ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 11 / 384 ∧
        (∀ q : QueryIndex, queryError q.2.1 q.2.2 n < delta) ∧
        (∀ w : AllWallIndex, absoluteWallError w.1.2.1 w.1.2.2 w.2 n < delta) := by
  obtain ⟨delta, hd, _, hbudget⟩ :=
    P5RenewalFiniteError.exists_local_reserve reserve 1 hr (by norm_num)
  have hq : ∀ q : QueryIndex, ∀ᶠ n : ℕ in atTop,
      queryError q.2.1 q.2.2 n < delta := fun q =>
    (queryError_tendsto q.2.1 q.2.2).eventually (eventually_lt_nhds hd)
  have hw : ∀ w : AllWallIndex, ∀ᶠ n : ℕ in atTop,
      absoluteWallError w.1.2.1 w.1.2.2 w.2 n < delta := fun w =>
    (absoluteWallError_tendsto w.1.2.1 w.1.2.2 w.2).eventually (eventually_lt_nhds hd)
  have hn : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ 11 / 384 :=
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 11 / 384))).mono
        (fun _ h => h.le)
  obtain ⟨n, hn, hq, hw⟩ :=
    (hn.and ((Filter.eventually_all.mpr hq).and (Filter.eventually_all.mpr hw))).exists
  exact ⟨delta, hd, hbudget, n, hn, hq, hw⟩

end
end ImbalancedChen.Part5OriginalH430GeometricWalls
