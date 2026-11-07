import ImbalancedChen.Part5OriginalH430AbsoluteQueries

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

One cumulative finite partition of the VARYING original root level.
Its lower level is constant on each cell and is frozen through every
descendant.  The loss is at most 1/(n+1) in physical exponent units.
Structural max-two clamps survive the lowering exactly.

This supplies the previously missing literal common-Q choice.  It does
not assert a smooth prime-family approximation for the discontinuous
descendant queries; that arithmetic geometric realization remains OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430FrozenRootRefinement

noncomputable section
open Set Filter Topology
open P2PhysicalIncomingPrefixCells
open P2EnhancedLowerPhysicalNode P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalH430PhysicalRoots
open Part5UpperTables Part5UpperTables.OriginalU34
open Part5OriginalUpsilon5CausalDictionary (a floorValue)

def lowerEndpoint (n : ℕ) : CellCode n → ℝ
  | none => 1
  | some j => logPrimeMeshPoint 0 1 n j.val

def rawLower (n : ℕ) (nu : ℝ) : ℝ :=
  lowerEndpoint n (exponentCode 0 1 n nu)

theorem rawLower_bounds {nu : ℝ} (hnu : nu ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    rawLower n nu ≤ nu ∧ nu - rawLower n nu ≤ 1 / ((n : ℝ) + 1) := by
  have hm := exponentCode_membership (m := n) hnu
  cases hc : exponentCode 0 1 n nu with
  | none =>
      have he : nu = 1 := by simpa [hc, exponentCell] using hm
      subst nu
      constructor
      · simp [rawLower, hc, lowerEndpoint]
      · simp only [rawLower, hc, lowerEndpoint, sub_self]
        positivity
  | some j =>
      have hh : nu ∈ Ico (logPrimeMeshPoint 0 1 n j.val)
          (logPrimeMeshPoint 0 1 n (j.val + 1)) := by simpa [hc, exponentCell] using hm
      have hstep := logPrimeMeshPoint_succ (0 : ℝ) 1 n j.val
      constructor
      · simpa [rawLower, hc, lowerEndpoint] using hh.1
      · simp only [rawLower, hc, lowerEndpoint]
        rw [hstep] at hh
        simpa [logPrimeMeshStep, add_comm] using (sub_le_iff_le_add).mpr
          (by simpa only [add_comm] using hh.2.le)

/-- Retain every previous cut, so the frozen lower level is monotone
even though arbitrary meshes n+1 need not divide later meshes. -/
def frozenLevel : ℕ → ℝ → ℝ
  | 0, nu => rawLower 0 nu
  | n + 1, nu => max (frozenLevel n nu) (rawLower (n + 1) nu)

theorem frozenLevel_bounds {nu : ℝ} (hnu : nu ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    frozenLevel n nu ≤ nu ∧ nu - frozenLevel n nu ≤ 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => exact rawLower_bounds hnu 0
  | succ n ih =>
      have hr := rawLower_bounds hnu (n + 1)
      refine ⟨max_le ih.1 hr.1, ?_⟩
      have hl : rawLower (n + 1) nu ≤ frozenLevel (n + 1) nu := le_max_right _ _
      linarith only [hl, hr.2]

theorem frozenLevel_step (n : ℕ) (nu : ℝ) :
    frozenLevel n nu ≤ frozenLevel (n + 1) nu := le_max_left _ _

abbrev RootCode (n : ℕ) := (j : Fin (n + 1)) → CellCode j.val
def rootCode (n : ℕ) (nu : ℝ) : RootCode n := fun j => exponentCode 0 1 j.val nu
def rootCell (n : ℕ) (c : RootCode n) : Set ℝ := {nu | rootCode n nu = c}

theorem rootCode_finite (n : ℕ) : (Set.range (rootCode n)).Finite := Set.finite_range _

def restrictRootCode {m n : ℕ} (h : m ≤ n) (c : RootCode n) : RootCode m :=
  fun j => c ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_succ h)⟩

theorem rootCell_refines {m n : ℕ} (h : m ≤ n) (c : RootCode n) :
    rootCell n c ⊆ rootCell m (restrictRootCode h c) := by
  intro nu hn
  change rootCode m nu = restrictRootCode h c
  rw [← hn]
  rfl

theorem rootCell_covers (n : ℕ) (nu : ℝ) : nu ∈ rootCell n (rootCode n nu) := rfl

theorem frozenLevel_eq_of_code {n : ℕ} {nu mu : ℝ}
    (h : rootCode n nu = rootCode n mu) : frozenLevel n nu = frozenLevel n mu := by
  induction n with
  | zero =>
      have he := congrFun h ⟨0, by omega⟩
      exact congrArg (lowerEndpoint 0) he
  | succ n ih =>
      have hp : rootCode n nu = rootCode n mu := by
        ext j
        exact congrFun h ⟨j.val, by omega⟩
      have he := congrFun h ⟨n + 1, by omega⟩
      change max (frozenLevel n nu) (rawLower (n + 1) nu) =
        max (frozenLevel n mu) (rawLower (n + 1) mu)
      rw [ih hp]
      exact congrArg (max (frozenLevel n mu)) (congrArg (lowerEndpoint (n + 1)) he)

theorem root_total_bounds {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12) (ht : t ∈ rootBand k) :
    (sourceRoot k tau t).physical.total ∈ Icc (0 : ℝ) 1 := by
  have hr := sourceResidual_bounds htau htauhi ht
  have hc := rootBand_subset k ht
  have ht0 : 0 ≤ t := (by norm_num [a] : (0 : ℝ) ≤ a).trans hc.1
  change 0 ≤ t + sourceResidual k tau t ∧ t + sourceResidual k tau t ≤ 1
  constructor <;> linarith [hr.1, hr.2, hc.2]

def frozenRoot (n : ℕ) (k : Root) (tau t : ℝ) : TypedNode :=
  let nu := frozenLevel n (sourceRoot k tau t).physical.total
  { sourceRoot k tau t with physical :=
    { (sourceRoot k tau t).physical with total := nu,
      argument := max 2 ((nu - t) / a) } }

@[simp] theorem frozenRoot_residual (n : ℕ) (k : Root) (tau t : ℝ) :
    residual (frozenRoot n k tau t).physical =
      frozenLevel n (sourceRoot k tau t).physical.total - t := by
  simp [frozenRoot, residual, word, sourceRoot]

theorem frozenRoot_residual_bounds {n : ℕ} {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12) (ht : t ∈ rootBand k)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) :
    (11 / 384 : ℝ) ≤ residual (frozenRoot n k tau t).physical ∧
      residual (frozenRoot n k tau t).physical ≤ 1 / 2 := by
  have h := frozenLevel_bounds (root_total_bounds htau htauhi ht) n
  have hr := sourceResidual_bounds htau htauhi ht
  rw [frozenRoot_residual]
  change frozenLevel n (t + sourceResidual k tau t) ≤ t + sourceResidual k tau t ∧
    t + sourceResidual k tau t - frozenLevel n (t + sourceResidual k tau t) ≤
      1 / ((n : ℝ) + 1) at h
  constructor <;> linarith [h.1, h.2, hr.1, hr.2]

theorem frozenRoot_argument_bounds {n : ℕ} {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12) (ht : t ∈ rootBand k)
    (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384) :
    (frozenRoot n k tau t).physical.argument ∈ Icc (1 : ℝ) 6 := by
  have hr := frozenRoot_residual_bounds htau htauhi ht hn
  have ha : 0 < a := by norm_num [a]
  change 1 ≤ max 2 ((frozenLevel n (sourceRoot k tau t).physical.total - t) / a) ∧ _
  refine ⟨(by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _), max_le (by norm_num) ?_⟩
  apply (div_le_iff₀ ha).mpr
  rw [frozenRoot_residual] at hr
  dsimp [a] at *
  linarith [hr.2]

def frozenResidualFloor : ℝ := (11 / 384) / (101 : ℝ)^440
def frozenLeafCutoffFloor : ℝ := frozenResidualFloor / 6

theorem frozenLeafCutoffFloor_pos : 0 < frozenLeafCutoffFloor := by
  unfold frozenLeafCutoffFloor frozenResidualFloor
  positivity

/-- The common-Q freezing has paid its own loss BEFORE the 440 possible
transitions.  Every resulting leaf still has a fixed positive cutoff. -/
theorem frozen430_leaf_cutoff_floor {n : ℕ} {k : Root} {tau t lo hi : ℝ}
    {mesh depth : ℕ} (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12)
    (ht : t ∈ rootBand k) (hn : 1 / ((n : ℝ) + 1) ≤ 11 / 384)
    (hd : depth ≤ 440) {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (frozenRoot n k tau t) code z) :
    frozenLeafCutoffFloor ≤
      residual (realize depth (frozenRoot n k tau t) code z).physical /
        (realize depth (frozenRoot n k tau t) code z).physical.argument := by
  have hroot := frozenRoot_residual_bounds htau htauhi ht hn
  have hpow : 0 < (101 : ℝ)^depth := pow_pos (by norm_num) _
  have hp : (101 : ℝ)^depth ≤ (101 : ℝ)^440 :=
    pow_le_pow_right₀ (by norm_num) hd
  have hres : frozenResidualFloor ≤
      residual (realize depth (frozenRoot n k tau t) code z).physical := by
    calc
      frozenResidualFloor ≤ (11 / 384 : ℝ) / (101 : ℝ)^depth :=
        div_le_div_of_nonneg_left (by norm_num) hpow hp
      _ ≤ residual (frozenRoot n k tau t).physical / (101 : ℝ)^depth :=
        div_le_div_of_nonneg_right hroot.1 hpow.le
      _ ≤ _ := realize_residual_bound hz
  have hs := Part5OriginalH430PhysicalRoots.realize_argument_bounds
    (frozenRoot_argument_bounds htau htauhi ht hn) hz
  have hres0 : 0 ≤ residual (realize depth (frozenRoot n k tau t) code z).physical :=
    (by unfold frozenResidualFloor; positivity : 0 ≤ frozenResidualFloor).trans hres
  calc
    frozenLeafCutoffFloor ≤
        residual (realize depth (frozenRoot n k tau t) code z).physical / 6 :=
      div_le_div_of_nonneg_right hres (by norm_num)
    _ ≤ _ := div_le_div_of_nonneg_left hres0 (zero_lt_one.trans_le hs.1) hs.2

/-- For each common root cell, the value Q=N^nu is chosen once and
kept through all children, including each original W2 pair transition. -/
theorem descendants_share_frozen_Q (N n : ℕ) (k : Root) (tau t : ℝ)
    {mesh depth : ℕ} (code : Program mesh depth) (z : Coordinates depth) :
    (N : ℝ)^((realize depth (frozenRoot n k tau t) code z).physical.total) =
      (N : ℝ)^(frozenLevel n (sourceRoot k tau t).physical.total) := by
  rw [realize_total]
  rfl

theorem frozen_Q_constant_on_root_cell (N n : ℕ) {nu mu : ℝ} {c : RootCode n}
    (hnu : nu ∈ rootCell n c) (hmu : mu ∈ rootCell n c) :
    (N : ℝ)^(frozenLevel n nu) = (N : ℝ)^(frozenLevel n mu) := by
  rw [frozenLevel_eq_of_code (hnu.trans hmu.symm)]

/-- Lowering Q cannot un-clamp an actual upper root at two. -/
theorem frozenRoot_keeps_clamp {n : ℕ} {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1 / 12) (ht : t ∈ rootBand k)
    (hclamp : (sourceRoot k tau t).physical.argument = 2) :
    (frozenRoot n k tau t).physical.argument = 2 := by
  have hl := (frozenLevel_bounds (root_total_bounds htau htauhi ht) n).1
  have ha : 0 ≤ a := by norm_num [a]
  have hres : frozenLevel n (sourceRoot k tau t).physical.total - t ≤
      sourceResidual k tau t := by
    change frozenLevel n (t + sourceResidual k tau t) ≤ t + sourceResidual k tau t at hl
    linarith
  have hq := div_le_div_of_nonneg_right hres ha
  have hc : sourceResidual k tau t / a ≤ 2 :=
    (le_max_right 2 _).trans_eq hclamp
  exact max_eq_left (hq.trans hc)

theorem frozen_U3_clamp_lookup {n : ℕ} {t : ℝ}
    (ht : t ∈ rootBand .U3) (hc : clampStart ≤ t) :
    H430 ((frozenRoot n .U3 0 t).physical.argument) =
      min (floorValue H430Numerators 49) (floorValue H430Numerators 50) := by
  rw [frozenRoot_keeps_clamp (by norm_num) (by norm_num) ht (actual_U3_clamp hc).1]
  exact H430_two_eq_adjacent_min

/-- Uniform finite precision is fixed before N, and works for both
original root bands and every allowed finite U3 half-level reserve. -/
theorem exists_common_root_precision {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 11 / 384 ∧
      ∀ k tau t, 0 ≤ tau → tau ≤ 1 / 12 → t ∈ rootBand k →
        0 ≤ (sourceRoot k tau t).physical.total -
            (frozenRoot n k tau t).physical.total ∧
        (sourceRoot k tau t).physical.total -
            (frozenRoot n k tau t).physical.total < epsilon := by
  have hpos : 0 < min epsilon (11 / 384 : ℝ) := lt_min he (by norm_num)
  obtain ⟨n, hn⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (eventually_lt_nhds hpos)).exists
  refine ⟨n, (hn.trans_le (min_le_right _ _)).le, ?_⟩
  intro k tau t htau htauhi ht
  have hb := frozenLevel_bounds (root_total_bounds htau htauhi ht) n
  exact ⟨sub_nonneg.mpr hb.1, hb.2.trans_lt (hn.trans_le (min_le_left _ _))⟩

end
end ImbalancedChen.Part5OriginalH430FrozenRootRefinement
