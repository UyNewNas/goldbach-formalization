/-!
SOURCE ONLY / UNCOMPILED.

A fixed complete axis-cut cover of the literal original compact third region.
The existing ClosedCutTree and its closed-face integral aggregation are reused.
This file constructs the tree and its rational bounding boxes together, proves
their pairing, full coverage including every boundary, and automatic positivity
of all coordinate floors. No arbitrary complete-tree or leaf-containment input
is left in the final certificate consumer. Only actual rational node/denominator
guard checks and the final finite numerical total remain to be supplied.

The depth12 construction has4096 leaves and cycles x,y,z. It is data source,
not a runtime replay; this task has not expanded or executed the tree.
-/
import ImbalancedChen.P2ThirdCompactCertifiedBoxIntegral

set_option Elab.async false

namespace ImbalancedChen.P2ThirdCompactUniformCover

noncomputable section
open Set MeasureTheory
open P2ThirdCompactCertifiedBoxIntegral

abbrev Point := Fin 3 → ℝ
abbrev Tree := OriginalThirdCompactPartitionSourceOnly.ClosedCutTree

/-- Exactly the original physical coordinate denominator. -/
def scale : ℤ := 805306368000

theorem scale_pos : (0 : ℝ) < (scale : ℝ) := by norm_num [scale]

theorem scale_eq_original : (scale : ℝ) =
    OriginalThirdCompactPartitionSourceOnly.coordinateDenominator := by
  norm_num [scale, OriginalThirdCompactPartitionSourceOnly.coordinateDenominator]

def normalizedPoint (a : Fin 3 → ℤ) : Point := fun i => (a i : ℝ) / (scale : ℝ)
def rationalPoint (a : Fin 3 → ℤ) : Fin 3 → ℚ := fun i => (a i : ℚ) / (scale : ℚ)

theorem realPoint_rationalPoint (a : Fin 3 → ℤ) :
    P2ThirdCompactCertifiedBoxIntegral.realPoint (rationalPoint a) = normalizedPoint a := by
  funext i
  simp only [P2ThirdCompactCertifiedBoxIntegral.realPoint, rationalPoint,
    normalizedPoint, Rat.cast_div, Rat.cast_intCast]

structure IntBox where
  lo : Fin 3 → ℤ
  hi : Fin 3 → ℤ

def IntBox.box (b : IntBox) : Set Point := Icc (normalizedPoint b.lo) (normalizedPoint b.hi)
def rootLow : ℤ := 480 * 2^24
def rootHigh : ℤ := 9500 * 2^24
def rootBox : IntBox := ⟨fun _ => rootLow, fun _ => rootHigh⟩

def IntBox.Bounded (b : IntBox) : Prop :=
  ∀ i, rootLow ≤ b.lo i ∧ b.lo i ≤ b.hi i ∧ b.hi i ≤ rootHigh

theorem rootBox_bounded : rootBox.Bounded := by
  intro i
  exact ⟨le_rfl, by norm_num [rootBox, rootLow, rootHigh], le_rfl⟩

theorem rootLow_value : (rootLow : ℝ) / (scale : ℝ) = 1 / 100 := by
  norm_num [rootLow, scale]

theorem rootHigh_value : (rootHigh : ℝ) / (scale : ℝ) = thirdPrefixRho := by
  norm_num [rootHigh, scale, thirdPrefixRho]

/-- All three coordinates of the actual compact ordered domain lie in the
root box. The proof includes z=1/100, x=rho, ordering walls and cube face. -/
theorem compactRegion_subset_rootBox :
    OriginalThirdCompactPartitionSourceOnly.compactRegion ⊆ rootBox.box := by
  intro t ht
  rcases ht with ⟨⟨⟨hz, _hzrho, hzy, hyx, hxrho⟩, _hcube⟩, hcut⟩
  constructor
  · intro i
    change (rootLow : ℝ) / (scale : ℝ) ≤ t i
    rw [rootLow_value]
    fin_cases i
    · exact hcut.trans (hzy.trans hyx)
    · exact hcut.trans hzy
    · exact hcut
  · intro i
    change t i ≤ (rootHigh : ℝ) / (scale : ℝ)
    rw [rootHigh_value]
    fin_cases i
    · exact hxrho
    · exact hyx.trans hxrho
    · exact hzy.trans (hyx.trans hxrho)

def axis (step : ℕ) : Fin 3 := ⟨step % 3, Nat.mod_lt _ (by norm_num)⟩
def IntBox.midpoint (b : IntBox) (j : Fin 3) : ℤ := (b.lo j + b.hi j) / 2

def IntBox.left (b : IntBox) (j : Fin 3) : IntBox :=
  ⟨b.lo, Function.update b.hi j (b.midpoint j)⟩

def IntBox.right (b : IntBox) (j : Fin 3) : IntBox :=
  ⟨Function.update b.lo j (b.midpoint j), b.hi⟩

theorem midpoint_bounds {b : IntBox} (hb : b.Bounded) (j : Fin 3) :
    b.lo j ≤ b.midpoint j ∧ b.midpoint j ≤ b.hi j := by
  have h := (hb j).2.1
  unfold IntBox.midpoint
  omega

theorem left_bounded {b : IntBox} (hb : b.Bounded) (j : Fin 3) :
    (b.left j).Bounded := by
  intro i
  by_cases hij : i = j
  · subst i
    have hm := midpoint_bounds hb j
    simpa only [IntBox.left, Function.update_self] using
      (show rootLow ≤ b.lo j ∧ b.lo j ≤ b.midpoint j ∧ b.midpoint j ≤ rootHigh
        from ⟨(hb j).1, hm.1, hm.2.trans (hb j).2.2⟩)
  · simpa only [IntBox.left, Function.update_of_ne hij] using hb i

theorem right_bounded {b : IntBox} (hb : b.Bounded) (j : Fin 3) :
    (b.right j).Bounded := by
  intro i
  by_cases hij : i = j
  · subst i
    have hm := midpoint_bounds hb j
    simpa only [IntBox.right, Function.update_self] using
      (show rootLow ≤ b.midpoint j ∧ b.midpoint j ≤ b.hi j ∧ b.hi j ≤ rootHigh
        from ⟨(hb j).1.trans hm.1, hm.2, (hb j).2.2⟩)
  · simpa only [IntBox.right, Function.update_of_ne hij] using hb i

/-- The metadata update uses the same physical cut as ClosedCutTree.split. -/
theorem subset_left_box {s : Set Point} {b : IntBox} (hs : s ⊆ b.box) (j : Fin 3) :
    s ∩ {t : Point | t j ≤ (b.midpoint j : ℝ) /
      OriginalThirdCompactPartitionSourceOnly.coordinateDenominator} ⊆ (b.left j).box := by
  intro t ht
  have hroot := hs ht.1
  constructor
  · exact hroot.1
  · intro i
    by_cases hij : i = j
    · subst i
      simpa only [IntBox.left, normalizedPoint, Function.update_self,
        scale_eq_original] using ht.2
    · simpa only [IntBox.left, normalizedPoint, Function.update_of_ne hij] using hroot.2 i

theorem subset_right_box {s : Set Point} {b : IntBox} (hs : s ⊆ b.box) (j : Fin 3) :
    s ∩ {t : Point | (b.midpoint j : ℝ) /
      OriginalThirdCompactPartitionSourceOnly.coordinateDenominator ≤ t j} ⊆ (b.right j).box := by
  intro t ht
  have hroot := hs ht.1
  constructor
  · intro i
    by_cases hij : i = j
    · subst i
      simpa only [IntBox.right, normalizedPoint, Function.update_self,
        scale_eq_original] using ht.2
    · simpa only [IntBox.right, normalizedPoint, Function.update_of_ne hij] using hroot.1 i
  · exact hroot.2

/-- Balanced finite axis-cut generator. Every cut is an original-denominator
integer; no rational cut is rounded outside the existing tree semantics. -/
def axisTree : ℕ → ℕ → IntBox → Tree
  | 0, _, _ => .leaf
  | n+1, step, b => .split (axis step) (b.midpoint (axis step))
      (axisTree n (step+1) (b.left (axis step)))
      (axisTree n (step+1) (b.right (axis step)))

def axisBoxes : ℕ → ℕ → IntBox → List IntBox
  | 0, _, b => [b]
  | n+1, step, b =>
      axisBoxes n (step+1) (b.left (axis step)) ++
      axisBoxes n (step+1) (b.right (axis step))

/-- Every actual clipped leaf is paired with its own computable enclosing
box. The metadata list and actual closed-child list have exactly the same order. -/
theorem axisTree_containment (n step : ℕ) (b : IntBox) {s : Set Point}
    (hs : s ⊆ b.box) :
    List.Forall₂ (fun (leaf : Set Point) (box : IntBox) => leaf ⊆ box.box)
      (OriginalThirdCompactPartitionSourceOnly.closedLeaves (axisTree n step b) s)
      (axisBoxes n step b) := by
  induction n generalizing step b s with
  | zero =>
      exact List.Forall₂.cons hs List.Forall₂.nil
  | succ n ih =>
      change List.Forall₂ (fun (leaf : Set Point) (box : IntBox) => leaf ⊆ box.box)
        (OriginalThirdCompactPartitionSourceOnly.closedLeaves
          (axisTree n (step+1) (b.left (axis step)))
          (s ∩ {t : Point | t (axis step) ≤ (b.midpoint (axis step) : ℝ) /
            OriginalThirdCompactPartitionSourceOnly.coordinateDenominator}) ++
         OriginalThirdCompactPartitionSourceOnly.closedLeaves
          (axisTree n (step+1) (b.right (axis step)))
          (s ∩ {t : Point | (b.midpoint (axis step) : ℝ) /
            OriginalThirdCompactPartitionSourceOnly.coordinateDenominator ≤ t (axis step)}))
        (axisBoxes n (step+1) (b.left (axis step)) ++
          axisBoxes n (step+1) (b.right (axis step)))
      exact List.rel_append (ih _ _ (subset_left_box hs _))
        (ih _ _ (subset_right_box hs _))

theorem axisBoxes_bounded (n step : ℕ) {b : IntBox} (hb : b.Bounded) :
    ∀ box ∈ axisBoxes n step b, box.Bounded := by
  induction n generalizing step b with
  | zero =>
      intro box hbox
      have heq : box = b := List.mem_singleton.mp hbox
      simpa only [heq] using hb
  | succ n ih =>
      intro box hbox
      change box ∈ axisBoxes n (step+1) (b.left (axis step)) ++
        axisBoxes n (step+1) (b.right (axis step)) at hbox
      rcases List.mem_append.mp hbox with hl | hr
      · exact ih _ (left_bounded hb _) box hl
      · exact ih _ (right_bounded hb _) box hr

theorem axisBoxes_length (n step : ℕ) (b : IntBox) :
    (axisBoxes n step b).length = 2^n := by
  induction n generalizing step b with
  | zero => rfl
  | succ n ih =>
      simp only [axisBoxes, List.length_append, ih, pow_succ]
      omega

/-- No compact point, including a point on a closed split wall, is omitted.
This uses the same existing tree leaf definition as the integral aggregator. -/
theorem closedLeaves_cover (tree : Tree) {s : Set Point} {t : Point} (ht : t ∈ s) :
    ∃ leaf ∈ OriginalThirdCompactPartitionSourceOnly.closedLeaves tree s, t ∈ leaf := by
  induction tree generalizing s with
  | leaf => exact ⟨s, by simp [OriginalThirdCompactPartitionSourceOnly.closedLeaves], ht⟩
  | split j m left right ihL ihR =>
      rcases le_total (t j)
        ((m : ℝ) / OriginalThirdCompactPartitionSourceOnly.coordinateDenominator) with hl | hr
      · obtain ⟨leaf, hmem, htleaf⟩ := ihL ⟨ht, hl⟩
        exact ⟨leaf, List.mem_append.mpr (Or.inl hmem), htleaf⟩
      · obtain ⟨leaf, hmem, htleaf⟩ := ihR ⟨ht, hr⟩
        exact ⟨leaf, List.mem_append.mpr (Or.inr hmem), htleaf⟩

/-- Fixed complete data source: four cuts per coordinate,4096 retained leaves. -/
def uniformDepth : ℕ := 12
def completeTree : Tree := axisTree uniformDepth 0 rootBox
def completeBoxes : List IntBox := axisBoxes uniformDepth 0 rootBox
def completeLeaves : List (Set Point) :=
  OriginalThirdCompactPartitionSourceOnly.closedLeaves completeTree
    OriginalThirdCompactPartitionSourceOnly.compactRegion

theorem completeBoxes_length : completeBoxes.length = 4096 := by
  rw [completeBoxes, axisBoxes_length]
  norm_num [uniformDepth]

theorem complete_containment :
    List.Forall₂ (fun (leaf : Set Point) (box : IntBox) => leaf ⊆ box.box)
      completeLeaves completeBoxes :=
  axisTree_containment uniformDepth 0 rootBox compactRegion_subset_rootBox

theorem completeLeaves_length : completeLeaves.length = 4096 :=
  complete_containment.length_eq.trans completeBoxes_length

/-- The same complete list, with all empty or nonpositive-cost children
retained, appears in the existing exact integral aggregation. -/
theorem originalCompact_eq_completeLeafSum :
    OriginalThirdFiniteReserveSourceOnly.originalCompactThirdCorrection =
      (completeLeaves.map (fun leaf => ∫ t in leaf,
        OriginalThirdCompactPartitionSourceOnly.compactKernel t)).sum :=
  OriginalThirdCompactPartitionSourceOnly.
    originalCompactThirdCorrection_eq_sum_closedLeaves completeTree

theorem complete_coverage {t : Point}
    (ht : t ∈ OriginalThirdCompactPartitionSourceOnly.compactRegion) :
    ∃ leaf ∈ completeLeaves, t ∈ leaf :=
  closedLeaves_cover completeTree ht

theorem completeBoxes_bounded : ∀ box ∈ completeBoxes, box.Bounded :=
  axisBoxes_bounded uniformDepth 0 rootBox_bounded

/-- Automatic cutoff and denominator positivity. This is a theorem for every
computed box, not an assumption about a positive subset of the original domain. -/
theorem completeBox_coordinate_guards {b : IntBox} (hb : b ∈ completeBoxes) (i : Fin 3) :
    (1 / 100 : ℚ) ≤ rationalPoint b.lo i ∧
      0 < rationalPoint b.lo i ∧ rationalPoint b.lo i ≤ rationalPoint b.hi i := by
  have h := completeBoxes_bounded b hb i
  have hd : (0 : ℚ) < (scale : ℚ) := by norm_num [scale]
  have hlo : (rootLow : ℚ) ≤ (b.lo i : ℚ) := by exact_mod_cast h.1
  have hle : (b.lo i : ℚ) ≤ (b.hi i : ℚ) := by exact_mod_cast h.2.1
  have hmin := div_le_div_of_nonneg_right hlo hd.le
  have hbound : (1 / 100 : ℚ) ≤ rationalPoint b.lo i := by
    simpa only [rationalPoint, show (rootLow : ℚ)/(scale : ℚ) = 1/100 by
      norm_num [rootLow, scale]] using hmin
  exact ⟨hbound, lt_of_lt_of_le (by norm_num) hbound,
    div_le_div_of_nonneg_right hle hd.le⟩

/-- Only query choices and a rational denominator floor are caller data;
all spatial coordinates are fixed by the already complete axis-cut generator. -/
def nodeGuard (b : IntBox) (oldNode newNode denominator : ℚ) (coarseOld : Bool) : BoxGuard where
  lo := rationalPoint b.lo
  hi := rationalPoint b.hi
  oldNode := oldNode
  newNode := newNode
  denominator := denominator
  coarseOld := coarseOld

theorem nodeGuard_box (b : IntBox) (oldNode newNode denominator : ℚ) (coarseOld : Bool) :
    (nodeGuard b oldNode newNode denominator coarseOld).box = b.box := by
  simp only [nodeGuard, BoxGuard.box, IntBox.box, realPoint_rationalPoint]

def completeCertificates (oldNode newNode denominator : IntBox → ℚ)
    (coarseOld : IntBox → Bool) : List BoxGuard :=
  completeBoxes.map (fun b => nodeGuard b (oldNode b) (newNode b) (denominator b) (coarseOld b))

/-- The caller no longer supplies an arbitrary tree, complete cover, positive
z hypothesis, or leaf/box containment. It supplies only the finite rational
node/denominator guard checks on the fixed complete list. -/
theorem fullIntegral_le_uniform_checked_boxes
    (oldNode newNode denominator : IntBox → ℚ) (coarseOld : IntBox → Bool)
    (hcheck : ∀ b ∈ completeBoxes,
      (nodeGuard b (oldNode b) (newNode b) (denominator b) (coarseOld b)).check = true) :
    actualExtendedThirdIdealFunctional ≤
      (((completeCertificates oldNode newNode denominator coarseOld).map BoxGuard.integralUpper).
        map (fun q : ℚ => (q : ℝ))).sum + OriginalThirdTailActualIdealSourceOnly.Tnew := by
  apply P2ThirdCompactCertifiedBoxIntegral.fullIntegral_le_checked_boxes completeTree
    (completeCertificates oldNode newNode denominator coarseOld)
  have hflip : List.Forall₂ (fun (box : IntBox) (leaf : Set Point) => leaf ⊆ box.box)
      completeBoxes completeLeaves :=
    List.Forall₂.flip complete_containment
  have hboth : List.Forall₂
      (fun (box : IntBox) (leaf : Set Point) =>
        (nodeGuard box (oldNode box) (newNode box) (denominator box) (coarseOld box)).check = true ∧
          leaf ⊆ box.box) completeBoxes completeLeaves :=
    (List.forall₂_and_left _ _).2 ⟨hcheck, hflip⟩
  have hnormal : List.Forall₂
      (fun (leaf : Set Point) (box : IntBox) =>
        (nodeGuard box (oldNode box) (newNode box) (denominator box) (coarseOld box)).check = true ∧
          leaf ⊆ box.box) completeLeaves completeBoxes := List.Forall₂.flip hboth
  change List.Forall₂ _ completeLeaves (completeBoxes.map _)
  rw [List.forall₂_map_right_iff]
  exact hnormal.imp fun leaf box h =>
    ⟨h.1, by simpa only [nodeGuard_box] using h.2⟩

end
end ImbalancedChen.P2ThirdCompactUniformCover

