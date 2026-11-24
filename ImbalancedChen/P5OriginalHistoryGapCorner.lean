import ImbalancedChen.P5HistoricalHistoryTransportConsumers

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original Jensen/adaptive third-domain test has a common minimizing
corner. All eleven correlated gap planes decrease in the first three
coordinates, with common rates 1/2, 1/2, 5/2. This is stronger than a
separate lower bound for each plane. In particular, the exact original
integer thirdgap is 12800 times the real gap at the raw upper corner.

No assertion that every archived row passes the producer test is made.
The integer formulas are the eleven analytic planes, not archive data.
-/
namespace ImbalancedChen.P5OriginalHistoryGapCorner
noncomputable section
open Set
open scoped Classical BigOperators
open VariableEnvelope P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthCorrelatedRawBoxGates
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthTypedBaseGeometry
open P5HistoricalThirdTransportStripPayment

/-- Same five tents and W as the original third cap. The W position is
irrelevant to the maximum; the two planes within each tent stay paired. -/
def gapMerge {α : Type*} [LinearOrder α] (a : Fin 11 → α) : α :=
  max (min (a 0) (a 1))
    (max (min (a 2) (a 3)) (max (min (a 4) (a 5))
      (max (a 6) (max (min (a 7) (a 8)) (min (a 9) (a 10))))))

/-- Literal producer loop order: masks 1,3,7,5,6, followed by W. -/
theorem gapMerge_original_order {α : Type*} [LinearOrder α] (a : Fin 11 → α) :
    gapMerge a = max
      (max (max (max (max (min (a 0) (a 1)) (min (a 2) (a 3)))
        (min (a 4) (a 5))) (min (a 7) (a 8))) (min (a 9) (a 10))) (a 6) := by
  simp only [gapMerge, max_assoc, max_left_comm, max_comm]

theorem gapMerge_mono {α : Type*} [LinearOrder α]
    (a b : Fin 11 → α) (h : ∀ k, a k ≤ b k) : gapMerge a ≤ gapMerge b := by
  exact max_le_max (min_le_min (h 0) (h 1))
    (max_le_max (min_le_min (h 2) (h 3))
      (max_le_max (min_le_min (h 4) (h 5))
        (max_le_max (h 6)
          (max_le_max (min_le_min (h 7) (h 8)) (min_le_min (h 9) (h 10))))))

theorem gapMerge_add (a : Fin 11 → ℝ) (b : ℝ) :
    gapMerge (fun k => a k + b) = gapMerge a + b := by
  simp only [gapMerge, min_add_add_right, max_add_add_right]

theorem gapMerge_eval (t : Fin 5 → ℝ) :
    gapMerge (fun k => (historyGapPlane k).eval t) =
      six (t 0) (t 1) (t 2) - thirdCube t := by
  simp only [gapMerge, historyGapPlane_eval,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  simp only [six, v_eq_min, min_sub_sub_right, max_sub_sub_right]

def upperPoint (raw : FifthWireRow) : Fin 5 → ℝ := fun k => (raw.upper k : ℝ)

/-- Positive distance below the common worst corner, with the actual
minimum slopes of the eleven original gap planes. -/
def cornerEscape (t u : Fin 5 → ℝ) : ℝ :=
  (u 0 - t 0) / 2 + (u 1 - t 1) / 2 + 5 * (u 2 - t 2) / 2

theorem gap_plane_corner_escape (t u : Fin 5 → ℝ)
    (h0 : t 0 ≤ u 0) (h1 : t 1 ≤ u 1) (h2 : t 2 ≤ u 2) (k : Fin 11) :
    (historyGapPlane k).eval u + cornerEscape t u ≤ (historyGapPlane k).eval t := by
  fin_cases k <;>
    norm_num [historyGapPlane_eval, A, C, B, cap, thirdCube, cornerEscape] <;>
    linarith

/-- One quantitative monotonicity inequality for the TRUE maximum of
five tents and W. It includes switching winners and all ties. -/
theorem six_gap_corner_escape (t u : Fin 5 → ℝ)
    (h0 : t 0 ≤ u 0) (h1 : t 1 ≤ u 1) (h2 : t 2 ≤ u 2) :
    six (u 0) (u 1) (u 2) - thirdCube u + cornerEscape t u ≤
      six (t 0) (t 1) (t 2) - thirdCube t := by
  have hm := gapMerge_mono
    (fun k => (historyGapPlane k).eval u + cornerEscape t u)
    (fun k => (historyGapPlane k).eval t)
    (gap_plane_corner_escape t u h0 h1 h2)
  simpa only [gapMerge_add, gapMerge_eval] using hm

/-- This is precisely the correlated affbound test used by both original
producers, before multiplication by 32*grid. -/
def rawThirdGapQ (raw : FifthWireRow) : ℚ :=
  gapMerge (fun k => (historyGapPlane k).lower raw.lower raw.upper)

theorem gap_plane_lower_eq_upper (raw : FifthWireRow) (k : Fin 11) :
    ((historyGapPlane k).lower raw.lower raw.upper : ℝ) =
      (historyGapPlane k).eval (upperPoint raw) := by
  fin_cases k <;>
    norm_num [historyGapPlane, Affine5.lower, Affine5.eval, upperPoint,
      Fin.sum_univ_succ] <;> ring

/-- The max of individual plane minima loses NO correlation here:
every one of those minima is attained at this same upper corner. -/
theorem rawThirdGapQ_eq_upper_gap (raw : FifthWireRow) :
    (rawThirdGapQ raw : ℝ) =
      six (upperPoint raw 0) (upperPoint raw 1) (upperPoint raw 2) -
        thirdCube (upperPoint raw) := by
  calc
    (rawThirdGapQ raw : ℝ) =
        gapMerge (fun k => ((historyGapPlane k).lower raw.lower raw.upper : ℝ)) := by
      simp only [rawThirdGapQ, gapMerge, Rat.cast_max, Rat.cast_min]
    _ = gapMerge (fun k => (historyGapPlane k).eval (upperPoint raw)) := by
      congr 1
      funext k
      exact gap_plane_lower_eq_upper raw k
    _ = _ := gapMerge_eval _

theorem rawThirdGapQ_le_point_gap (raw : FifthWireRow) (t : Fin 5 → ℝ)
    (ht : t ∈ rawClosedBox raw) :
    (rawThirdGapQ raw : ℝ) + cornerEscape t (upperPoint raw) ≤
      six (t 0) (t 1) (t 2) - thirdCube t := by
  rw [rawThirdGapQ_eq_upper_gap]
  exact six_gap_corner_escape t (upperPoint raw) (ht 0).2 (ht 1).2 (ht 2).2

/-- The correlated minimum is attained at one genuine closed-box point,
not a formal choice of mutually incompatible branchwise corners. -/
theorem rawThirdGapQ_attained_minimum (raw : FifthWireRow) (hg : 0 < raw.grid) :
    (∀ t ∈ rawClosedBox raw, (rawThirdGapQ raw : ℝ) ≤
      six (t 0) (t 1) (t 2) - thirdCube t) ∧
    upperPoint raw ∈ rawClosedBox raw ∧
    (rawThirdGapQ raw : ℝ) =
      six (upperPoint raw 0) (upperPoint raw 1) (upperPoint raw 2) -
        thirdCube (upperPoint raw) := by
  refine ⟨?_, ?_, rawThirdGapQ_eq_upper_gap raw⟩
  · intro t ht
    have hm := rawThirdGapQ_le_point_gap raw t ht
    have h0 := (ht 0).2
    have h1 := (ht 1).2
    have h2 := (ht 2).2
    change t 0 ≤ upperPoint raw 0 at h0
    change t 1 ≤ upperPoint raw 1 at h1
    change t 2 ≤ upperPoint raw 2 at h2
    dsimp only [cornerEscape] at hm
    linarith
  · intro k
    exact ⟨by exact_mod_cast raw_endpoints_ordered raw hg k, le_rfl⟩

/-- Strictness comes from the genuine half-open source box. A zero
corner gap is harmless inside that box; no open equality region is cut. -/
theorem rawThirdGapQ_lt_point_gap (raw : FifthWireRow) (t : Fin 5 → ℝ)
    (ht : t ∈ raw.originalBox) :
    (rawThirdGapQ raw : ℝ) < six (t 0) (t 1) (t 2) - thirdCube t := by
  have hclosed : t ∈ rawClosedBox raw := fun k => ⟨(ht k).1, (ht k).2.le⟩
  have he := rawThirdGapQ_le_point_gap raw t hclosed
  have h0 := (ht 0).2
  have h1 := (ht 1).2
  have h2 := (ht 2).2
  change t 0 < upperPoint raw 0 at h0
  change t 1 < upperPoint raw 1 at h1
  change t 2 < upperPoint raw 2 at h2
  dsimp only [cornerEscape] at he
  linarith

/-- Original adjacent integer-key test lo[j] >= hi[j+1]. This is
independent of mask, saved Jensen statistics, support gates and mesh. -/
def rawKeyOrdered (raw : FifthWireRow) : Prop :=
  ∀ j : Fin 4, raw.lo j.succ + 1 ≤ raw.lo j.castSucc

theorem rawKeyOrdered_strictAnti (raw : FifthWireRow) (hg : 0 < raw.grid)
    (ho : rawKeyOrdered raw) (t : Fin 5 → ℝ) (ht : t ∈ raw.originalBox) :
    StrictAnti t := by
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro j
  have hgR : (0 : ℝ) < raw.grid := by exact_mod_cast hg
  have hk : (raw.lo j.succ : ℝ) + 1 ≤ (raw.lo j.castSucc : ℝ) := by
    exact_mod_cast ho j
  have hcut : (raw.upper j.succ : ℝ) ≤ (raw.lower j.castSucc : ℝ) := by
    simp only [FifthWireRow.upper, FifthWireRow.lower, Rat.cast_div,
      Rat.cast_add, Rat.cast_intCast, Rat.cast_one]
    exact div_le_div_of_nonneg_right hk hgR.le
  exact ((ht j.succ).2.trans_le hcut).trans_le (ht j.castSucc).1

/-- Eleven closed INTEGER formulas from original affbound at grid400.
Coordinates 3 and 4 have zero coefficient; hi=lo+1 is never reordered. -/
def producerGapPlane400 (raw : FifthWireRow) : Fin 11 → ℤ :=
  let x := raw.lo 0 + 1
  let y := raw.lo 1 + 1
  let z := raw.lo 2 + 1
  ![6400 - 16*x - 32*y - 96*z,
    11400 - 80*x - 32*y - 96*z,
    6400 - 16*x - 16*y - 96*z,
    11400 - 80*x - 80*y - 96*z,
    6400 - 16*x - 16*y - 80*z,
    11400 - 80*x - 80*y - 144*z,
    7650 - 32*x - 32*y - 108*z,
    6400 - 16*x - 32*y - 80*z,
    11400 - 80*x - 32*y - 144*z,
    6400 - 32*x - 16*y - 80*z,
    11400 - 32*x - 80*y - 144*z]

def producerThirdGap400 (raw : FifthWireRow) : ℤ := gapMerge (producerGapPlane400 raw)

theorem producerGapPlane400_exact (raw : FifthWireRow) (hg : raw.grid = 400)
    (k : Fin 11) :
    (producerGapPlane400 raw k : ℝ) / 12800 =
      (historyGapPlane k).eval (upperPoint raw) := by
  fin_cases k <;>
    norm_num [producerGapPlane400, historyGapPlane_eval, upperPoint,
      FifthWireRow.upper, hg, A, C, B, cap, thirdCube] <;> ring

theorem producerThirdGap400_exact (raw : FifthWireRow) (hg : raw.grid = 400) :
    (producerThirdGap400 raw : ℝ) / 12800 = (rawThirdGapQ raw : ℝ) := by
  calc
    (producerThirdGap400 raw : ℝ) / 12800 =
        gapMerge (fun k => (producerGapPlane400 raw k : ℝ) / 12800) := by
      simp only [producerThirdGap400, gapMerge, Int.cast_max, Int.cast_min,
        min_div_div_right (by norm_num : (0 : ℝ) ≤ 12800),
        max_div_div_right (by norm_num : (0 : ℝ) ≤ 12800)]
    _ = gapMerge (fun k => (historyGapPlane k).eval (upperPoint raw)) := by
      congr 1
      funext k
      exact producerGapPlane400_exact raw hg k
    _ = (rawThirdGapQ raw : ℝ) :=
      (gapMerge_eval (upperPoint raw)).trans (rawThirdGapQ_eq_upper_gap raw).symm

/-- The original producer initializes its running maximum with -10^9.
That sentinel cannot create or destroy a positive admission. -/
theorem original_sentinel_positive_iff (raw : FifthWireRow) :
    (0 : ℤ) < max (-1000000000) (producerThirdGap400 raw) ↔
      0 < producerThirdGap400 raw := by
  rw [lt_max_iff]
  norm_num

/-- Positive original integer thirdgap has a UNIFORM source margin,
independent of archive cardinality, later mesh, rough cutoff and N. -/
theorem producerThirdGap400_uniform_margin (raw : FifthWireRow)
    (hg : raw.grid = 400) (hp : 0 < producerThirdGap400 raw)
    (t : Fin 5 → ℝ) (ht : t ∈ raw.originalBox) :
    thirdCube t + (1 / 12800 : ℝ) < six (t 0) (t 1) (t 2) := by
  have hz : (1 : ℤ) ≤ producerThirdGap400 raw := by omega
  have hR : (1 : ℝ) ≤ producerThirdGap400 raw := by exact_mod_cast hz
  have he := producerThirdGap400_exact raw hg
  have hpoint := rawThirdGapQ_lt_point_gap raw t ht
  linarith

end
end ImbalancedChen.P5OriginalHistoryGapCorner
