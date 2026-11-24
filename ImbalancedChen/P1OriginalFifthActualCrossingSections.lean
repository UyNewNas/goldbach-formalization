import ImbalancedChen.P1OriginalFifthMovingMeshFiberBands
import ImbalancedChen.P1OriginalFifthGammaRateOwnerVolume
import Mathlib

/-!
Actual selected/firstStop moving-owner sections. SOURCE_ONLY / UNCOMPILED.
The section proof compares the two actual Ico mesh owners of two points;
no globally extended Gamma selector and no child-count factor is needed.
-/
namespace ImbalancedChen.P1OriginalFifthActualCrossingSections
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators ENNReal
open HistoricalThirdCoarse VariableEnvelope
open HistoricalThirdCoarse.P1OriginalCoarseFifth
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalCoarseFifthContinuation P1FifthUnitBoxGainDecomposition
open P1OriginalFifthActualOwnerGateCrossing
open P1OriginalThirdGammaFirstCoordinateRise
open P1OriginalThirdGammaMeshSectionBridge
open P1OriginalFifthGammaRateOwnerVolume
open P1OriginalFifthMovingMeshFubiniBridge
open P1OriginalFifthMovingMeshFiberBands

abbrev Point := Fin 5 → ℝ
abbrev Base := Fin 4 → ℝ

def splitEquiv : Point ≃ᵐ (ℝ × Base) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => ℝ) (0 : Fin 5)

def insertFirst (x : ℝ) (y : Base) : Point := splitEquiv.symm (x, y)

theorem insertFirst_zero (x : ℝ) (y : Base) : insertFirst x y 0 = x :=
  congrArg Prod.fst (splitEquiv.apply_symm_apply (x, y))

theorem insertFirst_rest (x : ℝ) (y : Base) (i : Fin 4) :
    insertFirst x y ((0 : Fin 5).succAbove i) = y i :=
  congrArg (fun p : ℝ × Base => p.2 i) (splitEquiv.apply_symm_apply (x, y))

def fiber (S : Set Point) (y : Base) : Set ℝ := {x | insertFirst x y ∈ S}

private theorem fixedBase_raw (raw : FifthWireRow) (m : ℕ) (j : Label5 m)
    {t : Point} (ht : t ∈ fixedOwnerBase raw m j) : t ∈ raw.originalBox := by
  simp only [fixedOwnerBase, mem_inter_iff] at ht
  tauto

private theorem fixedBase_mesh (raw : FifthWireRow) (m : ℕ) (j : Label5 m)
    {t : Point} (ht : t ∈ fixedOwnerBase raw m j) :
    t ∈ logPrimeMeshCell 0 (19 / 96) m j := by
  simp only [fixedOwnerBase, mem_inter_iff] at ht
  tauto

/-- Literal Ico ownership, including shared endpoints, orders the mesh
indices in any coordinate whenever the physical coordinates are ordered. -/
theorem owner_index_le_of_coordinate_le (m : ℕ) (j k : Label5 m)
    (t u : Point) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (hu : u ∈ logPrimeMeshCell 0 (19 / 96) m k) (i : Fin 5)
    (htu : t i ≤ u i) : (j i).val ≤ (k i).val := by
  by_contra h
  have hk : (k i).val + 1 ≤ (j i).val := by omega
  have hsep : logPrimeMeshHi 0 (19 / 96) m k i ≤
      logPrimeMeshLo 0 (19 / 96) m j i :=
    logPrimeMeshPoint_mono (by norm_num : (0 : ℝ) ≤ 19 / 96) m hk
  have hti := mem_logPrimeMeshCell.mp ht i
  have hui := mem_logPrimeMeshCell.mp hu i
  linarith

theorem owner_index_eq_of_coordinate_eq (m : ℕ) (j k : Label5 m)
    (t u : Point) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) m j)
    (hu : u ∈ logPrimeMeshCell 0 (19 / 96) m k) (i : Fin 5)
    (htu : t i = u i) : j i = k i :=
  Fin.ext (Nat.le_antisymm
    (owner_index_le_of_coordinate_le m j k t u ht hu i htu.le)
    (owner_index_le_of_coordinate_le m k j u t hu ht i htu.ge))

def zeroGamma (m : ℕ) (j : Label5 m) : ℝ := (gamma 0 (box m (thirdOwner j)) : ℝ)

private theorem box_lx_cast (m : ℕ) (j : Label5 m) :
    ((box m (thirdOwner j)).lx : ℝ) = logPrimeMeshLo 0 (19 / 96) m j 0 := by
  simpa [box, thirdOwner, historicalPrefixProject, logPrimeMeshLo] using
    congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m (thirdOwner j)) 0

private theorem box_full_at_zero (raw : FifthWireRow) (q : ℕ) (hq : 0 < q)
    (hgrid : raw.grid = 400) (hkey : raw.lo 0 ≤ 77)
    (j : Label5 (refinedMesh q)) {t : Point}
    (ht : t ∈ fixedOwnerBase raw (refinedMesh q) j) :
    ((box (refinedMesh q) (thirdOwner j)).ux : ℝ) ≤ mu - 4 * (0 : ℝ) := by
  have hc := refined_owner_is_contained q hq raw hgrid t
    (fixedBase_raw raw _ j ht) j (fixedBase_mesh raw _ j ht)
  have hux : (box (refinedMesh q) (thirdOwner j)).ux ≤ raw.upper 0 := by
    simpa [box, thirdOwner, historicalPrefixProject] using (hc (0 : Fin 5)).2
  have hr : raw.upper 0 ≤ (78 / 400 : ℚ) := by
    unfold FifthWireRow.upper
    rw [hgrid]
    have hk : (raw.lo 0 : ℚ) ≤ 77 := by exact_mod_cast hkey
    norm_num at *
    linarith
  have hR : ((box (refinedMesh q) (thirdOwner j)).ux : ℝ) ≤ 78 / 400 := by
    exact_mod_cast hux.trans hr
  norm_num [mu] at *
  linarith

/-- The genuine decoded owners give the q-uniform quasi-rise needed by
the moving historical walls, directly on every pair of section points. -/
theorem actual_section_gamma_quasirise (raw : FifthWireRow)
    (q : ℕ) (hq : 0 < q) (hgrid : raw.grid = 400) (hkey : raw.lo 0 ≤ 77)
    (y : Base) (x z : ℝ) (hxz : x ≤ z)
    (j k : Label5 (refinedMesh q))
    (hx : insertFirst x y ∈ fixedOwnerBase raw (refinedMesh q) j)
    (hz : insertFirst z y ∈ fixedOwnerBase raw (refinedMesh q) k) :
    zeroGamma (refinedMesh q) k - zeroGamma (refinedMesh q) j ≤
      (z - x + logPrimeMeshStep 0 (19 / 96) (refinedMesh q)) / 2 := by
  let m := refinedMesh q
  have hj := fixedBase_mesh raw m j hx
  have hk := fixedBase_mesh raw m k hz
  have hx0 := insertFirst_zero x y
  have hz0 := insertFirst_zero z y
  have hjk : (j 0).val ≤ (k 0).val :=
    owner_index_le_of_coordinate_le m j k _ _ hj hk 0 (by simpa only [hx0, hz0] using hxz)
  have h1 : insertFirst x y 1 = insertFirst z y 1 := by
    simpa using (insertFirst_rest x y (0 : Fin 4)).trans
      (insertFirst_rest z y (0 : Fin 4)).symm
  have h2 : insertFirst x y 2 = insertFirst z y 2 := by
    simpa using (insertFirst_rest x y (1 : Fin 4)).trans
      (insertFirst_rest z y (1 : Fin 4)).symm
  have hy := owner_index_eq_of_coordinate_eq m j k _ _ hj hk 1 h1
  have hz' := owner_index_eq_of_coordinate_eq m j k _ _ hj hk 2 h2
  have hjk3 : ((thirdOwner j) 0).val ≤ ((thirdOwner k) 0).val := by
    simpa [thirdOwner, historicalPrefixProject] using hjk
  have hy3 : thirdOwner j 1 = thirdOwner k 1 := by
    simpa [thirdOwner, historicalPrefixProject] using hy
  have hz3 : thirdOwner j 2 = thirdOwner k 2 := by
    simpa [thirdOwner, historicalPrefixProject] using hz'
  have hg := gamma_mesh_first_rise 0 m (thirdOwner j) (thirdOwner k)
    hjk3 hy3 hz3 (box_full_at_zero raw q hq hgrid hkey j hx)
      (box_full_at_zero raw q hq hgrid hkey k hz)
  have hgR : zeroGamma m k ≤ zeroGamma m j +
      (firstDelta m (thirdOwner j) (thirdOwner k) : ℝ) / 2 := by
    exact_mod_cast hg
  have hshift := box_first_coordinate_shift m (thirdOwner j) (thirdOwner k) hy3 hz3
  have hlQ : (box m (thirdOwner k)).lx = (box m (thirdOwner j)).lx +
      firstDelta m (thirdOwner j) (thirdOwner k) := by
    simpa [shiftX] using congrArg (fun b : RationalBox => b.lx) hshift
  have hlR : ((box m (thirdOwner k)).lx : ℝ) =
      ((box m (thirdOwner j)).lx : ℝ) +
        (firstDelta m (thirdOwner j) (thirdOwner k) : ℝ) := by exact_mod_cast hlQ
  rw [box_lx_cast m k, box_lx_cast m j] at hlR
  have hxl := mem_logPrimeMeshCell.mp hj (0 : Fin 5)
  have hzl := mem_logPrimeMeshCell.mp hk (0 : Fin 5)
  rw [hx0] at hxl
  rw [hz0] at hzl
  rw [logPrimeMeshHi_eq_lo_add_step] at hxl
  linarith

/-- A wall band uses the actual Gamma of whichever actual mesh cell owns
the point. Its members carry their literal raw/cell geometry witnesses. -/
def actualGammaBand (raw : FifthWireRow) (q : ℕ)
    (J : Finset (Label5 (refinedMesh q))) (y : Base) (a c d : ℝ) : Set ℝ :=
  {x | ∃ j ∈ J, insertFirst x y ∈ fixedOwnerBase raw (refinedMesh q) j ∧
    c ≤ a * x - zeroGamma (refinedMesh q) j ∧
      a * x - zeroGamma (refinedMesh q) j ≤ c + d}

theorem actualGammaBand_volume_le (raw : FifthWireRow) (q : ℕ) (hq : 0 < q)
    (hgrid : raw.grid = 400) (hkey : raw.lo 0 ≤ 77)
    (J : Finset (Label5 (refinedMesh q))) (y : Base) (a c d : ℝ)
    (ha : 1 / 2 < a) :
    volume (actualGammaBand raw q J y a c d) ≤
      ENNReal.ofReal ((d + logPrimeMeshStep 0 (19 / 96) (refinedMesh q) / 2) /
        (a - 1 / 2)) := by
  have hspan : ∀ x ∈ actualGammaBand raw q J y a c d,
      ∀ z ∈ actualGammaBand raw q J y a c d,
      dist x z ≤ (d + logPrimeMeshStep 0 (19 / 96) (refinedMesh q) / 2) / (a - 1 / 2) := by
    intro x hx z hz
    obtain ⟨j, _hj, hxbase, hxlo, hxhi⟩ := hx
    obtain ⟨k, _hk, hzbase, hzlo, hzhi⟩ := hz
    rcases le_total x z with horder | horder
    · have hs := section_span_of_one_sided_rise a _ d x z _ _ c ha horder
        (actual_section_gamma_quasirise raw q hq hgrid hkey y x z horder j k hxbase hzbase)
        hxlo hxhi hzlo hzhi
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr horder)]
      exact hs
    · have hs := section_span_of_one_sided_rise a _ d z x _ _ c ha horder
        (actual_section_gamma_quasirise raw q hq hgrid hkey y z x horder k j hzbase hxbase)
        hzlo hzhi hxlo hxhi
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr horder)]
      exact hs
  exact (Real.volume_le_diam _).trans (ediam_le_of_forall_dist_le hspan)

private theorem real_between_of_directed_crossing (v G L d : ℝ)
    (hdrop : 0 ≤ G - L) (hwidth : G - L ≤ d)
    (h : (v < G ∧ L ≤ v) ∨ (v < L ∧ G ≤ v)) :
    -d ≤ v - G ∧ v - G ≤ 0 := by
  rcases h with h | h <;> constructor <;> linarith

/-- Literal seven-gate crossing: the four ordering gates cannot move;
the independent initial cube and BOTH original third-level cubes remain. -/
theorem actual_crossing_fiber_subset_three_bands (raw : FifthWireRow)
    (q : ℕ) (hq : 0 < q) (hgrid : raw.grid = 400) (hkey : raw.lo 0 ≤ 77)
    (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200) (chi0 chi omega0 omega : ℝ)
    (hchi : chi ≤ (e : ℝ) / 10)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi)
    (J : Finset (Label5 (refinedMesh q)))
    (hselected0 : ∀ j ∈ J, j ∈ selectedFifthCells 0 chi0 (refinedMesh q) omega0 J)
    (hselected : ∀ j ∈ J, j ∈ selectedFifthCells e chi (refinedMesh q) omega J)
    (hstop0 : ∀ j ∈ J,
      P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck 0 (refinedMesh q) j = true)
    (hstop : ∀ j ∈ J,
      P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck (e : ℝ) (refinedMesh q) j = true)
    (y : Base) :
    fiber (ownerSymmDiff raw 0 e chi0 chi (refinedMesh q) omega0 omega J) y ⊆
      initialBand (e : ℝ) ∪
        actualGammaBand raw q J y 3 (-(41 * (e : ℝ) / 20)) (41 * (e : ℝ) / 20) ∪
          actualGammaBand raw q J y 1
            (-(y 0 + 3 * y 1) - 41 * (e : ℝ) / 20) (41 * (e : ℝ) / 20) := by
  intro x hx
  obtain ⟨j, hj, hbase, i, hi⟩ := mem_iUnion₂.mp
    (actual_ownerSymmDiff_subset_crossingUnion raw e chi0 chi (refinedMesh q)
      omega0 omega J hselected0 hselected hstop0 hstop hx)
  have hc := refined_owner_is_contained q hq raw hgrid (insertFirst x y)
    (fixedBase_raw raw _ j hbase) j (fixedBase_mesh raw _ j hbase)
  have hadopted := ((mem_selectedFifthCells e chi (refinedMesh q) omega J j).mp
    (hselected j hj)).2.1
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hemaxR : (e : ℝ) ≤ 3 / 51200 := by exact_mod_cast hemax
  have hd := actual_refined_gamma_drop_bounds q hq raw j (e : ℝ) chi heR hemaxR
    hchi hstep hgrid hkey hc hadopted
  have hdrop : 0 ≤ zeroGamma (refinedMesh q) j -
      levelExponent (e : ℝ) (box (refinedMesh q) (thirdOwner j)) := by
    unfold zeroGamma levelExponent
    linarith [hd.1]
  have hwidth : zeroGamma (refinedMesh q) j -
      levelExponent (e : ℝ) (box (refinedMesh q) (thirdOwner j)) ≤ 41 * (e : ℝ) / 20 := by
    unfold zeroGamma levelExponent
    linarith [hd.2]
  have ht0 := insertFirst_zero x y
  have ht1 : insertFirst x y 1 = y 0 := by simpa using insertFirst_rest x y (0 : Fin 4)
  have ht2 : insertFirst x y 2 = y 1 := by simpa using insertFirst_rest x y (1 : Fin 4)
  fin_cases i
  · change ((_ < (0 : ℝ) ∧ 0 ≤ _) ∨ (_ < (0 : ℝ) ∧ 0 ≤ _)) at hi
    rcases hi with hi | hi <;> linarith
  · change ((_ < (0 : ℝ) ∧ 0 ≤ _) ∨ (_ < (0 : ℝ) ∧ 0 ≤ _)) at hi
    rcases hi with hi | hi <;> linarith
  · change ((_ < (0 : ℝ) ∧ 0 ≤ _) ∨ (_ < (0 : ℝ) ∧ 0 ≤ _)) at hi
    rcases hi with hi | hi <;> linarith
  · change ((_ < (0 : ℝ) ∧ 0 ≤ _) ∨ (_ < (0 : ℝ) ∧ 0 ≤ _)) at hi
    rcases hi with hi | hi <;> linarith
  · apply Or.inl
    apply Or.inl
    change x ∈ Icc (initial (e : ℝ) / 3) (initial 0 / 3)
    change ((3 * insertFirst x y 0 < initial 0 ∧ initial (e : ℝ) ≤ 3 * insertFirst x y 0) ∨
      (3 * insertFirst x y 0 < initial (e : ℝ) ∧ initial 0 ≤ 3 * insertFirst x y 0)) at hi
    rw [ht0] at hi
    have hinit : initial (e : ℝ) ≤ initial 0 := by unfold initial; linarith
    rcases hi with hi | hi <;> constructor <;> linarith
  · apply Or.inl
    apply Or.inr
    refine ⟨j, hj, hbase, ?_⟩
    have hi' : (3 * x < zeroGamma (refinedMesh q) j ∧
        levelExponent (e : ℝ) (box (refinedMesh q) (thirdOwner j)) ≤ 3 * x) ∨
      (3 * x < levelExponent (e : ℝ) (box (refinedMesh q) (thirdOwner j)) ∧
        zeroGamma (refinedMesh q) j ≤ 3 * x) := by
      simpa [P1OriginalHistoricalFifthOwnCubeAffineGates.parentBounds,
        historicalUnorderedThirdGateBounds, historicalUnorderedThirdGateForms,
        levelExponent, zeroGamma, ht0] using hi
    have hb := real_between_of_directed_crossing _ _ _ _ hdrop hwidth hi'
    constructor <;> linarith
  · apply Or.inr
    refine ⟨j, hj, hbase, ?_⟩
    have hi' : (x + y 0 + 3 * y 1 < zeroGamma (refinedMesh q) j ∧
        levelExponent (e : ℝ) (box (refinedMesh q) (thirdOwner j)) ≤ x + y 0 + 3 * y 1) ∨
      (x + y 0 + 3 * y 1 < levelExponent (e : ℝ) (box (refinedMesh q) (thirdOwner j)) ∧
        zeroGamma (refinedMesh q) j ≤ x + y 0 + 3 * y 1) := by
      simpa [P1OriginalHistoricalFifthOwnCubeAffineGates.parentBounds,
        historicalUnorderedThirdGateBounds, historicalUnorderedThirdGateForms,
        levelExponent, zeroGamma, ht0, ht1, ht2] using hi
    have hb := real_between_of_directed_crossing _ _ _ _ hdrop hwidth hi'
    constructor <;> linarith

/-- The exact one-dimensional section bound for the actual selected,
firstStop owner union. It is uniform in q and in the number of children. -/
theorem actual_ownerSymmDiff_fiber_volume_le (raw : FifthWireRow)
    (q : ℕ) (hq : 0 < q) (hgrid : raw.grid = 400) (hkey : raw.lo 0 ≤ 77)
    (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200) (chi0 chi omega0 omega : ℝ)
    (hchi : chi ≤ (e : ℝ) / 10)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi)
    (J : Finset (Label5 (refinedMesh q)))
    (hselected0 : ∀ j ∈ J, j ∈ selectedFifthCells 0 chi0 (refinedMesh q) omega0 J)
    (hselected : ∀ j ∈ J, j ∈ selectedFifthCells e chi (refinedMesh q) omega J)
    (hstop0 : ∀ j ∈ J,
      P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck 0 (refinedMesh q) j = true)
    (hstop : ∀ j ∈ J,
      P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck (e : ℝ) (refinedMesh q) j = true)
    (y : Base) :
    volume (fiber (ownerSymmDiff raw 0 e chi0 chi (refinedMesh q) omega0 omega J) y) ≤
      ENNReal.ofReal ((428 / 75 : ℝ) * e) := by
  let h := logPrimeMeshStep 0 (19 / 96) (refinedMesh q)
  let d := 41 * (e : ℝ) / 20
  have hi := initialBand_volume (e : ℝ)
  have h3 := actualGammaBand_volume_le raw q hq hgrid hkey J y 3 (-d) d (by norm_num)
  have h1 := actualGammaBand_volume_le raw q hq hgrid hkey J y 1
    (-(y 0 + 3 * y 1) - d) d (by norm_num)
  have h3' : volume (actualGammaBand raw q J y 3 (-d) d) ≤
      ENNReal.ofReal ((2 * d + h) / 5) := by convert h3 using 1 <;> congr 1 <;> ring
  have h1' : volume (actualGammaBand raw q J y 1 (-(y 0 + 3 * y 1) - d) d) ≤
      ENNReal.ofReal (2 * d + h) := by convert h1 using 1 <;> congr 1 <;> ring
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hh : 0 ≤ h := (logPrimeMeshStep_pos (by norm_num : (0 : ℝ) < 19 / 96) _).le
  have hsmall : h ≤ (e : ℝ) / 10 := hstep.trans hchi
  have hn0 : 0 ≤ 2 * (e : ℝ) / 3 := by positivity
  have hn3 : 0 ≤ (2 * d + h) / 5 := by dsimp [d]; positivity
  have hn1 : 0 ≤ 2 * d + h := by dsimp [d]; positivity
  calc
    volume (fiber (ownerSymmDiff raw 0 e chi0 chi (refinedMesh q) omega0 omega J) y) ≤
        volume (initialBand (e : ℝ) ∪ actualGammaBand raw q J y 3 (-d) d ∪
          actualGammaBand raw q J y 1 (-(y 0 + 3 * y 1) - d) d) :=
      measure_mono (actual_crossing_fiber_subset_three_bands raw q hq hgrid hkey e he hemax
        chi0 chi omega0 omega hchi hstep J hselected0 hselected hstop0 hstop y)
    _ ≤ volume (initialBand (e : ℝ)) + volume (actualGammaBand raw q J y 3 (-d) d) +
        volume (actualGammaBand raw q J y 1 (-(y 0 + 3 * y 1) - d) d) :=
      (measure_union_le _ _).trans (add_le_add_right (measure_union_le _ _) _)
    _ ≤ ENNReal.ofReal (2 * (e : ℝ) / 3) + ENNReal.ofReal ((2 * d + h) / 5) +
        ENNReal.ofReal (2 * d + h) := add_le_add (add_le_add (le_of_eq hi) h3') h1'
    _ = ENNReal.ofReal (2 * (e : ℝ) / 3 + (2 * d + h) / 5 + (2 * d + h)) := by
      rw [← ENNReal.ofReal_add hn0 hn3,
        ← ENNReal.ofReal_add (add_nonneg hn0 hn3) hn1]
    _ ≤ ENNReal.ofReal ((428 / 75 : ℝ) * e) :=
      ENNReal.ofReal_le_ofReal (by dsimp [d] at *; linarith)

/-- Fubini now consumes the PROVED actual sections. No five-dimensional
volume bound is assumed. The same raw saved parent supplies the four
remaining widths, so this remains uniform in the moving refinement. -/
theorem actual_ownerSymmDiff_volume_le (raw : FifthWireRow)
    (q : ℕ) (hq : 0 < q) (hgrid : raw.grid = 400) (hkey : raw.lo 0 ≤ 77)
    (e : ℚ) (he : 0 ≤ e) (hemax : e ≤ 3 / 51200) (chi0 chi omega0 omega : ℝ)
    (hchi : chi ≤ (e : ℝ) / 10)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi)
    (J : Finset (Label5 (refinedMesh q)))
    (hselected0 : ∀ j ∈ J, j ∈ selectedFifthCells 0 chi0 (refinedMesh q) omega0 J)
    (hselected : ∀ j ∈ J, j ∈ selectedFifthCells e chi (refinedMesh q) omega J)
    (hstop0 : ∀ j ∈ J,
      P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck 0 (refinedMesh q) j = true)
    (hstop : ∀ j ∈ J,
      P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck (e : ℝ) (refinedMesh q) j = true) :
    volume (ownerSymmDiff raw 0 e chi0 chi (refinedMesh q) omega0 omega J) ≤
      ENNReal.ofReal ((428 / 75 : ℝ) * (e : ℝ) / (400 : ℝ)^4) := by
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hb := raw_volume_le_of_fiber_bound raw hgrid
    (ownerSymmDiff raw 0 e chi0 chi (refinedMesh q) omega0 omega J)
    ((428 / 75 : ℝ) * (e : ℝ))
    (ownerSymmDiff_measurable raw 0 e chi0 chi _ omega0 omega J)
    (ownerSymmDiff_subset_raw raw 0 e chi0 chi _ omega0 omega J) (by
      intro y _hy
      change volume (fiber (ownerSymmDiff raw 0 e chi0 chi (refinedMesh q) omega0 omega J) y) ≤ _
      exact actual_ownerSymmDiff_fiber_volume_le raw q hq hgrid hkey e he hemax
        chi0 chi omega0 omega hchi hstep J hselected0 hselected hstop0 hstop y)
  calc
    volume (ownerSymmDiff raw 0 e chi0 chi (refinedMesh q) omega0 omega J) ≤
        ENNReal.ofReal ((428 / 75 : ℝ) * e) * (ENNReal.ofReal (1 / 400 : ℝ))^4 := hb
    _ = ENNReal.ofReal ((428 / 75 : ℝ) * (e : ℝ) / (400 : ℝ)^4) := by
      rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 400),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (428 / 75 : ℝ) * (e : ℝ))]
      congr 1
      ring

end
end ImbalancedChen.P1OriginalFifthActualCrossingSections
