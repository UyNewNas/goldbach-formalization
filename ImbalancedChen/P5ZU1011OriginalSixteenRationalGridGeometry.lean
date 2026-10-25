import ImbalancedChen.P5ZU1011OriginalSixteenBoxCertificates
import ImbalancedChen.P5ZU1011OriginalSourceGeometryMesh
import ImbalancedChen.LogPrimeBoxMesh

/-!
# Generated rational four-grid for the original full16 integral

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The automatic grid is the original [417/5000,59/250)^4, with n+1 cells
per coordinate. Existing generic Ico mesh cover and ownership theorems
are reused. Every generated cell has exact rational volume step^4.

The six rational affine tests below are the actual original source
inequalities. Upper gap<0 certifies an inner cell; lower gap<=0 is the
necessary outer test. Coverage and inner inclusion are proved from the
actual formula. Proper source walls are null, with no boundary supplier.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenRationalGridGeometry

noncomputable section

open Set MeasureTheory U11Integral
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSourceGeometryMesh P2OriginalFourthCapProducerInterface
open scoped BigOperators

def a : ℚ := 417 / 5000
def b : ℚ := 59 / 250
def step (n : ℕ) : ℚ := (b - a) / (n + 1 : ℕ)
def point (n k : ℕ) : ℚ := a + (k : ℚ) * step n
abbrev Index (n : ℕ) := Fin 4 → Fin (n + 1)

def gridBox (n : ℕ) (j : Index n) : Box :=
  ⟨fun i => point n (j i).val, fun i => point n ((j i).val + 1)⟩

def cell (n : ℕ) (j : Index n) : Set LogFour :=
  logPrimeBox (fun i => ((gridBox n j).lo i : ℝ)) (fun i => ((gridBox n j).hi i : ℝ))

def cube : Set LogFour := logPrimeBox (fun _ => (a : ℝ)) (fun _ => (b : ℝ))
def cellVolume (n : ℕ) : ℚ := step n ^ 4

theorem step_pos (n : ℕ) : 0 < step n := by
  exact div_pos (by norm_num [a, b]) (by positivity)

theorem point_cast (n k : ℕ) :
    (point n k : ℝ) = logPrimeMeshPoint (a : ℝ) (b : ℝ) n k := by
  simp [point, step, logPrimeMeshPoint, logPrimeMeshStep]

theorem cell_eq_generic (n : ℕ) (j : Index n) :
    cell n j = logPrimeMeshCell (a : ℝ) (b : ℝ) n j := by
  simp only [cell, gridBox, point_cast, logPrimeMeshCell, logPrimeMeshLo, logPrimeMeshHi]

theorem gridBox_valid (n : ℕ) (j : Index n) : (gridBox n j).Valid := by
  intro i
  have h := (logPrimeMeshLoHi_bounds (by norm_num [a, b] : (a : ℝ) < (b : ℝ)) n j i).2.1.le
  change (point n (j i).val : ℚ) ≤ point n ((j i).val + 1)
  have hR : (point n (j i).val : ℝ) ≤ (point n ((j i).val + 1) : ℝ) := by
    simpa only [point_cast, logPrimeMeshLo, logPrimeMeshHi] using h
  exact_mod_cast hR

theorem gridBox_corner_bounds (n : ℕ) (j : Index n) (i : Fin 4) :
    a ≤ (gridBox n j).lo i ∧ (gridBox n j).hi i ≤ b := by
  have h := logPrimeMeshLoHi_bounds (by norm_num [a, b] : (a : ℝ) < (b : ℝ)) n j i
  constructor
  · have hR : (a : ℝ) ≤ (point n (j i).val : ℝ) := by
      simpa only [point_cast, logPrimeMeshLo] using h.1
    exact_mod_cast hR
  · have hR : (point n ((j i).val + 1) : ℝ) ≤ (b : ℝ) := by
      simpa only [point_cast, logPrimeMeshHi] using h.2.2
    exact_mod_cast hR

theorem cell_subset_closedBox (n : ℕ) (j : Index n) : cell n j ⊆ (gridBox n j).region := by
  intro v hv
  have h := mem_logPrimeBox.mp hv
  exact ⟨fun i => (h i).1, fun i => (h i).2.le⟩

theorem cell_measurable (n : ℕ) (j : Index n) : MeasurableSet (cell n j) :=
  measurableSet_logPrimeBox _ _

theorem cells_pairwiseDisjoint (n : ℕ) :
    (Set.univ : Set (Index n)).PairwiseDisjoint (cell n) := by
  simpa only [cell_eq_generic] using
    (logPrimeMeshCell_pairwiseDisjoint (d := 4) (by norm_num [a, b] : (a : ℝ) ≤ (b : ℝ)) n)

theorem cells_union (n : ℕ) : (⋃ j : Index n, cell n j) = cube := by
  simpa only [cell_eq_generic, cube] using
    (logPrimeMeshCells_union (d := 4) (by norm_num [a, b] : (a : ℝ) < (b : ℝ)) n)

theorem cell_unique {n : ℕ} {j k : Index n} {v : LogFour}
    (hj : v ∈ cell n j) (hk : v ∈ cell n k) : j = k := by
  rw [cell_eq_generic] at hj hk
  exact logPrimeMeshCell_unique (by norm_num [a, b]) hj hk

theorem corner_difference (n : ℕ) (j : Index n) (i : Fin 4) :
    (gridBox n j).hi i - (gridBox n j).lo i = step n := by
  simp only [gridBox, point, Nat.cast_add, Nat.cast_one]
  ring

theorem cell_volume (n : ℕ) (j : Index n) :
    volume (cell n j) = ENNReal.ofReal (cellVolume n : ℝ) := by
  rw [cell, logPrimeBox, volume_pi_pi]
  simp only [Real.volume_Ico]
  have hd (i : Fin 4) :
      ((gridBox n j).hi i : ℝ) - ((gridBox n j).lo i : ℝ) = (step n : ℝ) := by
    exact_mod_cast corner_difference n j i
  simp_rw [hd]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by exact_mod_cast (step_pos n).le)]
  simp only [cellVolume, Rat.cast_pow]

theorem cell_volume_real (n : ℕ) (j : Index n) :
    volume.real (cell n j) = (cellVolume n : ℝ) := by
  have hp : (0 : ℝ) ≤ (cellVolume n : ℝ) := by
    exact_mod_cast pow_nonneg (step_pos n).le 4
  rw [Measure.real, cell_volume, ENNReal.toReal_ofReal hp]

/-- The literal original six affine inequalities, as rational data. -/
def sourceQBounds : Fin 6 → ℚ := ![-(417 / 5000), 0, 0, 19 / 125, -(19 / 125), 59 / 250]
def sourceQCoefficients : Fin 6 → Fin 4 → ℚ :=
  ![![0, 0, 0, -1], ![0, 0, -1, 1], ![0, -1, 1, 0],
    ![0, 1, 0, 0], ![-1, 0, 0, 0], ![1, 0, 0, 0]]

def sourcePiece (i : Fin 6) : Affine := ⟨-sourceQBounds i, sourceQCoefficients i⟩

theorem sourcePiece_eval (i : Fin 6) (v : LogFour) :
    (sourcePiece i).eval v = sourceGap i v := by
  fin_cases i <;>
    simp [sourcePiece, sourceQBounds, sourceQCoefficients, Affine.eval,
      sourceGap, sourceForms, sourceBounds, Fin.sum_univ_succ]
  <;> ring

def InnerTest (n : ℕ) (j : Index n) : Prop :=
  ∀ i : Fin 6, (sourcePiece i).upper (gridBox n j).lo (gridBox n j).hi < 0
def OuterTest (n : ℕ) (j : Index n) : Prop :=
  ∀ i : Fin 6, (sourcePiece i).lower (gridBox n j).lo (gridBox n j).hi ≤ 0

instance (n : ℕ) (j : Index n) : Decidable (InnerTest n j) := by unfold InnerTest; infer_instance
instance (n : ℕ) (j : Index n) : Decidable (OuterTest n j) := by unfold OuterTest; infer_instance

def inner (n : ℕ) : Finset (Index n) := Finset.univ.filter (InnerTest n)
def outer (n : ℕ) : Finset (Index n) := Finset.univ.filter (OuterTest n)

theorem inner_cell_subset_domain (n : ℕ) {j : Index n} (hj : j ∈ inner n) :
    cell n j ⊆ sourceDomain := by
  intro v hv
  have hB := cell_subset_closedBox n j hv
  apply (mem_sourceDomain_iff v).mpr
  intro i
  have hU := (sourcePiece i).eval_le_upper (gridBox n j).lo (gridBox n j).hi v hB.1 hB.2
  rw [sourcePiece_eval] at hU
  have htest : (((sourcePiece i).upper (gridBox n j).lo (gridBox n j).hi : ℚ) : ℝ) < 0 := by
    exact_mod_cast (Finset.mem_filter.mp hj).2 i
  have hgap : sourceGap i v < 0 := hU.trans_lt htest
  split_ifs
  · exact hgap.le
  · exact hgap

theorem domain_cell_is_outer (n : ℕ) {j : Index n} {v : LogFour}
    (hv : v ∈ sourceDomain) (hj : v ∈ cell n j) : j ∈ outer n := by
  have hB := cell_subset_closedBox n j hj
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro i
  have hL := (sourcePiece i).lower_le_eval (gridBox n j).lo (gridBox n j).hi v hB.1 hB.2
  rw [sourcePiece_eval] at hL
  have hgap : sourceGap i v ≤ 0 := by
    have hh := (mem_sourceDomain_iff v).mp hv i
    split_ifs at hh
    · exact hh
    · exact hh.le
  have hreal : (((sourcePiece i).lower (gridBox n j).lo (gridBox n j).hi : ℚ) : ℝ) ≤ 0 := hL.trans hgap
  exact_mod_cast hreal

theorem domain_outer_cover (n : ℕ) {v : LogFour} (hv : v ∈ sourceDomain) :
    ∃ j ∈ outer n, v ∈ cell n j := by
  have hc : v ∈ cube := by
    obtain ⟨ha, h32, h21, h1, h0lo, h0hi, hm⟩ := hv
    apply mem_logPrimeBox.mpr
    intro i
    fin_cases i <;> dsimp [a, b] <;> constructor <;> linarith
  rw [← cells_union n] at hc
  obtain ⟨j, hj⟩ := mem_iUnion.mp hc
  exact ⟨j, domain_cell_is_outer n hv hj, hj⟩

theorem actual_source_wall_volume_zero (i : Fin 6) :
    volume {v : LogFour | sourceForms i v = sourceBounds i} = 0 :=
  affinePrimeWall_volume_zero (sourceForms i) (sourceForms_ne_zero i) (sourceBounds i)

/-- Exact boundary-null supplier for any future open/closed refinement.
It is proved from the original six proper forms, never assumed. -/
theorem ae_no_actual_source_walls :
    ∀ᵐ v : LogFour ∂volume, ∀ i : Fin 6, sourceForms i v ≠ sourceBounds i :=
  ae_primeAffineGate_no_wall sourceForms sourceBounds sourceForms_ne_zero

end

end ImbalancedChen.P5Z.U1011OriginalSixteenRationalGridGeometry
