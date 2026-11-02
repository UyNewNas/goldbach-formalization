import ImbalancedChen.Part3OriginalRetainedPhaseMixedDifference
import ImbalancedChen.Part3OriginalActualRetainedPhaseCost
import ImbalancedChen.Part3OriginalActualAbelPrefixCost

/-!
SOURCE ONLY / NOT COMPILED / ZERO FORMAL CREDIT.

The missing finite-boundary step for the actual five-coordinate Abel weight.
All 32 boundary patterns are represented by filtering the five DISTINCT
coordinates. The upper endpoint contributes 1, an interior point contributes
its normalized mesh. Summing the meshes gives at most 2*2*2*2*3 = 48.
The input is primitive C5 smoothness, never a variation estimate.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumPhysicalQAbel
open ImbalancedChen.Part3.OriginalMediumPhysicalFiveAbelTower
open ImbalancedChen.Part3.OriginalMediumPhysicalShiftReindex
open ImbalancedChen.Part3.OriginalMediumFiveAbelGlobalFubini
open ImbalancedChen.Part3.OriginalMediumOneTimeVariationTransfer
open ImbalancedChen.Part3.OriginalMediumAbelPhysicalBox
open ImbalancedChen.Part3.OriginalMediumWeight0Normalized
open ImbalancedChen.Part3.OriginalMediumSmoothWeightInput
open ImbalancedChen.Part3.OriginalMediumPhysicalFiveJets
open ImbalancedChen.Part3.OriginalMediumCompleteWAllSubsetSteps
open ImbalancedChen.Part3.OriginalMediumCompleteWOneDifference
open ImbalancedChen.Part3.OriginalMediumSubsetLeibnizStep
open ImbalancedChen.Part3.OriginalRetainedPhaseMixedDifference20261102
open ImbalancedChen.Part3.OriginalActualAbelPrefixCost20261028
open ImbalancedChen.Part3.OriginalActualRetainedPhaseCost20261028

namespace ImbalancedChen.Part3.OriginalRetainedPhaseBoundaryVariation20261102

attribute [local instance] Classical.propDecidable

def lengths (B : FixedBlock) : Coordinate → ℕ :=
  ![B.qLength, wLength B, wLength B, nLength B, hLength B]

def bases (B : FixedBlock) : Coordinate → ℝ :=
  ![(B.qLo : ℝ), (wBase B : ℝ), (wBase B : ℝ), (nBase B : ℝ), (B.hLo : ℝ)]

def scales (B : FixedBlock) : Coordinate → ℝ :=
  ![B.q0, B.roughLength, B.roughLength, B.atom.U, B.H]

def point (B : FixedBlock) (r : Coordinate → ℕ) : Vector5 :=
  fun i => (bases B i + (r i : ℝ)) / scales B i

def inGrid (B : FixedBlock) (r : Coordinate → ℕ) : Prop :=
  ∀ i, r i ≤ lengths B i

def nextPoint (B : FixedBlock) (r : Coordinate → ℕ) : Vector5 :=
  fun i => if r i = lengths B i then point B r i
    else point B r i + (scales B i)⁻¹

def active (B : FixedBlock) (r : Coordinate → ℕ) : List Coordinate :=
  ([4, 3, 2, 1, 0] : List Coordinate).filter (fun i => r i ≠ lengths B i)

def meshCharge (N : ℕ) (s : ℝ) (i : ℕ) : ℝ :=
  if i = N then 1 else s⁻¹

theorem scales_pos (B : FixedBlock) (hp : PhysicalBox B) (i : Coordinate) :
    0 < scales B i := by
  fin_cases i <;> simp only [scales, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  · exact B.q0_pos
  · exact B.rough_pos
  · exact B.rough_pos
  · exact B.U_pos
  · exact H_pos B hp

/-- Scalar lengths are differences of the ACTUAL original endpoints. -/
theorem terminal_point (B : FixedBlock) (hp : PhysicalBox B) :
    point B (lengths B) =
      ![(B.qHi : ℝ) / B.q0,
        (Nat.floor (2 * B.roughLength) : ℝ) / B.roughLength,
        (Nat.floor (2 * B.roughLength) : ℝ) / B.roughLength,
        (Nat.floor (2 * B.atom.U) : ℝ) / B.atom.U, (B.hHi : ℝ) / B.H] := by
  have hq : B.qLo + B.qLength = B.qHi := by
    dsimp [qLength]; omega
  have hw : wBase B + wLength B = Nat.floor (2 * B.roughLength) := by
    dsimp [wBase, wLength]; have := hp.w; omega
  have hn : nBase B + nLength B = Nat.floor (2 * B.atom.U) := by
    dsimp [nBase, nLength]; have := hp.n; omega
  have hh : B.hLo + (hLength B : ℤ) = B.hHi := by
    dsimp [hLength]; have := hp.h; omega
  funext i
  fin_cases i <;> simp only [point, bases, lengths, scales,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four]
  · rw [← Nat.cast_add, hq]
  · rw [← Nat.cast_add, hw]
  · rw [← Nat.cast_add, hw]
  · rw [← Nat.cast_add, hn]
  · have hhR : (B.hLo : ℝ) + (hLength B : ℝ) = (B.hHi : ℝ) := by
      exact_mod_cast hh
    rw [hhR]

theorem point_order (B : FixedBlock) (hp : PhysicalBox B)
    {r s : Coordinate → ℕ} (hrs : ∀ i, r i ≤ s i) (i : Coordinate) :
    point B r i ≤ point B s i := by
  apply div_le_div_of_nonneg_right _ (scales_pos B hp i).le
  exact add_le_add_left (by exact_mod_cast hrs i) _

/-- The entire closed normalized rectangle, not just integer support,
lies in the derivative domain. h=0 is harmless; it is never a denominator. -/
theorem global_box (B : FixedBlock) (hp : PhysicalBox B) (v : Vector5)
    (hv : InRectangle (point B (fun _ => 0)) (point B (lengths B)) v) :
    NormBox v := by
  have hq := q_box B hp B.qLo le_rfl hp.q
  have hw := w_box B hp (wBase B) le_rfl hp.w
  have hn := n_box B hp (nBase B) le_rfl hp.n
  have hlo := h_box B hp B.hLo le_rfl hp.h
  have hhi := h_box B hp B.hHi hp.h le_rfl
  have he := terminal_point B hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hq.1.trans (by simpa [point, bases, scales] using (hv 0).1)
  · exact hw.1.trans (by simpa [point, bases, scales] using (hv 1).1)
  · exact hw.1.trans (by simpa [point, bases, scales] using (hv 2).1)
  · exact hn.1.trans (by simpa [point, bases, scales] using (hv 3).1)
  · apply abs_le.mpr
    constructor
    · exact (abs_le.mp hlo).1.trans
        (by simpa [point, bases, scales] using (hv 4).1)
    · have hvhi : v 4 ≤ (B.hHi : ℝ) / B.H := by
        simpa only [he, Matrix.cons_val_four] using (hv 4).2
      exact hvhi.trans (abs_le.mp hhi).2

theorem point_le_next (B : FixedBlock) (hp : PhysicalBox B)
    (r : Coordinate → ℕ) (i : Coordinate) : point B r i ≤ nextPoint B r i := by
  unfold nextPoint
  split_ifs
  · exact le_rfl
  · exact le_add_of_nonneg_right (inv_nonneg.mpr (scales_pos B hp i).le)

theorem next_le_terminal (B : FixedBlock) (hp : PhysicalBox B)
    {r : Coordinate → ℕ} (hr : inGrid B r) (i : Coordinate) :
    nextPoint B r i ≤ point B (lengths B) i := by
  unfold nextPoint
  split_ifs with he
  · exact point_order B hp hr i
  · have hsucc : r i + 1 ≤ lengths B i := by have := hr i; omega
    have hcast : (r i : ℝ) + 1 ≤ (lengths B i : ℝ) := by exact_mod_cast hsucc
    have hs := scales_pos B hp i
    dsimp [point]
    rw [inv_eq_one_div, ← add_div]
    apply div_le_div_of_nonneg_right _ hs.le
    linarith

theorem local_box (B : FixedBlock) (hp : PhysicalBox B)
    {r : Coordinate → ℕ} (hr : inGrid B r) (v : Vector5)
    (hv : InRectangle (point B r) (nextPoint B r) v) : NormBox v := by
  apply global_box B hp v
  intro i
  exact ⟨(point_order B hp (fun j => Nat.zero_le _) i).trans (hv i).1,
    (hv i).2.trans (next_le_terminal B hp hr i)⟩

theorem active_nodup (B : FixedBlock) (r : Coordinate → ℕ) :
    (active B r).Nodup := by
  exact List.Nodup.filter _ (by decide : ([4,3,2,1,0] : List Coordinate).Nodup)

/-- Boundary coordinates contribute only their original endpoint value;
the complementary coordinates contribute one physical mesh each. -/
theorem active_widths (B : FixedBlock) (r : Coordinate → ℕ) :
    widths (active B r) (point B r) (nextPoint B r) =
      meshCharge (lengths B 4) (scales B 4) (r 4) *
      meshCharge (lengths B 3) (scales B 3) (r 3) *
      meshCharge (lengths B 2) (scales B 2) (r 2) *
      meshCharge (lengths B 1) (scales B 1) (r 1) *
      meshCharge (lengths B 0) (scales B 0) (r 0) := by
  by_cases h4 : r 4 = lengths B 4 <;>
    by_cases h3 : r 3 = lengths B 3 <;>
    by_cases h2 : r 2 = lengths B 2 <;>
    by_cases h1 : r 1 = lengths B 1 <;>
    by_cases h0 : r 0 = lengths B 0 <;>
    simp [active, widths, meshCharge, nextPoint, h4,h3,h2,h1,h0,
      mul_assoc]

theorem weight0_eq_fullWFace (B : FixedBlock) (hp : PhysicalBox B)
    (q w1 w2 n h : ℕ) :
    weight0 B q w1 w2 n h =
      fullWFace B (poissonAmplitude B) (phaseAmplitude B) ∅
        (point B ![q,w1,w2,n,h]) := by
  rw [fullWFace_empty]
  have hq : 0 < B.qLo + q := by
    have : (0 : ℝ) < B.qLo := B.q0_pos.trans_le B.qLo_block
    have : 0 < B.qLo := by exact_mod_cast this
    omega
  have hw : 0 < wBase B := Nat.ceil_pos.mpr B.rough_pos
  have hn : 0 < nBase B := Nat.ceil_pos.mpr B.U_pos
  have he := rowWeight_eq_normalizedW B hp (B.qLo+q)
    (wBase B+w1) (wBase B+w2) (nBase B+n) (B.hLo+(h : ℤ))
    hq (by omega) (by omega) (by omega)
  simpa [weight0, point, bases, scales, Nat.cast_add, Int.cast_add] using he

/-- Exact identity for the original weight5. This is finite algebra,
including all endpoint patterns; it assumes no norm or variation bound. -/
theorem weight5_eq_mixedDifference (B : FixedBlock) (hp : PhysicalBox B)
    (q w1 w2 n h : ℕ) :
    weight5 B q w1 w2 n h =
      mixedDifference (active B ![q,w1,w2,n,h])
        (point B ![q,w1,w2,n,h]) (nextPoint B ![q,w1,w2,n,h])
        (fullWFace B (poissonAmplitude B) (phaseAmplitude B) ∅)
        (point B ![q,w1,w2,n,h]) := by
  by_cases hh : h = hLength B <;>
    by_cases hn : n = nLength B <;>
    by_cases hw2 : w2 = wLength B <;>
    by_cases hw1 : w1 = wLength B <;>
    by_cases hq : q = B.qLength <;>
    simp [weight5,weight4,weight3,weight2,weight1,
      diffH,diffN1,diffW2,diffW1,diffQ,forward,
      weight0_eq_fullWFace B hp, fullWFace_empty, active, lengths,
      mixedDifference, nextPoint, point, bases, scales,
      hh,hn,hw2,hw1,hq, Function.update, Nat.cast_add,
      add_div, inv_eq_one_div, add_assoc]

theorem weight5_point_bound (B : FixedBlock) (hp : PhysicalBox B)
    (Smooth : SmoothInput B) (q w1 w2 n h : ℕ)
    (hq : q ≤ B.qLength) (hw1 : w1 ≤ wLength B)
    (hw2 : w2 ≤ wLength B) (hn : n ≤ nLength B) (hh : h ≤ hLength B) :
    ‖weight5 B q w1 w2 n h‖ ≤
      fifthEnvelope B Smooth (poissonAmplitude B) (phaseAmplitude B) *
        (meshCharge (hLength B) B.H h *
         meshCharge (nLength B) B.atom.U n *
         meshCharge (wLength B) B.roughLength w2 *
         meshCharge (wLength B) B.roughLength w1 *
         meshCharge B.qLength B.q0 q) := by
  let r : Coordinate → ℕ := ![q,w1,w2,n,h]
  have hr : inGrid B r := by
    intro i; fin_cases i <;> simp [r,lengths,hq,hw1,hw2,hn,hh]
  rw [weight5_eq_mixedDifference B hp]
  have hb := mixedDifference_bound B Smooth (poissonAmplitude B) (phaseAmplitude B)
    (point B r) (nextPoint B r) (point_le_next B hp r)
    (local_box B hp hr) (active B r) (active_nodup B r)
    ∅ (by simp) (point B r)
    (fun i => ⟨le_rfl, point_le_next B hp r i⟩)
  simpa [active_widths, r, lengths, scales] using hb

theorem sum_meshCharge (N : ℕ) (s : ℝ) :
    (∑ i ∈ range (N+1), meshCharge N s i) = 1 + (N : ℝ) / s := by
  rw [sum_range_succ]
  have he : (∑ i ∈ range N, meshCharge N s i) = (N : ℝ) * s⁻¹ := by
    calc
      _ = ∑ _i ∈ range N, s⁻¹ := by
        apply sum_congr rfl
        intro i hi
        simp only [meshCharge, if_neg (Nat.ne_of_lt (mem_range.mp hi))]
      _ = _ := by simp
  rw [he]
  simp [meshCharge, div_eq_mul_inv, add_comm]

theorem normalized_lengths (B : FixedBlock) (hp : PhysicalBox B) :
    (B.qLength : ℝ) / B.q0 ≤ 1 ∧
    (wLength B : ℝ) / B.roughLength ≤ 1 ∧
    (nLength B : ℝ) / B.atom.U ≤ 1 ∧
    (hLength B : ℝ) / B.H ≤ 2 := by
  have he := terminal_point B hp
  have hq := congrFun he 0
  have hw := congrFun he 1
  have hn := congrFun he 3
  have hh := congrFun he 4
  simp only [point,bases,lengths,scales,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four] at hq hw hn hh
  have hqlo := (q_box B hp B.qLo le_rfl hp.q).1
  have hqhi := (q_box B hp B.qHi hp.q le_rfl).2
  have hwlo := (w_box B hp (wBase B) le_rfl hp.w).1
  have hwhi := (w_box B hp (Nat.floor (2*B.roughLength)) hp.w le_rfl).2
  have hnlo := (n_box B hp (nBase B) le_rfl hp.n).1
  have hnhi := (n_box B hp (Nat.floor (2*B.atom.U)) hp.n le_rfl).2
  have hhlo := (abs_le.mp (h_box B hp B.hLo le_rfl hp.h)).1
  have hhhi := (abs_le.mp (h_box B hp B.hHi hp.h le_rfl)).2
  simp only [add_div] at hq hw hn hh
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- All faces and edges are paid in one finite sum. The bound is uniform
even when a scalar interval is a singleton (its entire charge is 1). -/
theorem actual_weight5_variation_le (B : FixedBlock) (hp : PhysicalBox B)
    (Smooth : SmoothInput B) :
    variation B (weight5 B) ≤
      48 * fifthEnvelope B Smooth (poissonAmplitude B) (phaseAmplitude B) := by
  let C := fifthEnvelope B Smooth (poissonAmplitude B) (phaseAmplitude B)
  have hC : 0 ≤ C := fifthEnvelope_nonneg _ _ _ _
  have hq := (normalized_lengths B hp).1
  have hw := (normalized_lengths B hp).2.1
  have hn := (normalized_lengths B hp).2.2.1
  have hh := (normalized_lengths B hp).2.2.2
  have hsum : variation B (weight5 B) ≤
      C * ((1 + (hLength B : ℝ)/B.H) *
        (1 + (nLength B : ℝ)/B.atom.U) *
        (1 + (wLength B : ℝ)/B.roughLength) *
        (1 + (wLength B : ℝ)/B.roughLength) *
        (1 + (B.qLength : ℝ)/B.q0)) := by
    unfold variation box
    simp only [sum_product, value]
    calc
      _ ≤ ∑ h ∈ hSet B, ∑ n ∈ nSet B, ∑ w2 ∈ wSet B,
          ∑ w1 ∈ wSet B, ∑ q ∈ qSet B,
            C * (meshCharge (hLength B) B.H h *
              meshCharge (nLength B) B.atom.U n *
              meshCharge (wLength B) B.roughLength w2 *
              meshCharge (wLength B) B.roughLength w1 *
              meshCharge B.qLength B.q0 q) := by
        apply sum_le_sum; intro h hh'
        apply sum_le_sum; intro n hn'
        apply sum_le_sum; intro w2 hw2'
        apply sum_le_sum; intro w1 hw1'
        apply sum_le_sum; intro q hq'
        exact weight5_point_bound B hp Smooth q w1 w2 n h
          (by have := mem_range.mp hq'; omega)
          (by have := mem_range.mp hw1'; omega)
          (by have := mem_range.mp hw2'; omega)
          (by have := mem_range.mp hn'; omega)
          (by have := mem_range.mp hh'; omega)
      _ = _ := by
        simp only [hSet,nSet,wSet,qSet,← mul_sum,sum_meshCharge,mul_assoc]
  apply hsum.trans
  have hqp : 0 ≤ (B.qLength : ℝ)/B.q0 := div_nonneg (Nat.cast_nonneg _) B.q0_pos.le
  have hwp : 0 ≤ (wLength B : ℝ)/B.roughLength :=
    div_nonneg (Nat.cast_nonneg _) B.rough_pos.le
  have hnp : 0 ≤ (nLength B : ℝ)/B.atom.U := div_nonneg (Nat.cast_nonneg _) B.U_pos.le
  have hhp : 0 ≤ (hLength B : ℝ)/B.H := div_nonneg (Nat.cast_nonneg _) (H_pos B hp).le
  calc
    _ ≤ C * (3 * 2 * 2 * 2 * 2) := by gcongr <;> linarith
    _ = _ := by ring

/-- One single phase charge on the genuine pre-partition E3; the true
prefix maximum remains visible for the independently owned spectral task. -/
theorem actual_E3_le_prefix_fifthEnvelope (B : FixedBlock) (hp : PhysicalBox B)
    (Smooth : SmoothInput B) :
    ‖B.E3‖ ≤ actualPrefixEnvelope B *
      (48 * fifthEnvelope B Smooth (poissonAmplitude B) (phaseAmplitude B)) := by
  exact (E3_le_prefix_times_variation B hp.toOrderedBox (actualPrefixEnvelope B)
    (actualPrefixEnvelope_nonneg B) (actual_coeff5_le_prefixEnvelope B)).trans
      (mul_le_mul_of_nonneg_left (actual_weight5_variation_le B hp Smooth)
        (actualPrefixEnvelope_nonneg B))

end ImbalancedChen.Part3.OriginalRetainedPhaseBoundaryVariation20261102
