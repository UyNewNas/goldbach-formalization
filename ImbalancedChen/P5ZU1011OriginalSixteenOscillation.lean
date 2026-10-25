import ImbalancedChen.P5ZU1011OriginalSixteenPolicyBank
import ImbalancedChen.P5ZU1011H248CommonPartition
import ImbalancedChen.LogPrimeBoxMesh
import Mathlib.Algebra.Order.Group.MinMax

/-!
Quantitative oscillation for the ACTUAL original sixteen-policy cap and
residual circuit, including points on opposite sides of cap-branch walls.
The H248 atom is frozen only after the exact common-state partition.
Its literal array bounds give a uniform ordinary-kernel constant 2000
at clip 417/5000, including every marked knot and the zero exterior.

One explicit mesh then approximates every frozen atom and all sixteen
policies simultaneously. No continuity, Lipschitz, kernel oscillation,
count, AP, or full-mean premise is requested as a supplier.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenOscillation

open Set Filter Topology
open Classical
open U11Integral U11H248 U1011OriginalSixteenPolicyBank U1011H248Partition
open scoped BigOperators

noncomputable section

def l1Delta (v w : LogFour) : ℝ := ∑ i : Fin 4, |v i-w i|

theorem l1Delta_nonneg (v w : LogFour) : 0≤l1Delta v w :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem coordinate_abs_sub_le_l1Delta (v w : LogFour) (j : Fin 4) :
    |v j-w j|≤l1Delta v w :=
  Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ j)

theorem selectedMass_abs_sub_le (p : Policy) (v w : LogFour) :
    |selectedMass p v-selectedMass p w|≤l1Delta v w := by
  unfold selectedMass l1Delta
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin 4, |(if Selected p i then v i else 0)-
        (if Selected p i then w i else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : Selected p i
      · simp only [if_pos hi]
        exact le_rfl
      · simp only [if_neg hi,sub_self,abs_zero]
        exact abs_nonneg _

theorem prefixSum_eq_sum (v : LogFour) : U11SelectedLargest.prefixSum v=∑ i : Fin 4, v i := by
  simp [U11SelectedLargest.prefixSum,Fin.sum_univ_succ]
  <;> ring

theorem prefixSum_abs_sub_le (v w : LogFour) :
    |U11SelectedLargest.prefixSum v-U11SelectedLargest.prefixSum w|≤l1Delta v w := by
  rw [prefixSum_eq_sum,prefixSum_eq_sum,←Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

/-- The same constant is valid across the actual selected min's branch
wall, and on the distinct W branch. It is global on real four-space. -/
theorem cap_abs_sub_le (p : Policy) (v w : LogFour) :
    |cap p v-cap p w|≤(3/2:ℝ)*l1Delta v w := by
  have hd := l1Delta_nonneg v w
  have hmass := selectedMass_abs_sub_le p v w
  by_cases hp : p.val<15
  · have hA : |(1+selectedMass p v)/2-(1+selectedMass p w)/2|≤
        (3/2:ℝ)*l1Delta v w := by
      rw [show (1+selectedMass p v)/2-(1+selectedMass p w)/2=
        (1/2:ℝ)*(selectedMass p v-selectedMass p w) by ring,abs_mul]
      norm_num
      nlinarith
    have hC : |(57/64-(3/2:ℝ)*selectedMass p v)-
        (57/64-(3/2:ℝ)*selectedMass p w)|≤(3/2:ℝ)*l1Delta v w := by
      rw [show (57/64-(3/2:ℝ)*selectedMass p v)-
        (57/64-(3/2:ℝ)*selectedMass p w)=
          -(3/2:ℝ)*(selectedMass p v-selectedMass p w) by ring,abs_mul]
      norm_num
      nlinarith
    simp only [cap,if_pos hp]
    exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le hA hC)
  · have hcoord := coordinate_abs_sub_le_l1Delta v w 2
    simp only [cap,if_neg hp]
    rw [show ((153/256:ℝ)-(3/8:ℝ)*v 2)-((153/256:ℝ)-(3/8:ℝ)*w 2)=
      -(3/8:ℝ)*(v 2-w 2) by ring,abs_mul]
    norm_num
    nlinarith

theorem typedResidual_abs_sub_le (p : Policy) (v w : LogFour) :
    |typedResidual p v-typedResidual p w|≤(5/2:ℝ)*l1Delta v w := by
  have hc := cap_abs_sub_le p v w
  have hs := prefixSum_abs_sub_le v w
  unfold typedResidual
  calc
    _ = |(cap p v-cap p w)+ -(U11SelectedLargest.prefixSum v-
        U11SelectedLargest.prefixSum w)| := by congr 1; ring
    _ ≤ |cap p v-cap p w|+|-(U11SelectedLargest.prefixSum v-
        U11SelectedLargest.prefixSum w)| := abs_add_le _ _
    _ ≤ _ := by rw [abs_neg]; linarith

/-- Clipping does not increase the already proved actual residual error. -/
theorem clippedResidual_abs_sub_le (a : ℝ) (p : Policy) (v w : LogFour) :
    |max a (typedResidual p v)-max a (typedResidual p w)|≤(5/2:ℝ)*l1Delta v w := by
  have hr := typedResidual_abs_sub_le p v w
  have hd := l1Delta_nonneg v w
  exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp; positivity) hr)

/-- The actual reciprocal denominator has a quantitative global modulus
once the clip is positive; no residual positivity away from a cell is needed. -/
theorem reciprocal_clippedResidual_abs_sub_le (a : ℝ) (ha : 0<a)
    (p : Policy) (v w : LogFour) :
    |1/max a (typedResidual p v)-1/max a (typedResidual p w)|≤
      ((5/2:ℝ)/a^2)*l1Delta v w := by
  let X := max a (typedResidual p v)
  let Y := max a (typedResidual p w)
  have hax : a≤X := le_max_left _ _
  have hay : a≤Y := le_max_left _ _
  have hX : 0<X := ha.trans_le hax
  have hY : 0<Y := ha.trans_le hay
  have hXY : 0<X*Y := mul_pos hX hY
  have hden : a^2≤X*Y := by
    simpa only [pow_two] using mul_le_mul hax hay ha.le hX.le
  have hclip : |X-Y|≤(5/2:ℝ)*l1Delta v w := clippedResidual_abs_sub_le a p v w
  have hid : 1/X-1/Y=(Y-X)/(X*Y) := by
    field_simp [hX.ne',hY.ne']
    <;> ring
  change |1/X-1/Y|≤_
  rw [hid,abs_div,abs_of_pos hXY,abs_sub_comm Y X]
  calc
    _ ≤ ((5/2:ℝ)*l1Delta v w)/(X*Y) := div_le_div_of_nonneg_right hclip hXY.le
    _ ≤ ((5/2:ℝ)*l1Delta v w)/a^2 :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (l1Delta_nonneg v w))
        (pow_pos ha _) hden
    _ = _ := by ring

/-- Every state value is from the actual H248 array or its exact exterior zero. -/
theorem stateValue_bounds (b : AtomState) : 0≤stateValue b ∧ stateValue b≤1 := by
  cases b with
  | none => norm_num [stateValue]
  | some b => exact H248_atom_bounds b

def frozenOrdinary (a : ℝ) (b : AtomState) (p : Policy) (v : LogFour) : ℝ :=
  4*(1-stateValue b)/max a (typedResidual p v)

theorem frozenOrdinary_abs_sub_le (a : ℝ) (ha : 0<a)
    (b : AtomState) (p : Policy) (v w : LogFour) :
    |frozenOrdinary a b p v-frozenOrdinary a b p w|≤(10/a^2)*l1Delta v w := by
  have hb := stateValue_bounds b
  have hd := l1Delta_nonneg v w
  have hc0 : 0≤4*(1-stateValue b) := by nlinarith
  have hc4 : 4*(1-stateValue b)≤4 := by nlinarith
  have hrec := reciprocal_clippedResidual_abs_sub_le a ha p v w
  have hnonneg : 0≤((5/2:ℝ)/a^2)*l1Delta v w := by positivity
  unfold frozenOrdinary
  rw [show 4*(1-stateValue b)/max a (typedResidual p v)-
      4*(1-stateValue b)/max a (typedResidual p w)=
      (4*(1-stateValue b))*(1/max a (typedResidual p v)-1/max a (typedResidual p w)) by ring,
    abs_mul,abs_of_nonneg hc0]
  calc
    _ ≤ (4*(1-stateValue b))*(((5/2:ℝ)/a^2)*l1Delta v w) :=
      mul_le_mul_of_nonneg_left hrec hc0
    _ ≤ 4*(((5/2:ℝ)/a^2)*l1Delta v w) := mul_le_mul_of_nonneg_right hc4 hnonneg
    _ = _ := by ring

/-- Conservative explicit constant for the genuine original lower wall. -/
theorem original_frozenOrdinary_abs_sub_le (b : AtomState) (p : Policy) (v w : LogFour) :
    |frozenOrdinary (417/5000:ℝ) b p v-frozenOrdinary (417/5000:ℝ) b p w|≤
      2000*l1Delta v w := by
  have h := frozenOrdinary_abs_sub_le (417/5000:ℝ) (by norm_num) b p v w
  have hconstant : (10:ℝ)/(417/5000:ℝ)^2≤2000 := by norm_num
  exact h.trans (mul_le_mul_of_nonneg_right hconstant (l1Delta_nonneg v w))

/-- On its actual table state and above its clip, the smooth expression
equals the original bank's ordinary candidate, with the original residual. -/
theorem frozenOrdinary_eq_actual_on_cell (a : ℝ) (b : AtomState) (p : Policy) (v : LogFour)
    (hclip : a≤typedResidual p v)
    (hcell : typedResidual p v/v 3∈scalarCell b) :
    frozenOrdinary a b p v=ordinaryKernel Part5UpperTables.H248 residual p.val v := by
  have hr : residual p.val v=typedResidual p v := by
    simp only [residual,dif_pos p.isLt]
  unfold frozenOrdinary ordinaryKernel
  rw [hr,H248_eq_stateValue hcell,max_eq_right hclip]

/-- Actual original eligibility gives the required clip license. This
does not replace the original L>w condition by the stronger L>=2w. -/
theorem original_frozenOrdinary_eq_actual_on_cell (mask : Set (ℝ×ℝ))
    (b : AtomState) (p : Policy) (v : LogFour) (hv : v∈originalDomain mask)
    (he : TypedEligible p v) (hcell : typedResidual p v/v 3∈scalarCell b) :
    frozenOrdinary (417/5000:ℝ) b p v=
      ordinaryKernel Part5UpperTables.H248 residual p.val v := by
  have hres := typedEligible_residual_gt_smallest p v he
  exact frozenOrdinary_eq_actual_on_cell _ b p v (hv.1.trans hres.le) hcell

/-- A local modulus for the ACTUAL ordinary kernel when the common
partition assigns the same literal H248 atom to the two points. -/
theorem original_ordinary_sameAtom_abs_sub_le (mask : Set (ℝ×ℝ))
    (b : AtomState) (p : Policy) (v w : LogFour)
    (hv : v∈originalDomain mask) (hw : w∈originalDomain mask)
    (hev : TypedEligible p v) (hew : TypedEligible p w)
    (hcellv : typedResidual p v/v 3∈scalarCell b)
    (hcellw : typedResidual p w/w 3∈scalarCell b) :
    |ordinaryKernel Part5UpperTables.H248 residual p.val v-
      ordinaryKernel Part5UpperTables.H248 residual p.val w|≤2000*l1Delta v w := by
  rw [←original_frozenOrdinary_eq_actual_on_cell mask b p v hv hev hcellv,
    ←original_frozenOrdinary_eq_actual_on_cell mask b p w hw hew hcellw]
  exact original_frozenOrdinary_abs_sub_le b p v w

theorem continuous_frozenOrdinary (a : ℝ) (ha : 0<a) (b : AtomState) (p : Policy) :
    Continuous (frozenOrdinary a b p) := by
  have hR : Continuous (typedResidual p) :=
    (continuous_cap p).sub U11SelectedLargest.continuous_prefixSum
  exact continuous_const.div (continuous_const.max hR)
    (fun v => (ha.trans_le (le_max_left a (typedResidual p v))).ne')

/-- Geometry, with the actual four labelled coordinates and no oscillation premise. -/
theorem l1Delta_meshLo_le {m : ℕ} {lo hi : ℝ}
    (j : Fin 4 → Fin (m+1)) {v : LogFour} (hv : v∈logPrimeMeshCell lo hi m j) :
    l1Delta v (logPrimeMeshLo lo hi m j)≤4*logPrimeMeshStep lo hi m := by
  unfold l1Delta
  calc
    _ ≤ ∑ _i : Fin 4, logPrimeMeshStep lo hi m := by
      apply Finset.sum_le_sum
      intro i _
      have hvi := mem_logPrimeMeshCell.mp hv i
      rw [abs_of_nonneg (sub_nonneg.mpr hvi.1)]
      have hstep := logPrimeMeshHi_eq_lo_add_step lo hi m j i
      linarith
    _ = _ := by simp; ring

/-- All sixteen policies and every actual marked atom share this one
explicit error bound, even when the cap changes branch inside the cell. -/
theorem original_frozenOrdinary_mesh_error {m : ℕ} {lo hi : ℝ}
    (b : AtomState) (p : Policy) (j : Fin 4 → Fin (m+1)) {v : LogFour}
    (hv : v∈logPrimeMeshCell lo hi m j) :
    |frozenOrdinary (417/5000:ℝ) b p v-
      frozenOrdinary (417/5000:ℝ) b p (logPrimeMeshLo lo hi m j)|≤
        8000*logPrimeMeshStep lo hi m := by
  exact (original_frozenOrdinary_abs_sub_le b p v _).trans
    (by nlinarith [l1Delta_meshLo_le j hv])

/-- A genuine simultaneous mesh supplier, before ALL policies and atoms.
The only input is the requested positive accuracy; the actual circuit,
array bounds, and quantitative modulus are all proved above. -/
theorem exists_original_frozenOrdinary_mesh (lo hi : ℝ) {epsilon : ℝ}
    (hepsilon : 0<epsilon) :
    ∃ m : ℕ, ∀ (b : AtomState) (p : Policy) (j : Fin 4 → Fin (m+1))
      (v : LogFour), v∈logPrimeMeshCell lo hi m j →
        |frozenOrdinary (417/5000:ℝ) b p v-
          frozenOrdinary (417/5000:ℝ) b p (logPrimeMeshLo lo hi m j)|≤epsilon := by
  obtain ⟨m,hm⟩ := ((tendsto_logPrimeMeshStep lo hi).eventually
    (gt_mem_nhds (show (0:ℝ)<epsilon/8000 by positivity))).exists
  refine ⟨m,fun b p j v hv => ?_⟩
  have h := original_frozenOrdinary_mesh_error b p j hv
  linarith

end

end ImbalancedChen.P5Z.U1011OriginalSixteenOscillation
