import ImbalancedChen.P4BSmoothPhysicalPairOuterRamp
import ImbalancedChen.P4BOuterRampRoughness
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.FinCases

/-!
# P4B: one common compact support for the actual all-space smooth profiles

YELLOW / SOURCE-ONLY / UNCOMPILED. The two project imports are future
normal module names of sibling source-only drafts.

This is a statement about the actual continuous smoothPhysicalProfile on
all of Fin 2 -> R, not only its evaluations on prime tuples. For fixed
parameters width and theta the SAME closed cube contains the topological
support for every N>=2. Both bounds of this cube are independent of N.

Nonzero profile supplies its own four actual physical margins. The first
three imply both coordinates >theta by the proved elementary geometry.
The upper-product physical margin bounds their sum by 1+width/log N,
which is at most 1+width/log 2. Closure is taken only after inclusion in
this closed common cube has been proved.

The existing genuine all-space ContDiff theorem is retained at every
finite and infinite order. No uniform derivative-size bound, prime-source
Siegel--Walfisz licence, Part 3 estimate or spectral supplier is asserted.
-/

namespace ImbalancedChen.P4BSmoothProfileCommonCompactSupport

noncomputable section

open Set
open scoped BigOperators
open Classical
open ImbalancedChen.P4B
open ImbalancedChen.P4BLabelledLogGeometry
open ImbalancedChen.P4BOuterRampRoughness

/-- Actual full-plane nonzero smooth support supplies its own margins.
There is no prime tuple, integer factor or sampled-point premise. -/
theorem smoothPhysicalProfile_nonzero_margin_support
    {b T width : ℝ} {N : ℕ} (hwidth : 0 < width)
    {v : Fin 2 → ℝ} (hnonzero : smoothPhysicalProfile b N T width v ≠ 0) :
    ∀ i : Fin 4, -width < smoothPhysicalProfileMargin b N T v i := by
  intro i
  apply smoothGateUpperStep_nonzero_support hwidth
  intro hzero
  apply hnonzero
  exact Finset.prod_eq_zero (Finset.mem_univ i) hzero

/-- The first three full-plane profile margins are the exact normalized
affine margins. Only the last product wall has the log N physical scale. -/
theorem smoothPhysicalProfileMargin_eq_original_of_ne_upper
    (b T : ℝ) (N : ℕ) (v : Fin 2 → ℝ) {i : Fin 4} (hi : i ≠ 3) :
    smoothPhysicalProfileMargin b N T v i =
      actualPairMargins b (Real.log T / Real.log (N : ℝ)) v i := by
  simp only [smoothPhysicalProfileMargin, physicalProductWallScale, if_neg hi, one_mul]

/-- Nonzero continuous profile has the same proved rough-coordinate
geometry, derived on the entire plane before selecting any arithmetic point. -/
theorem smoothPhysicalProfile_nonzero_coordinates_above_theta
    {b kappa width theta : ℝ} {N : ℕ} (hb : 0 < b) (hN : 2 ≤ N)
    (hwidth : 0 < width) (hgap : 2 * width ≤ baseline b kappa - theta)
    {v : Fin 2 → ℝ}
    (hnonzero : smoothPhysicalProfile b N
      (manuscriptHalfProductCutoff kappa N) width v ≠ 0) :
    theta < v 0 ∧ theta < v 1 := by
  have hsoft := smoothPhysicalProfile_nonzero_margin_support hwidth hnonzero
  have horder := hsoft (0 : Fin 4)
  have hbalance := hsoft (1 : Fin 4)
  have hlower := hsoft (2 : Fin 4)
  rw [smoothPhysicalProfileMargin_eq_original_of_ne_upper b _ N v
    (by decide : (0 : Fin 4) ≠ 3)] at horder
  rw [smoothPhysicalProfileMargin_eq_original_of_ne_upper b _ N v
    (by decide : (1 : Fin 4) ≠ 3)] at hbalance
  rw [smoothPhysicalProfileMargin_eq_original_of_ne_upper b _ N v
    (by decide : (2 : Fin 4) ≠ 3)] at hlower
  change -width < v 1 - v 0 at horder
  change -width < v 0 - b * v 1 at hbalance
  change -width < v 0 + v 1 -
    Real.log (manuscriptHalfProductCutoff kappa N) / Real.log (N : ℝ) at hlower
  have hcutoff := manuscript_log_cutoff_ratio_ge (kappa := kappa) hN
  exact relaxed_three_margins_above_theta hb hwidth.le horder hbalance
    (by linarith only [hlower, hcutoff]) hgap

/-- The true physical upper margin bounds the sum of continuous log
coordinates. This identity does not assert a power-sized product shell. -/
theorem smoothPhysicalProfile_nonzero_coordinate_sum_lt
    {b T width : ℝ} {N : ℕ} (hN : 2 ≤ N) (hwidth : 0 < width)
    {v : Fin 2 → ℝ} (hnonzero : smoothPhysicalProfile b N T width v ≠ 0) :
    v 0 + v 1 < 1 + width / Real.log (N : ℝ) := by
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hupper := smoothPhysicalProfile_nonzero_margin_support hwidth hnonzero (3 : Fin 4)
  change -width < Real.log (N : ℝ) * (1 - v 0 - v 1) at hupper
  have hmul : (v 0 + v 1 - 1) * Real.log (N : ℝ) < width := by
    nlinarith only [hupper]
  have hquot : v 0 + v 1 - 1 < width / Real.log (N : ℝ) :=
    (lt_div_iff₀ hlog).mpr hmul
  linarith only [hquot]

/-- A fixed positive width has an N-independent upper coordinate wall. -/
def commonUpper (width : ℝ) : ℝ := 1 + width / Real.log 2

theorem width_div_log_nat_le_log_two
    {width : ℝ} {N : ℕ} (hwidth : 0 ≤ width) (hN : 2 ≤ N) :
    width / Real.log (N : ℝ) ≤ width / Real.log 2 := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  have htwoOne : (1 : ℝ) < 2 := by norm_num
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact div_le_div_of_nonneg_left hwidth (Real.log_pos htwoOne)
    (Real.log_le_log htwo hNreal)

/-- Actual nonzero full-plane profile coordinates lie strictly inside one
fixed cube, uniformly over every N>=2. Parameters precede the varying N. -/
theorem smoothPhysicalProfile_nonzero_coordinates_bounds
    {b kappa width theta : ℝ} {N : ℕ} (hb : 0 < b) (htheta : 0 < theta)
    (hN : 2 ≤ N) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - theta)
    {v : Fin 2 → ℝ}
    (hnonzero : smoothPhysicalProfile b N
      (manuscriptHalfProductCutoff kappa N) width v ≠ 0) :
    ∀ i : Fin 2, theta < v i ∧ v i < 1 + width / Real.log 2 := by
  obtain ⟨hx, hy⟩ := smoothPhysicalProfile_nonzero_coordinates_above_theta
    hb hN hwidth hgap hnonzero
  have hsum := smoothPhysicalProfile_nonzero_coordinate_sum_lt hN hwidth hnonzero
  have hratio := width_div_log_nat_le_log_two hwidth.le hN
  have hx0 : 0 < v 0 := htheta.trans hx
  have hy0 : 0 < v 1 := htheta.trans hy
  intro i
  fin_cases i
  · exact ⟨hx, by linarith only [hsum, hratio, hy0]⟩
  · exact ⟨hy, by linarith only [hsum, hratio, hx0]⟩

/-- One genuine closed cube on the full plane. Its definition has no N. -/
def commonCube (theta width : ℝ) : Set (Fin 2 → ℝ) :=
  Icc (fun _ => theta) (fun _ => commonUpper width)

/-- Pinned native Pi-interval compactness applies directly to this cube. -/
theorem isCompact_commonCube (theta width : ℝ) : IsCompact (commonCube theta width) := by
  exact isCompact_Icc

theorem isClosed_commonCube (theta width : ℝ) : IsClosed (commonCube theta width) :=
  (isCompact_commonCube theta width).isClosed

theorem support_smoothPhysicalProfile_subset_commonCube
    {b kappa width theta : ℝ} {N : ℕ} (hb : 0 < b) (htheta : 0 < theta)
    (hN : 2 ≤ N) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - theta) :
    Function.support (smoothPhysicalProfile b N
      (manuscriptHalfProductCutoff kappa N) width) ⊆ commonCube theta width := by
  intro v hv
  have hbound := smoothPhysicalProfile_nonzero_coordinates_bounds
    hb htheta hN hwidth hgap hv
  exact ⟨fun i => (hbound i).1.le, fun i => (hbound i).2.le⟩

/-- Topological support includes closure points, which stay in the SAME
closed common cube. No N-dependent enlargement is made at closure. -/
theorem tsupport_smoothPhysicalProfile_subset_commonCube
    {b kappa width theta : ℝ} {N : ℕ} (hb : 0 < b) (htheta : 0 < theta)
    (hN : 2 ≤ N) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - theta) :
    tsupport (smoothPhysicalProfile b N
      (manuscriptHalfProductCutoff kappa N) width) ⊆ commonCube theta width := by
  exact closure_minimal
    (support_smoothPhysicalProfile_subset_commonCube hb htheta hN hwidth hgap)
    (isClosed_commonCube theta width)

/-- The actual full-plane smooth function has compact topological support. -/
theorem hasCompactSupport_smoothPhysicalProfile
    {b kappa width theta : ℝ} {N : ℕ} (hb : 0 < b) (htheta : 0 < theta)
    (hN : 2 ≤ N) (hwidth : 0 < width)
    (hgap : 2 * width ≤ baseline b kappa - theta) :
    HasCompactSupport (smoothPhysicalProfile b N
      (manuscriptHalfProductCutoff kappa N) width) := by
  apply (isCompact_commonCube theta width).of_isClosed_subset isClosed_closure
  exact tsupport_smoothPhysicalProfile_subset_commonCube hb htheta hN hwidth hgap

/-- A concrete common compact set is fixed BEFORE all targets and all
differentiability orders. This is a genuine smooth compact test family
prerequisite, with no assertion of uniform derivative sizes or P3 licensing. -/
theorem common_compact_support_and_smoothness
    {b kappa width theta : ℝ} (hb : 0 < b) (htheta : 0 < theta)
    (hwidth : 0 < width) (hgap : 2 * width ≤ baseline b kappa - theta) :
    IsCompact (commonCube theta width) ∧ ∀ N : ℕ, 2 ≤ N →
      tsupport (smoothPhysicalProfile b N (manuscriptHalfProductCutoff kappa N) width) ⊆
          commonCube theta width ∧
      HasCompactSupport (smoothPhysicalProfile b N (manuscriptHalfProductCutoff kappa N) width) ∧
      (∀ n : ℕ∞, ContDiff ℝ n
        (smoothPhysicalProfile b N (manuscriptHalfProductCutoff kappa N) width)) := by
  refine ⟨isCompact_commonCube theta width, ?_⟩
  intro N hN
  exact ⟨tsupport_smoothPhysicalProfile_subset_commonCube hb htheta hN hwidth hgap,
    hasCompactSupport_smoothPhysicalProfile hb htheta hN hwidth hgap,
    fun n => contDiff_smoothPhysicalProfile b N (manuscriptHalfProductCutoff kappa N) width⟩

end

end ImbalancedChen.P4BSmoothProfileCommonCompactSupport
