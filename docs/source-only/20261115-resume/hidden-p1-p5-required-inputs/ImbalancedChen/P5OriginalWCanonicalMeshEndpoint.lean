import ImbalancedChen.P5PresievedRoughSmoothCover
import ImbalancedChen.P5OriginalNearCapRealEndpointGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The ORIGINAL canonical rough word, with its literal half-open fine-mesh
owner, has one fixed upper vector on that cell. All positive affine
upper-prefix rows survive inflation by a fixed number of mesh steps.
The cell is chosen before the W group run and before any signed sum.
This is the genuine rough endpoint construction, not a tuple-specific
completedBins witness. Arithmetic wall points remain in their cells.
-/
namespace ImbalancedChen.P5Z.OriginalWCanonicalMeshEndpoint
noncomputable section
open Classical Set
open scoped BigOperators
open PresievedRoughSlotAffineGates PresievedRoughGateMeshReserve
open PresievedRoughSmoothCover OriginalPresievedRoughPrimeSlots
open JointPresievedSlotAffineRealization

/-- Every coordinate of a fixed upper corner costs at most one mesh step
above its actual point, including a point exactly on a lower grid face. -/
theorem mesh_upper_le_point_add_step {r n : ℕ} {a b : ℝ}
    {j : Grid r n} {y : Fin r → ℝ}
    (hy : y ∈ cell a b n j) (i : Fin r) :
    logPrimeMeshHi a b n j i ≤ y i + logPrimeMeshStep a b n := by
  have hlo := (mem_logPrimeMeshCell.mp hy i).1
  rw [logPrimeMeshHi_eq_lo_add_step]
  linarith

/-- The same fixed upper corner is antitone when an actual ordered rough
word owns the half-open cell. The upper labels need not be strictly apart. -/
theorem mesh_upper_antitone {r n : ℕ} {a b : ℝ} (hab : a < b)
    {j : Grid r n} {y : Fin r → ℝ}
    (hy : y ∈ cell a b n j) (hanti : StrictAnti y) :
    Antitone (logPrimeMeshHi a b n j) := by
  intro i k hik
  by_cases hEq : i = k
  · subst k
    exact le_rfl
  have hik' : i < k := lt_of_le_of_ne hik hEq
  by_contra hn
  have hindex : (j i).val < (j k).val := by
    by_contra hnot
    have hki : (j k).val ≤ (j i).val := Nat.le_of_not_gt hnot
    exact hn (logPrimeMeshPoint_mono hab.le n (Nat.succ_le_succ hki))
  have hsep : logPrimeMeshHi a b n j i ≤ logPrimeMeshLo a b n j k :=
    logPrimeMeshPoint_mono hab.le n (Nat.succ_le_of_lt hindex)
  have hiy := (mem_logPrimeMeshCell.mp hy i).2
  have hky := (mem_logPrimeMeshCell.mp hy k).1
  have hdec := hanti hik'
  linarith

/-- Actual strict total and every original even-indexed cubic prefix row
hold at the single fixed upper corner with a (r+3)-step inflation. -/
theorem mesh_upper_original_gates {r n : ℕ} {a b ell width : ℝ}
    {j : Grid r n} {y : Fin r → ℝ}
    (hab : a < b) (hy : y ∈ cell a b n j) (hregion : y ∈ region r ell)
    (hstep : ((r : ℝ) + 3) * logPrimeMeshStep a b n ≤ width) :
    (∑ i : Fin r, logPrimeMeshHi a b n j i) < ell + width ∧
      ∀ i : Fin r, Even i.val →
        cube (logPrimeMeshHi a b n j) i < ell + width := by
  let s := logPrimeMeshStep a b n
  let v := logPrimeMeshHi a b n j
  have hcoord (i : Fin r) : v i ≤ y i + s := mesh_upper_le_point_add_step hy i
  have htotal : (∑ i : Fin r, v i) ≤ (∑ i : Fin r, y i) + r * s := by
    calc
      _ ≤ ∑ i : Fin r, (y i + s) := Finset.sum_le_sum (fun i _ => hcoord i)
      _ = (∑ i : Fin r, y i) + r * s := by simp [Finset.sum_add_distrib]
  have hs : 0 ≤ s := (logPrimeMeshStep_pos hab n).le
  have hrs : (r : ℝ) * s ≤ width := by nlinarith
  refine ⟨lt_of_le_of_lt htotal (by linarith [hregion.1]), ?_⟩
  intro i hi
  have hpre : prefix v i ≤ prefix y i + r * s := by
    unfold prefix
    have hh : (∑ j : Fin r with j.val < i.val, v j) ≤
        ∑ j : Fin r with j.val < i.val, (y j + s) :=
      Finset.sum_le_sum (fun j _ => hcoord j)
    have hcard : ((Finset.univ.filter (fun j : Fin r => j.val < i.val)).card : ℝ) ≤ r := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hh
    nlinarith
  have hcube : cube v i ≤ cube y i + ((r : ℝ) + 3) * s := by
    unfold cube
    linarith [hcoord i]
  exact lt_of_le_of_lt hcube (by linarith [hregion.2 i hi])

/-- An actual prime at this fixed label is no larger than the physical
N-power upper endpoint used by the W completion run. -/
theorem prime_le_mesh_upper {r N n : ℕ} (hN : 1 < N)
    {a b : ℝ} {j : Grid r n} (p : Fin r → ℕ)
    (hp : ∀ i, 0 < p i)
    (hy : actualPrimeTupleLog N p ∈ cell a b n j) (i : Fin r) :
    (p i : ℝ) ≤ (N : ℝ) ^ (logPrimeMeshHi a b n j i) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hpow := actualPrimeTupleLog_rpow hN p hp i
  rw [← hpow]
  exact Real.rpow_le_rpow_of_exponent_le hn.le (mem_logPrimeMeshCell.mp hy i).2.le

/-- The late-slot condition is a fixed-cell inequality. The W native
cutoff-to-third-prefix comparison supplies `hlate`. -/
theorem mesh_upper_late {r n : ℕ} {a b u2 : ℝ}
    (hab : a < b) {j : Grid r n} (hlate : b ≤ u2) :
    ∀ i, logPrimeMeshHi a b n j i ≤ u2 := by
  intro i
  exact (logPrimeMeshLoHi_bounds hab n j i).2.2.trans hlate

/-- The literal canonical rough word is placed in one fixed mesh cell;
its endpoint tests use only that cell and the chosen width. The `j` here
may be a wall cell: no arithmetic wall point is erased. -/
theorem canonical_rough_fixed_endpoint {N cap d n : ℕ} (hN : 1 < N)
    (rho zeta ell width : ℝ) (hrho : 0 ≤ rho) (hcut : rho < zeta)
    (hL : 1 < (N : ℝ) ^ ell)
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd ((N : ℝ) ^ ell)) N cap
      ((N : ℝ) ^ rho) ((N : ℝ) ^ zeta))
    (hstep : (((canonicalSlots N cap ((N : ℝ) ^ rho)
      ((N : ℝ) ^ zeta) d).length : ℝ) + 3) *
      logPrimeMeshStep rho zeta n ≤ width) :
    let ps := canonicalSlots N cap ((N : ℝ) ^ rho) ((N : ℝ) ^ zeta) d
    let y := actualPrimeTupleLog N (slotVector ps)
    ∃ j : Grid ps.length n,
      y ∈ cell rho zeta n j ∧
      (∀ i, 0 ≤ logPrimeMeshHi rho zeta n j i) ∧
      Antitone (logPrimeMeshHi rho zeta n j) ∧
      (∑ i, logPrimeMeshHi rho zeta n j i) < ell + width ∧
      (∀ i, Even i.val → cube (logPrimeMeshHi rho zeta n j) i < ell + width) := by
  let ps := canonicalSlots N cap ((N : ℝ) ^ rho) ((N : ℝ) ^ zeta) d
  let y := actualPrimeTupleLog N (slotVector ps)
  have hp := retained_rough_point hN rho zeta ell hL hd
  obtain ⟨j,hj⟩ := exists_logPrimeMeshCell rho zeta n hp.1
  have hreg : y ∈ region ps.length ell := (roughRegion_dictionary ell y).mp hp.2 |>.1
  have hanti : StrictAnti y := (roughRegion_dictionary ell y).mp hp.2 |>.2
  have hg := mesh_upper_original_gates hcut hj hreg hstep
  refine ⟨j,hj,?_,mesh_upper_antitone hcut hj hanti,hg.1,hg.2⟩
  intro i
  have hlo := (logPrimeMeshLoHi_bounds hcut n j i).1
  have hhi := (logPrimeMeshLoHi_bounds hcut n j i).2.1
  linarith

end
end ImbalancedChen.P5Z.OriginalWCanonicalMeshEndpoint
