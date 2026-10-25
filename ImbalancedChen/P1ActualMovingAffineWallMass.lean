import ImbalancedChen.ActualPrimeBoxMass
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

Exact affine hyperplanes can contain arithmetic prime atoms. We retain
those atoms and estimate their mass uniformly in an arbitrary wall height.
Choose a nonzero coefficient coordinate j. Projection away from j is
injective on the exact wall, since the wall equality determines log(p_j),
and the original positive-target logarithmic dictionary determines p_j.
The omitted weight is at most 1/(N^(a_j)-1). The remaining sum is bounded
by the actual target-deleted prime box mass, whose product limit is already
proved from PNT/Mertens. Thus the exact wall mass tends to zero even when
its real height is an arbitrary function of N. No fixed-wall strip limit,
Lebesgue atom deletion, or desired prime-mean premise is used.
-/

namespace ImbalancedChen.P1ActualMovingAffineWallMass

noncomputable section
open scoped Classical BigOperators Topology
open Filter

def tupleWeight {d : ℕ} (p : Fin d → ℕ) : ℝ :=
  ∏ i, 1 / ((p i : ℝ)-1)

def affineValue {d : ℕ} (v x : Fin d → ℝ) : ℝ := ∑ i, v i*x i

def wallTuples {d : ℕ} (N : ℕ) (a b v : Fin d → ℝ) (c : ℝ) :
    Finset (Fin d → ℕ) :=
  (actualPrimeBoxTuples N a b).filter
    (fun p => affineValue v (actualPrimeTupleLog N p) = c)

def wallMass {d : ℕ} (N : ℕ) (a b v : Fin d → ℝ) (c : ℝ) : ℝ :=
  ∑ p ∈ wallTuples N a b v c, tupleWeight p

theorem wallMass_nonneg {d : ℕ} (N : ℕ) (a b v : Fin d → ℝ) (c : ℝ) :
    0 ≤ wallMass N a b v c := by
  apply Finset.sum_nonneg
  intro p hp
  exact actualPrimeBoxWeight_nonneg (Finset.mem_filter.mp hp).1

/-- Dropping a coordinate preserves each original target exclusion and
the exact endpoint convention of every remaining prime interval. -/
theorem removeNth_mem_box {k N : ℕ} {a b : Fin (k+1) → ℝ}
    (j : Fin (k+1)) {p : Fin (k+1) → ℕ} (hp : p ∈ actualPrimeBoxTuples N a b) :
    j.removeNth p ∈ actualPrimeBoxTuples N (j.removeNth a) (j.removeNth b) := by
  apply mem_actualPrimeBoxTuples_iff.mpr
  intro i
  exact mem_actualPrimeBoxTuples_iff.mp hp (j.succAbove i)

theorem tupleWeight_removeNth {k : ℕ} (j : Fin (k+1)) (p : Fin (k+1) → ℕ) :
    tupleWeight p = (1 / ((p j : ℝ)-1))*tupleWeight (j.removeNth p) := by
  simpa only [tupleWeight,Fin.removeNth] using
    (Fin.mul_prod_removeNth j (fun i => (1 : ℝ)/((p i : ℝ)-1))).symm

/-- The exact affine wall has at most one prime completion over each
remaining tuple. The moving height c is unrestricted. -/
theorem wall_removeNth_injOn {k N : ℕ} {a b v : Fin (k+1) → ℝ}
    (hN : 1 < N) (j : Fin (k+1)) (hv : v j ≠ 0) (c : ℝ) :
    Set.InjOn (j.removeNth : (Fin (k+1) → ℕ) → (Fin k → ℕ))
      (wallTuples N a b v c) := by
  intro p hp q hq hdrop
  obtain ⟨hpbox,hpwall⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqbox,hqwall⟩ := Finset.mem_filter.mp hq
  have hpPos : ∀ i, 0 < p i := fun i => (mem_actualPrimeBoxTuples_iff.mp hpbox i).1.pos
  have hqPos : ∀ i, 0 < q i := fun i => (mem_actualPrimeBoxTuples_iff.mp hqbox i).1.pos
  have hrest :
      (∑ i : Fin k, v (j.succAbove i)*actualPrimeTupleLog N p (j.succAbove i)) =
      ∑ i : Fin k, v (j.succAbove i)*actualPrimeTupleLog N q (j.succAbove i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have he := congrFun hdrop i
    change p (j.succAbove i) = q (j.succAbove i) at he
    simp only [actualPrimeTupleLog,he]
  have hpsplit := Fin.add_sum_removeNth j
    (fun i => v i*actualPrimeTupleLog N p i)
  have hqsplit := Fin.add_sum_removeNth j
    (fun i => v i*actualPrimeTupleLog N q i)
  change v j*actualPrimeTupleLog N p j +
      (∑ i : Fin k, v (j.succAbove i)*actualPrimeTupleLog N p (j.succAbove i)) =
      affineValue v (actualPrimeTupleLog N p) at hpsplit
  change v j*actualPrimeTupleLog N q j +
      (∑ i : Fin k, v (j.succAbove i)*actualPrimeTupleLog N q (j.succAbove i)) =
      affineValue v (actualPrimeTupleLog N q) at hqsplit
  have hmul : v j*actualPrimeTupleLog N p j = v j*actualPrimeTupleLog N q j := by
    linarith
  have hjlog := mul_left_cancel₀ hv hmul
  have hjR : (p j : ℝ) = (q j : ℝ) := by
    calc
      (p j : ℝ) = (N : ℝ)^(actualPrimeTupleLog N p j) :=
        (actualPrimeTupleLog_rpow hN p hpPos j).symm
      _ = (N : ℝ)^(actualPrimeTupleLog N q j) := by rw [hjlog]
      _ = (q j : ℝ) := actualPrimeTupleLog_rpow hN q hqPos j
  have hj : p j = q j := by exact_mod_cast hjR
  calc
    p = j.insertNth (p j) (j.removeNth p) := (Fin.insertNth_self_removeNth j p).symm
    _ = j.insertNth (q j) (j.removeNth q) := by rw [hj,hdrop]
    _ = q := Fin.insertNth_self_removeNth j q

/-- Exact finite arithmetic bound. The right side is independent of the
wall height. There is no loss of target-linked prime deletion. -/
theorem wallMass_le {k N : ℕ} {a b v : Fin (k+1) → ℝ}
    (hN : 1 < N) (j : Fin (k+1)) (hv : v j ≠ 0)
    (hA : 1 < (N : ℝ)^(a j)) (c : ℝ) :
    wallMass N a b v c ≤
      (1/((N : ℝ)^(a j)-1)) *
        ∏ i : Fin k, actualPrimeReciprocalMass N (a (j.succAbove i)) (b (j.succAbove i)) := by
  let S := wallTuples N a b v c
  let T := actualPrimeBoxTuples N (j.removeNth a) (j.removeNth b)
  let delta : ℝ := 1/((N : ℝ)^(a j)-1)
  have hd : 0 ≤ delta := (one_div_pos.mpr (sub_pos.mpr hA)).le
  have hsub : S.image j.removeNth ⊆ T := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact removeNth_mem_box j (Finset.mem_filter.mp hp).1
  have hweight : ∀ p ∈ S, tupleWeight p ≤ delta*tupleWeight (j.removeNth p) := by
    intro p hp
    have hpbox := (Finset.mem_filter.mp hp).1
    have hpi := mem_actualPrimeBoxTuples_iff.mp hpbox j
    have hden : (N : ℝ)^(a j)-1 ≤ (p j : ℝ)-1 := by linarith [hpi.2.2.1]
    have hsingle : 1/((p j : ℝ)-1) ≤ delta :=
      div_le_div_of_nonneg_left zero_le_one (sub_pos.mpr hA) hden
    rw [tupleWeight_removeNth j p]
    exact mul_le_mul_of_nonneg_right hsingle
      (actualPrimeBoxWeight_nonneg (removeNth_mem_box j hpbox))
  calc
    wallMass N a b v c ≤ ∑ p ∈ S, delta*tupleWeight (j.removeNth p) :=
      Finset.sum_le_sum hweight
    _ = delta*(∑ p ∈ S, tupleWeight (j.removeNth p)) := by rw [Finset.mul_sum]
    _ = delta*(∑ q ∈ S.image j.removeNth, tupleWeight q) := by
      congr 1
      exact (Finset.sum_image (wall_removeNth_injOn hN j hv c)).symm
    _ ≤ delta*actualPrimeBoxMass N (j.removeNth a) (j.removeNth b) := by
      apply mul_le_mul_of_nonneg_left _ hd
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro q hq hnot
      exact actualPrimeBoxWeight_nonneg hq
    _ = _ := by rw [actualPrimeBoxMass_eq_prod]; rfl

theorem tendsto_wallEnvelope_zero {k : ℕ} (a b : Fin (k+1) → ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i) (j : Fin (k+1)) :
    Tendsto (fun N : ℕ =>
      (1/((N : ℝ)^(a j)-1)) *
        ∏ i : Fin k, actualPrimeReciprocalMass N (a (j.succAbove i)) (b (j.succAbove i)))
      atTop (𝓝 0) := by
  have hpower : Tendsto (fun N : ℕ => (N : ℝ)^(a j)) atTop atTop :=
    (tendsto_rpow_atTop (ha j)).comp tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun N : ℕ => (N : ℝ)^(a j)-1) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right _ (-1 : ℝ) hpower
  have hinv : Tendsto (fun N : ℕ => 1/((N : ℝ)^(a j)-1)) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hden
  have hbox := tendsto_actualPrimeBoxMass (j.removeNth a) (j.removeNth b)
    (fun i => ha (j.succAbove i)) (fun i => hab (j.succAbove i))
  rw [show (fun N : ℕ => actualPrimeBoxMass N (j.removeNth a) (j.removeNth b)) =
      (fun N => ∏ i : Fin k,
        actualPrimeReciprocalMass N (a (j.succAbove i)) (b (j.succAbove i))) from by
        funext N; exact actualPrimeBoxMass_eq_prod N _ _] at hbox
  simpa only [zero_mul] using hinv.mul hbox

/-- One threshold works simultaneously for every real wall height. -/
theorem exists_wallMass_uniform_threshold {k : ℕ}
    (a b v : Fin (k+1) → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (j : Fin (k+1)) (hv : v j ≠ 0) (eps : ℝ) (heps : 0 < eps) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ c : ℝ, wallMass N a b v c < eps := by
  have henvelope := (tendsto_wallEnvelope_zero a b ha hab j).eventually (gt_mem_nhds heps)
  obtain ⟨M,hM⟩ := eventually_atTop.mp henvelope
  refine ⟨max 2 M,le_max_left _ _,?_⟩
  intro N hN c
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hnR : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact (wallMass_le (by omega) j hv (Real.one_lt_rpow hnR (ha j)) c).trans_lt
    (hM N ((le_max_right _ _).trans hN))

/-- Arbitrary dependence of the wall height on N is permitted. -/
theorem tendsto_wallMass_moving {k : ℕ}
    (a b v : Fin (k+1) → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (j : Fin (k+1)) (hv : v j ≠ 0) (c : ℕ → ℝ) :
    Tendsto (fun N : ℕ => wallMass N a b v (c N)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_wallEnvelope_zero a b ha hab j)
  · exact Filter.Eventually.of_forall (fun N => wallMass_nonneg N a b v (c N))
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have hnR : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    exact wallMass_le (by omega) j hv (Real.one_lt_rpow hnR (ha j)) (c N)

theorem exists_nonzero_coordinate {d : ℕ} {v : Fin d → ℝ} (hv : v ≠ 0) :
    ∃ j, v j ≠ 0 := by
  by_contra h
  apply hv
  funext j
  by_contra hj
  exact h ⟨j,hj⟩

theorem tendsto_wallMass_moving_of_ne_zero {k : ℕ}
    (a b v : Fin (k+1) → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (hv : v ≠ 0) (c : ℕ → ℝ) :
    Tendsto (fun N : ℕ => wallMass N a b v (c N)) atTop (𝓝 0) := by
  obtain ⟨j,hj⟩ := exists_nonzero_coordinate hv
  exact tendsto_wallMass_moving a b v ha hab j hj c

/-- Coefficients of an arbitrary continuous real linear form. -/
def linearCoefficients {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] ℝ) : Fin d → ℝ :=
  fun j => L (Pi.single j 1)

theorem linear_apply_eq_affineValue {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] ℝ)
    (x : Fin d → ℝ) : L x = affineValue (linearCoefficients L) x := by
  have hx : x = ∑ j, x j • Pi.single j (1 : ℝ) := by
    ext i
    simp
  calc
    L x = L (∑ j, x j • Pi.single j (1 : ℝ)) := congrArg L hx
    _ = ∑ j, x j*L (Pi.single j 1) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [map_smul,smul_eq_mul]
    _ = affineValue (linearCoefficients L) x := by
      unfold affineValue linearCoefficients
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem linearCoefficients_ne_zero {d : ℕ} {L : (Fin d → ℝ) →L[ℝ] ℝ}
    (hL : L ≠ 0) : linearCoefficients L ≠ 0 := by
  intro hc
  apply hL
  ext x
  rw [linear_apply_eq_affineValue]
  simp [affineValue,hc]

def linearWallMass {d : ℕ} (N : ℕ) (a b : Fin d → ℝ)
    (L : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ) : ℝ :=
  ∑ p ∈ (actualPrimeBoxTuples N a b).filter
    (fun p => L (actualPrimeTupleLog N p) = c), tupleWeight p

theorem linearWallMass_eq {d : ℕ} (N : ℕ) (a b : Fin d → ℝ)
    (L : (Fin d → ℝ) →L[ℝ] ℝ) (c : ℝ) :
    linearWallMass N a b L c = wallMass N a b (linearCoefficients L) c := by
  simp only [linearWallMass,wallMass,wallTuples,linear_apply_eq_affineValue]

/-- General nonzero affine hyperplanes, with arbitrary moving height.
The box may have independent positive endpoints in every coordinate. -/
theorem tendsto_linearWallMass_moving {k : ℕ}
    (a b : Fin (k+1) → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (L : (Fin (k+1) → ℝ) →L[ℝ] ℝ) (hL : L ≠ 0) (c : ℕ → ℝ) :
    Tendsto (fun N : ℕ => linearWallMass N a b L (c N)) atTop (𝓝 0) := by
  simpa only [linearWallMass_eq] using
    tendsto_wallMass_moving_of_ne_zero a b (linearCoefficients L) ha hab
      (linearCoefficients_ne_zero hL) c

end
end ImbalancedChen.P1ActualMovingAffineWallMass
