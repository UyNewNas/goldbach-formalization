import ImbalancedChen.ActualPrimePolyhedralTestFunctions

/-!
# Actual prime mass in thin affine-wall strips

A continuous tent majorizes every closed strip at a fixed width. Its
true integral tends to zero because all nondegenerate walls are null.
The width is selected before the common arithmetic threshold.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators Topology
open MeasureTheory Filter Set

def primeAffineWallStrip {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (delta : ℝ) :
    Set (Fin d → ℝ) := {x | ∃ j, |L j x - c j| ≤ delta}

def affinePrimeWallMajorant {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (m : ℕ) (x : Fin d → ℝ) : ℝ :=
  ∑ j, affinePrimeClamp (2 - (m + 1 : ℝ) * |L j x - c j|)

theorem continuous_affinePrimeWallMajorant {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (m : ℕ) :
    Continuous (affinePrimeWallMajorant L c m) := by
  unfold affinePrimeWallMajorant
  apply continuous_finsetSum
  intro j _
  exact continuous_affinePrimeClamp.comp (continuous_const.sub
    (continuous_const.mul ((L j).continuous.sub continuous_const).abs))

theorem affinePrimeWallMajorant_bounds {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (m : ℕ) (x : Fin d → ℝ) :
    0 ≤ affinePrimeWallMajorant L c m x ∧ affinePrimeWallMajorant L c m x ≤ r := by
  refine ⟨Finset.sum_nonneg (fun j _ => (affinePrimeClamp_bounds _).1), ?_⟩
  calc
    _ ≤ ∑ _j : Fin r, (1 : ℝ) := Finset.sum_le_sum (fun j _ => (affinePrimeClamp_bounds _).2)
    _ = r := by simp

theorem affinePrimeWallMajorant_ge_one {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (m : ℕ) {x : Fin d → ℝ}
    (hx : x ∈ primeAffineWallStrip L c (1 / (m + 1 : ℝ))) :
    1 ≤ affinePrimeWallMajorant L c m x := by
  obtain ⟨j, hj⟩ := hx
  have hpos : (0 : ℝ) < m + 1 := by positivity
  have hmul : (m + 1 : ℝ) * |L j x - c j| ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hj hpos.le
    simpa only [mul_one_div_cancel hpos.ne'] using h
  have heq : affinePrimeClamp (2 - (m + 1 : ℝ) * |L j x - c j|) = 1 :=
    affinePrimeClamp_eq_one (by linarith)
  rw [← heq]
  unfold affinePrimeWallMajorant
  exact Finset.single_le_sum
    (f := fun i : Fin r => affinePrimeClamp (2 - (m + 1 : ℝ) * |L i x - c i|))
    (fun i _ => (affinePrimeClamp_bounds _).1) (Finset.mem_univ j)

theorem tendsto_affinePrimeWallMajorant {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (x : Fin d → ℝ) (hx : ∀ j, L j x ≠ c j) :
    Tendsto (fun m => affinePrimeWallMajorant L c m x) atTop (𝓝 0) := by
  have ht : ∀ j : Fin r, Tendsto (fun m : ℕ =>
      affinePrimeClamp (2 - (m + 1 : ℝ) * |L j x - c j|)) atTop (𝓝 0) := by
    intro j
    have hpos : 0 < |L j x - c j| := abs_pos.mpr (sub_ne_zero.mpr (hx j))
    have hg : Tendsto (fun m : ℕ => (m + 1 : ℝ) * |L j x - c j|) atTop atTop :=
      (tendsto_atTop_add_const_right _ (1 : ℝ) tendsto_natCast_atTop_atTop).atTop_mul_const hpos
    exact tendsto_const_nhds.congr' ((hg.eventually (eventually_ge_atTop (2 : ℝ))).mono
      (fun m hm => (affinePrimeClamp_eq_zero (sub_nonpos.mpr hm)).symm))
  simpa only [affinePrimeWallMajorant, Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.univ : Finset (Fin r)) (fun j _ => ht j)

theorem tendsto_integral_affinePrimeWallMajorant {d r : ℕ} {a b : ℝ}
    (ha : 0 < a)
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (hL : ∀ j, L j ≠ 0) :
    Tendsto (fun m => ∫ x in logPrimeBox (fun _ : Fin d => a) (fun _ => b),
      affinePrimeWallMajorant L c m x * ∏ i, 1 / x i) atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (logPrimeBox (fun _ : Fin d => a) (fun _ => b)))
    (fun x : Fin d → ℝ => (r : ℝ) * ∏ i, 1 / x i)
    (fun m => (integrableOn_logPrimeBox_test_cube ha _
      (continuous_affinePrimeWallMajorant L c m).continuousOn).aestronglyMeasurable)
    (integrableOn_logPrimeBox_const_mul_one_div (r : ℝ) _ _ (fun _ => ha))
    (fun m => by
      filter_upwards [ae_restrict_mem (measurableSet_logPrimeBox
        (fun _ : Fin d => a) (fun _ => b))] with x hx
      have hd : 0 ≤ ∏ i, 1 / x i := Finset.prod_nonneg (fun i _ =>
        (one_div_pos.mpr (ha.trans_le (mem_logPrimeBox.mp hx i).1)).le)
      have hb := affinePrimeWallMajorant_bounds L c m x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hb.1, abs_of_nonneg hd]
      exact mul_le_mul_of_nonneg_right hb.2 hd)
    (show ∀ᵐ x ∂volume.restrict (logPrimeBox (fun _ : Fin d => a) (fun _ => b)),
        Tendsto (fun m => affinePrimeWallMajorant L c m x * ∏ i, 1 / x i)
          atTop (𝓝 (0 : ℝ)) from by
      filter_upwards [ae_restrict_of_ae (ae_primeAffineGate_no_wall L c hL)] with x hx
      simpa only [zero_mul] using (tendsto_affinePrimeWallMajorant L c x hx).mul_const
        (∏ i, 1 / x i))
  simpa only [integral_zero] using ht

/-- Actual arithmetic mass in the union of the closed affine-wall strips.
The enumeration and target-exclusion conditions are unchanged. -/
def actualPrimeAffineWallStripMass {d r : ℕ} (N : ℕ) (a b : Fin d → ℝ)
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (delta : ℝ) : ℝ :=
  ∑ p ∈ (actualPrimeBoxTuples N a b).filter
    (fun p => actualPrimeTupleLog N p ∈ primeAffineWallStrip L c delta),
    ∏ i, 1 / ((p i : ℝ) - 1)

theorem actualPrimeAffineWallStripMass_le_majorant {d r : ℕ} (N : ℕ)
    (a b : Fin d → ℝ)
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (m : ℕ) :
    actualPrimeAffineWallStripMass N a b L c (1 / (m + 1 : ℝ)) ≤
      actualPrimeBoxTestSum N a b (affinePrimeWallMajorant L c m) := by
  unfold actualPrimeAffineWallStripMass actualPrimeBoxTestSum
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro p hp
  have hw := actualPrimeBoxWeight_nonneg hp
  by_cases hx : actualPrimeTupleLog N p ∈ primeAffineWallStrip L c (1 / (m + 1 : ℝ))
  · rw [if_pos hx]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (affinePrimeWallMajorant_ge_one L c m hx) hw
  · rw [if_neg hx]
    exact mul_nonneg hw (affinePrimeWallMajorant_bounds L c m _).1

/-- Given any reserve, first choose a positive fixed strip width and then
one threshold for every later target N. The finite gate family may be
empty; no even-target or tuple-ordering condition is needed. -/
theorem exists_actualPrimeAffineWallStrip_mass_lt {d r : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (hL : ∀ j, L j ≠ 0)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      actualPrimeAffineWallStripMass N (fun _ : Fin d => a) (fun _ => b) L c delta < eta := by
  obtain ⟨m, hm⟩ := ((tendsto_integral_affinePrimeWallMajorant ha L c hL).eventually
    (gt_mem_nhds (half_pos heta))).exists
  let I := ∫ x in logPrimeBox (fun _ : Fin d => a) (fun _ => b),
    affinePrimeWallMajorant L c m x * ∏ i, 1 / x i
  have hI : I < eta / 2 := hm
  have hactual : ∀ᶠ N : ℕ in atTop,
      actualPrimeBoxTestSum N (fun _ : Fin d => a) (fun _ => b)
        (affinePrimeWallMajorant L c m) < eta :=
    (tendsto_actualPrimeBoxTestSum_cube ha hab (affinePrimeWallMajorant L c m)
      (continuous_affinePrimeWallMajorant L c m).continuousOn).eventually
        (gt_mem_nhds (show I < eta by linarith))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hactual
  refine ⟨1 / (m + 1 : ℝ), by positivity, max 2 N₁, le_max_left _ _, ?_⟩
  intro N hN
  exact (actualPrimeAffineWallStripMass_le_majorant N _ _ L c m).trans_lt
    (hN₁ N ((le_max_right _ _).trans hN))

end

end ImbalancedChen
