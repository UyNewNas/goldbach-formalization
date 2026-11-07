import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Finite affine gates and continuous ramps

Nonzero real linear forms have genuinely null level sets. Finite products
of continuous scalar ramps approximate the strict intersection away from
those level sets. The empty gate family is allowed.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators Topology
open MeasureTheory Filter Set

def primeAffineGateRegion {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) :
    Set (Fin d → ℝ) := {x | ∀ j, L j x < c j}

theorem measurableSet_primeAffineGateRegion {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) :
    MeasurableSet (primeAffineGateRegion L c) := by
  simpa only [primeAffineGateRegion, ofPred_forall] using
    MeasurableSet.iInter (fun j => (isOpen_lt (L j).continuous
      (continuous_const : Continuous (fun _ : Fin d → ℝ => c j))).measurableSet)

/-- No null-wall assumption is supplied by the caller: nonzero linearity
proves that the actual affine level set is a proper affine subspace. -/
theorem affinePrimeWall_volume_zero {d : ℕ}
    (L : (Fin d → ℝ) →L[ℝ] ℝ) (hL : L ≠ 0) (c : ℝ) :
    volume {x | L x = c} = 0 := by
  let A : AffineSubspace ℝ (Fin d → ℝ) :=
    { carrier := {x | L x = c}
      smul_vsub_vadd_mem' := by
        intro t x y z hx hy hz
        change L (t • (x - y) + z) = c
        change L x = c at hx
        change L y = c at hy
        change L z = c at hz
        simp only [map_add, map_smul, map_sub, hx, hy, hz, sub_self, smul_zero, zero_add] }
  have hA : A ≠ ⊤ := by
    intro h
    have hall (x : Fin d → ℝ) : L x = c := by
      have hx : x ∈ A := by rw [h]; trivial
      exact hx
    have hc : c = 0 := by simpa using (hall 0).symm
    apply hL
    ext x
    simpa [hc] using hall x
  exact Measure.addHaar_affineSubspace volume A hA

theorem ae_primeAffineGate_no_wall {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (hL : ∀ j, L j ≠ 0) :
    ∀ᵐ x ∂volume, ∀ j, L j x ≠ c j := by
  apply ae_all_iff.mpr
  intro j
  rw [ae_iff]
  simpa only [not_not] using affinePrimeWall_volume_zero (L j) (hL j) (c j)

def affinePrimeClamp (t : ℝ) : ℝ := max 0 (min 1 t)

theorem continuous_affinePrimeClamp : Continuous affinePrimeClamp := by
  unfold affinePrimeClamp
  fun_prop

theorem affinePrimeClamp_bounds (t : ℝ) :
    0 ≤ affinePrimeClamp t ∧ affinePrimeClamp t ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem affinePrimeClamp_mono : Monotone affinePrimeClamp := by
  intro a b hab
  exact max_le_max le_rfl (min_le_min le_rfl hab)

theorem affinePrimeClamp_eq_zero {t : ℝ} (ht : t ≤ 0) : affinePrimeClamp t = 0 := by
  unfold affinePrimeClamp
  exact max_eq_left ((min_le_right _ _).trans ht)

theorem affinePrimeClamp_eq_one {t : ℝ} (ht : 1 ≤ t) : affinePrimeClamp t = 1 := by
  simp only [affinePrimeClamp, min_eq_left ht, max_eq_right zero_le_one]

def affinePrimeGateRamp {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (upper : Bool) (m : ℕ) (x : Fin d → ℝ) : ℝ :=
  ∏ j, affinePrimeClamp ((if upper then 1 else 0) + (m + 1 : ℝ) * (c j - L j x))

theorem continuous_affinePrimeGateRamp {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (upper : Bool) (m : ℕ) : Continuous (affinePrimeGateRamp L c upper m) := by
  unfold affinePrimeGateRamp
  exact continuous_finsetProd _ (fun j _ => continuous_affinePrimeClamp.comp
    (continuous_const.add (continuous_const.mul (continuous_const.sub (L j).continuous))))

theorem affinePrimeGateRamp_bounds {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (upper : Bool) (m : ℕ) (x : Fin d → ℝ) :
    0 ≤ affinePrimeGateRamp L c upper m x ∧ affinePrimeGateRamp L c upper m x ≤ 1 := by
  refine ⟨Finset.prod_nonneg (fun j _ => (affinePrimeClamp_bounds _).1), ?_⟩
  exact Finset.prod_le_one (fun j _ => (affinePrimeClamp_bounds _).1)
    (fun j _ => (affinePrimeClamp_bounds _).2)

theorem affinePrimeGateRamp_lower_le_upper {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (m : ℕ) (x : Fin d → ℝ) :
    affinePrimeGateRamp L c false m x ≤ affinePrimeGateRamp L c true m x := by
  apply Finset.prod_le_prod (fun j _ => (affinePrimeClamp_bounds _).1)
  intro j _
  apply affinePrimeClamp_mono
  simp

theorem affinePrimeGateRamp_lower_eq_zero {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (m : ℕ)
    {x : Fin d → ℝ} (hx : x ∉ primeAffineGateRegion L c) :
    affinePrimeGateRamp L c false m x = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, c j ≤ L j x := by
    simpa only [primeAffineGateRegion, mem_ofPred_eq, not_forall, not_lt] using hx
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  apply affinePrimeClamp_eq_zero
  simp only [Bool.false_eq_true, if_false, zero_add]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hj)

theorem affinePrimeGateRamp_upper_eq_one {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (m : ℕ)
    {x : Fin d → ℝ} (hx : x ∈ primeAffineGateRegion L c) :
    affinePrimeGateRamp L c true m x = 1 := by
  apply Finset.prod_eq_one
  intro j _
  apply affinePrimeClamp_eq_one
  simp only [if_true]
  have hpos : 0 ≤ (m + 1 : ℝ) * (c j - L j x) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr (hx j).le)
  linarith

theorem affinePrimeGateRamp_test_error {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (m : ℕ)
    (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    |(primeAffineGateRegion L c).indicator f x -
        f x * affinePrimeGateRamp L c false m x| ≤
      |f x| * (affinePrimeGateRamp L c true m x - affinePrimeGateRamp L c false m x) := by
  by_cases hx : x ∈ primeAffineGateRegion L c
  · rw [indicator_of_mem hx, affinePrimeGateRamp_upper_eq_one L c m hx]
    rw [show f x - f x * affinePrimeGateRamp L c false m x =
      f x * (1 - affinePrimeGateRamp L c false m x) by ring, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr (affinePrimeGateRamp_bounds L c false m x).2)]
  · rw [indicator_of_notMem hx, affinePrimeGateRamp_lower_eq_zero L c m hx]
    simp only [mul_zero, sub_zero, abs_zero]
    exact mul_nonneg (abs_nonneg _) (affinePrimeGateRamp_bounds L c true m x).1

private theorem tendsto_affinePrimeClamp {v : ℝ} (hv : v ≠ 0) (upper : Bool) :
    Tendsto (fun m : ℕ => affinePrimeClamp ((if upper then 1 else 0) + (m + 1 : ℝ) * v))
      atTop (𝓝 (if 0 < v then 1 else 0)) := by
  rcases lt_or_gt_of_ne hv with hvneg | hvpos
  · rw [if_neg (not_lt.mpr hvneg.le)]
    have ht : Tendsto (fun m : ℕ => (if upper then (1 : ℝ) else 0) + (m + 1 : ℝ) * v)
        atTop atBot := tendsto_atBot_add_const_left _ _
          ((tendsto_atTop_add_const_right _ (1 : ℝ) tendsto_natCast_atTop_atTop).atTop_mul_const_of_neg hvneg)
    exact tendsto_const_nhds.congr' ((ht.eventually (eventually_le_atBot (0 : ℝ))).mono
      (fun m hm => (affinePrimeClamp_eq_zero hm).symm))
  · rw [if_pos hvpos]
    have ht : Tendsto (fun m : ℕ => (if upper then (1 : ℝ) else 0) + (m + 1 : ℝ) * v)
        atTop atTop := tendsto_atTop_add_const_left _ _
          ((tendsto_atTop_add_const_right _ (1 : ℝ) tendsto_natCast_atTop_atTop).atTop_mul_const hvpos)
    exact tendsto_const_nhds.congr' ((ht.eventually (eventually_ge_atTop (1 : ℝ))).mono
      (fun m hm => (affinePrimeClamp_eq_one hm).symm))

theorem tendsto_affinePrimeGateRamp {d r : ℕ}
    (L : Fin r → (Fin d → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) (upper : Bool)
    (x : Fin d → ℝ) (hx : ∀ j, L j x ≠ c j) :
    Tendsto (fun m => affinePrimeGateRamp L c upper m x) atTop
      (𝓝 ((primeAffineGateRegion L c).indicator (fun _ => (1 : ℝ)) x)) := by
  have ht := tendsto_finsetProd (Finset.univ : Finset (Fin r))
    (fun j _ => tendsto_affinePrimeClamp (sub_ne_zero.mpr (hx j).symm) upper)
  have heq : (∏ j, if 0 < c j - L j x then (1 : ℝ) else 0) =
      (primeAffineGateRegion L c).indicator (fun _ => (1 : ℝ)) x := by
    by_cases h : x ∈ primeAffineGateRegion L c
    · rw [indicator_of_mem h]
      exact Finset.prod_eq_one (fun j _ => if_pos (sub_pos.mpr (h j)))
    · rw [indicator_of_notMem h]
      obtain ⟨j, hj⟩ : ∃ j, ¬ L j x < c j := by
        simpa only [primeAffineGateRegion, mem_ofPred_eq, not_forall] using h
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg (by simpa using hj))
  simpa only [affinePrimeGateRamp, heq] using ht

end

end ImbalancedChen
