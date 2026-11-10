import ImbalancedChen.P5SmoothChartHBDyadicPartition
import ImbalancedChen.P5OriginalHBMediumChartReserves

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- The manuscript psi support itself supplies the physical group window.
-- No R/128<=n or short/long branch conclusion is a primitive input.
namespace ImbalancedChen.P5Z.SmoothChartPhysicalHBBranch
noncomputable section
open Classical
open scoped BigOperators
open LiteralHeathBrownOccurrenceWords ActualRoughHeathBrownWords
open HBRightClosedDyadicRoles ActualHBDyadicOccurrenceFamily
open ActualHBDyadicProductWindow ActualHBMediumBranchPartition
open ActualHBMediumRoleSupports OriginalHBMediumChartReserves
open SmoothChartHBDyadicPartition

theorem smooth_group_support {psi : ℝ → ℂ} {R : ℝ} (hR : 0 < R)
    (hlo : ∀ t : ℝ, t < 1/2 → psi t = 0)
    (hhi : ∀ t : ℝ, 2 < t → psi t = 0) (w : ℕ → ℂ) {n : ℕ}
    (hw : chartWeight psi R w n ≠ 0) :
    R/2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*R := by
  have hp : psi ((n : ℝ)/R) ≠ 0 := by
    intro h
    exact hw (by simp [chartWeight,h])
  have hq : (1/2 : ℝ) ≤ (n : ℝ)/R :=
    le_of_not_gt (fun h => hp (hlo _ h))
  have hl := (le_div_iff₀ hR).mp hq
  exact ⟨by linarith,chart_support hR hhi w hw⟩

-- R/128 is derived from psi's R/2 floor and the actual at-most-six
-- occurrence inequality n<=64*prod(lower), including all unit atoms.
theorem active_smooth_rectangle {psi : ℝ → ℂ} {R z y : ℝ}
    (hR : 0 < R) (hz : 0 ≤ z)
    (hlo : ∀ t : ℝ, t < 1/2 → psi t = 0)
    (hhi : ∀ t : ℝ, 2 < t → psi t = 0)
    (w : ℕ → ℂ) {j n : ℕ} {bs : List Block}
    (hj : j ∈ Finset.range 3)
    (hactive : chartWeight psi R w n * blockCoefficient z y j n bs ≠ 0) :
    bs.length = 2*(j+1) ∧ bs.length ≤ 6 ∧
      R/2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*R ∧
      R/128 ≤ rawProduct bs ∧ rawProduct bs ≤ 2*R := by
  have hh := mul_ne_zero_iff.mp hactive
  have hs := smooth_group_support hR hlo hhi w hh.1
  have he := actual_block_product_window hz hh.2
  have h6 := actual_block_six_slot_window hz hj hh.2
  have hl : rawProduct bs ≤ (n : ℝ) := by exact_mod_cast h6.2.1
  have hu : (n : ℝ) ≤ 64*rawProduct bs := by exact_mod_cast h6.2.2
  exact ⟨he.1,h6.1,hs.1,hs.2,by linarith,hl.trans hs.2⟩

-- Explicit absorption of a fixed scale-comparison constant by a strict
-- exponent reserve. This is used for both medium endpoints and long U.
theorem scale_power_absorb {x X C a d : ℝ}
    (hx : 0 ≤ x) (hX : 0 < X) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hcompare : x ≤ C*X) (hreserve : C^a ≤ X^d) :
    x^a ≤ X^(a+d) := by
  calc
    x^a ≤ (C*X)^a := Real.rpow_le_rpow hx hcompare ha
    _ = C^a*X^a := Real.mul_rpow hC hX.le
    _ ≤ X^d*X^a := mul_le_mul_of_nonneg_right hreserve (Real.rpow_nonneg hX.le _)
    _ = X^(a+d) := by rw [← Real.rpow_add hX]; congr 1; ring

theorem original_to_local_medium {x X C zeta U : ℝ}
    (hx : 1 ≤ x) (hX : 1 ≤ X) (hC : 0 ≤ C) (hzeta : 0 ≤ zeta)
    (hxX : x ≤ C*X) (hXx : X ≤ C*x)
    (hlowerReserve : C^(2*zeta) ≤ X^zeta)
    (hupperReserve : C^(1/3+zeta/4) ≤ x^(zeta/4))
    (hU : originalLower X zeta ≤ U ∧ U ≤ originalUpper X zeta) :
    x^(2*zeta) ≤ U ∧ U ≤ x^(1/3+zeta/2) := by
  have hXp : 0 < X := by linarith
  have hxp : 0 < x := by linarith
  have hl := scale_power_absorb (by linarith : 0 ≤ x) hXp hC
    (by linarith : 0 ≤ 2*zeta) hxX hlowerReserve
  have hu := scale_power_absorb (by linarith : 0 ≤ X) hxp hC
    (by linarith : 0 ≤ (1/3+zeta/4 : ℝ)) hXx hupperReserve
  have hel : (2*zeta+zeta : ℝ) = 3*zeta := by ring
  have heu : (1/3+zeta/4+zeta/4 : ℝ) = 1/3+zeta/2 := by ring
  rw [hel] at hl
  rw [heu] at hu
  exact ⟨hl.trans hU.1,hU.2.trans hu⟩

-- The branch selector is fixed by the original block word. In the medium
-- case it supplies the actual integer coordinate and local length U.
-- In the Type I case it supplies one/two actual non-Mobius long roles.
theorem physical_original_branch_assignment
    {psi : ℝ → ℂ} {R z y X zeta a C x Cscale : ℝ}
    (hR : 0 < R) (hz : 0 ≤ z) (hy : 0 ≤ y)
    (hlo : ∀ t : ℝ, t < 1/2 → psi t = 0)
    (hhi : ∀ t : ℝ, 2 < t → psi t = 0)
    (hX : 1 ≤ X) (hx : 1 ≤ x) (hzeta : 0 ≤ zeta) (hC : 0 ≤ C)
    (hgroup : X^a ≤ R) (hcomplete : 2*R ≤ C*X) (hcube : y^3 = 2*R)
    (hshortGrowth : 8192 < X^(a-18*zeta))
    (hlongGrowth : 2*C < X^(3*zeta/4))
    (hA : 1 < originalLower X zeta)
    (hCscale : 0 ≤ Cscale) (hxX : x ≤ Cscale*X) (hXx : X ≤ Cscale*x)
    (hlowerReserve : Cscale^(2*zeta) ≤ X^zeta)
    (hupperReserve : Cscale^(1/3+zeta/4) ≤ x^(zeta/4))
    (w : ℕ → ℂ) {j n : ℕ} {bs : List Block}
    (hj : j ∈ Finset.range 3)
    (hactive : chartWeight psi R w n * blockCoefficient z y j n bs ≠ 0) :
    (∃ i : ℕ, firstMedium (originalLower X zeta) (originalUpper X zeta) bs = some i ∧
      ∃ ps ∈ factorTuples (2*(j+1)) n,
        assignedWeight z y (roles j) bs ps ≠ 0 ∧
        ∃ hi : i < bs.length, ∃ hp : i < ps.length,
          x^(2*zeta) ≤ (lower bs[i] : ℝ) ∧
          (lower bs[i] : ℝ) ≤ x^(1/3+zeta/2) ∧
          (lower bs[i] : ℝ) < (ps[i] : ℝ) ∧
          (ps[i] : ℝ) ≤ 2*(lower bs[i] : ℝ) ∧
          0 < ps[i] ∧ ps[i] ≤ n ∧
          (∀ p ∈ ps.take (j+1), (p : ℝ) ≤ y)) ∨
    (firstMedium (originalLower X zeta) (originalUpper X zeta) bs = none ∧
      ((longBlocks (originalUpper X zeta) bs).length = 1 ∨
        (longBlocks (originalUpper X zeta) bs).length = 2) ∧
      (∀ rb ∈ (roles j).zip bs,
        originalUpper X zeta < (lower rb.2 : ℝ) →
          rb.1 = .one ∨ rb.1 = .logarithm)) := by
  have hh := mul_ne_zero_iff.mp hactive
  have hs := smooth_group_support hR hlo hhi w hh.1
  have hdyadic : R/128 ≤ (n : ℝ) := by linarith
  have hnCX : (n : ℝ) ≤ C*X := hs.2.trans hcomplete
  have hRCX : R ≤ C*X := by linarith
  cases hsel : firstMedium (originalLower X zeta) (originalUpper X zeta) bs with
  | none =>
    have hb := original_actual_noMedium_from_chart hz hX hzeta hC hj hh.2
      hgroup hRCX hdyadic hnCX hy hcube hshortGrowth hlongGrowth hsel
    exact Or.inr ⟨hsel,hb.1,hb.2⟩
  | some i =>
    obtain ⟨ps,hps,ha,hi,hp,hm,hlt,hle,hpos,hpn,hcut⟩ :=
      actual_selected_medium_support hz hA hh.2 hsel
    have hlocal := original_to_local_medium hx hX hCscale hzeta hxX hXx
      hlowerReserve hupperReserve hm
    exact Or.inl ⟨i,hsel,ps,hps,ha,hi,hp,hlocal.1,hlocal.2,hlt,hle,hpos,hpn,hcut⟩

-- A long occurrence has a positive-power local length. Its integer
-- coordinate lower bound then follows from literal interval ownership.
theorem original_long_local_length {x X Cscale zeta U : ℝ}
    (hx : 1 ≤ x) (hX : 1 ≤ X) (hCscale : 0 ≤ Cscale)
    (hxX : x ≤ Cscale*X) (hreserve : Cscale^(1/3 : ℝ) ≤ X^(zeta/4))
    (hU : originalUpper X zeta < U) : x^(1/3 : ℝ) < U := by
  have h := scale_power_absorb (by linarith : 0 ≤ x)
    (by linarith : 0 < X) hCscale (by norm_num : (0 : ℝ) ≤ 1/3) hxX hreserve
  exact h.trans_lt hU

end
end ImbalancedChen.P5Z.SmoothChartPhysicalHBBranch
