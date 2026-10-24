import ImbalancedChen.Part3ActualFixedFeatureCountGeometry
import ImbalancedChen.Part3SignedDivisorDeletion
import ImbalancedChen.Part3FactorFiberDivisor
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED / NOT ACCEPTED -- 20261024z P3 continuation 4.
This module specializes existing actual geometry and physical-modulus APIs.
The old powers, ranges, signed residue and coprime center are unchanged.
The one uniform physical constant is 8, chosen before B,sigma,kappa,c0,d.
No RestrictedMediumTarget, distribution estimate or analytic budget is an input.
-/

namespace ImbalancedChen.Part3.ActualMovingResiduePolynomialBudget_20261024z
noncomputable section
open Classical
open scoped BigOperators
open GeneralDActivePairCountSourceOnly (factorCarrier_bounds)
open ActualFixedFeatureCountGeometrySourceOnly (actual_admissible_geometry)

theorem actual_scale_gt_one {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) : 1 < d.scale := by
  exact (Real.one_lt_exp_iff.mpr (Real.exp_pos (1 : ℝ))).trans hd.2.2.2.2.2.1

/-- Reuse the existing public geometry for U,Q1,Q2,Q3; V follows from UV=x. -/
theorem actual_parameters_le_scale {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma) :
    (1 ≤ d.U ∧ d.U ≤ d.scale) ∧ (1 ≤ d.V ∧ d.V ≤ d.scale) ∧
      (1 ≤ d.Q1 ∧ d.Q1 ≤ d.scale) ∧ (1 ≤ d.Q2 ∧ d.Q2 ≤ d.scale) ∧
        (1 ≤ d.Q3 ∧ d.Q3 ≤ d.scale) := by
  obtain ⟨_hx, hUx, hQ1x, hQ2x, hQ3x⟩ := actual_admissible_geometry hd hsigma
  have hVx : d.V ≤ d.scale := by
    change d.V ≤ d.U*d.V
    exact le_mul_of_one_le_left (zero_le_one.trans hd.2.1) hd.1
  exact ⟨⟨hd.1, hUx⟩, ⟨hd.2.1, hVx⟩, ⟨hd.2.2.1, hQ1x⟩,
    ⟨hd.2.2.2.1, hQ2x⟩, ⟨hd.2.2.2.2.1, hQ3x⟩⟩

/-- The original upper exponent 1+kappa is used before comparison to 2. -/
theorem actual_residue_abs_le_scale_sq {B : ℕ} {sigma kappa c0 : ℝ}
    {d : MediumAtom} (hd : MediumAdmissible B sigma kappa c0 d)
    (hkappa : kappa ≤ 1) : |(d.residue : ℝ)| ≤ d.scale^2 := by
  obtain ⟨_, _, _, _, _, _, _, hresidue, _⟩ := hd
  have hcast : (d.residue.natAbs : ℝ) = |(d.residue : ℝ)| := by
    simpa only [Int.cast_natCast, Int.cast_abs] using
      congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs d.residue)
  rw [← hcast]
  calc
    _ ≤ d.scale ^ (1+kappa) := hresidue
    _ ≤ d.scale ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le
      (actual_scale_gt_one hd).le (by linarith)
    _ = d.scale^2 := Real.rpow_two d.scale

theorem actual_parameters_and_residue {B : ℕ} {sigma kappa c0 : ℝ}
    {d : MediumAtom} (hd : MediumAdmissible B sigma kappa c0 d)
    (hsigma : 0 ≤ sigma) (hkappa : kappa ≤ 1) (hc0 : 0 < c0) :
    1 < d.scale ∧
      ((1 ≤ d.U ∧ d.U ≤ d.scale) ∧ (1 ≤ d.V ∧ d.V ≤ d.scale) ∧
        (1 ≤ d.Q1 ∧ d.Q1 ≤ d.scale) ∧ (1 ≤ d.Q2 ∧ d.Q2 ≤ d.scale) ∧
          (1 ≤ d.Q3 ∧ d.Q3 ≤ d.scale)) ∧
      d.residue ≠ 0 ∧ |(d.residue : ℝ)| ≤ d.scale^2 := by
  exact ⟨actual_scale_gt_one hd, actual_parameters_le_scale hd hsigma,
    mediumAdmissible_residue_ne_zero hc0 hd, actual_residue_abs_le_scale_sq hd hkappa⟩

/-- The actual alpha filter only shortens its original dyadic U interval. -/
theorem actual_alphaCarrier_bounds {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {n : ℕ} (hn : n ∈ d.alphaCarrier) :
    0 < n ∧ d.U ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*d.U := by
  exact factorCarrier_bounds hd.1 (Finset.mem_filter.mp hn).1

theorem actual_betaCarrier_bounds {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {m : ℕ} (hm : m ∈ d.betaCarrier) :
    0 < m ∧ d.V ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2*d.V := by
  exact factorCarrier_bounds hd.2.1 hm

theorem actual_factorCarrier_bounds {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) {q1 q2 q3 : ℕ}
    (hq1 : q1 ∈ factorCarrier d.Q1) (hq2 : q2 ∈ factorCarrier d.Q2)
    (hq3 : q3 ∈ factorCarrier d.Q3) :
    (0 < q1 ∧ d.Q1 ≤ (q1 : ℝ) ∧ (q1 : ℝ) ≤ 2*d.Q1) ∧
      (0 < q2 ∧ d.Q2 ≤ (q2 : ℝ) ∧ (q2 : ℝ) ≤ 2*d.Q2) ∧
        (0 < q3 ∧ d.Q3 ≤ (q3 : ℝ) ∧ (q3 : ℝ) ≤ 2*d.Q3) := by
  exact ⟨factorCarrier_bounds hd.2.2.1 hq1,
    factorCarrier_bounds hd.2.2.2.1 hq2, factorCarrier_bounds hd.2.2.2.2.1 hq3⟩

private theorem factorCarrier_subset_scaleBox {Q x : ℝ}
    (hQ : 1 ≤ Q) (hQx : Q ≤ x) :
    factorCarrier Q ⊆ Finset.Ioc 0 (Nat.floor (2*x)) := by
  intro n hn
  obtain ⟨hnpos, _hlo, hhi⟩ := factorCarrier_bounds hQ hn
  exact Finset.mem_Ioc.mpr ⟨hnpos, Nat.le_floor (hhi.trans (by linarith))⟩

/-- Carrier maps retain the actual source intervals before embedding in x. -/
theorem actual_alpha_beta_carrier_maps {B : ℕ} {sigma kappa c0 : ℝ}
    {d : MediumAtom} (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma) :
    d.alphaCarrier ⊆ Finset.Ioc 0 (Nat.floor (2*d.scale)) ∧
      d.betaCarrier ⊆ Finset.Ioc 0 (Nat.floor (2*d.scale)) := by
  obtain ⟨hU, hV, _hQ1, _hQ2, _hQ3⟩ := actual_parameters_le_scale hd hsigma
  constructor
  · intro n hn
    exact factorCarrier_subset_scaleBox hU.1 hU.2 (Finset.mem_filter.mp hn).1
  · exact factorCarrier_subset_scaleBox hV.1 hV.2

theorem actual_factor_carrier_maps {B : ℕ} {sigma kappa c0 : ℝ}
    {d : MediumAtom} (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma) :
    factorCarrier d.Q1 ⊆ Finset.Ioc 0 (Nat.floor (2*d.scale)) ∧
      factorCarrier d.Q2 ⊆ Finset.Ioc 0 (Nat.floor (2*d.scale)) ∧
        factorCarrier d.Q3 ⊆ Finset.Ioc 0 (Nat.floor (2*d.scale)) := by
  obtain ⟨_hU, _hV, hQ1, hQ2, hQ3⟩ := actual_parameters_le_scale hd hsigma
  exact ⟨factorCarrier_subset_scaleBox hQ1.1 hQ1.2,
    factorCarrier_subset_scaleBox hQ2.1 hQ2.2, factorCarrier_subset_scaleBox hQ3.1 hQ3.2⟩

/-- This bounds the EXISTING physical cap, not a replacement range. -/
theorem actual_physicalFactorCap_le {B : ℕ} {sigma kappa c0 : ℝ}
    {d : MediumAtom} (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma) :
    d.physicalFactorCap ≤ 8*d.scale^3 := by
  obtain ⟨_hU, _hV, hQ1, hQ2, hQ3⟩ := actual_parameters_le_scale hd hsigma
  have hx0 : 0 ≤ d.scale := zero_le_one.trans (actual_scale_gt_one hd).le
  have h12 : d.Q1*d.Q2 ≤ d.scale*d.scale :=
    mul_le_mul hQ1.2 hQ2.2 (zero_le_one.trans hQ2.1) hx0
  have h123 : d.Q1*d.Q2*d.Q3 ≤ d.scale*d.scale*d.scale :=
    mul_le_mul h12 hQ3.2 (zero_le_one.trans hQ3.1) (mul_nonneg hx0 hx0)
  calc
    d.physicalFactorCap = 8*(d.Q1*d.Q2*d.Q3) := by unfold MediumAtom.physicalFactorCap; ring
    _ ≤ 8*(d.scale*d.scale*d.scale) := mul_le_mul_of_nonneg_left h123 (by norm_num)
    _ = _ := by ring

/-- The existing physical image is embedded with no factor multiplicity loss. -/
theorem actual_physicalFactorModuli_map {B : ℕ} {sigma kappa c0 : ℝ}
    {d : MediumAtom} (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma) :
    d.physicalFactorModuli ⊆ Finset.Ioc 0 (Nat.floor (8*d.scale^3)) := by
  intro q hq
  obtain ⟨hqpos, hqcap⟩ := Finset.mem_Ioc.mp (d.physicalFactorModuli_subset_cap hd hq)
  have hcap0 : 0 ≤ d.physicalFactorCap := zero_le_one.trans (d.one_le_physicalFactorCap hd)
  have hqR : (q : ℝ) ≤ d.physicalFactorCap :=
    (show (q : ℝ) ≤ (Nat.floor d.physicalFactorCap : ℝ) by exact_mod_cast hqcap).trans
      (Nat.floor_le hcap0)
  exact Finset.mem_Ioc.mpr ⟨hqpos, Nat.le_floor (hqR.trans (actual_physicalFactorCap_le hd hsigma))⟩

theorem actual_physical_product_le {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (hsigma : 0 ≤ sigma)
    {q1 q2 q3 : ℕ} (hq1 : q1 ∈ factorCarrier d.Q1)
    (hq2 : q2 ∈ factorCarrier d.Q2) (hq3 : q3 ∈ factorCarrier d.Q3) :
    ((q1*q2*q3 : ℕ) : ℝ) ≤ 8*d.scale^3 := by
  have hx0 : 0 ≤ d.scale := zero_le_one.trans (actual_scale_gt_one hd).le
  have hlabels : (q1,q2,q3) ∈ d.complexFactorLabels :=
    Finset.mem_product.mpr ⟨hq1, Finset.mem_product.mpr ⟨hq2,hq3⟩⟩
  have hphysical : q1*q2*q3 ∈ d.physicalFactorModuli :=
    Finset.mem_image.mpr ⟨(q1,q2,q3), hlabels, rfl⟩
  have hb := (Finset.mem_Ioc.mp (actual_physicalFactorModuli_map hd hsigma hphysical)).2
  exact (show ((q1*q2*q3 : ℕ) : ℝ) ≤ (Nat.floor (8*d.scale^3) : ℝ) by
    exact_mod_cast hb).trans (Nat.floor_le (by positivity))

/-- Uniformity is literal: C is fixed before every moving parameter and atom.
Only the original kappa<=1 upper bound is used; kappa>=0 is not needed. -/
theorem uniform_moving_residue_budget :
    ∃ C : ℝ, C = 8 ∧ 0 < C ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
        0 ≤ sigma → kappa ≤ 1 → 0 < c0 → MediumAdmissible B sigma kappa c0 d →
        1 < d.scale ∧ d.residue ≠ 0 ∧ |(d.residue : ℝ)| ≤ d.scale^2 ∧
          d.physicalFactorCap ≤ C*d.scale^3 ∧
            d.physicalFactorModuli ⊆ Finset.Ioc 0 (Nat.floor (C*d.scale^3)) := by
  refine ⟨8, rfl, by norm_num, ?_⟩
  intro B sigma kappa c0 d hsigma hkappa hc0 hd
  exact ⟨actual_scale_gt_one hd, mediumAdmissible_residue_ne_zero hc0 hd,
    actual_residue_abs_le_scale_sq hd hkappa, actual_physicalFactorCap_le hd hsigma,
    actual_physicalFactorModuli_map hd hsigma⟩

/-- Complete range/carrier interface, with a constant preceding kappa,d. -/
theorem uniform_full_parameter_carrier_budget :
    ∃ C : ℝ, C = 8 ∧ 0 < C ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
        0 ≤ sigma → kappa ≤ 1 → 0 < c0 → MediumAdmissible B sigma kappa c0 d →
        1 < d.scale ∧
          ((1 ≤ d.U ∧ d.U ≤ d.scale) ∧ (1 ≤ d.V ∧ d.V ≤ d.scale) ∧
            (1 ≤ d.Q1 ∧ d.Q1 ≤ d.scale) ∧ (1 ≤ d.Q2 ∧ d.Q2 ≤ d.scale) ∧
              (1 ≤ d.Q3 ∧ d.Q3 ≤ d.scale)) ∧
          d.residue ≠ 0 ∧ |(d.residue : ℝ)| ≤ d.scale^2 ∧
          (d.alphaCarrier ⊆ Finset.Ioc 0 (Nat.floor (2*d.scale)) ∧
            d.betaCarrier ⊆ Finset.Ioc 0 (Nat.floor (2*d.scale))) ∧
          (factorCarrier d.Q1 ⊆ Finset.Ioc 0 (Nat.floor (2*d.scale)) ∧
            factorCarrier d.Q2 ⊆ Finset.Ioc 0 (Nat.floor (2*d.scale)) ∧
              factorCarrier d.Q3 ⊆ Finset.Ioc 0 (Nat.floor (2*d.scale))) ∧
          d.physicalFactorCap ≤ C*d.scale^3 ∧
            d.physicalFactorModuli ⊆ Finset.Ioc 0 (Nat.floor (C*d.scale^3)) := by
  refine ⟨8, rfl, by norm_num, ?_⟩
  intro B sigma kappa c0 d hsigma hkappa hc0 hd
  exact ⟨actual_scale_gt_one hd, actual_parameters_le_scale hd hsigma,
    mediumAdmissible_residue_ne_zero hc0 hd, actual_residue_abs_le_scale_sq hd hkappa,
    actual_alpha_beta_carrier_maps hd hsigma, actual_factor_carrier_maps hd hsigma,
    actual_physicalFactorCap_le hd hsigma, actual_physicalFactorModuli_map hd hsigma⟩

end
end ImbalancedChen.Part3.ActualMovingResiduePolynomialBudget_20261024z
