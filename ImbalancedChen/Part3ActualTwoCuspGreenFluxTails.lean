import ImbalancedChen.Part3ActualTwoCuspHeightRemainders
import ImbalancedChen.Part3PrimeTopBoundaryFluxGrouping

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Actual finite-oldform Green flux at BOTH physical cusps splits into its
literal completed-constant flux and the nonconstant/nonconstant flux.
All four mixed terms vanish by the proved actual remainder and height-jet
zero means. Their genuine exponential bounds give explicit finite-level
flux errors. Binding to the ORIGINAL prime top trace retains heights T
and T/p, and requires T>=p before applying the high-height bounds. No
uniform-level estimate, held-side cancellation, or spectral measure is used.
-/

noncomputable section
open Set Complex MeasureTheory
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.ActualTwoCuspHeightRemainders20261026b
open ImbalancedChen.Part3.ActualPrimeHorizontalGreenFlux20261026b
open ImbalancedChen.Part3.PrimeExplicitCosetGreenTrace20261026b
open ImbalancedChen.Part3.PrimeTopBoundaryFluxGrouping20261026b
open ImbalancedChen.Part3.ActualCompletedGamma0Sides20261026b
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a
open ImbalancedChen.Part3.CompletedEisensteinCuspTail20261025a
open ImbalancedChen.Part3.ActualEisensteinHeightDerivativeTail20261026b
open ImbalancedChen.Part3.SLRealGreenCurrent20261026b
open ImbalancedChen.Part3.ActualEisensteinFourierInterchange20261025a
open ImbalancedChen.Part3.ActualFiniteCosetGreenDivergence20261026b

namespace ImbalancedChen.Part3.ActualTwoCuspGreenFluxTails20261026b

def physicalCuspGreenCurrent (N : ℕ) (hN : 0 < N) (s u : ℂ)
    (b : Bool) (y x : ℝ) : ℂ :=
  star (physicalCuspChart N hN s b (x, y)) *
      deriv (fun v : ℝ => physicalCuspChart N hN u b (x, v)) y -
    star (deriv (fun v : ℝ => physicalCuspChart N hN s b (x, v)) y) *
      physicalCuspChart N hN u b (x, y)

def physicalCuspConstantCurrent (N : ℕ) (hN : 0 < N) (s u : ℂ)
    (b : Bool) (y : ℝ) : ℂ :=
  star (physicalCuspConstant N s b y) * physicalCuspConstantFirst N hN u b y -
    star (physicalCuspConstantFirst N hN s b y) * physicalCuspConstant N u b y

def physicalCuspTailCurrent (N : ℕ) (hN : 0 < N) (s u : ℂ)
    (b : Bool) (y x : ℝ) : ℂ :=
  star (physicalCuspRemainder N hN s b y x) * physicalCuspRemainderY N hN u b y x -
    star (physicalCuspRemainderY N hN s b y x) * physicalCuspRemainder N hN u b y x

def physicalCuspFluxErrorConstant (N : ℕ) (hN : 0 < N) (M : ℕ)
    (s u : ℂ) (b : Bool) : ℝ :=
  (cuspTailConstant M * derivativeTailConstant M) *
    (physicalCuspMass N hN s b * physicalCuspFirstMass N hN u b +
      physicalCuspFirstMass N hN s b * physicalCuspMass N hN u b)

theorem physicalCuspFluxErrorConstant_nonneg (N : ℕ) (hN : 0 < N) (M : ℕ)
    (s u : ℂ) (b : Bool) : 0 ≤ physicalCuspFluxErrorConstant N hN M s u b := by
  unfold physicalCuspFluxErrorConstant
  exact mul_nonneg (mul_nonneg (cuspTailConstant_pos M).le (derivativeTailConstant_pos M).le)
    (add_nonneg (mul_nonneg (physicalCuspMass_nonneg N hN s b) (physicalCuspFirstMass_nonneg N hN u b))
      (mul_nonneg (physicalCuspFirstMass_nonneg N hN s b) (physicalCuspMass_nonneg N hN u b)))

theorem complex_vertical_slice_deriv (F : ℂ → ℂ) (x y : ℝ) (hy : 0 < y)
    (hF : DifferentiableAt ℝ F (horizontalPoint y hy x)) :
    deriv (fun v : ℝ => F ⟨x, v⟩) y = fderiv ℝ F (horizontalPoint y hy x) I := by
  have he : (fun v : ℝ => (⟨x, v⟩ : ℂ)) = fun v : ℝ => (x : ℂ) + (v : ℂ) * I := by
    funext v
    ext <;> simp
  have hv : HasDerivAt (fun v : ℝ => (⟨x, v⟩ : ℂ)) I y := by
    rw [he]
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add (x : ℂ)
  exact (hF.hasFDerivAt.comp_hasDerivAt y hv).deriv

theorem horizontalGreenDensity_eq_slice_current (F G : ℂ → ℂ)
    (hF : ∀ z : UpperHalfPlane, DifferentiableAt ℝ F (z : ℂ))
    (hG : ∀ z : UpperHalfPlane, DifferentiableAt ℝ G (z : ℂ))
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    horizontalGreenDensity F G y hy x =
      star (F ⟨x, y⟩) * deriv (fun v : ℝ => G ⟨x, v⟩) y -
        star (deriv (fun v : ℝ => F ⟨x, v⟩) y) * G ⟨x, y⟩ := by
  rw [horizontalGreenDensity_eq_verticalCurrent, complex_vertical_slice_deriv G x y hy (hG _),
    complex_vertical_slice_deriv F x y hy (hF _)]
  rfl

theorem physicalCuspGreenCurrent_eq_density (N : ℕ) (hN : 0 < N) (s u : ℂ)
    (b : Bool) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    physicalCuspGreenCurrent N hN s u b y x =
      if b then actualFrickeGreenDensity N hN s u y hy x else actualInfinityGreenDensity N s u y hy x := by
  cases b with
  | false =>
      simpa only [physicalCuspGreenCurrent, physicalCuspChart, Bool.false_eq_true, ↓reduceIte,
        actualInfinityGreenDensity, completedComplexField] using
        (horizontalGreenDensity_eq_slice_current (completedComplexField N s) (completedComplexField N u)
          (fun z => (completedComplexField_contDiffAt N s z).differentiableAt (by simp))
          (fun z => (completedComplexField_contDiffAt N u z).differentiableAt (by simp)) y hy x).symm
  | true =>
      simpa only [physicalCuspGreenCurrent, physicalCuspChart, Bool.true_eq_true, ↓reduceIte,
        actualFrickeGreenDensity] using
        (horizontalGreenDensity_eq_slice_current (frickeField N hN (completedComplexField N s))
          (frickeField N hN (completedComplexField N u))
          (fun z => frickeField_differentiableAt N hN _
            (fun w => (completedComplexField_contDiffAt N s w).differentiableAt (by simp)) z)
          (fun z => frickeField_differentiableAt N hN _
            (fun w => (completedComplexField_contDiffAt N u w).differentiableAt (by simp)) z) y hy x).symm

/-- Unit-interval current equals the EXACT centered physical flux used
by the original top-boundary grouping. The current period is proved. -/
theorem physicalCuspGreenCurrent_integral_eq_flux (N : ℕ) (hN : 0 < N) (s u : ℂ)
    (hs : s ∈ completedRegularDomain N) (hu : u ∈ completedRegularDomain N)
    (b : Bool) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, physicalCuspGreenCurrent N hN s u b y x) =
      if b then actualFrickeGreenFlux N hN s u y hy else actualInfinityGreenFlux N s u y hy := by
  simp_rw [physicalCuspGreenCurrent_eq_density N hN s u b y hy]
  cases b with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, actualInfinityGreenFlux]
      convert (actualInfinityGreenDensity_periodic N hN s u hs hu y hy)
        .intervalIntegral_add_eq 0 (-(1 / 2)) using 1 <;> norm_num
  | true =>
      simp only [Bool.true_eq_true, ↓reduceIte, actualFrickeGreenFlux]
      convert (actualFrickeGreenDensity_periodic N hN s u hs hu y hy)
        .intervalIntegral_add_eq 0 (-(1 / 2)) using 1 <;> norm_num

/-- All mixed physical constant/remainder terms vanish by honest means
of the ACTUAL subtracted fields and ACTUAL first height derivatives. -/
theorem physicalCuspGreenCurrent_split (N : ℕ) (hN : 0 < N) (s u : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hu0 : u ≠ 0) (hu1 : u ≠ 1)
    (b : Bool) {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, physicalCuspGreenCurrent N hN s u b y x) =
      physicalCuspConstantCurrent N hN s u b y +
        ∫ x in (0 : ℝ)..1, physicalCuspTailCurrent N hN s u b y x := by
  let Rs := physicalCuspRemainder N hN s b y
  let Ru := physicalCuspRemainder N hN u b y
  let Ds := physicalCuspRemainderY N hN s b y
  let Du := physicalCuspRemainderY N hN u b y
  let Cs := physicalCuspConstant N s b y
  let Cu := physicalCuspConstant N u b y
  let Js := physicalCuspConstantFirst N hN s b y
  let Ju := physicalCuspConstantFirst N hN u b y
  have hRs : Continuous Rs := physicalCuspRemainder_continuous_x N hN s hs0 hs1 b hy
  have hRu : Continuous Ru := physicalCuspRemainder_continuous_x N hN u hu0 hu1 b hy
  have hDs : Continuous Ds := physicalCuspRemainderY_continuous_x N hN s hs0 hs1 b hy
  have hDu : Continuous Du := physicalCuspRemainderY_continuous_x N hN u hu0 hu1 b hy
  have hRsm : (∫ x in (0 : ℝ)..1, Rs x) = 0 := physicalCuspRemainder_mean_zero N hN s hs0 hs1 b hy
  have hRum : (∫ x in (0 : ℝ)..1, Ru x) = 0 := physicalCuspRemainder_mean_zero N hN u hu0 hu1 b hy
  have hDsm : (∫ x in (0 : ℝ)..1, Ds x) = 0 := physicalCuspRemainderY_mean_zero N hN s hs0 hs1 b hy
  have hDum : (∫ x in (0 : ℝ)..1, Du x) = 0 := physicalCuspRemainderY_mean_zero N hN u hu0 hu1 b hy
  have hRsStar : (∫ x in (0 : ℝ)..1, star (Rs x)) = 0 := by
    have hh : (∫ x in (0 : ℝ)..1, star (Rs x)) = star (∫ x in (0 : ℝ)..1, Rs x) := by
      simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), Complex.star_def, integral_conj]
    rw [hh, hRsm, star_zero]
  have hDsStar : (∫ x in (0 : ℝ)..1, star (Ds x)) = 0 := by
    have hh : (∫ x in (0 : ℝ)..1, star (Ds x)) = star (∫ x in (0 : ℝ)..1, Ds x) := by
      simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), Complex.star_def, integral_conj]
    rw [hh, hDsm, star_zero]
  have hvalue (v : ℂ) (x : ℝ) : physicalCuspChart N hN v b (x, y) =
      physicalCuspConstant N v b y + physicalCuspRemainder N hN v b y x := by
    unfold physicalCuspRemainder
    ring
  have hjet (v : ℂ) (hv0 : v ≠ 0) (hv1 : v ≠ 1) (x : ℝ) :
      deriv (fun t : ℝ => physicalCuspChart N hN v b (x, t)) y =
        physicalCuspConstantFirst N hN v b y + physicalCuspRemainderY N hN v b y x := by
    unfold physicalCuspRemainderY
    rw [(physicalCuspConstant_hasDerivAt N hN v hv0 hv1 b hy).deriv]
    ring
  have hleft : (∫ x in (0 : ℝ)..1, star (Cs + Rs x) * (Ju + Du x)) =
      star Cs * Ju + ∫ x in (0 : ℝ)..1, star (Rs x) * Du x := by
    simp only [star_add, add_mul, mul_add]
    rw [intervalIntegral.integral_add
      ((continuous_const.add (hDu.const_mul _)).intervalIntegrable 0 1)
      (((hRs.star.mul_const _).add (hRs.star.mul hDu)).intervalIntegrable 0 1),
      intervalIntegral.integral_add intervalIntegrable_const ((hDu.const_mul _).intervalIntegrable 0 1),
      intervalIntegral.integral_add ((hRs.star.mul_const _).intervalIntegrable 0 1)
        ((hRs.star.mul hDu).intervalIntegrable 0 1)]
    simp only [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const, hDum, hRsStar, sub_zero, one_smul, mul_zero, zero_mul,
      add_zero, zero_add]
  have hright : (∫ x in (0 : ℝ)..1, star (Js + Ds x) * (Cu + Ru x)) =
      star Js * Cu + ∫ x in (0 : ℝ)..1, star (Ds x) * Ru x := by
    simp only [star_add, add_mul, mul_add]
    rw [intervalIntegral.integral_add
      ((continuous_const.add (hRu.const_mul _)).intervalIntegrable 0 1)
      (((hDs.star.mul_const _).add (hDs.star.mul hRu)).intervalIntegrable 0 1),
      intervalIntegral.integral_add intervalIntegrable_const ((hRu.const_mul _).intervalIntegrable 0 1),
      intervalIntegral.integral_add ((hDs.star.mul_const _).intervalIntegrable 0 1)
        ((hDs.star.mul hRu).intervalIntegrable 0 1)]
    simp only [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const, hRum, hDsStar, sub_zero, one_smul, mul_zero, zero_mul,
      add_zero, zero_add]
  unfold physicalCuspGreenCurrent
  simp_rw [hvalue, hjet s hs0 hs1, hjet u hu0 hu1]
  change (∫ x in (0 : ℝ)..1, star (Cs + Rs x) * (Ju + Du x) - star (Js + Ds x) * (Cu + Ru x)) = _
  rw [intervalIntegral.integral_sub
    (((continuous_const.add hRs).star.mul (continuous_const.add hDu)).intervalIntegrable 0 1)
    (((continuous_const.add hDs).star.mul (continuous_const.add hRu)).intervalIntegrable 0 1), hleft, hright]
  unfold physicalCuspConstantCurrent physicalCuspTailCurrent
  rw [intervalIntegral.integral_sub ((hRs.star.mul hDu).intervalIntegrable 0 1)
    ((hDs.star.mul hRu).intervalIntegrable 0 1)]
  dsimp only [Cs, Cu, Js, Ju, Rs, Ru, Ds, Du]
  ring

theorem physicalCuspTailCurrent_bound (N : ℕ) (hN : 0 < N) (M : ℕ) {s u : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) (hu : |u.re| ≤ (M : ℝ))
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hu0 : u ≠ 0) (hu1 : u ≠ 1)
    (b : Bool) {y : ℝ} (hy : 1 ≤ y) (x : ℝ) :
    ‖physicalCuspTailCurrent N hN s u b y x‖ ≤
      physicalCuspFluxErrorConstant N hN M s u b * (Real.exp (-(Real.pi / 2) * y)) ^ 2 := by
  have hrs := physicalCuspRemainder_bound N hN M hs hs0 hs1 b hy x
  have hru := physicalCuspRemainder_bound N hN M hu hu0 hu1 b hy x
  have hds := physicalCuspRemainderY_bound N hN M hs hs0 hs1 b hy x
  have hdu := physicalCuspRemainderY_bound N hN M hu hu0 hu1 b hy x
  unfold physicalCuspTailCurrent
  calc
    _ ≤ ‖star (physicalCuspRemainder N hN s b y x) * physicalCuspRemainderY N hN u b y x‖ +
        ‖star (physicalCuspRemainderY N hN s b y x) * physicalCuspRemainder N hN u b y x‖ := norm_sub_le _ _
    _ = ‖physicalCuspRemainder N hN s b y x‖ * ‖physicalCuspRemainderY N hN u b y x‖ +
        ‖physicalCuspRemainderY N hN s b y x‖ * ‖physicalCuspRemainder N hN u b y x‖ := by
      simp only [norm_mul, norm_star]
    _ ≤ ((physicalCuspMass N hN s b * cuspTailConstant M) * Real.exp (-(Real.pi / 2) * y)) *
          ((physicalCuspFirstMass N hN u b * derivativeTailConstant M) * Real.exp (-(Real.pi / 2) * y)) +
        ((physicalCuspFirstMass N hN s b * derivativeTailConstant M) * Real.exp (-(Real.pi / 2) * y)) *
          ((physicalCuspMass N hN u b * cuspTailConstant M) * Real.exp (-(Real.pi / 2) * y)) :=
      add_le_add (mul_le_mul hrs hdu (norm_nonneg _)
        (mul_nonneg (mul_nonneg (physicalCuspMass_nonneg N hN s b) (cuspTailConstant_pos M).le)
          (Real.exp_pos _).le))
        (mul_le_mul hds hru (norm_nonneg _)
          (mul_nonneg (mul_nonneg (physicalCuspFirstMass_nonneg N hN s b) (derivativeTailConstant_pos M).le)
            (Real.exp_pos _).le))
    _ = _ := by unfold physicalCuspFluxErrorConstant; ring

theorem actual_physical_cusp_flux_constant_error (N : ℕ) (hN : 0 < N) (M : ℕ) {s u : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) (hu : |u.re| ≤ (M : ℝ))
    (hsr : s ∈ completedRegularDomain N) (hur : u ∈ completedRegularDomain N)
    (b : Bool) {y : ℝ} (hy : 1 ≤ y) :
    ‖(if b then actualFrickeGreenFlux N hN s u y (by linarith)
        else actualInfinityGreenFlux N s u y (by linarith)) - physicalCuspConstantCurrent N hN s u b y‖ ≤
      physicalCuspFluxErrorConstant N hN M s u b * (Real.exp (-(Real.pi / 2) * y)) ^ 2 := by
  rw [← physicalCuspGreenCurrent_integral_eq_flux N hN s u hsr hur b y (by linarith),
    physicalCuspGreenCurrent_split N hN s u hsr.1 hsr.2.1 hur.1 hur.2.1 b (by linarith),
    add_sub_cancel_left]
  simpa only [sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x _ => physicalCuspTailCurrent_bound N hN M hs hu hsr.1 hsr.2.1 hur.1 hur.2.1 b hy x)

/-- The ORIGINAL prime top boundary has two different physical error
heights. T>=p is proved sufficient for BOTH high-height invocations. -/
theorem actual_prime_top_constant_error (p : ℕ) [NeZero p] (hp : p.Prime) (M : ℕ)
    {s u : ℂ} (hs : |s.re| ≤ (M : ℝ)) (hu : |u.re| ≤ (M : ℝ))
    (hsr : s ∈ completedRegularDomain p) (hur : u ∈ completedRegularDomain p)
    {T : ℝ} (hT : (p : ℝ) ≤ T) :
    ‖(∫ x in (-(1 / 2) : ℝ)..(1 / 2), actualCosetTraceY p s u (x, T)) -
        (physicalCuspConstantCurrent p hp.pos s u false T +
          physicalCuspConstantCurrent p hp.pos s u true (T / (p : ℝ)))‖ ≤
      physicalCuspFluxErrorConstant p hp.pos M s u false * (Real.exp (-(Real.pi / 2) * T)) ^ 2 +
        physicalCuspFluxErrorConstant p hp.pos M s u true *
          (Real.exp (-(Real.pi / 2) * (T / (p : ℝ)))) ^ 2 := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hT1 : 1 ≤ T := hp1.trans hT
  have hTp : 1 ≤ T / (p : ℝ) := (le_div_iff₀ hpR).mpr (by simpa using hT)
  rw [actualCosetTraceY_top_integral_two_cusps p hp s u hsr hur T (hpR.trans_le hT)]
  rw [show actualInfinityGreenFlux p s u T (hpR.trans_le hT) +
      actualFrickeGreenFlux p hp.pos s u (T / (p : ℝ)) (div_pos (hpR.trans_le hT) hpR) -
        (physicalCuspConstantCurrent p hp.pos s u false T +
          physicalCuspConstantCurrent p hp.pos s u true (T / (p : ℝ))) =
      (actualInfinityGreenFlux p s u T (by linarith) - physicalCuspConstantCurrent p hp.pos s u false T) +
        (actualFrickeGreenFlux p hp.pos s u (T / (p : ℝ)) (by linarith) -
          physicalCuspConstantCurrent p hp.pos s u true (T / (p : ℝ))) by ring]
  exact (norm_add_le _ _).trans (add_le_add
    (by simpa only [Bool.false_eq_true, ↓reduceIte] using
      actual_physical_cusp_flux_constant_error p hp.pos M hs hu hsr hur false hT1)
    (by simpa only [Bool.true_eq_true, ↓reduceIte] using
      actual_physical_cusp_flux_constant_error p hp.pos M hs hu hsr hur true hTp))

end ImbalancedChen.Part3.ActualTwoCuspGreenFluxTails20261026b
