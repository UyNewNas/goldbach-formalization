import ImbalancedChen.P4AActualFirstIntegralSelectedK
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Catalog saving 5, above_mu_second_coarse_only.  The existing supplier bounds
two chart integrals but does not identify them with the original (x,y)
integral.  Here both affine substitutions, the negative-chart orientation,
the y=mu fibre split, and all integrability obligations are proved.  The
physical integral is defined independently from the chart integral and from
its rational endpoint.  No endpoint or change-of-variables premise occurs.

This is an endpoint integral supplier, not the limiting density of an
arbitrary frozen finite policy.  Common finite realization and its tail
error remain separate, as required by the original source note.
-/

namespace ImbalancedChen.P4AOriginalSecondPhysicalIntegral

noncomputable section
open Set MeasureTheory
open scoped Interval
open Certificates.AboveMuSecondCoarse
open P4AAll22OriginalKLedger20261024zSourceOnly
open P4AAll22AdditionalActualSuppliers20261024zSourceOnly

def lowerBoundary (x : ℝ) : ℝ := 25 / 32 - 3 * x

/-- Literal physical saving with factor four and no ordering factorial. -/
def physicalKernel (x y : ℝ) : ℝ :=
  4 * (endpointEnvelope y - endpointEnvelope x) /
    (x * y * (endpointEnvelope x - x - y) * (endpointEnvelope y - x - y))

/-- The original whole improvement region, in its original x,y order. -/
def physicalSaving : ℝ :=
  ∫ x in mu..rho, ∫ y in lowerBoundary x..x, physicalKernel x y

def negativePhysicalRow (x : ℝ) : ℝ :=
  ∫ y in lowerBoundary x..mu, physicalKernel x y

def positivePhysicalRow (x : ℝ) : ℝ :=
  ∫ y in mu..x, physicalKernel x y

theorem boundary_order {x : ℝ} (hx : x ∈ Icc mu rho) :
    (3 / 16 : ℝ) ≤ lowerBoundary x ∧ lowerBoundary x ≤ mu ∧ mu ≤ x := by
  dsimp [lowerBoundary, mu, rho] at *
  constructor
  · linarith [hx.2]
  constructor
  · linarith [hx.1]
  · exact hx.1

theorem physicalDomain_iff (x y : ℝ) :
    (x,y) ∈ physicalDomain ↔ x ∈ Ioo mu rho ∧ y ∈ Ioo (lowerBoundary x) x := by
  simp only [physicalDomain,lowerBoundary,mem_setOf_eq,mem_Ioo,and_assoc]

/-- Positivity holds on the entire closed physical region, including its
seam and the zero-width fibre at x=mu. -/
theorem physical_denominator_bounds {x y : ℝ} (hx : x ∈ Icc mu rho)
    (hy : y ∈ Icc (lowerBoundary x) x) :
    mu ≤ x ∧ (3 / 16 : ℝ) ≤ y ∧
      rho ≤ endpointEnvelope x - x - y ∧
      rho ≤ endpointEnvelope y - x - y := by
  have hvx : endpointEnvelope x = 57 / 64 - 3 * x / 2 := by
    apply min_eq_right
    dsimp [mu] at hx
    linarith [hx.1]
  have hfirst : 57 / 64 - 3 * x / 2 ≤ (1 + y) / 2 := by
    dsimp [lowerBoundary] at hy
    linarith [hy.1]
  have hsecond : 57 / 64 - 3 * x / 2 ≤ 57 / 64 - 3 * y / 2 := by
    linarith [hy.2]
  have hvxy : endpointEnvelope x ≤ endpointEnvelope y := by
    rw [hvx]
    exact le_min hfirst hsecond
  have hold : rho ≤ endpointEnvelope x - x - y := by
    rw [hvx]
    dsimp [rho] at *
    linarith [hx.2, hy.2]
  exact ⟨hx.1, (boundary_order hx).1.trans hy.1, hold,
    hold.trans (by linarith only [hvxy])⟩

theorem continuous_endpointEnvelope : Continuous endpointEnvelope := by
  unfold endpointEnvelope
  fun_prop

/-! The clamps are used only outside the original integration region. -/

private def safeKernel (x y : ℝ) : ℝ :=
  4 * (endpointEnvelope y - endpointEnvelope x) /
    (max mu x * max (3 / 16 : ℝ) y *
      max rho (endpointEnvelope x - x - y) *
      max rho (endpointEnvelope y - x - y))

private theorem continuous_safeKernel :
    Continuous (fun p : ℝ × ℝ => safeKernel p.1 p.2) := by
  have hx : Continuous (fun p : ℝ × ℝ => p.1) := continuous_fst
  have hy : Continuous (fun p : ℝ × ℝ => p.2) := continuous_snd
  have hvx := continuous_endpointEnvelope.comp hx
  have hvy := continuous_endpointEnvelope.comp hy
  apply (continuous_const.mul (hvy.sub hvx)).div
    ((((continuous_const.max hx).mul (continuous_const.max hy)).mul
      (continuous_const.max ((hvx.sub hx).sub hy))).mul
      (continuous_const.max ((hvy.sub hx).sub hy)))
  intro p
  have hm : 0 < mu := by norm_num [mu]
  have hr : 0 < rho := by norm_num [rho]
  exact (mul_pos (mul_pos (mul_pos
    (hm.trans_le (le_max_left _ _))
    ((by norm_num : (0:ℝ) < 3/16).trans_le (le_max_left _ _)))
    (hr.trans_le (le_max_left _ _)))
    (hr.trans_le (le_max_left _ _))).ne'

private theorem safeKernel_eq {x y : ℝ} (hx : x ∈ Icc mu rho)
    (hy : y ∈ Icc (lowerBoundary x) x) : safeKernel x y = physicalKernel x y := by
  obtain ⟨h1,h2,h3,h4⟩ := physical_denominator_bounds hx hy
  simp only [safeKernel, physicalKernel, max_eq_right h1,
    max_eq_right h2, max_eq_right h3, max_eq_right h4]

private theorem continuous_safeRow (a b : ℝ → ℝ)
    (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x : ℝ => ∫ y in a x..b x, safeKernel x y) := by
  have hu : Continuous (fun x : ℝ => ∫ y in (0:ℝ)..b x, safeKernel x y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      continuous_safeKernel hb
  have hl : Continuous (fun x : ℝ => ∫ y in (0:ℝ)..a x, safeKernel x y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      continuous_safeKernel ha
  have heq : (fun x : ℝ => ∫ y in a x..b x, safeKernel x y) =
      fun x : ℝ => (∫ y in (0:ℝ)..b x, safeKernel x y) -
        ∫ y in (0:ℝ)..a x, safeKernel x y := by
    funext x
    exact (intervalIntegral.integral_interval_sub_left
      ((continuous_safeKernel.uncurry_left x).intervalIntegrable 0 (b x))
      ((continuous_safeKernel.uncurry_left x).intervalIntegrable 0 (a x))).symm
  rw [heq]
  exact hu.sub hl

theorem physical_fibre_intervalIntegrable {x a b : ℝ} (hx : x ∈ Icc mu rho)
    (ha : lowerBoundary x ≤ a) (hab : a ≤ b) (hb : b ≤ x) :
    IntervalIntegrable (physicalKernel x) volume a b := by
  apply ((continuous_safeKernel.uncurry_left x).intervalIntegrable a b).congr
  intro y hy
  rw [uIoc_of_le hab] at hy
  exact safeKernel_eq hx ⟨ha.trans hy.1.le,hy.2.trans hb⟩

theorem physical_row_split {x : ℝ} (hx : x ∈ Icc mu rho) :
    (∫ y in lowerBoundary x..x, physicalKernel x y) =
      negativePhysicalRow x + positivePhysicalRow x := by
  obtain ⟨_,hlo,hhi⟩ := boundary_order hx
  exact (intervalIntegral.integral_add_adjacent_intervals
    (physical_fibre_intervalIntegrable hx le_rfl hlo hhi)
    (physical_fibre_intervalIntegrable hx hlo hhi le_rfl)).symm

theorem negativePhysicalRow_intervalIntegrable :
    IntervalIntegrable negativePhysicalRow volume mu rho := by
  have hs := (continuous_safeRow lowerBoundary (fun _ => mu)
    (by unfold lowerBoundary; fun_prop) continuous_const).intervalIntegrable mu rho
  apply hs.congr
  intro x hx
  rw [uIoc_of_le (by norm_num [mu,rho])] at hx
  have hxc : x ∈ Icc mu rho := ⟨hx.1.le,hx.2⟩
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le (boundary_order hxc).2.1] at hy
  exact safeKernel_eq hxc ⟨hy.1,hy.2.trans hxc.1⟩

theorem positivePhysicalRow_intervalIntegrable :
    IntervalIntegrable positivePhysicalRow volume mu rho := by
  have hs := (continuous_safeRow (fun _ => mu) id
    continuous_const continuous_id).intervalIntegrable mu rho
  apply hs.congr
  intro x hx
  rw [uIoc_of_le (by norm_num [mu,rho])] at hx
  have hxc : x ∈ Icc mu rho := ⟨hx.1.le,hx.2⟩
  apply intervalIntegral.integral_congr
  intro y hy
  rw [uIcc_of_le hxc.1] at hy
  exact safeKernel_eq hxc ⟨(boundary_order hxc).2.1.trans hy.1,hy.2⟩

theorem physical_outer_intervalIntegrable :
    IntervalIntegrable (fun x => ∫ y in lowerBoundary x..x, physicalKernel x y)
      volume mu rho := by
  apply (negativePhysicalRow_intervalIntegrable.add
    positivePhysicalRow_intervalIntegrable).congr
  intro x hx
  rw [uIoc_of_le (by norm_num [mu,rho])] at hx
  exact (physical_row_split ⟨hx.1.le,hx.2⟩).symm

theorem physicalSaving_eq_split :
    physicalSaving = (∫ x in mu..rho, negativePhysicalRow x) +
      ∫ x in mu..rho, positivePhysicalRow x := by
  unfold physicalSaving
  calc
    _ = ∫ x in mu..rho, negativePhysicalRow x + positivePhysicalRow x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num [mu,rho])] at hx
      exact physical_row_split hx
    _ = _ := intervalIntegral.integral_add
      negativePhysicalRow_intervalIntegrable positivePhysicalRow_intervalIntegrable

/-- Signed orientation: for k=-3 this runs from mu DOWN to a(x). -/
def orientedPhysicalChart (k : ℝ) : ℝ :=
  ∫ x in mu..rho, ∫ y in mu..(mu + k * (x-mu)), physicalKernel x y

/-- Genuine affine change of variables.  It also covers u=0, where the
inner interval and its Jacobian both vanish; no division by u occurs. -/
theorem orientedPhysicalChart_eq_pullback (k : ℝ) :
    orientedPhysicalChart k =
      squareIntegral (fun u v =>
        physicalKernel (chartX u) (chartY k u v) * (k * step^2 * u)) := by
  have houter := intervalIntegral.smul_integral_comp_mul_add
    (f := fun x : ℝ => ∫ y in mu..(mu+k*(x-mu)), physicalKernel x y)
    (a := (0:ℝ)) (b := 1) step mu
  have hout0 : step * 0 + mu = mu := by ring
  have hout1 : step * 1 + mu = rho := by norm_num [step,mu,rho]
  rw [hout0,hout1] at houter
  change step * (∫ u in (0:ℝ)..1,
    ∫ y in mu..(mu+k*(step*u+mu-mu)), physicalKernel (step*u+mu) y) =
      orientedPhysicalChart k at houter
  calc
    orientedPhysicalChart k = step * (∫ u in (0:ℝ)..1,
        ∫ y in mu..(mu+k*(chartX u-mu)), physicalKernel (chartX u) y) := by
      convert houter.symm using 1 <;>
        simp only [chartX_eq, add_comm]
    _ = ∫ u in (0:ℝ)..1, step *
        (∫ y in mu..(mu+k*(chartX u-mu)), physicalKernel (chartX u) y) :=
      (intervalIntegral.integral_const_mul step _).symm
    _ = squareIntegral (fun u v =>
        physicalKernel (chartX u) (chartY k u v) * (k*step^2*u)) := by
      apply intervalIntegral.integral_congr
      intro u _hu
      have hinner := intervalIntegral.smul_integral_comp_mul_add
        (f := physicalKernel (chartX u)) (a := (0:ℝ)) (b := 1)
        (k*step*u) mu
      have hleft : (k*step*u)*0+mu = mu := by ring
      have hright : (k*step*u)*1+mu = mu+k*(chartX u-mu) := by
        rw [chartX_eq]
        ring
      rw [hleft,hright] at hinner
      change (k*step*u) * (∫ v in (0:ℝ)..1,
        physicalKernel (chartX u) ((k*step*u)*v+mu)) = _ at hinner
      rw [← hinner]
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro v _hv
      have harg : (k*step*u)*v+mu = chartY k u v := by
        rw [chartY_eq]
        ring
      rw [harg]
      ring

theorem negative_oriented_chart : orientedPhysicalChart (-3) = -chartIntegral (-3) := by
  rw [orientedPhysicalChart_eq_pullback]
  unfold chartIntegral squareIntegral
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hv
  rw [chartKernel_eq_physical_pullback (Or.inl rfl) hu hv]
  change physicalKernel (chartX u) (chartY (-3) u v) * ((-3)*step^2*u) =
    -(physicalKernel (chartX u) (chartY (-3) u v) * (|(-3:ℝ)|*step^2*u))
  norm_num only [abs_of_neg (by norm_num : (-3:ℝ) < 0)] <;> ring

theorem positive_oriented_chart : orientedPhysicalChart 1 = chartIntegral 1 := by
  rw [orientedPhysicalChart_eq_pullback]
  unfold chartIntegral squareIntegral
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hv
  rw [chartKernel_eq_physical_pullback (Or.inr rfl) hu hv]
  change physicalKernel (chartX u) (chartY 1 u v) * (1*step^2*u) =
    physicalKernel (chartX u) (chartY 1 u v) * (|(1:ℝ)|*step^2*u)
  norm_num

theorem negativePhysicalIntegral_eq_chart :
    (∫ x in mu..rho, negativePhysicalRow x) = chartIntegral (-3) := by
  have h : orientedPhysicalChart (-3) =
      -(∫ x in mu..rho, negativePhysicalRow x) := by
    unfold orientedPhysicalChart negativePhysicalRow
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _hx
    have he : mu+(-3)*(x-mu) = lowerBoundary x := by
      unfold mu lowerBoundary
      ring
    rw [he,intervalIntegral.integral_symm]
  linarith only [h,negative_oriented_chart]

theorem positivePhysicalIntegral_eq_chart :
    (∫ x in mu..rho, positivePhysicalRow x) = chartIntegral 1 := by
  calc
    _ = orientedPhysicalChart 1 := by
      unfold orientedPhysicalChart positivePhysicalRow
      apply intervalIntegral.integral_congr
      intro x _hx
      rw [show mu+1*(x-mu)=x by ring]
    _ = chartIntegral 1 := positive_oriented_chart

/-- Closed physical-domain/chart dictionary; no integral enclosure premise. -/
theorem physicalSaving_eq_totalChartIntegral : physicalSaving = totalChartIntegral := by
  rw [physicalSaving_eq_split,negativePhysicalIntegral_eq_chart,
    positivePhysicalIntegral_eq_chart]
  rfl

/-- Catalog 5 now bounds the original whole physical x,y integral. -/
theorem original_physical_saving_ge_catalog_five :
    (640339 / 15210735000 : ℝ) ≤ physicalSaving := by
  rw [physicalSaving_eq_totalChartIntegral]
  exact adopted_coarse_lower

/-- Replacement only: the old chart saving is restored before the physical
one is subtracted.  In particular this is not an extra 23rd saving. -/
def physicalSecondLedger : ℝ :=
  threeSupplierLedger + actualCoarseSecondSaving - physicalSaving

theorem physicalSecondLedger_eq_threeSupplierLedger :
    physicalSecondLedger = threeSupplierLedger := by
  rw [physicalSecondLedger,physicalSaving_eq_totalChartIntegral]
  unfold actualCoarseSecondSaving
  ring

/-- Original K and both original reserves, without any change to quoted
unpaid slots, common-policy assumptions, or their eventual realization. -/
theorem physicalSecondLedger_with_original_reserves_lt_K :
    physicalSecondLedger + densityReserve + compilerReserve < currentK := by
  rw [physicalSecondLedger_eq_threeSupplierLedger]
  exact P4AActualFirstIntegralSelectedK.three_supplier_with_reserves_lt_K

end
end ImbalancedChen.P4AOriginalSecondPhysicalIntegral
