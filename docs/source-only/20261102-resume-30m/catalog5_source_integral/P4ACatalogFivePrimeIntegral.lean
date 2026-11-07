import ImbalancedChen.P4AOriginalSecondResidualSupplier
import ImbalancedChen.ActualPrimeIcoCellTestFunctions
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Catalog 5 alone: actual target-deleted, strictly decreasing prime pairs;
the original K compact trims; the actual ordinary upper residual difference.
Four literal affine rows and the original denominator floors supply the
mixed-boundary prime test. No Riemann integrability, prime limit, null-wall,
causal restoration, all-22 assembly, or numerical endpoint is a premise.

The final order is epsilon, fixed positive trim, one threshold, all later
positive even targets. This does not identify the ordinary residual saving
with a saving of the complete historically causal coefficient.
-/

namespace ImbalancedChen.P4ACatalogFivePrimeIntegral

noncomputable section
open scoped Classical BigOperators Topology Interval
open Set MeasureTheory Filter
open Certificates.AboveMuSecondCoarse
open P4AOriginalSecondPhysicalIntegral P4AOriginalSecondResidualSupplier

abbrev Point := Fin 2 → ℝ

def cube : Set Point :=
  logPrimeBox (fun _ : Fin 2 => (3 / 16 : ℝ)) (fun _ => rho)

def closedCube : Set Point := Icc (fun _ => (3 / 16 : ℝ)) (fun _ => rho)

def sourceRegion : Set Point := {t | (t 0,t 1) ∈ physicalDomain}

/-- Exact pullback of K's trim; weak boundary ownership is preserved. -/
def trimRegion (delta : ℝ) : Set Point :=
  {t | (t 0,t 1) ∈ trimmedRegion delta}

theorem mem_sourceRegion (t : Point) :
    t ∈ sourceRegion ↔ t 0 ∈ Ioo mu rho ∧ t 1 ∈ Ioo (lowerBoundary (t 0)) (t 0) :=
  physicalDomain_iff _ _

theorem trimRegion_subset_sourceRegion {delta : ℝ} (hd : 0 < delta) :
    trimRegion delta ⊆ sourceRegion := by
  intro t ht
  exact trimmedRegion_subset_physicalDomain hd ht

theorem sourceRegion_subset_cube : sourceRegion ⊆ cube := by
  intro t ht
  obtain ⟨hx,hy⟩ := (mem_sourceRegion t).mp ht
  have hxc : t 0 ∈ Icc mu rho := ⟨hx.1.le,hx.2.le⟩
  apply mem_logPrimeBox.mpr
  intro i
  fin_cases i
  · exact ⟨(by norm_num [mu] : (3/16:ℝ) ≤ mu).trans hx.1.le,hx.2⟩
  · exact ⟨(boundary_order hxc).1.trans hy.1.le,hy.2.trans hx.2⟩

theorem cube_subset_closedCube : cube ⊆ closedCube := by
  intro t ht
  exact ⟨fun i => (mem_logPrimeBox.mp ht i).1,
    fun i => (mem_logPrimeBox.mp ht i).2.le⟩

theorem isOpen_sourceRegion : IsOpen sourceRegion := by
  change IsOpen {t : Point | mu < t 0 ∧ t 0 < rho ∧
    lowerBoundary (t 0) < t 1 ∧ t 1 < t 0}
  exact (isOpen_lt continuous_const (continuous_apply 0)).inter
    ((isOpen_lt (continuous_apply 0) continuous_const).inter
      ((isOpen_lt (by unfold lowerBoundary; fun_prop) (continuous_apply 1)).inter
        (isOpen_lt (continuous_apply 1) (continuous_apply 0))))

theorem isClosed_trimRegion (delta : ℝ) : IsClosed (trimRegion delta) := by
  change IsClosed {t : Point | mu+delta ≤ t 0 ∧ t 0 ≤ rho-delta ∧
    lowerBoundary (t 0)+delta ≤ t 1 ∧ t 1 ≤ t 0-delta}
  exact (isClosed_le continuous_const (continuous_apply 0)).inter
    ((isClosed_le (continuous_apply 0) continuous_const).inter
      ((isClosed_le (by unfold lowerBoundary; fun_prop) (continuous_apply 1)).inter
        (isClosed_le (continuous_apply 1) (by fun_prop))))

theorem isCompact_trimRegion {delta : ℝ} (hd : 0 < delta) :
    IsCompact (trimRegion delta) :=
  (show IsCompact closedCube from isCompact_Icc).of_isClosed_subset
    (isClosed_trimRegion delta)
    ((trimRegion_subset_sourceRegion hd).trans
      (sourceRegion_subset_cube.trans cube_subset_closedCube))

/-- The actual four trim walls, in original coordinate order. -/
def trimForms : Fin 4 → Point →L[ℝ] ℝ :=
  ![-ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 0,
    -(3:ℝ) • ContinuousLinearMap.proj 0 - ContinuousLinearMap.proj 1,
    -ContinuousLinearMap.proj 0 + ContinuousLinearMap.proj 1]

def trimBounds (delta : ℝ) : Fin 4 → ℝ :=
  ![-(mu+delta),rho-delta,-(25/32+delta),-delta]

theorem trimForms_ne_zero (j : Fin 4) : trimForms j ≠ 0 := by
  fin_cases j <;> intro h
  all_goals
    have hv := congrArg (fun F : Point →L[ℝ] ℝ => F ![1,0]) h
    norm_num [trimForms] at hv

/-- Properness is proved from explicit rows, including at delta=0. -/
theorem ae_trim_no_wall (delta : ℝ) :
    ∀ᵐ t ∂(volume : Measure Point), ∀ j, trimForms j t ≠ trimBounds delta j :=
  ae_primeAffineGate_no_wall trimForms (trimBounds delta) trimForms_ne_zero

theorem strictGates_subset_trim (delta : ℝ) :
    primeAffineGateRegion trimForms (trimBounds delta) ⊆ trimRegion delta := by
  intro t ht
  have h0 := ht (0 : Fin 4)
  have h1 := ht (1 : Fin 4)
  have h2 := ht (2 : Fin 4)
  have h3 := ht (3 : Fin 4)
  norm_num [trimForms,trimBounds] at h0 h1 h2 h3
  change mu+delta ≤ t 0 ∧ t 0 ≤ rho-delta ∧
    lowerBoundary (t 0)+delta ≤ t 1 ∧ t 1 ≤ t 0-delta
  unfold lowerBoundary
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem trim_weak_gates (delta : ℝ) (t : Point) (ht : t ∈ trimRegion delta) :
    ∀ j, trimForms j t ≤ trimBounds delta j := by
  change mu+delta ≤ t 0 ∧ t 0 ≤ rho-delta ∧
    lowerBoundary (t 0)+delta ≤ t 1 ∧ t 1 ≤ t 0-delta at ht
  rcases ht with ⟨h0,h1,h2,h3⟩
  unfold lowerBoundary at h2
  intro j
  fin_cases j <;> norm_num [trimForms,trimBounds] <;> linarith

/-- The actual topological trim boundary is null, including empty trims. -/
theorem volume_frontier_trimRegion (delta : ℝ) :
    volume (frontier (trimRegion delta)) = 0 := by
  have hO : IsOpen (primeAffineGateRegion trimForms (trimBounds delta)) := by
    simpa only [primeAffineGateRegion,ofPred_forall] using
      isOpen_iInter_of_finite (fun j : Fin 4 =>
        isOpen_lt (trimForms j).continuous
          (continuous_const : Continuous (fun _ : Point => trimBounds delta j)))
  have ha : ∀ᵐ t ∂(volume : Measure Point), t ∉ frontier (trimRegion delta) := by
    filter_upwards [ae_trim_no_wall delta] with t ht
    intro hfront
    have htr := (isClosed_trimRegion delta).frontier_subset hfront
    have hstrict : t ∈ primeAffineGateRegion trimForms (trimBounds delta) :=
      fun j => lt_of_le_of_ne (trim_weak_gates delta t htr j) (ht j)
    exact ((mem_frontier_iff_notMem_interior htr).mp hfront)
      (interior_maximal (strictGates_subset_trim delta) hO hstrict)
  simpa only [ae_iff,not_not] using ha

theorem sourceRegion_eq_strictGates :
    sourceRegion = primeAffineGateRegion trimForms (trimBounds 0) := by
  ext t
  rw [mem_sourceRegion]
  constructor
  · rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩ j
    unfold lowerBoundary at h2
    fin_cases j <;> norm_num [trimForms,trimBounds] <;> linarith
  · intro ht
    have h0 := ht (0 : Fin 4)
    have h1 := ht (1 : Fin 4)
    have h2 := ht (2 : Fin 4)
    have h3 := ht (3 : Fin 4)
    norm_num [trimForms,trimBounds] at h0 h1 h2 h3
    unfold lowerBoundary
    exact ⟨⟨by linarith,h1⟩,⟨by linarith,by linarith⟩⟩

/-! Continuous extension, authenticated by the original denominator floors. -/

def safePhysical (t : Point) : ℝ :=
  4 * (endpointEnvelope (t 1)-endpointEnvelope (t 0)) /
    (max mu (t 0) * max (3/16:ℝ) (t 1) *
      max rho (endpointEnvelope (t 0)-t 0-t 1) *
      max rho (endpointEnvelope (t 1)-t 0-t 1))

theorem continuous_safePhysical : Continuous safePhysical := by
  have hx : Continuous (fun t : Point => t 0) := continuous_apply 0
  have hy : Continuous (fun t : Point => t 1) := continuous_apply 1
  have hvx := continuous_endpointEnvelope.comp hx
  have hvy := continuous_endpointEnvelope.comp hy
  apply (continuous_const.mul (hvy.sub hvx)).div
    ((((continuous_const.max hx).mul (continuous_const.max hy)).mul
      (continuous_const.max ((hvx.sub hx).sub hy))).mul
      (continuous_const.max ((hvy.sub hx).sub hy)))
  intro t
  have hm : 0 < mu := by norm_num [mu]
  have hr : 0 < rho := by norm_num [rho]
  exact (mul_pos (mul_pos (mul_pos
    (hm.trans_le (le_max_left _ _))
    ((by norm_num : (0:ℝ) < 3/16).trans_le (le_max_left _ _)))
    (hr.trans_le (le_max_left _ _)))
    (hr.trans_le (le_max_left _ _))).ne'

theorem safePhysical_eq {t : Point} (hx : t 0 ∈ Icc mu rho)
    (hy : t 1 ∈ Icc (lowerBoundary (t 0)) (t 0)) :
    safePhysical t = physicalKernel (t 0) (t 1) := by
  obtain ⟨h0,h1,h2,h3⟩ := physical_denominator_bounds hx hy
  simp only [safePhysical,physicalKernel,max_eq_right h0,max_eq_right h1,
    max_eq_right h2,max_eq_right h3]

def safeResidual (t : Point) : ℝ := safePhysical t * (t 0*t 1)

theorem continuous_safeResidual : Continuous safeResidual :=
  continuous_safePhysical.mul ((continuous_apply 0).mul (continuous_apply 1))

theorem safeResidual_eq {t : Point} (ht : t ∈ sourceRegion) :
    safeResidual t = residualSaving (t 0) (t 1) := by
  obtain ⟨hx,hy⟩ := (mem_sourceRegion t).mp ht
  have hxc : t 0 ∈ Icc mu rho := ⟨hx.1.le,hx.2.le⟩
  have hyc : t 1 ∈ Icc (lowerBoundary (t 0)) (t 0) := ⟨hy.1.le,hy.2.le⟩
  have hxp : 0 < t 0 := (by norm_num [mu] : 0 < mu).trans hx.1
  have hyp : 0 < t 1 := (by norm_num : (0:ℝ) < 3/16).trans_le
    ((boundary_order hxc).1.trans hy.1.le)
  rw [safeResidual,safePhysical_eq hxc hyc]
  exact ((div_eq_iff (mul_pos hxp hyp).ne').mp
    (residualSaving_div_eq_physicalKernel hxc hyc)).symm

theorem safeResidual_weighted {t : Point} (ht : t ∈ cube) :
    safeResidual t * (∏ i, 1 / t i) = safePhysical t := by
  have h0 : t 0 ≠ 0 := ne_of_gt
    ((by norm_num : (0:ℝ) < 3/16).trans_le (mem_logPrimeBox.mp ht 0).1)
  have h1 : t 1 ≠ 0 := ne_of_gt
    ((by norm_num : (0:ℝ) < 3/16).trans_le (mem_logPrimeBox.mp ht 1).1)
  simp only [safeResidual,Fin.prod_univ_two]
  field_simp [h0,h1]
  <;> ring

theorem integrableOn_safePhysical_source : IntegrableOn safePhysical sourceRegion :=
  ((continuous_safePhysical.continuousOn : ContinuousOn safePhysical closedCube).
    integrableOn_compact (show IsCompact closedCube from isCompact_Icc)).mono_set
      (sourceRegion_subset_cube.trans cube_subset_closedCube)

def trimIntegral (delta : ℝ) : ℝ := ∫ t in trimRegion delta, safePhysical t

/-- The integrand of the new limit is literally the original rational kernel. -/
theorem trimIntegral_eq_physical (delta : ℝ) (hd : 0 < delta) :
    trimIntegral delta = ∫ t in trimRegion delta, physicalKernel (t 0) (t 1) := by
  apply setIntegral_congr_fun (isClosed_trimRegion delta).measurableSet
  intro t ht
  obtain ⟨hx,hy⟩ := (mem_sourceRegion t).mp (trimRegion_subset_sourceRegion hd ht)
  exact safePhysical_eq ⟨hx.1.le,hx.2.le⟩ ⟨hy.1.le,hy.2.le⟩

theorem trimIntegral_eq_original_upperProfile (delta : ℝ) (hd : 0 < delta) :
    trimIntegral delta = ∫ t in trimRegion delta, sourceProfileKernel (t 0) (t 1) := by
  rw [trimIntegral_eq_physical delta hd]
  apply setIntegral_congr_fun (isClosed_trimRegion delta).measurableSet
  intro t ht
  obtain ⟨hx,hy⟩ := (mem_sourceRegion t).mp (trimRegion_subset_sourceRegion hd ht)
  exact (sourceProfileKernel_eq_physicalKernel
    ⟨hx.1.le,hx.2.le⟩ ⟨hy.1.le,hy.2.le⟩).symm

/-- The carrier really consists of strict pairs avoiding the same target. -/
theorem trimmed_actual_pair_source {delta : ℝ} (hd : 0 < delta)
    {N : ℕ} (hN : 1 < N) {p : Fin 2 → ℕ} (hp : p ∈ trimmedPrimePairs delta N) :
    (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N) ∧ p 1 < p 0 ∧ (∏ i, p i).Coprime N := by
  have h := trimmedPrimePairs_prime_target hp
  exact ⟨h.1,trimmedPrimePairs_strict_order hd hN hp,h.2⟩

/-- Exact arithmetic sum identity; no prime tuple or weak trim face is removed. -/
theorem profileSum_eq_testSum (delta : ℝ) (hd : 0 < delta) (N : ℕ) :
    trimmedRationalProfileSum delta N =
      actualPrimeBoxTestSum N (fun _ : Fin 2 => (3/16:ℝ)) (fun _ => rho)
        ((trimRegion delta).indicator safeResidual) := by
  unfold trimmedRationalProfileSum trimmedPrimePairs actualPrimeBoxTestSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases ht : (actualPrimeTupleLog N p 0,actualPrimeTupleLog N p 1) ∈ trimmedRegion delta
  · have htr : actualPrimeTupleLog N p ∈ trimRegion delta := ht
    rw [if_pos ht,indicator_of_mem htr,
      safeResidual_eq (trimRegion_subset_sourceRegion hd htr)]
  · have htr : actualPrimeTupleLog N p ∉ trimRegion delta := ht
    rw [if_neg ht,indicator_of_notMem htr,mul_zero]

/-- Genuine target-deleted reciprocal-prime test applied to K's rational profile. -/
theorem tendsto_trimmedRationalProfileSum (delta : ℝ) (hd : 0 < delta) :
    Tendsto (trimmedRationalProfileSum delta) atTop (𝓝 (trimIntegral delta)) := by
  have ht := tendsto_actualPrimeBoxTestSum_cube_affineSandwich
    (by norm_num : (0:ℝ) < 3/16) (by norm_num [rho] : (3/16:ℝ) < rho)
    trimForms (trimBounds delta) trimForms_ne_zero
    (trimRegion delta) (isClosed_trimRegion delta).measurableSet
    (strictGates_subset_trim delta) (trim_weak_gates delta)
    safeResidual continuous_safeResidual.continuousOn
  have hset : cube ∩ trimRegion delta = trimRegion delta :=
    inter_eq_right.mpr ((trimRegion_subset_sourceRegion hd).trans sourceRegion_subset_cube)
  have hint : (∫ t in cube ∩ trimRegion delta,
      safeResidual t * ∏ i, 1 / t i) = trimIntegral delta := by
    rw [hset]
    apply setIntegral_congr_fun (isClosed_trimRegion delta).measurableSet
    intro t htr
    exact safeResidual_weighted (sourceRegion_subset_cube (trimRegion_subset_sourceRegion hd htr))
  change Tendsto _ atTop (𝓝 (∫ t in cube ∩ trimRegion delta,
    safeResidual t * ∏ i, 1 / t i)) at ht
  rw [hint] at ht
  exact ht.congr' (Eventually.of_forall (fun N => (profileSum_eq_testSum delta hd N).symm))

/-- Fixed trim first; a single limit for the actual original ordinary residual sum. -/
theorem tendsto_trimmedArithmeticSaving (delta : ℝ) (hd : 0 < delta) :
    Tendsto (trimmedArithmeticSaving delta)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 (trimIntegral delta)) := by
  have hp := (tendsto_trimmedRationalProfileSum delta hd).mono_left
    (show atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N} ≤ atTop from inf_le_left)
  have h := (tendsto_trimmedArithmeticSaving_sub_profile delta hd).add hp
  simpa only [sub_add_cancel,zero_add] using h

/-! Genuine product-volume identification with the original iterated integral. -/

private theorem integral_fin_two (F : Point → ℝ) (hF : Integrable F) :
    (∫ t, F t) = ∫ x : ℝ, ∫ y : ℝ, F ![x,y] := by
  let E := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hE : MeasurePreserving E := volume_preserving_piFinTwo _
  have hi : Integrable (fun p : ℝ × ℝ => F (E.symm p)) :=
    hE.symm.integrable_comp_of_integrable hF
  have hvec (x y : ℝ) : E.symm (x,y) = ![x,y] := by
    ext i
    fin_cases i <;> rfl
  calc
    _ = ∫ p : ℝ × ℝ, F (E.symm p) := (hE.symm.integral_comp' F).symm
    _ = _ := by simpa only [hvec] using integral_prod _ hi

private theorem integral_fixed_indicator (s : Set ℝ) (x : ℝ) (F : ℝ → ℝ → ℝ) :
    (∫ y : ℝ, s.indicator (fun x => F x y) x) =
      s.indicator (fun x => ∫ y : ℝ, F x y) x := by
  by_cases hx : x ∈ s <;> simp [hx]

private theorem source_indicator_vec (x y : ℝ) :
    sourceRegion.indicator safePhysical ![x,y] =
      (Ioo mu rho).indicator (fun x =>
        (Ioo (lowerBoundary x) x).indicator (physicalKernel x) y) x := by
  have hm : ![x,y] ∈ sourceRegion ↔ x ∈ Ioo mu rho ∧ y ∈ Ioo (lowerBoundary x) x :=
    mem_sourceRegion ![x,y]
  by_cases hx : x ∈ Ioo mu rho
  · rw [indicator_of_mem hx]
    by_cases hy : y ∈ Ioo (lowerBoundary x) x
    · rw [indicator_of_mem hy,indicator_of_mem (hm.mpr ⟨hx,hy⟩)]
      exact safePhysical_eq ⟨hx.1.le,hx.2.le⟩ ⟨hy.1.le,hy.2.le⟩
    · rw [indicator_of_notMem hy,indicator_of_notMem (fun ht => hy (hm.mp ht).2)]
  · rw [indicator_of_notMem hx,indicator_of_notMem (fun ht => hx (hm.mp ht).1)]

private theorem integral_Ioo_eq_interval {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ x in Ioo a b, f x) = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab,integral_Ioc_eq_integral_Ioo]

theorem sourceLebesgueIntegral_eq_physicalSaving :
    (∫ t in sourceRegion, safePhysical t) = physicalSaving := by
  have hF := integrableOn_safePhysical_source.integrable_indicator isOpen_sourceRegion.measurableSet
  calc
    _ = ∫ t, sourceRegion.indicator safePhysical t :=
      (integral_indicator isOpen_sourceRegion.measurableSet).symm
    _ = ∫ x : ℝ, ∫ y : ℝ, sourceRegion.indicator safePhysical ![x,y] :=
      integral_fin_two _ hF
    _ = ∫ x in Ioo mu rho, ∫ y in Ioo (lowerBoundary x) x, physicalKernel x y := by
      simp_rw [source_indicator_vec,integral_fixed_indicator,
        integral_indicator measurableSet_Ioo]
    _ = physicalSaving := by
      rw [integral_Ioo_eq_interval (by norm_num [mu,rho])]
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num [mu,rho])] at hx
      exact integral_Ioo_eq_interval ((boundary_order hx).2.1.trans hx.1) _

/-! Delta loss: the literal compact interiors exhaust the original source. -/

def width (n : ℕ) : ℝ := 1 / (n+1:ℝ)

theorem width_pos (n : ℕ) : 0 < width n := by unfold width; positivity

theorem width_tendsto : Tendsto width atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem source_eventually_retained {t : Point} (ht : t ∈ sourceRegion) :
    ∀ᶠ n : ℕ in atTop, t ∈ trimRegion (width n) := by
  obtain ⟨hx,hy⟩ := (mem_sourceRegion t).mp ht
  filter_upwards
    [width_tendsto.eventually (gt_mem_nhds (sub_pos.mpr hx.1)),
     width_tendsto.eventually (gt_mem_nhds (sub_pos.mpr hx.2)),
     width_tendsto.eventually (gt_mem_nhds (sub_pos.mpr hy.1)),
     width_tendsto.eventually (gt_mem_nhds (sub_pos.mpr hy.2))] with n h0 h1 h2 h3
  change mu+width n ≤ t 0 ∧ t 0 ≤ rho-width n ∧
    lowerBoundary (t 0)+width n ≤ t 1 ∧ t 1 ≤ t 0-width n
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem tendsto_trimIntegral :
    Tendsto (fun n => trimIntegral (width n)) atTop (𝓝 physicalSaving) := by
  let F : ℕ → Point → ℝ := fun n => (trimRegion (width n)).indicator safePhysical
  let G : Point → ℝ := sourceRegion.indicator safePhysical
  let bound : Point → ℝ := sourceRegion.indicator (fun t => |safePhysical t|)
  have hb : Integrable bound :=
    integrableOn_safePhysical_source.abs.integrable_indicator isOpen_sourceRegion.measurableSet
  have hF (n : ℕ) : Integrable (F n) :=
    (integrableOn_safePhysical_source.mono_set
      (trimRegion_subset_sourceRegion (width_pos n))).integrable_indicator
        (isClosed_trimRegion _).measurableSet
  have hlim := tendsto_integral_of_dominated_convergence bound
    (fun n => (hF n).aestronglyMeasurable) hb
    (fun n => Eventually.of_forall (fun t => by
      by_cases ht : t ∈ trimRegion (width n)
      · simp only [F,bound,indicator_of_mem ht,
          indicator_of_mem (trimRegion_subset_sourceRegion (width_pos n) ht),
          Real.norm_eq_abs,le_refl]
      · rw [show F n t = 0 from indicator_of_notMem ht _]
        rw [norm_zero]
        exact indicator_nonneg (fun _ _ => abs_nonneg _) t))
    (show ∀ᵐ t ∂(volume : Measure Point),
      Tendsto (fun n => F n t) atTop (𝓝 (G t)) from Eventually.of_forall (fun t => by
      apply tendsto_const_nhds.congr'
      by_cases ht : t ∈ sourceRegion
      · filter_upwards [source_eventually_retained ht] with n hn
        simp only [F,G,indicator_of_mem ht,indicator_of_mem hn]
      · exact Eventually.of_forall (fun n => by
          have hn : t ∉ trimRegion (width n) := fun h =>
            ht (trimRegion_subset_sourceRegion (width_pos n) h)
          simp only [F,G,indicator_of_notMem ht,indicator_of_notMem hn])))
  simpa only [F,G,integral_indicator (isClosed_trimRegion _).measurableSet,
    integral_indicator isOpen_sourceRegion.measurableSet,
    sourceLebesgueIntegral_eq_physicalSaving,trimIntegral] using hlim

def discarded (delta : ℝ) : Set Point := sourceRegion \ trimRegion delta

theorem measurableSet_discarded (delta : ℝ) : MeasurableSet (discarded delta) :=
  isOpen_sourceRegion.measurableSet.diff (isClosed_trimRegion delta).measurableSet

/-- Absolute discarded mass, not cancellation of a signed integral. -/
theorem tendsto_discarded_absoluteIntegral :
    Tendsto (fun n => ∫ t in discarded (width n), |safePhysical t|) atTop (𝓝 0) := by
  let F : ℕ → Point → ℝ := fun n =>
    (discarded (width n)).indicator (fun t => |safePhysical t|)
  let bound : Point → ℝ := sourceRegion.indicator (fun t => |safePhysical t|)
  have hb : Integrable bound :=
    integrableOn_safePhysical_source.abs.integrable_indicator isOpen_sourceRegion.measurableSet
  have hF (n : ℕ) : Integrable (F n) :=
    (integrableOn_safePhysical_source.abs.mono_set
      (show discarded (width n) ⊆ sourceRegion from diff_subset)).integrable_indicator
        (measurableSet_discarded _)
  have hlim := tendsto_integral_of_dominated_convergence bound
    (fun n => (hF n).aestronglyMeasurable) hb
    (fun n => Eventually.of_forall (fun t => by
      by_cases ht : t ∈ discarded (width n)
      · simp only [F,bound,indicator_of_mem ht,indicator_of_mem ht.1,
          Real.norm_eq_abs,abs_abs,le_refl]
      · rw [show F n t = 0 from indicator_of_notMem ht _,norm_zero]
        exact indicator_nonneg (fun _ _ => abs_nonneg _) t))
    (show ∀ᵐ t ∂(volume : Measure Point),
      Tendsto (fun n => F n t) atTop (𝓝 (0:ℝ)) from Eventually.of_forall (fun t => by
      apply tendsto_const_nhds.congr'
      by_cases ht : t ∈ sourceRegion
      · filter_upwards [source_eventually_retained ht] with n hn
        exact (indicator_of_notMem (by simp [discarded,hn]) _).symm
      · exact Eventually.of_forall (fun n =>
          (indicator_of_notMem (fun h => ht h.1) _).symm)))
  simpa only [F,integral_indicator (measurableSet_discarded _),integral_zero] using hlim

theorem abs_physicalSaving_sub_trim_le (delta : ℝ) (hd : 0 < delta) :
    |physicalSaving-trimIntegral delta| ≤
      ∫ t in discarded delta, |safePhysical t| := by
  have heq := setIntegral_sdiff (isClosed_trimRegion delta).measurableSet
    integrableOn_safePhysical_source (trimRegion_subset_sourceRegion hd)
  rw [sourceLebesgueIntegral_eq_physicalSaving] at heq
  change (∫ t in discarded delta, safePhysical t) = physicalSaving-trimIntegral delta at heq
  rw [← heq]
  simpa only [Real.norm_eq_abs] using
    (norm_integral_le_integral_norm (μ := volume.restrict (discarded delta)) safePhysical)

theorem exists_trim_loss (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ |trimIntegral delta-physicalSaving| < epsilon := by
  obtain ⟨n,hn⟩ := (Metric.tendsto_nhds.mp tendsto_trimIntegral epsilon he).exists
  exact ⟨width n,width_pos n,by simpa only [Real.dist_eq] using hn⟩

/-- Actual saving limit in the required order. The trim is fixed before N0.
This is the catalog5 ordinary-residual source, not a causal-tree identity. -/
theorem exists_trim_then_actual_threshold (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ |trimIntegral delta-physicalSaving| < epsilon/2 ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
        |trimmedArithmeticSaving delta N-physicalSaving| < epsilon := by
  obtain ⟨delta,hd,htrim⟩ := exists_trim_loss (epsilon/2) (half_pos he)
  have hactual := Metric.tendsto_nhds.mp (tendsto_trimmedArithmeticSaving delta hd)
    (epsilon/2) (half_pos he)
  have hevent : ∀ᶠ N : ℕ in atTop, 0 < N ∧ Even N →
      |trimmedArithmeticSaving delta N-trimIntegral delta| < epsilon/2 := by
    simpa only [eventually_inf_principal,mem_setOf_eq,Real.dist_eq] using hactual
  obtain ⟨N1,hN1⟩ := eventually_atTop.mp hevent
  refine ⟨delta,hd,htrim,max 2 N1,le_max_left _ _,?_⟩
  intro N hN hEven
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have h := hN1 N ((le_max_right _ _).trans hN) ⟨by omega,hEven⟩
  exact (abs_sub_le _ (trimIntegral delta) _).trans_lt (by linarith)

/-- The authenticated catalog5 endpoint is approached from the actual prime
source, after choosing one trim. No reserves or other savings are reallocated. -/
theorem exists_catalogFive_actual_lower_threshold (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N →
        (640339/15210735000:ℝ)-epsilon < trimmedArithmeticSaving delta N := by
  obtain ⟨delta,hd,_,N0,hN0,hbound⟩ := exists_trim_then_actual_threshold epsilon he
  refine ⟨delta,hd,N0,hN0,?_⟩
  intro N hN hEven
  have h := (abs_lt.mp (hbound N hN hEven)).1
  linarith [original_physical_saving_ge_catalog_five]

/-- The same final threshold targets the actual continuous upper-factor integral. -/
theorem exists_originalProfile_actual_threshold (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N →
        |trimmedArithmeticSaving delta N-sourceProfileSaving| < epsilon := by
  obtain ⟨delta,hd,_,N0,hN0,hbound⟩ := exists_trim_then_actual_threshold epsilon he
  refine ⟨delta,hd,N0,hN0,?_⟩
  simpa only [sourceProfileSaving_eq_physicalSaving] using hbound

end
end ImbalancedChen.P4ACatalogFivePrimeIntegral
