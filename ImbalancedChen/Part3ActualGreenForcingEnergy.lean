import ImbalancedChen.Part3ActualGreenForcingRegularity
import ImbalancedChen.Part3GeneralIRealPositiveEndpoint
import ImbalancedChen.Part3GeneralKRightEndpoint
import Mathlib.Topology.Order.Compact

/-!
The literal compact-forcing Green solution has finite actual form energy.
Its two remote branches and their native derivatives are calculated exactly.
The extra potential weight exp(r) is paid by an actual q*K(q) estimate on
the right and bounded multiplication on the genuine I left tail.
No energy or form-membership hypothesis is supplied.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualGreenForcingEnergy20261025a

noncomputable section
open Set MeasureTheory Filter Topology
open GeneralActualRadialGreenSourceOnly ComplexOrderKRadialRegularitySourceOnly
open ActualGreenCompactForcing20261025a ActualGreenForcingRegularity20261025a
open GeneralIRealPositiveEndpoint20261025a GeneralKRightEndpoint20261025a
open ComplexOrderKBridgeSourceOnly

private theorem legal_order {nu : ℝ} (hnu : 0 < nu) : -1 < (nu : ℂ).re := by
  simp only [Complex.ofReal_re]
  linarith

private theorem left_amplitudes {nu : ℂ} (hnu : -1 < nu.re)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    {A r : ℝ} (hzero : ∀ s ≤ A, f s = 0) (hr : r ≤ A) :
    leftAmplitude nu f r = 0 ∧
      rightAmplitude nu f r = ∫ s : ℝ, radialK nu s * f s := by
  have hz (g : ℝ → ℂ) : (∫ s in Iic r, g s * f s) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro s hs
    rw [hzero s (hs.trans hr), mul_zero]
  refine ⟨hz _, ?_⟩
  have hKi := ((radialK_C2 nu).continuous.mul hf).integrable_of_hasCompactSupport hc.mul_left
  have hs := integral_add_compl (s := Iic r) measurableSet_Iic hKi
  rw [compl_Iic, hz _, zero_add] at hs
  exact hs

private theorem right_amplitudes {nu : ℂ} (hnu : -1 < nu.re)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    {B r : ℝ} (hzero : ∀ s, B ≤ s → f s = 0) (hr : B ≤ r) :
    leftAmplitude nu f r = (∫ s : ℝ, radialI nu s * f s) ∧
      rightAmplitude nu f r = 0 := by
  have hz (g : ℝ → ℂ) : (∫ s in Ioi r, g s * f s) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro s hs
    rw [hzero s (hr.trans hs.le), mul_zero]
  refine ⟨?_, hz _⟩
  have hIi := ((radialI_C2 hnu).continuous.mul hf).integrable_of_hasCompactSupport hc.mul_left
  have hs := integral_add_compl (s := Iic r) measurableSet_Iic hIi
  rw [compl_Iic, hz _, add_zero] at hs
  exact hs

/-- The actual solution is exactly a fixed I mode left of the forcing.
The fixed coefficient is its literal K-forcing integral. -/
theorem greenForcing_left_tail {nu : ℂ} (hnu : -1 < nu.re)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    {A r : ℝ} (hzero : ∀ s ≤ A, f s = 0) (hr : r ≤ A) :
    greenForcing nu f r = radialI nu r * (∫ s : ℝ, radialK nu s * f s) := by
  obtain ⟨hL, hR⟩ := left_amplitudes hnu hf hc hzero hr
  rw [greenForcing_eq_amplitudes hnu hf hc, hL, hR, mul_zero, zero_add]

/-- The same left formula for the native real derivative of the solution. -/
theorem greenForcing_deriv_left_tail {nu : ℂ} (hnu : -1 < nu.re)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    {A r : ℝ} (hzero : ∀ s ≤ A, f s = 0) (hr : r ≤ A) :
    deriv (greenForcing nu f) r =
      deriv (radialI nu) r * (∫ s : ℝ, radialK nu s * f s) := by
  obtain ⟨hL, hR⟩ := left_amplitudes hnu hf hc hzero hr
  rw [(greenForcing_hasDerivAt hnu hf hc r).deriv, greenForcingFirst,
    hL, hR, mul_zero, zero_add]

/-- The actual solution is exactly a fixed K mode right of the forcing. -/
theorem greenForcing_right_tail {nu : ℂ} (hnu : -1 < nu.re)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    {B r : ℝ} (hzero : ∀ s, B ≤ s → f s = 0) (hr : B ≤ r) :
    greenForcing nu f r = radialK nu r * (∫ s : ℝ, radialI nu s * f s) := by
  obtain ⟨hL, hR⟩ := right_amplitudes hnu hf hc hzero hr
  rw [greenForcing_eq_amplitudes hnu hf hc, hL, hR, mul_zero, add_zero]

/-- The native derivative has the same fixed coefficient on the right. -/
theorem greenForcing_deriv_right_tail {nu : ℂ} (hnu : -1 < nu.re)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    {B r : ℝ} (hzero : ∀ s, B ≤ s → f s = 0) (hr : B ≤ r) :
    deriv (greenForcing nu f) r =
      deriv (radialK nu) r * (∫ s : ℝ, radialI nu s * f s) := by
  obtain ⟨hL, hR⟩ := right_amplitudes hnu hf hc hzero hr
  rw [(greenForcing_hasDerivAt hnu hf hc r).deriv, greenForcingFirst,
    hL, hR, mul_zero, add_zero]

private theorem q_exp_absorption (q : ℝ) :
    q * Real.exp (1 - q) ≤ 2 * Real.exp 1 * Real.exp (-q / 2) := by
  have hq : q ≤ 2 * Real.exp (q / 2) := by
    have := Real.add_one_le_exp (q / 2)
    linarith
  calc
    q * Real.exp (1 - q) ≤ 2 * Real.exp (q / 2) * Real.exp (1 - q) :=
      mul_le_mul_of_nonneg_right hq (Real.exp_pos _).le
    _ = 2 * Real.exp 1 * Real.exp (-q / 2) := by
      rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The extra actual potential factor q multiplying K is absorbed by
its proved exp(-q) moment estimate, for every complex order. -/
theorem q_complexOrderK_exp_bound (nu : ℂ) {q : ℝ} (hq : 1 ≤ q) :
    ‖(q : ℂ) * complexOrderK nu q‖ ≤
      (2 * Real.exp 1 * momentMass 0 nu) * Real.exp (-q / 2) := by
  have hqpos : 0 < q := by linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos]
  calc
    q * ‖complexOrderK nu q‖ ≤ q * (Real.exp (1 - q) * momentMass 0 nu) :=
      mul_le_mul_of_nonneg_left (complexOrderK_norm_exp_bound nu hq) hqpos.le
    _ ≤ (2 * Real.exp 1 * momentMass 0 nu) * Real.exp (-q / 2) := by
      have h := mul_le_mul_of_nonneg_right (q_exp_absorption q) (momentMass_nonneg 0 nu)
      nlinarith only [h]

/-- A concrete dr envelope for exp(r)*K(exp r), with its actual finite
moment constant. In particular the potential weight is integrable. -/
theorem exponential_radialK_norm_bound (nu : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ‖(Real.exp r : ℂ) * radialK nu r‖ ≤
      (2 * Real.exp 1 * momentMass 0 nu) * Real.exp (-(r / 2)) := by
  have hq : 1 ≤ Real.exp r := by simpa using Real.exp_le_exp.mpr hr
  apply (q_complexOrderK_exp_bound nu hq).trans
  apply mul_le_mul_of_nonneg_left _ (by
    exact mul_nonneg (by positivity) (momentMass_nonneg 0 nu))
  apply Real.exp_le_exp.mpr
  have := Real.add_one_le_exp r
  linarith

/-- The actual potential-weighted K mode is in right-end L2(dr). -/
theorem exponential_radialK_memLp_two_Ioi (nu : ℂ) :
    MemLp (fun r : ℝ => (Real.exp r : ℂ) * radialK nu r) 2
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hf : Continuous (fun r : ℝ => (Real.exp r : ℂ) * radialK nu r) :=
    (Complex.continuous_ofReal.comp Real.continuous_exp).mul (radialK_C2 nu).continuous
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  let C : ℝ := 2 * Real.exp 1 * momentMass 0 nu
  have he : IntegrableOn (fun r : ℝ => C ^ 2 * Real.exp (-r)) (Ioi 0) := by
    simpa only [neg_one_mul] using
      (integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) 0).const_mul (C ^ 2)
  apply he.mono' (hf.norm.pow 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hsq := pow_le_pow_left₀ (norm_nonneg ((Real.exp r : ℂ) * radialK nu r))
    (exponential_radialK_norm_bound nu hr.le) 2
  have hexp : (Real.exp (-(r / 2))) ^ 2 = Real.exp (-r) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [mul_pow, hexp] at hsq
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), C] using hsq

private theorem tail_congr {u v : ℝ → ℂ} {S : Set ℝ} (hS : MeasurableSet S)
    (hv : MemLp v 2 (volume.restrict S)) (he : ∀ r ∈ S, u r = v r) :
    MemLp u 2 (volume.restrict S) := by
  apply (memLp_congr_ae (show u =ᵐ[volume.restrict S] v from ?_)).mpr hv
  filter_upwards [ae_restrict_mem hS] with r hr
  exact he r hr

private theorem glue_two_tails {u : ℝ → ℂ} (hu : Continuous u) {A B : ℝ}
    (hL : MemLp u 2 (volume.restrict (Iic A)))
    (hR : MemLp u 2 (volume.restrict (Ioi B))) : MemLp u 2 (volume : Measure ℝ) := by
  have hiL := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hL
  have hiR := (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hR
  have hiC : IntegrableOn (fun r : ℝ => ‖u r‖ ^ 2) (Icc A B) :=
    (hu.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hi := (hiL.union hiC).union hiR
  have hcover : Iic A ∪ Icc A B ∪ Ioi B = (univ : Set ℝ) := by
    ext r
    simp only [mem_union, mem_Iic, mem_Icc, mem_Ioi, mem_univ, iff_true]
    by_cases hA : r ≤ A
    · exact Or.inl (Or.inl hA)
    · by_cases hB : r ≤ B
      · exact Or.inl (Or.inr ⟨(lt_of_not_ge hA).le, hB⟩)
      · exact Or.inr (lt_of_not_ge hB)
  apply (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mpr
  simpa only [hcover, integrableOn_univ] using hi

private theorem actual_forcing_energy {nu : ℝ} (hnu : 0 < nu) (hnuUpper : nu < 1)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    MemLp (greenForcing (nu : ℂ) f) 2 (volume : Measure ℝ) ∧
      MemLp (deriv (greenForcing (nu : ℂ) f)) 2 (volume : Measure ℝ) ∧
      MemLp (fun r : ℝ => (Real.exp r : ℂ) * greenForcing (nu : ℂ) f r) 2
        (volume : Measure ℝ) := by
  have hn := legal_order hnu
  have hC2 := greenForcing_C2
    (show 0 < (nu : ℂ).re by simpa using hnu)
    (show (nu : ℂ).re < 1 by simpa using hnuUpper) hf hc
  have hU := hC2.continuous
  have hD := hC2.continuous_deriv (by norm_num)
  have hE : Continuous (fun r : ℝ => (Real.exp r : ℂ) * greenForcing (nu : ℂ) f r) :=
    (Complex.continuous_ofReal.comp Real.continuous_exp).mul hU
  obtain ⟨R, hi, hd⟩ := exists_left_log_L2 hnu
  have hI : MemLp (radialI (nu : ℂ)) 2 (volume.restrict (Iic R)) := by
    simpa only [radialI, realILogMode] using hi
  have hID : MemLp (deriv (radialI (nu : ℂ))) 2 (volume.restrict (Iic R)) := by
    simpa only [radialI, realILogMode] using hd
  obtain ⟨a, ha⟩ := hc.isCompact.bddBelow
  obtain ⟨b, hb⟩ := hc.isCompact.bddAbove
  let A : ℝ := min (a - 1) R
  let B : ℝ := max (b + 1) 0
  have hAR : A ≤ R := min_le_right _ _
  have hAa : A ≤ a - 1 := min_le_left _ _
  have hB0 : 0 ≤ B := le_max_right _ _
  have hbB : b + 1 ≤ B := le_max_left _ _
  have hzL : ∀ s ≤ A, f s = 0 := by
    intro s hs
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hsa := ha hmem
    linarith
  have hzR : ∀ s, B ≤ s → f s = 0 := by
    intro s hs
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hsb := hb hmem
    linarith
  have hIA := hI.mono_measure (Measure.restrict_mono
    (show Iic A ⊆ Iic R from fun r hr => hr.trans hAR) le_rfl)
  have hIDA := hID.mono_measure (Measure.restrict_mono
    (show Iic A ⊆ Iic R from fun r hr => hr.trans hAR) le_rfl)
  have hKB := (radialK_memLp_two_Ioi (nu : ℂ)).mono_measure (Measure.restrict_mono
    (show Ioi B ⊆ Ioi (0 : ℝ) from fun r hr => lt_of_le_of_lt hB0 hr) le_rfl)
  have hKDB := (radialK_deriv_memLp_two_Ioi (nu : ℂ)).mono_measure (Measure.restrict_mono
    (show Ioi B ⊆ Ioi (0 : ℝ) from fun r hr => lt_of_le_of_lt hB0 hr) le_rfl)
  have hKEB := (exponential_radialK_memLp_two_Ioi (nu : ℂ)).mono_measure (Measure.restrict_mono
    (show Ioi B ⊆ Ioi (0 : ℝ) from fun r hr => lt_of_le_of_lt hB0 hr) le_rfl)
  have hIEA : MemLp (fun r : ℝ => (Real.exp r : ℂ) * radialI (nu : ℂ) r) 2
      (volume.restrict (Iic A)) := by
    apply (hIA.const_mul (Real.exp R : ℂ)).of_le
      (((Complex.continuous_ofReal.comp Real.continuous_exp).mul
        (radialI_C2 hn).continuous).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Iic] with r hr
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (Real.exp_pos r), abs_of_pos (Real.exp_pos R)]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hr.trans hAR)) (norm_nonneg _)
  have hUL : MemLp (greenForcing (nu : ℂ) f) 2 (volume.restrict (Iic A)) := by
    apply tail_congr measurableSet_Iic (hIA.mul_const (∫ s : ℝ, radialK (nu : ℂ) s * f s))
    intro r hr
    exact greenForcing_left_tail hn hf hc hzL hr
  have hUR : MemLp (greenForcing (nu : ℂ) f) 2 (volume.restrict (Ioi B)) := by
    apply tail_congr measurableSet_Ioi (hKB.mul_const (∫ s : ℝ, radialI (nu : ℂ) s * f s))
    intro r hr
    exact greenForcing_right_tail hn hf hc hzR hr.le
  have hDL : MemLp (deriv (greenForcing (nu : ℂ) f)) 2 (volume.restrict (Iic A)) := by
    apply tail_congr measurableSet_Iic (hIDA.mul_const (∫ s : ℝ, radialK (nu : ℂ) s * f s))
    intro r hr
    exact greenForcing_deriv_left_tail hn hf hc hzL hr
  have hDR : MemLp (deriv (greenForcing (nu : ℂ) f)) 2 (volume.restrict (Ioi B)) := by
    apply tail_congr measurableSet_Ioi (hKDB.mul_const (∫ s : ℝ, radialI (nu : ℂ) s * f s))
    intro r hr
    exact greenForcing_deriv_right_tail hn hf hc hzR hr.le
  have hEL : MemLp (fun r : ℝ => (Real.exp r : ℂ) * greenForcing (nu : ℂ) f r) 2
      (volume.restrict (Iic A)) := by
    apply tail_congr measurableSet_Iic (hIEA.mul_const (∫ s : ℝ, radialK (nu : ℂ) s * f s))
    intro r hr
    rw [greenForcing_left_tail hn hf hc hzL hr]
    ring
  have hER : MemLp (fun r : ℝ => (Real.exp r : ℂ) * greenForcing (nu : ℂ) f r) 2
      (volume.restrict (Ioi B)) := by
    apply tail_congr measurableSet_Ioi (hKEB.mul_const (∫ s : ℝ, radialI (nu : ℂ) s * f s))
    intro r hr
    rw [greenForcing_right_tail hn hf hc hzR hr.le]
    ring
  exact ⟨glue_two_tails hU hUL hUR, glue_two_tails hD hDL hDR, glue_two_tails hE hEL hER⟩

/-- Whole-line L2 for the literal compact-forcing Green solution. -/
theorem greenForcing_memLp_two {nu : ℝ} (hnu : 0 < nu) (hnuUpper : nu < 1)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    MemLp (greenForcing (nu : ℂ) f) 2 (volume : Measure ℝ) :=
  (actual_forcing_energy hnu hnuUpper hf hc).1

/-- Whole-line L2 for its actual native derivative. -/
theorem greenForcing_deriv_memLp_two {nu : ℝ} (hnu : 0 < nu) (hnuUpper : nu < 1)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    MemLp (deriv (greenForcing (nu : ℂ) f)) 2 (volume : Measure ℝ) :=
  (actual_forcing_energy hnu hnuUpper hf hc).2.1

/-- The actual exp(r) potential weight also belongs to whole-line L2. -/
theorem greenForcing_exponential_memLp_two {nu : ℝ} (hnu : 0 < nu) (hnuUpper : nu < 1)
    {f : ℝ → ℂ} (hf : Continuous f) (hc : HasCompactSupport f) :
    MemLp (fun r : ℝ => (Real.exp r : ℂ) * greenForcing (nu : ℂ) f r) 2
      (volume : Measure ℝ) :=
  (actual_forcing_energy hnu hnuUpper hf hc).2.2

end
end ImbalancedChen.Part3.ActualGreenForcingEnergy20261025a
