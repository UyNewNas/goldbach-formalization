import ImbalancedChen.Part3ActualRadialGreenMassBound
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The actual positive I/K Green kernel satisfies the Schur L² estimate on
genuine continuous compact forcing. Row Cauchy--Schwarz is proved with the
actual square-root kernel; product integrability and Fubini use the actual
column mass bound. No Schur, boundary, or operator-norm premise is supplied.
The native L² extension and agreement with a closed resolvent are separate.
-/

namespace ImbalancedChen.Part3.ActualRadialGreenSchur20261025a

noncomputable section
open Set MeasureTheory Filter
open GeneralActualRadialGreenSourceOnly ComplexOrderKRadialRegularitySourceOnly
open ActualRadialGreenMassBound20261025a

def greenAction (nu : ℝ) (f : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ r : ℝ, realGreen nu s r • f r

def rowEnergy (nu : ℝ) (f : ℝ → ℂ) (s : ℝ) : ℝ :=
  ∫ r : ℝ, realGreen nu s r * ‖f r‖^2

private theorem realGreen_nonneg {nu : ℝ} (hnu : 0 < nu) (s r : ℝ) :
    0 ≤ realGreen nu s r := (realGreen_pos hnu s r).le

theorem realGreen_joint_continuous {nu : ℝ} (hnu : 0 < nu) :
    Continuous (fun p : ℝ × ℝ => realGreen nu p.1 p.2) := by
  have hi : -1 < (nu : ℂ).re := by simpa using (show -1 < nu by linarith)
  change Continuous (fun p : ℝ × ℝ =>
    (radialI (nu : ℂ) (min p.2 p.1) * radialK (nu : ℂ) (max p.2 p.1)).re)
  exact (((radialI_C2 hi).continuous.comp (continuous_snd.min continuous_fst)).mul
    ((radialK_C2 (nu : ℂ)).continuous.comp (continuous_snd.max continuous_fst))).re

private theorem forcing_square_integrable (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) : Integrable (fun r : ℝ => ‖f r‖^2) :=
  (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1
    (hf.memLp_of_hasCompactSupport hc)

/-- Every actual row action is an honest absolutely convergent integral. -/
theorem greenAction_row_integrable {nu : ℝ} (hnu : 0 < nu) (hnuUpper : nu < 1)
    (f : ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) (s : ℝ) :
    Integrable (fun r : ℝ => realGreen nu s r • f r) := by
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hf
  have hrow := (actualGreen_row_mass_bound hnu hnuUpper s).1
  apply (hrow.mul_const B).mono'
    (((realGreen_continuous hnu s).smul hf).aestronglyMeasurable)
  exact Eventually.of_forall fun r => by
    rw [norm_smul, Real.norm_of_nonneg (realGreen_nonneg hnu s r)]
    exact mul_le_mul_of_nonneg_left (hB r) (realGreen_nonneg hnu s r)

theorem rowEnergy_integrable {nu : ℝ} (hnu : 0 < nu) (hnuUpper : nu < 1)
    (f : ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) (s : ℝ) :
    Integrable (fun r : ℝ => realGreen nu s r * ‖f r‖^2) := by
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hf
  have hrow := (actualGreen_row_mass_bound hnu hnuUpper s).1
  apply (hrow.mul_const (B^2)).mono'
    (((realGreen_continuous hnu s).mul (hf.norm.pow 2)).aestronglyMeasurable)
  exact Eventually.of_forall fun r => by
    rw [Real.norm_of_nonneg (mul_nonneg (realGreen_nonneg hnu s r) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg (f r)) (hB r) 2) (realGreen_nonneg hnu s r)

theorem rowEnergy_nonneg {nu : ℝ} (hnu : 0 < nu) (f : ℝ → ℂ) (s : ℝ) :
    0 ≤ rowEnergy nu f s :=
  integral_nonneg (fun r => mul_nonneg (realGreen_nonneg hnu s r) (sq_nonneg _))

/-- Pointwise weighted Cauchy--Schwarz for the literal actual Green row. -/
theorem greenAction_pointwise_schur {nu : ℝ} (hnu : 0 < nu) (hnuUpper : nu < 1)
    (f : ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) (s : ℝ) :
    ‖greenAction nu f s‖^2 ≤ (1 / nu^2) * rowEnergy nu f s := by
  let a : ℝ → ℝ := fun r => Real.sqrt (realGreen nu s r)
  let b : ℝ → ℝ := fun r => a r * ‖f r‖
  have haC : Continuous a := (realGreen_continuous hnu s).sqrt
  have hbC : Continuous b := haC.mul hf.norm
  have haSq (r : ℝ) : a r ^ 2 = realGreen nu s r :=
    Real.sq_sqrt (realGreen_nonneg hnu s r)
  have hbSq (r : ℝ) : b r ^ 2 = realGreen nu s r * ‖f r‖^2 := by
    dsimp [b]
    rw [mul_pow, haSq]
  have ha2 : MemLp a 2 (volume : Measure ℝ) := by
    apply (memLp_two_iff_integrable_sq haC.aestronglyMeasurable).2
    simpa only [haSq] using (actualGreen_row_mass_bound hnu hnuUpper s).1
  have hb2 : MemLp b 2 (volume : Measure ℝ) := by
    apply (memLp_two_iff_integrable_sq hbC.aestronglyMeasurable).2
    simpa only [hbSq] using rowEnergy_integrable hnu hnuUpper f hf hc s
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun r => Real.sqrt_nonneg (realGreen nu s r))
    (Eventually.of_forall fun r => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg (f r)))
    (by simpa only [ENNReal.ofReal_ofNat] using ha2)
    (by simpa only [ENNReal.ofReal_ofNat] using hb2)
  have hprod (r : ℝ) : a r * b r = realGreen nu s r * ‖f r‖ := by
    dsimp [b]
    rw [← mul_assoc, ← pow_two, haSq]
  have hCS : (∫ r : ℝ, realGreen nu s r * ‖f r‖) ≤
      Real.sqrt (∫ r : ℝ, realGreen nu s r) * Real.sqrt (rowEnergy nu f s) := by
    simpa only [Real.rpow_ofNat, ← Real.sqrt_eq_rpow, hprod, haSq, hbSq, rowEnergy]
      using hholder
  have hnorm' : ‖greenAction nu f s‖ ≤
      Real.sqrt (∫ r : ℝ, realGreen nu s r) * Real.sqrt (rowEnergy nu f s) := by
    calc
      _ ≤ ∫ r : ℝ, ‖realGreen nu s r • f r‖ := norm_integral_le_integral_norm
      _ = ∫ r : ℝ, realGreen nu s r * ‖f r‖ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun r => by
          rw [norm_smul, Real.norm_of_nonneg (realGreen_nonneg hnu s r)]
      _ ≤ _ := hCS
  have hmassNonneg : 0 ≤ ∫ r : ℝ, realGreen nu s r :=
    integral_nonneg (realGreen_nonneg hnu s)
  have hsq := pow_le_pow_left₀ (norm_nonneg (greenAction nu f s)) hnorm' 2
  have hrow : ‖greenAction nu f s‖^2 ≤
      (∫ r : ℝ, realGreen nu s r) * rowEnergy nu f s := by
    simpa only [mul_pow, Real.sq_sqrt hmassNonneg,
      Real.sq_sqrt (rowEnergy_nonneg hnu f s)] using hsq
  exact hrow.trans (mul_le_mul_of_nonneg_right
    (actualGreen_row_mass_bound hnu hnuUpper s).2 (rowEnergy_nonneg hnu f s))

private def energyIntegrand (nu : ℝ) (f : ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  realGreen nu p.1 p.2 * ‖f p.2‖^2

private theorem energyIntegrand_nonneg {nu : ℝ} (hnu : 0 < nu) (f : ℝ → ℂ)
    (p : ℝ × ℝ) : 0 ≤ energyIntegrand nu f p :=
  mul_nonneg (realGreen_nonneg hnu p.1 p.2) (sq_nonneg _)

private theorem energyIntegrand_continuous {nu : ℝ} (hnu : 0 < nu)
    (f : ℝ → ℂ) (hf : Continuous f) : Continuous (energyIntegrand nu f) :=
  (realGreen_joint_continuous hnu).mul ((hf.comp continuous_snd).norm.pow 2)

private theorem energy_column_integral {nu : ℝ} (hnu : 0 < nu) (f : ℝ → ℂ) (r : ℝ) :
    (∫ s : ℝ, ‖energyIntegrand nu f (s,r)‖) =
      (∫ s : ℝ, realGreen nu s r) * ‖f r‖^2 := by
  have he : (fun s : ℝ => ‖energyIntegrand nu f (s,r)‖) =
      (fun s : ℝ => realGreen nu s r * ‖f r‖^2) := by
    funext s
    exact Real.norm_of_nonneg (energyIntegrand_nonneg hnu f (s,r))
  rw [he, integral_mul_const]

/-- The actual weighted square is integrable on the whole product line.
Compactness is imposed only on the forcing, never on the Green kernel. -/
theorem energyIntegrand_integrable {nu : ℝ} (hnu : 0 < nu) (hnuUpper : nu < 1)
    (f : ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (energyIntegrand nu f) (volume : Measure (ℝ × ℝ)) := by
  have hcont := energyIntegrand_continuous hnu f hf
  apply (integrable_prod_iff' hcont.aestronglyMeasurable).2
  constructor
  · exact Eventually.of_forall fun r =>
      ((actualGreen_column_mass_bound hnu hnuUpper r).1.mul_const (‖f r‖^2))
  · have hmajor : Integrable (fun r : ℝ => (1 / nu^2) * ‖f r‖^2) :=
      (forcing_square_integrable f hf hc).const_mul _
    apply hmajor.mono'
      hcont.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    exact Eventually.of_forall fun r => by
      rw [Real.norm_of_nonneg (integral_nonneg (fun s => norm_nonneg _)),
        energy_column_integral hnu f r]
      exact mul_le_mul_of_nonneg_right
        (actualGreen_column_mass_bound hnu hnuUpper r).2 (sq_nonneg _)

/-- Tonelli/Fubini plus the actual column mass yields the global row-energy
budget. Every product-integrability premise has been proved above. -/
theorem rowEnergy_integrable_and_bound {nu : ℝ} (hnu : 0 < nu) (hnuUpper : nu < 1)
    (f : ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (rowEnergy nu f) ∧
      (∫ s : ℝ, rowEnergy nu f s) ≤ (1 / nu^2) * (∫ r : ℝ, ‖f r‖^2) := by
  have hprod := energyIntegrand_integrable hnu hnuUpper f hf hc
  have hleft : Integrable (rowEnergy nu f) := hprod.integral_prod_left
  refine ⟨hleft, ?_⟩
  calc
    _ = ∫ r : ℝ, ∫ s : ℝ, energyIntegrand nu f (s,r) :=
      integral_integral_swap hprod
    _ ≤ ∫ r : ℝ, (1 / nu^2) * ‖f r‖^2 := by
      apply integral_mono hprod.integral_prod_right
        ((forcing_square_integrable f hf hc).const_mul _)
      intro r
      change (∫ s : ℝ, realGreen nu s r * ‖f r‖^2) ≤ _
      rw [integral_mul_const]
      exact mul_le_mul_of_nonneg_right
        (actualGreen_column_mass_bound hnu hnuUpper r).2 (sq_nonneg _)
    _ = _ := integral_const_mul _ _

theorem greenAction_stronglyMeasurable {nu : ℝ} (hnu : 0 < nu)
    (f : ℝ → ℂ) (hf : Continuous f) : StronglyMeasurable (greenAction nu f) := by
  have hc : Continuous (fun p : ℝ × ℝ => realGreen nu p.1 p.2 • f p.2) :=
    (realGreen_joint_continuous hnu).smul (hf.comp continuous_snd)
  exact hc.stronglyMeasurable.integral_prod_right'

/-- Actual Schur energy inequality on continuous compact forcing. -/
theorem actualGreen_schur_energy {nu : ℝ} (hnu : 0 < nu) (hnuUpper : nu < 1)
    (f : ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    MemLp (greenAction nu f) 2 (volume : Measure ℝ) ∧
      (∫ s : ℝ, ‖greenAction nu f s‖^2) ≤
        (1 / nu^2)^2 * (∫ r : ℝ, ‖f r‖^2) := by
  obtain ⟨henergy, hbound⟩ := rowEnergy_integrable_and_bound hnu hnuUpper f hf hc
  have hmajor : Integrable (fun s : ℝ => (1 / nu^2) * rowEnergy nu f s) :=
    henergy.const_mul _
  have hmeas := (greenAction_stronglyMeasurable hnu f hf).aestronglyMeasurable
  have hsquare : Integrable (fun s : ℝ => ‖greenAction nu f s‖^2) := by
    apply hmajor.mono' (hmeas.norm.pow 2)
    exact Eventually.of_forall fun s => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact greenAction_pointwise_schur hnu hnuUpper f hf hc s
  refine ⟨(memLp_two_iff_integrable_sq_norm hmeas).2 hsquare, ?_⟩
  calc
    _ ≤ ∫ s : ℝ, (1 / nu^2) * rowEnergy nu f s :=
      integral_mono hsquare hmajor (greenAction_pointwise_schur hnu hnuUpper f hf hc)
    _ = (1 / nu^2) * (∫ s : ℝ, rowEnergy nu f s) := integral_const_mul _ _
    _ ≤ (1 / nu^2) * ((1 / nu^2) * (∫ r : ℝ, ‖f r‖^2)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

private theorem toLp_norm_sq (f : ℝ → ℂ) (hf : MemLp f 2 (volume : Measure ℝ)) :
    ‖hf.toLp f‖^2 = ∫ r : ℝ, ‖f r‖^2 := by
  have hbase (F : Lp ℂ 2 (volume : Measure ℝ)) :
      (∫ r : ℝ, ‖F r‖^2) = ‖F‖^2 := by
    apply Complex.ofRealLI.injective
    simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
      (L2.inner_def (𝕜 := ℂ) F F).symm
  rw [← hbase (hf.toLp f)]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with r hr
  rw [hr]

/-- Native quotient-norm Schur bound, ready for the separate extension worker. -/
theorem actualGreen_schur_toLp_norm {nu : ℝ} (hnu : 0 < nu) (hnuUpper : nu < 1)
    (f : ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    ‖((actualGreen_schur_energy hnu hnuUpper f hf hc).1).toLp (greenAction nu f)‖ ≤
      (1 / nu^2) * ‖(hf.memLp_of_hasCompactSupport hc : MemLp f 2 volume).toLp f‖ := by
  have hs := (actualGreen_schur_energy hnu hnuUpper f hf hc).2
  rw [← toLp_norm_sq (greenAction nu f) (actualGreen_schur_energy hnu hnuUpper f hf hc).1,
    ← toLp_norm_sq f (hf.memLp_of_hasCompactSupport hc)] at hs
  have hout := norm_nonneg
    (((actualGreen_schur_energy hnu hnuUpper f hf hc).1).toLp (greenAction nu f))
  have hin := norm_nonneg ((hf.memLp_of_hasCompactSupport hc : MemLp f 2 volume).toLp f)
  have hC : 0 ≤ (1 / nu^2 : ℝ) := by positivity
  nlinarith

/-- The scalar action is literally integration against the original complex
I/K kernel; real-valuedness was proved from the actual positive solutions. -/
theorem greenAction_eq_actualKernel {nu : ℝ} (hnu : 0 < nu)
    (f : ℝ → ℂ) (s : ℝ) :
    greenAction nu f s = ∫ r : ℝ, actualRadialGreen (nu : ℂ) s r * f r := by
  apply integral_congr_ae
  exact Eventually.of_forall fun r => by
    have he : actualRadialGreen (nu : ℂ) s r = (realGreen nu s r : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa only [Complex.ofReal_im] using actualGreen_real_im_zero hnu s r
    rw [he]
    simp only [Complex.real_smul]

end
end ImbalancedChen.Part3.ActualRadialGreenSchur20261025a
