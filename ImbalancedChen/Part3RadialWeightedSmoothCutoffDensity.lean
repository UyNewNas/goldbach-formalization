import ImbalancedChen.Part3RadialScaledSmoothCutoff

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Every genuine smooth function with all three actual finite-energy L2
coordinates is approximated by the explicit compact smooth functions
chi_n U. The product derivative term chi_n' U is retained and controlled
by the proved C/(n+1) cutoff derivative bound. Dominated convergence
controls U, U', and exp(r)U on the whole real line.

The actual PiLp2 core vectors converge to (kappa U,U',exp(r)U), proving
membership in the independently constructed closed radial form domain.
No form-domain membership, approximation, weak equation or Green-kernel
property is assumed. Green smoothness and finite-energy estimates remain
the separate inputs of its actual integral consumer.
-/
namespace ImbalancedChen.Part3.RadialWeightedCutoffDensity20261025a

noncomputable section
open MeasureTheory Filter Set
open RadialSchrodingerL2Form20261025a

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- This is a literal compact C-infinity core test for each n. -/
def cutoffTest (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (n : ℕ) : RadialTest where
  function r := cutoff n r • U r
  smooth := (cutoff_smooth n).smul hU
  compact := (cutoff_compact n).smul_right

theorem cutoffTest_derivative (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (n : ℕ) (r : ℝ) :
    deriv (cutoffTest U hU n).function r =
      cutoff n r • deriv U r + deriv (cutoff n) r • U r := by
  have hc := (contDiff_infty_iff_deriv.mp (cutoff_smooth n)).1
  have hu := (contDiff_infty_iff_deriv.mp hU).1
  exact ((hc r).hasDerivAt.smul (hu r).hasDerivAt).deriv

theorem cutoffTest_derivative_tendsto (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (r : ℝ) :
    Tendsto (fun n => deriv (cutoffTest U hU n).function r) atTop (nhds (deriv U r)) := by
  have hmain := (tendsto_cutoff r).smul (tendsto_const_nhds (x := deriv U r))
  have herr := (tendsto_cutoff_derivative r).smul (tendsto_const_nhds (x := U r))
  simpa only [cutoffTest_derivative, one_smul, zero_smul, add_zero] using hmain.add herr

/-- The derivative error has a genuine L2 majorant from the input's two
L2 coordinates; no uniform bound on U or on its derivative is assumed. -/
theorem cutoffTest_derivative_error_bound (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (n : ℕ) (r : ℝ) :
    ‖deriv (cutoffTest U hU n).function r - deriv U r‖ ≤
      ‖deriv U r‖ + derivativeConstant * ‖U r‖ := by
  rw [cutoffTest_derivative]
  have heq : cutoff n r • deriv U r + deriv (cutoff n) r • U r - deriv U r =
      (cutoff n r • deriv U r - deriv U r) + deriv (cutoff n) r • U r := by abel
  rw [heq]
  apply (norm_add_le _ _).trans
  apply add_le_add (cutoff_error_bound n (deriv U) r)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (cutoff_derivative_uniform_bound n r) (norm_nonneg _)

theorem derivative_error_eLpNorm_tendsto (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hU2 : MemLp U 2 (volume : Measure ℝ)) (hD2 : MemLp (deriv U) 2 volume) :
    Tendsto (fun n => eLpNorm
      (fun r => deriv (cutoffTest U hU n).function r - deriv U r) 2 volume)
      atTop (nhds 0) := by
  let G : ℝ → ℝ := fun r => ‖deriv U r‖ + derivativeConstant * ‖U r‖
  have hG : MemLp G 2 volume := hD2.norm.add (hU2.norm.const_mul derivativeConstant)
  have hC : 0 ≤ derivativeConstant := (by norm_num : (0 : ℝ) ≤ 1).trans derivativeConstant_ge_one
  apply tendsto_eLpNorm_zero_of_dominated _ G hG
  · intro n
    exact ((cutoffTest U hU n).derivative_continuous.aestronglyMeasurable).
      sub hD2.aestronglyMeasurable
  · intro n r
    have hG0 : 0 ≤ G r := add_nonneg (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))
    simpa only [Real.norm_eq_abs, abs_of_nonneg hG0] using
      cutoffTest_derivative_error_bound U hU n r
  · intro r
    simpa only [sub_self] using (cutoffTest_derivative_tendsto U hU r).sub
      (tendsto_const_nhds (x := deriv U r))

theorem cutoffTest_exponential (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (n : ℕ) (r : ℝ) :
    exponentialProduct (cutoffTest U hU n).function r =
      cutoff n r • exponentialProduct U r := by
  change (Real.exp r : ℂ) * (cutoff n r • U r) =
    cutoff n r • ((Real.exp r : ℂ) * U r)
  exact mul_smul_comm _ _ _

/-- Physical input convergence in the actual radial L2 quotient. -/
theorem cutoffTest_coreL2_tendsto (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hU2 : MemLp U 2 (volume : Measure ℝ)) :
    Tendsto (fun n => radialCoreL2 (cutoffTest U hU n)) atTop (nhds (hU2.toLp U)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n => (cutoffTest U hU n).function)
    (fun n => (cutoffTest U hU n).function_memLp) U hU2).2
  exact cutoff_multiplier_eLpNorm_tendsto U hU2

/-- Derivative convergence includes the cutoff derivative error. -/
theorem cutoffTest_derivativeL2_tendsto (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hU2 : MemLp U 2 (volume : Measure ℝ)) (hD2 : MemLp (deriv U) 2 volume) :
    Tendsto (fun n => radialDerivativeL2 (cutoffTest U hU n)) atTop
      (nhds (hD2.toLp (deriv U))) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n => deriv (cutoffTest U hU n).function)
    (fun n => (cutoffTest U hU n).derivative_memLp) (deriv U) hD2).2
  exact derivative_error_eLpNorm_tendsto U hU hU2 hD2

/-- The exponential weight is never bounded or removed. It is the actual
third input coordinate and has its own supplied finite L2 norm. -/
theorem cutoffTest_exponentialL2_tendsto (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U)
    (hE2 : MemLp (exponentialProduct U) 2 (volume : Measure ℝ)) :
    Tendsto (fun n => radialExponentialL2 (cutoffTest U hU n)) atTop
      (nhds (hE2.toLp (exponentialProduct U))) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n => exponentialProduct (cutoffTest U hU n).function)
    (fun n => (cutoffTest U hU n).exponential_memLp) (exponentialProduct U) hE2).2
  simpa only [cutoffTest_exponential] using
    cutoff_multiplier_eLpNorm_tendsto (exponentialProduct U) hE2

/-- The literal proposed shifted energy vector, with all three actual
input quotient classes. This has the true PiLp2 Hilbert norm. -/
def smoothEnergyVector (kappa : ℝ) (U : ℝ → ℂ)
    (hU2 : MemLp U 2 (volume : Measure ℝ)) (hD2 : MemLp (deriv U) 2 volume)
    (hE2 : MemLp (exponentialProduct U) 2 volume) : RadialEnergyHilbert :=
  WithLp.toLp 2 ![(kappa : ℂ) • hU2.toLp U,
    hD2.toLp (deriv U), hE2.toLp (exponentialProduct U)]

/-- All three actual cutoff core coordinates converge together. -/
theorem cutoffTest_energyVector_tendsto (kappa : ℝ) (U : ℝ → ℂ)
    (hU : ContDiff ℝ ∞ U) (hU2 : MemLp U 2 (volume : Measure ℝ))
    (hD2 : MemLp (deriv U) 2 volume) (hE2 : MemLp (exponentialProduct U) 2 volume) :
    Tendsto (fun n => radialEnergyCoreVector kappa (cutoffTest U hU n)) atTop
      (nhds (smoothEnergyVector kappa U hU2 hD2 hE2)) := by
  have h0 := (tendsto_const_nhds (x := (kappa : ℂ))).smul
    (cutoffTest_coreL2_tendsto U hU hU2)
  have h1 := cutoffTest_derivativeL2_tendsto U hU hU2 hD2
  have h2 := cutoffTest_exponentialL2_tendsto U hU hE2
  have hp : Tendsto (fun n => ![(kappa : ℂ) • radialCoreL2 (cutoffTest U hU n),
      radialDerivativeL2 (cutoffTest U hU n), radialExponentialL2 (cutoffTest U hU n)])
      atTop (nhds (![(kappa : ℂ) • hU2.toLp U,
        hD2.toLp (deriv U), hE2.toLp (exponentialProduct U)] : Fin 3 → RadialL2)) := by
    apply tendsto_pi_nhds.2
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => RadialL2)).continuousAt.tendsto.comp hp

/-- Membership in the actual independently constructed form closure is
proved from this explicit sequence of actual compact core vectors. -/
theorem smoothEnergyVector_mem_closedDomain (kappa : ℝ) (U : ℝ → ℂ)
    (hU : ContDiff ℝ ∞ U) (hU2 : MemLp U 2 (volume : Measure ℝ))
    (hD2 : MemLp (deriv U) 2 volume) (hE2 : MemLp (exponentialProduct U) 2 volume) :
    smoothEnergyVector kappa U hU2 hD2 hE2 ∈ radialClosedEnergyDomain kappa := by
  exact (radialEnergyCoreSpan kappa).isClosed_topologicalClosure.mem_of_tendsto
    (cutoffTest_energyVector_tendsto kappa U hU hU2 hD2 hE2)
    (Filter.Eventually.of_forall (fun n =>
      (radialEnergyCoreSpan kappa).le_topologicalClosure
        (Submodule.subset_span ⟨cutoffTest U hU n, rfl⟩)))

/-- Constructed form-domain element for every genuine smooth finite-energy
input. kappa>0 permits exact recovery of the physical coordinate. -/
def smoothFiniteEnergyElement (kappa : ℝ) (_hkappa : 0 < kappa)
    (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hU2 : MemLp U 2 (volume : Measure ℝ))
    (hD2 : MemLp (deriv U) 2 volume) (hE2 : MemLp (exponentialProduct U) 2 volume) :
    radialClosedEnergyDomain kappa :=
  ⟨smoothEnergyVector kappa U hU2 hD2 hE2,
    smoothEnergyVector_mem_closedDomain kappa U hU hU2 hD2 hE2⟩

theorem smoothFiniteEnergyElement_physical (kappa : ℝ) (hkappa : 0 < kappa)
    (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hU2 : MemLp U 2 (volume : Measure ℝ))
    (hD2 : MemLp (deriv U) 2 volume) (hE2 : MemLp (exponentialProduct U) 2 volume) :
    radialPhysicalEmbedding kappa (smoothFiniteEnergyElement kappa hkappa U hU hU2 hD2 hE2) =
      hU2.toLp U := by
  change (kappa⁻¹ : ℂ) • ((kappa : ℂ) • hU2.toLp U) = _
  have he : (kappa⁻¹ : ℂ) * (kappa : ℂ) = 1 := by
    exact_mod_cast inv_mul_cancel₀ hkappa.ne'
  rw [smul_smul, he, one_smul]

theorem smoothFiniteEnergyElement_derivative (kappa : ℝ) (hkappa : 0 < kappa)
    (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hU2 : MemLp U 2 (volume : Measure ℝ))
    (hD2 : MemLp (deriv U) 2 volume) (hE2 : MemLp (exponentialProduct U) 2 volume) :
    radialClosedDerivative kappa (smoothFiniteEnergyElement kappa hkappa U hU hU2 hD2 hE2) =
      hD2.toLp (deriv U) := rfl

theorem smoothFiniteEnergyElement_exponential (kappa : ℝ) (hkappa : 0 < kappa)
    (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hU2 : MemLp U 2 (volume : Measure ℝ))
    (hD2 : MemLp (deriv U) 2 volume) (hE2 : MemLp (exponentialProduct U) 2 volume) :
    radialClosedExponential kappa (smoothFiniteEnergyElement kappa hkappa U hU hU2 hD2 hE2) =
      hE2.toLp (exponentialProduct U) := rfl

end
end ImbalancedChen.Part3.RadialWeightedCutoffDensity20261025a
