import ImbalancedChen.Part3ActualCutoffSquareSupportedEnergy

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Scalar cutoff nesting implies first-derivative nesting by a genuine local
zero germ, with no weak-gradient or Mobius covariance assumption. The
cutoff derivative-error density is therefore unchanged when the unknown
vector is multiplied by the outer cutoff. Specialization retains the
ORIGINAL actual modular cutoffs on their positive coordinate chart.
-/
namespace ImbalancedChen.Part3.NestedCutoffDerivativeError20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open CompactC2ProductMollifier20261026a
open MaassWeakOperatorCore20261024zz
open Gamma0SmoothCompactTensorCore20261025a Gamma0CompactTensorPoincareC2Core20261025a
open GammaSmoothMultiplierPeriodization20261026a GammaSmoothMultiplierLegalTests20261026a
open ActualModularCutoffMaassBudget20261025a

/-- Where the outer multiplier is not one, scalar nesting forces the
inner cutoff to be identically zero on a neighborhood. -/
theorem nested_cutoff_zero_germ {U : Set Plane} (hU : IsOpen U)
    {ψ χ : Plane → ℂ} (hψ : ContinuousOn ψ U)
    (hnest : ∀ p ∈ U, ψ p * χ p = χ p) {p : Plane} (hp : p ∈ U) (hne : ψ p ≠ 1) :
    χ =ᶠ[𝓝 p] (0 : Plane → ℂ) := by
  have hc : ContinuousAt ψ p := hψ.continuousAt (hU.mem_nhds hp)
  have hneigh : {q : Plane | ψ q ≠ 1} ∈ 𝓝 p :=
    hc.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hne)
  filter_upwards [hU.mem_nhds hp,hneigh] with q hq hqne
  have hzero : (ψ q - 1) * χ q = 0 := by
    calc
      _ = ψ q * χ q - χ q := by ring
      _ = 0 := sub_eq_zero.mpr (hnest q hq)
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hqne)

/-- Derivative nesting is a consequence, not an additional product-rule
or vanishing-cutoff-gradient premise. No differentiability of χ is
needed in the zero-germ branch. -/
theorem nested_cutoff_directional {U : Set Plane} (hU : IsOpen U)
    {ψ χ : Plane → ℂ} (hψ : ContinuousOn ψ U)
    (hnest : ∀ p ∈ U, ψ p * χ p = χ p) {p : Plane} (hp : p ∈ U) (v : Plane) :
    ψ p * directional v χ p = directional v χ p := by
  by_cases hone : ψ p = 1
  · simp only [hone,one_mul]
  · have hg := nested_cutoff_zero_germ hU hψ hnest hp hone
    have hd : directional v χ p = 0 := by
      unfold directional
      rw [hg.fderiv_eq]
      simp
    simp only [hd,mul_zero]

/-- Exact commutator/error-weight localization. This holds for complex
outer multipliers too; taking the norm of the derived derivative nesting
supplies the needed real scalar identity. -/
theorem nested_derivative_error_localization {U : Set Plane} (hU : IsOpen U)
    {ψ χ : Plane → ℂ} (hψ : ContinuousOn ψ U)
    (hnest : ∀ p ∈ U, ψ p * χ p = χ p) {p : Plane} (hp : p ∈ U) (F : Plane → ℂ) :
    (‖directional ex χ p‖^2 + ‖directional ey χ p‖^2) * ‖ψ p * F p‖^2 =
      (‖directional ex χ p‖^2 + ‖directional ey χ p‖^2) * ‖F p‖^2 := by
  have hx := congrArg (fun z : ℂ => ‖z‖^2) (nested_cutoff_directional hU hψ hnest hp ex)
  have hy := congrArg (fun z : ℂ => ‖z‖^2) (nested_cutoff_directional hU hψ hnest hp ey)
  simp only [norm_mul,mul_pow] at hx hy
  rw [norm_mul,mul_pow]
  calc
    _ = (‖ψ p‖^2 * ‖directional ex χ p‖^2 +
        ‖ψ p‖^2 * ‖directional ey χ p‖^2) * ‖F p‖^2 := by ring
    _ = _ := by rw [hx,hy]

/-- Native positive-chart specialization for the actual modular cutoffs.
The sole nesting input is the original scalar H-function equality. -/
theorem actual_cutoff_nesting_directional (Z Y : ℝ) (hZ : 0 < Z)
    (hnest : complexGlobalH Z * complexGlobalH Y = complexGlobalH Y)
    {p : Plane} (hp : p ∈ positiveChart) (v : Plane) :
    extendUpper (complexGlobalH Z) p * directional v (extendUpper (complexGlobalH Y)) p =
      directional v (extendUpper (complexGlobalH Y)) p := by
  have hmul : extendUpper (complexGlobalH Z) * extendUpper (complexGlobalH Y) =
      extendUpper (complexGlobalH Y) := by
    rw [← extendUpper_mul,hnest]
  exact nested_cutoff_directional (isOpen_lt continuous_const continuous_snd)
    (actualCutoff_cinfty Z hZ).continuousOn
    (fun q hq => congrFun hmul q) hp v

/-- The actual inner-cutoff derivative error against the outer-localized
unknown is LITERALLY the original error against that unknown. -/
theorem actual_cutoff_error_localization (Z Y : ℝ) (hZ : 0 < Z)
    (hnest : complexGlobalH Z * complexGlobalH Y = complexGlobalH Y)
    {p : Plane} (hp : p ∈ positiveChart) (F : Plane → ℂ) :
    (‖directional ex (extendUpper (complexGlobalH Y)) p‖^2 +
      ‖directional ey (extendUpper (complexGlobalH Y)) p‖^2) *
        ‖extendUpper (complexGlobalH Z) p * F p‖^2 =
      (‖directional ex (extendUpper (complexGlobalH Y)) p‖^2 +
        ‖directional ey (extendUpper (complexGlobalH Y)) p‖^2) * ‖F p‖^2 := by
  have hmul : extendUpper (complexGlobalH Z) * extendUpper (complexGlobalH Y) =
      extendUpper (complexGlobalH Y) := by
    rw [← extendUpper_mul,hnest]
  exact nested_derivative_error_localization (isOpen_lt continuous_const continuous_snd)
    (actualCutoff_cinfty Z hZ).continuousOn (fun q hq => congrFun hmul q) hp F

end
end ImbalancedChen.Part3.NestedCutoffDerivativeError20261026b
