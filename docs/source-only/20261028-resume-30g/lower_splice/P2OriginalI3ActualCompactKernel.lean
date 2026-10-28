import ImbalancedChen.P2OriginalI3FullRawActualPlusDensity
import ImbalancedChen.ActualRosserResidualDensity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual complete raw-I3 summand has the original normalized upper
sieve kernel, uniformly at OLD and actual NEW quotient parameters in a
fixed independently specified legal compact set. Compact membership is
geometric input, not a density/convergence premise. No full frontier
compact coverage, wall payment, prime-tuple integral or L5/L6 is asserted.
-/
namespace ImbalancedChen.P2OriginalI3ActualCompactKernel
noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalMixedThirdSignedFrontier
open P2OriginalI3FullRawActualPlusDensity
open MathlibNt.SieveTheory

/-- Original upper residual kernel at the literal whole-prefix quotient. -/
def frozenPlusProfile (N : ℕ) (pre : List ℕ) (lambda : ℝ) : ℝ :=
  let par := actualRosserQuotientParameters (N : ℝ) (pre.prod : ℝ)
    (pre.headD 0 : ℝ) lambda
  (2 * Real.exp (-Real.eulerMascheroniConstant) / par.2) *
    suzukiContinuousUpperFactor (par.1 / par.2)

/-- The same computed tag and mass as the exact complete raw-I3 sum. -/
def actualFullI3ProfileTerm {mesh : ℕ} (D : ThirdStage mesh) (N : ℕ)
    (tag : FirstExitDepthState ℕ ×
      Option P2OriginalLowerWholeBoxBranchSelect.SelectedBranchData) : ℝ :=
  let pre := tag.1.selectedPrefix
  let newCap := (integerTrace D.thirdPlan (D.start.epsilon : ℝ)
    (startCutoff D.start.start : ℝ) (baselineCap D.rho) N pre).cap
  tag.1.mass * (frozenPlusProfile N pre (baselineCap D.rho) -
    frozenPlusProfile N pre newCap)

/-- One threshold is chosen before the target, compiler, reached state,
actual selected label and enumeration cap. Both original quotient levels
are used exactly, and the finite error carries its TRUE accumulated mass. -/
theorem exists_actual_full_I3_compact_kernel_threshold
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hlegal : ∀ p ∈ T, 0 < p.2 ∧ p.2 < p.1) (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ mesh : ℕ, ∀ D : ThirdStage mesh, ∀ cap : ℕ, ∀ z : ℝ,
      ∀ state : FirstExitDepthState ℕ,
      state ∈ firstExitDepthFrontier 3 (D.oldPolicy N)
        (fun p => 1 / ((p : ℝ)-1)) [] true 1 (roughPrimeUniverse N cap 0 z) →
      let pre := state.selectedPrefix
      let newCap := (integerTrace D.thirdPlan (D.start.epsilon : ℝ)
        (startCutoff D.start.start : ℝ) (baselineCap D.rho) N pre).cap
      actualRosserQuotientParameters (N : ℝ) (pre.prod : ℝ)
        (pre.headD 0 : ℝ) (baselineCap D.rho) ∈ T →
      actualRosserQuotientParameters (N : ℝ) (pre.prod : ℝ)
        (pre.headD 0 : ℝ) newCap ∈ T →
      |actualFullI3PlusTerm D N cap (state,D.sourceLabel N pre) *
          Real.log (N : ℝ) / singularSeries N -
        actualFullI3ProfileTerm D N (state,D.sourceLabel N pre)| ≤ |state.mass| * eta := by
  obtain ⟨N0,hN0,hbound⟩ :=
    exists_actualSmallRosserPlusDensity_quotient_compact_normalized_threshold
      T hT hlegal (eta/2) (half_pos heta)
  refine ⟨N0,hN0,?_⟩
  intro N hN hEven mesh D cap z state hs
  dsimp only
  intro hOld hNew
  let pre := state.selectedPrefix
  let newCap := (integerTrace D.thirdPlan (D.start.epsilon : ℝ)
    (startCutoff D.start.start : ℝ) (baselineCap D.rho) N pre).cap
  have hg := actualPrimeFrontier_geometry 3 (by norm_num) (D.oldPolicy N)
    N cap z state hs
  have hP : (0 : ℝ) < pre.prod := hg.2.2.1
  obtain ⟨p,ps,hpre,_hlen⟩ := List.length_eq_succ_iff.mp hg.1
  have hhead : pre.headD 0 = p := by dsimp [pre]; rw [← hpre]; rfl
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist 3 (D.oldPolicy N)
    (fun p => 1 / ((p : ℝ)-1)) (roughPrimeUniverse N cap 0 z) state hs
  have hmem : p ∈ roughPrimeUniverse N cap 0 z :=
    hsub.subset (List.mem_reverse.mpr (by rw [← hpre]; simp))
  have hp := (mem_roughPrimeUniverse.mp hmem).2.1
  have hy : (0 : ℝ) < (pre.headD 0 : ℝ) := by
    rw [hhead]
    exact_mod_cast hp.pos
  have hcap : (pre.headD 0 : ℝ) ≤ (cap : ℝ) := by
    rw [hhead]
    exact_mod_cast (mem_roughPrimeUniverse.mp hmem).1.le
  have hbOld := hbound N hN hEven (pre.prod : ℝ) (pre.headD 0 : ℝ)
    (baselineCap D.rho) hP hy hOld cap hcap
  have hbNew := hbound N hN hEven (pre.prod : ℝ) (pre.headD 0 : ℝ)
    newCap hP hy hNew cap hcap
  let A := actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
    ((N : ℝ)^(baselineCap D.rho)/(pre.prod : ℝ))
  let B := actualSmallRosserPlusDensity N cap (pre.headD 0 : ℝ)
    ((N : ℝ)^newCap/(pre.prod : ℝ))
  let a := frozenPlusProfile N pre (baselineCap D.rho)
  let b := frozenPlusProfile N pre newCap
  have heOld : |A * Real.log (N : ℝ) / singularSeries N - a| < eta/2 := hbOld
  have heNew : |B * Real.log (N : ℝ) / singularSeries N - b| < eta/2 := hbNew
  have he : |(A * Real.log (N : ℝ) / singularSeries N - a) -
      (B * Real.log (N : ℝ) / singularSeries N - b)| ≤ eta := by
    have ho := abs_lt.mp heOld
    have hn := abs_lt.mp heNew
    apply abs_le.mpr
    constructor <;> linarith [ho.1,ho.2,hn.1,hn.2]
  calc
    _ = |state.mass| * |(A * Real.log (N : ℝ) / singularSeries N - a) -
          (B * Real.log (N : ℝ) / singularSeries N - b)| := by
      rw [← abs_mul]
      congr 1
      dsimp [actualFullI3PlusTerm,actualFullI3ProfileTerm,A,B,a,b,newCap,pre]
      ring
    _ ≤ |state.mass| * eta := mul_le_mul_of_nonneg_left he (abs_nonneg _)

end
end ImbalancedChen.P2OriginalI3ActualCompactKernel
