import ImbalancedChen.Part3ActualInfinityCuspAnnihilator
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual infinity horocycle zero coefficient iff annihilation of genuine
compact height zero-frequency Poincare sums, for continuous L2 lifts.
The reverse direction uses the smooth-test fundamental lemma and removes
the nonzero hyperbolic density only at positive heights. It is not an
assumed cusp classification. Arbitrary L2 representatives and other cusps
still require genuine additional unfolding/geometry suppliers.
-/
namespace ImbalancedChen.Part3.ActualInfinityCuspTestCharacterization20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.ActualPoincareSpectralCoefficient20261026a
open ImbalancedChen.Part3.ActualInfinityCuspAnnihilator20261026b

/-- Continuity of the actual zero mode in positive height, proved by
integrating the continuous genuine horizontal-point trace over [0,1]. -/
theorem actual_zero_mode_continuousOn (N : ℕ)
    (U : Gamma0OrbitSpace N → ℂ) (hU : Continuous (testLift N U)) :
    ContinuousOn (actualTestFourier N U 0) (Ioi (0 : ℝ)) := by
  letI : LocallyCompactSpace (Ioi (0 : ℝ)) := isOpen_Ioi.locallyCompactSpace
  let F : Ioi (0 : ℝ) → ℝ → ℂ := fun y x =>
    testLift N U (⟨⟨x, (y : ℝ)⟩, y.property⟩ : UpperHalfPlane)
  have hF : Continuous F.uncurry := by
    apply hU.comp
    exact Continuous.upperHalfPlaneMk (by fun_prop) (fun p => p.1.property)
  have hi : Continuous (fun y : Ioi (0 : ℝ) => ∫ x in Icc (0 : ℝ) 1, F y x) :=
    continuous_parametric_integral_of_continuous hF isCompact_Icc
  apply continuousOn_iff_continuous_restrict.mpr
  convert hi using 1
  funext y
  rw [actualTestFourier_positive_height N U 0 y.property,
    integral_Icc_eq_integral_Ico]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp [F, testLift]

/-- Local L1 of the true weighted coefficient follows from continuity;
it is not included as a disguised orthogonality hypothesis. -/
theorem weighted_zero_mode_locallyIntegrableOn (N : ℕ)
    (U : Gamma0OrbitSpace N → ℂ) (hU : Continuous (testLift N U)) :
    LocallyIntegrableOn
      (fun y => ((y⁻¹)^2 : ℝ) • actualTestFourier N U 0 y) (Ioi (0 : ℝ)) := by
  have hw : ContinuousOn (fun y : ℝ => (y⁻¹)^2) (Ioi (0 : ℝ)) :=
    (continuousOn_id.inv₀ (fun y hy => ne_of_gt hy)).pow 2
  exact (hw.smul (actual_zero_mode_continuousOn N U hU)).locallyIntegrableOn measurableSet_Ioi

/-- True AE horocycle condition. Every integrand is evaluated on the
actual Gamma0 orbit of x+iy, via actualTestFourier_positive_height. -/
def AEZeroInfinityMode (N : ℕ) (U : Gamma0OrbitSpace N → ℂ) : Prop :=
  ∀ᵐ y : ℝ, 0 < y → actualTestFourier N U 0 y = 0

theorem continuous_mem_iff_ae_zero_infinity_mode (N : ℕ) [NeZero N]
    (U : Gamma0OrbitSpace N → ℂ) (hU : Continuous (testLift N U))
    (hU2 : MemLp U 2 (carrierPushforward N)) :
    hU2.toLp U ∈ infinityCuspSubspace N ↔ AEZeroInfinityMode N U := by
  rw [continuous_mem_iff_compact_height_tests N U hU hU2]
  constructor
  · intro htests
    have hz : ∀ᵐ y : ℝ, y ∈ Ioi (0 : ℝ) →
        ((y⁻¹)^2 : ℝ) • actualTestFourier N U 0 y = 0 := by
      apply isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (weighted_zero_mode_locallyIntegrableOn N U hU)
      intro g hg hgc hgs
      let ψ : ℝ → ℂ := fun y => (g y : ℂ)
      have hψ : Continuous ψ := Complex.continuous_ofReal.comp hg.continuous
      have hcψ : HasCompactSupport ψ := hgc.comp_left (by simp)
      have hts : tsupport ψ ⊆ tsupport g := tsupport_comp_subset (g := Complex.ofReal) rfl g
      let s : HeightSeed := ⟨ψ, hψ, hcψ, hts.trans hgs⟩
      have hp := htests s
      have heq : (fun y => g y • (((y⁻¹)^2 : ℝ) • actualTestFourier N U 0 y)) =
          fun y => ((y⁻¹)^2 : ℝ) • (star (s.toFun y) * actualTestFourier N U 0 y) := by
        funext y
        simp [s, ψ, smul_smul, Complex.real_smul, mul_assoc, mul_comm, mul_left_comm]
      rw [heq, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ))]
      · exact hp
      · intro y hy
        have hg0 : g y = 0 := image_eq_zero_of_notMem_tsupport (fun hgy => hy (hgs hgy))
        simp [s, ψ, hg0]
    filter_upwards [hz] with y hy
    intro hpos
    have hw : (y⁻¹)^2 ≠ (0 : ℝ) := pow_ne_zero 2 (inv_ne_zero (ne_of_gt hpos))
    exact (smul_eq_zero.mp (hy hpos)).resolve_left hw
  · intro hz s
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_of_ae hz, ae_restrict_mem measurableSet_Ioi] with y hy hpos
    rw [hy hpos]
    simp

end
end ImbalancedChen.Part3.ActualInfinityCuspTestCharacterization20261026b
