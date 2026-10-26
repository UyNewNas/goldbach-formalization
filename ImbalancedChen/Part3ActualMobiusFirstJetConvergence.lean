import ImbalancedChen.Part3MobiusStrongFirstJetL2Errors

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Strong convergence of actual Mobius pullbacks and their two raw first-jet
components on each positive compact chart. The hypotheses are genuine
global planar L2 convergence of the three representatives. The bounds
come from the native Jacobian transport; no continuity of a pullback
operator, transported weak derivative, or weak chain rule is assumed.
-/

namespace ImbalancedChen.Part3.ActualMobiusFirstJetConvergence20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups UpperHalfPlane Topology
open ActualMobiusCompactLpTransport20261026b ActualMobiusPairChartL2Transport20261026b
open MobiusStrongFirstJetL2Errors20261026b

/-- The scalar compact pullback has a produced norm bound, obtained by
taking the nonnegative square root of its actual Jacobian estimate. -/
theorem compClass_norm_error (g : SL(2, ℤ)) {K : Set Plane}
    (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2)
    {F G : Plane → ℂ} (hF : MemLp F 2 volume) (hG : MemLp G 2 volume) :
    ‖compClass g hK hKp hF-compClass g hK hKp hG‖ ≤
      Real.sqrt (compactCompositionConstant g (complexSet K) (complexSet_isCompact hK)) *
        ‖hF.toLp F-hG.toLp G‖ := by
  have hC : 0 ≤ compactCompositionConstant g (complexSet K) (complexSet_isCompact hK) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (compactCompositionConstant_one_le g _)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt hC]
  exact compClass_norm_sq_error g hK hKp hF hG

/-- Each transported raw jet error is controlled by the sum of the two
target errors. Both estimates use the joint conformal energy inequality. -/
theorem jetClass_norm_errors (g : SL(2, ℤ)) {K : Set Plane}
    (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2)
    {U V P Q : Plane → ℂ} (hU : MemLp U 2 volume) (hV : MemLp V 2 volume)
    (hP : MemLp P 2 volume) (hQ : MemLp Q 2 volume) :
    (‖jetXClass g hK hKp hU hV-jetXClass g hK hKp hP hQ‖ ≤
        ‖hU.toLp U-hP.toLp P‖+‖hV.toLp V-hQ.toLp Q‖) ∧
    (‖jetYClass g hK hKp hU hV-jetYClass g hK hKp hP hQ‖ ≤
        ‖hU.toLp U-hP.toLp P‖+‖hV.toLp V-hQ.toLp Q‖) := by
  have h := jetClass_norm_sq_error g hK hKp hU hV hP hQ
  have hprod := mul_nonneg (norm_nonneg (hU.toLp U-hP.toLp P))
    (norm_nonneg (hV.toLp V-hQ.toLp Q))
  constructor
  · apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    nlinarith [sq_nonneg ‖jetYClass g hK hKp hU hV-jetYClass g hK hKp hP hQ‖]
  · apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    nlinarith [sq_nonneg ‖jetXClass g hK hKp hU hV-jetXClass g hK hKp hP hQ‖]

/-- Genuine strong L2 convergence of values survives the actual Mobius
pullback on every compact positive chart. -/
theorem compClass_tendsto {ι : Type*} {l : Filter ι}
    (g : SL(2, ℤ)) {K : Set Plane} (hK : IsCompact K)
    (hKp : ∀ p ∈ K, 0 < p.2) {F : ι → Plane → ℂ} {G : Plane → ℂ}
    (hF : ∀ i, MemLp (F i) 2 volume) (hG : MemLp G 2 volume)
    (hlim : Tendsto (fun i => (hF i).toLp (F i)) l (𝓝 (hG.toLp G))) :
    Tendsto (fun i => compClass g hK hKp (hF i)) l (𝓝 (compClass g hK hKp hG)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun i => norm_nonneg _)
    (fun i => compClass_norm_error g hK hKp (hF i) hG)
  simpa only [mul_zero] using
    (tendsto_iff_norm_sub_tendsto_zero.mp hlim).const_mul
      (Real.sqrt (compactCompositionConstant g (complexSet K) (complexSet_isCompact hK)))

/-- Both actual transpose-Jacobian components converge strongly in L2.
This is raw first-jet transport: no weak derivative identification is an input. -/
theorem jetClass_tendsto {ι : Type*} {l : Filter ι}
    (g : SL(2, ℤ)) {K : Set Plane} (hK : IsCompact K)
    (hKp : ∀ p ∈ K, 0 < p.2) {U V : ι → Plane → ℂ} {P Q : Plane → ℂ}
    (hU : ∀ i, MemLp (U i) 2 volume) (hV : ∀ i, MemLp (V i) 2 volume)
    (hP : MemLp P 2 volume) (hQ : MemLp Q 2 volume)
    (hlimU : Tendsto (fun i => (hU i).toLp (U i)) l (𝓝 (hP.toLp P)))
    (hlimV : Tendsto (fun i => (hV i).toLp (V i)) l (𝓝 (hQ.toLp Q))) :
    Tendsto (fun i => jetXClass g hK hKp (hU i) (hV i)) l
        (𝓝 (jetXClass g hK hKp hP hQ)) ∧
    Tendsto (fun i => jetYClass g hK hKp (hU i) (hV i)) l
        (𝓝 (jetYClass g hK hKp hP hQ)) := by
  have hsum : Tendsto (fun i => ‖(hU i).toLp (U i)-hP.toLp P‖+
      ‖(hV i).toLp (V i)-hQ.toLp Q‖) l (𝓝 0) := by
    simpa only [zero_add] using (tendsto_iff_norm_sub_tendsto_zero.mp hlimU).add
      (tendsto_iff_norm_sub_tendsto_zero.mp hlimV)
  constructor
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun i => norm_nonneg _)
      (fun i => (jetClass_norm_errors g hK hKp (hU i) (hV i) hP hQ).1) hsum
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun i => norm_nonneg _)
      (fun i => (jetClass_norm_errors g hK hKp (hU i) (hV i) hP hQ).2) hsum

end
end ImbalancedChen.Part3.ActualMobiusFirstJetConvergence20261026b
