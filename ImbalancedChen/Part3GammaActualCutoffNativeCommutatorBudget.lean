import ImbalancedChen.Part3GammaActualClosedFormIMS

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The genuine actual cutoff Maass and cross-gradient terms give a uniform
native commutator L2-density budget. A separate locality lemma proves that
a continuous multiplier fixing a function globally also fixes its native
Maass differential: on the open set where the multiplier differs from one,
the function has a ZERO GERM. Thus no isolated-value derivative inference
is used when proving eventual exact core commutator disappearance.
-/

namespace ImbalancedChen.Part3.GammaActualCutoffNativeCommutatorBudget20261026b

noncomputable section
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane
open MaassWeakOperatorCore20261024zz Gamma0CompactTensorPoincareC2Core20261025a
open GammaNativeMaassLeibniz20261026a GammaCompactOrbitCutoffJets20261026b
open GammaActualCutoffNativeGradientBudget20261026b GammaOriginalCoreCutoffEventualExact20261026b
open GammaCompactSeedCutoffPlateau20261026a Gamma0ActualSmoothQuotientCore20261025a
open ActualModularCutoffMaassBudget20261025a ActualModularCutoffGradient20261025a
open ActualCuspStripCutoffGraph20261025a ActualCuspStripCutoff20261025a
open GammaInfinityTranslationStrip20261025a Gamma0WeightedCutoffDefectLimit20261026a
open ActualCompactSeedMaassJoin20261025a

def nativeCutoffCommutator (Y : ℝ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  F z*upperMaass (complexGlobalH Y) z + maassCross (complexGlobalH Y) F z

theorem upperMaass_actualCutoff_uniform_square (Y : ℝ) (hY : 1 < Y) (z : UpperHalfPlane) :
    ‖upperMaass (complexGlobalH Y) z‖^2 ≤ cutoffGraphConstant := by
  rcases upperMaass_global_zero_or_height Y hY z with hz | ⟨q,hq⟩
  · rw [hz,norm_zero,zero_pow (by norm_num)]
    exact cutoffGraphConstant_nonneg
  · rw [hq]
    let w := (Gamma0ParabolicEffectiveDecomposition20261025a.parabolicRepresentative 1 q) • z
    obtain ⟨k,hk,_⟩ := unique_translate_mem_strip w
    have hb := upperMaass_complexCutoff_norm_sq_pointwise (w := 1)
      (lt_trans (by norm_num) hY) (translate k w) hk
    have htranslate : upperMaass (complexCutoffH Y) (translate k w) =
        upperMaass (complexCutoffH Y) w := by
      simp only [upperMaass_complexCutoff,translate_im]
    rw [htranslate] at hb
    exact hb.trans (by
      by_cases ht : translate k w ∈ highWidthStrip 1 Y
      · rw [indicator_of_mem ht]
      · rw [indicator_of_notMem ht]
        exact cutoffGraphConstant_nonneg)

private theorem complex_dot_square_le (a b c d : ℂ) :
    ‖a*c+b*d‖^2 ≤ (‖a‖^2+‖b‖^2)*(‖c‖^2+‖d‖^2) := by
  have hh : ‖a*c+b*d‖ ≤ ‖a‖*‖c‖+‖b‖*‖d‖ := by
    simpa only [norm_mul] using norm_add_le (a*c) (b*d)
  calc
    _ ≤ (‖a‖*‖c‖+‖b‖*‖d‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
    _ ≤ _ := by nlinarith [sq_nonneg (‖a‖*‖d‖-‖b‖*‖c‖)]

theorem maassCross_norm_square_le (chi F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    ‖maassCross chi F z‖^2 ≤ 4*nativeEnergySq chi z*nativeEnergySq F z := by
  have hd := complex_dot_square_le (nativeDx chi z) (nativeDy chi z) (nativeDx F z) (nativeDy F z)
  have hw := mul_le_mul_of_nonneg_left hd (show 0 ≤ 4*z.im^4 by positivity)
  unfold maassCross nativeEnergySq
  simp only [norm_mul,norm_neg,norm_pow,Complex.norm_ofNat,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos z.im_pos,mul_pow]
  convert hw using 1 <;> ring

theorem nativeCutoffCommutator_square_bound (Y : ℝ) (hY : 1 < Y)
    (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    ‖nativeCutoffCommutator Y F z‖^2 ≤
      2*cutoffGraphConstant*‖F z‖^2 + 8*cutoffEnergyConstant*nativeEnergySq F z := by
  have hsum := norm_add_le (F z*upperMaass (complexGlobalH Y) z) (maassCross (complexGlobalH Y) F z)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hsum 2
  have htwo : ‖nativeCutoffCommutator Y F z‖^2 ≤
      2*‖F z*upperMaass (complexGlobalH Y) z‖^2+2*‖maassCross (complexGlobalH Y) F z‖^2 := by
    unfold nativeCutoffCommutator
    nlinarith [sq_nonneg (‖F z*upperMaass (complexGlobalH Y) z‖-‖maassCross (complexGlobalH Y) F z‖)]
  have hmaass := mul_le_mul_of_nonneg_left (upperMaass_actualCutoff_uniform_square Y hY z) (sq_nonneg ‖F z‖)
  have he : nativeEnergySq (complexGlobalH Y) z ≤ cutoffEnergyConstant := by
    rw [nativeEnergySq_actualCutoff]
    exact cutoffEnergyH_uniform Y hY z
  have hcross := (maassCross_norm_square_le (complexGlobalH Y) F z).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ) ≤ 4))
      (nativeEnergySq_nonneg F z))
  simp only [norm_mul,mul_pow] at htwo
  nlinarith

/-- Global functional fixedness plus an actual open-neighborhood argument
fixes the true second differential, without any support invariance axiom. -/
theorem multiplier_fixes_upperMaass_of_fixes_function (chi F : UpperHalfPlane → ℂ)
    (hc : Continuous chi) (hfix : chi*F = F) : chi*upperMaass F = upperMaass F := by
  funext z
  by_cases hz : chi z = 1
  · simp only [Pi.mul_apply,hz,one_mul]
  · have hnear : ∀ᶠ w in 𝓝 z, chi w ≠ 1 := (isOpen_ne hc continuous_const).mem_nhds hz
    have hzero : F =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [hnear] with w hw
      have hprod : (chi w-1)*F w = 0 := by
        have hh := congrFun hfix w
        simp only [Pi.mul_apply] at hh
        linear_combination hh
      exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hw)
    have hdiff := (native_jet_zero_of_germ_const F z 0 hzero).2.2.2.2
    simp only [Pi.mul_apply,hdiff,mul_zero]

theorem nativeCutoffCommutator_eq_zero_of_fixed
    (Y : ℝ) (hY : 0 < Y) (F : UpperHalfPlane → ℂ)
    (hFs : ContDiffOn ℝ 2 (extendUpper F) positiveChart)
    (hfix : complexGlobalH Y*F = F) : nativeCutoffCommutator Y F = 0 := by
  have hdiff := multiplier_fixes_upperMaass_of_fixes_function (complexGlobalH Y) F
    (native_C2_continuous _ (extendGlobal_C2 Y hY)) hfix
  funext z
  calc
    _ = upperMaass (complexGlobalH Y*F) z-(complexGlobalH Y*upperMaass F) z :=
      (upperMaass_multiplier_commutator (complexGlobalH Y) F (extendGlobal_C2 Y hY) hFs z).symm
    _ = 0 := by rw [hfix,hdiff]; simp only [sub_self,Pi.zero_apply]

end
end ImbalancedChen.Part3.GammaActualCutoffNativeCommutatorBudget20261026b
