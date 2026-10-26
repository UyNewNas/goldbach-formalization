import ImbalancedChen.Part3ActualMobiusPairChartL2Transport
import Mathlib.MeasureTheory.Function.L2Space

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual Mobius value and first-jet L2 error bounds, on native Lp classes.
The geometric Jacobian suppliers are converted to genuine real norm
inequalities. No composition continuity or weak chain rule is assumed.
-/

namespace ImbalancedChen.Part3.MobiusStrongFirstJetL2Errors20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups UpperHalfPlane
open Gamma0CompactTensorPoincareC2Core20261025a
open ActualMobiusCompactLpTransport20261026b ActualMobiusPairChartL2Transport20261026b

abbrev Plane := ℝ × ℝ
abbrev LocalL2 (K : Set Plane) := Lp ℂ 2 ((volume : Measure Plane).restrict K)

theorem toLp_sub_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖hf.toLp f - hg.toLp g‖^2 = ∫ p, ‖f p-g p‖^2 ∂μ := by
  have hn : (∫ p, ‖(hf.toLp f-hg.toLp g) p‖^2 ∂μ) = ‖hf.toLp f-hg.toLp g‖^2 := by
    apply Complex.ofRealLI.injective
    simpa [← LinearIsometry.integral_comp_comm,inner_self_eq_norm_sq_to_K] using
      (L2.inner_def (𝕜 := ℂ) (hf.toLp f-hg.toLp g) (hf.toLp f-hg.toLp g)).symm
  rw [← hn]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g),hf.coeFn_toLp,hg.coeFn_toLp]
    with p hp hfp hgp
  rw [hp,hfp,hgp]

def compClass (g : SL(2, ℤ)) {K : Set Plane} (hK : IsCompact K)
    (hKp : ∀ p ∈ K, 0 < p.2) {F : Plane → ℂ} (hF : MemLp F 2 volume) : LocalL2 K :=
  (pairchart_memLp_comp g hK hKp (hF.restrict (mobiusChart g '' K))).toLp
    (fun p => F (mobiusChart g p))

def jetXClass (g : SL(2, ℤ)) {K : Set Plane} (hK : IsCompact K)
    (hKp : ∀ p ∈ K, 0 < p.2) {U V : Plane → ℂ}
    (hU : MemLp U 2 volume) (hV : MemLp V 2 volume) : LocalL2 K :=
  (pairchart_rawJet_memLp g hK hKp (hU.restrict _) (hV.restrict _)).1.toLp (pairRawJetX g U V)

def jetYClass (g : SL(2, ℤ)) {K : Set Plane} (hK : IsCompact K)
    (hKp : ∀ p ∈ K, 0 < p.2) {U V : Plane → ℂ}
    (hU : MemLp U 2 volume) (hV : MemLp V 2 volume) : LocalL2 K :=
  (pairchart_rawJet_memLp g hK hKp (hU.restrict _) (hV.restrict _)).2.toLp (pairRawJetY g U V)

theorem pairRawJetX_sub (g : SL(2, ℤ)) (U V P Q : Plane → ℂ) :
    pairRawJetX g (U-P) (V-Q) = pairRawJetX g U V-pairRawJetX g P Q := by
  funext p
  simp only [pairRawJetX,Pi.sub_apply,smul_sub]
  abel

theorem pairRawJetY_sub (g : SL(2, ℤ)) (U V P Q : Plane → ℂ) :
    pairRawJetY g (U-P) (V-Q) = pairRawJetY g U V-pairRawJetY g P Q := by
  funext p
  simp only [pairRawJetY,Pi.sub_apply,smul_sub]
  abel

theorem compClass_norm_sq_error (g : SL(2, ℤ)) {K : Set Plane}
    (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2)
    {F G : Plane → ℂ} (hF : MemLp F 2 volume) (hG : MemLp G 2 volume) :
    ‖compClass g hK hKp hF-compClass g hK hKp hG‖^2 ≤
      compactCompositionConstant g (complexSet K) (complexSet_isCompact hK) *
        ‖hF.toLp F-hG.toLp G‖^2 := by
  let C := compactCompositionConstant g (complexSet K) (complexSet_isCompact hK)
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans (compactCompositionConstant_one_le g _)
  have hsrc := (pairchart_memLp_comp g hK hKp (hF.restrict _)).sub
    (pairchart_memLp_comp g hK hKp (hG.restrict _))
  have hs : Integrable (fun p => ‖F (mobiusChart g p)-G (mobiusChart g p)‖^2)
      ((volume : Measure Plane).restrict K) := by
    simpa only [Pi.sub_apply] using hsrc.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have ht : Integrable (fun p => ‖F p-G p‖^2) volume := by
    simpa only [Pi.sub_apply] using (hF.sub hG).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  have hb := (pairchart_scalar_L2_error_le g hK hKp F G).trans
    (mul_le_mul_left' (lintegral_mono_measure (Measure.restrict_le_self
      (s := mobiusChart g '' K))) (ENNReal.ofReal C))
  rw [← ofReal_integral_eq_lintegral_ofReal hs (Eventually.of_forall (fun p => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal ht (Eventually.of_forall (fun p => sq_nonneg _))] at hb
  have hr := ENNReal.toReal_mono (by simp) hb
  rw [compClass,compClass,toLp_sub_norm_sq,toLp_sub_norm_sq]
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hC,
    ENNReal.toReal_ofReal (integral_nonneg (fun p => sq_nonneg _))] using hr

/-- Raw transformed gradient ERROR has a true joint contraction, derived
from the exact native Jacobian energy transport, including both components. -/
theorem jetClass_norm_sq_error (g : SL(2, ℤ)) {K : Set Plane}
    (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2)
    {U V P Q : Plane → ℂ} (hU : MemLp U 2 volume) (hV : MemLp V 2 volume)
    (hP : MemLp P 2 volume) (hQ : MemLp Q 2 volume) :
    ‖jetXClass g hK hKp hU hV-jetXClass g hK hKp hP hQ‖^2 +
      ‖jetYClass g hK hKp hU hV-jetYClass g hK hKp hP hQ‖^2 ≤
        ‖hU.toLp U-hP.toLp P‖^2 + ‖hV.toLp V-hQ.toLp Q‖^2 := by
  have hA := hU.sub hP
  have hB := hV.sub hQ
  obtain ⟨hX,hY⟩ := pairchart_rawJet_memLp g hK hKp (hA.restrict _) (hB.restrict _)
  have hs : Integrable (fun p => ‖pairRawJetX g (U-P) (V-Q) p‖^2 +
      ‖pairRawJetY g (U-P) (V-Q) p‖^2) ((volume : Measure Plane).restrict K) :=
    (hX.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).add
      (hY.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  have ht : Integrable (fun p => ‖(U-P) p‖^2+‖(V-Q) p‖^2) volume :=
    (hA.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).add
      (hB.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))
  have hb : (∫⁻ p in K, ENNReal.ofReal (‖pairRawJetX g (U-P) (V-Q) p‖^2+
        ‖pairRawJetY g (U-P) (V-Q) p‖^2)) ≤
      ∫⁻ p, ENNReal.ofReal (‖(U-P) p‖^2+‖(V-Q) p‖^2) := by
    rw [pairchart_rawJet_L2_energy g hK hKp]
    exact lintegral_mono_measure Measure.restrict_le_self
  rw [← ofReal_integral_eq_lintegral_ofReal hs (Eventually.of_forall
      (fun p => add_nonneg (sq_nonneg _) (sq_nonneg _))),
    ← ofReal_integral_eq_lintegral_ofReal ht (Eventually.of_forall
      (fun p => add_nonneg (sq_nonneg _) (sq_nonneg _)))] at hb
  have hr := ENNReal.toReal_mono (by simp) hb
  have hr' : (∫ p in K, ‖pairRawJetX g (U-P) (V-Q) p‖^2+
      ‖pairRawJetY g (U-P) (V-Q) p‖^2) ≤
      ∫ p, ‖(U-P) p‖^2+‖(V-Q) p‖^2 := by
    simpa only [ENNReal.toReal_ofReal (integral_nonneg
      (fun p => add_nonneg (sq_nonneg _) (sq_nonneg _)))] using hr
  rw [integral_add (hX.integrable_norm_pow (by decide)) (hY.integrable_norm_pow (by decide)),
    integral_add (hA.integrable_norm_pow (by decide)) (hB.integrable_norm_pow (by decide)),
    pairRawJetX_sub,pairRawJetY_sub] at hr'
  simpa only [jetXClass,jetYClass,toLp_sub_norm_sq,Pi.sub_apply] using hr'

end
end ImbalancedChen.Part3.MobiusStrongFirstJetL2Errors20261026b
