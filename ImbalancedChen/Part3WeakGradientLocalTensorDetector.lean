import ImbalancedChen.Part3WeakGradientRectangleTensorPairing
import ImbalancedChen.Part3UpperSupportedTensorL2Closure

/-! SOURCE ONLY / UNCOMPILED / NO FORMAL CREDIT.
A local tensor annihilator kills every compact tensor localization of an actual
L² function. The global density theorem is used only AFTER localization. No
local tensor density, representative regularity, or constancy is assumed. -/
namespace ImbalancedChen.Part3.WeakGradientLocalTensorDetector20261026a
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff
open ImbalancedChen.Part3.WeakGradientRectangleTensorPairing20261026a
open ImbalancedChen.Part3.PositiveRectangleSmoothTensorDensity20261025a
open ImbalancedChen.Part3.PositiveCompactTensorLpApproximation20261025a
open ImbalancedChen.Part3.CanonicalTensorHyperbolicLaplacianForm20261024z
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFirstGradientWeakLimit20261025a
open ImbalancedChen.Part3.MaassGradientUpperSupportClosure20261025a
open ImbalancedChen.Part3.UpperSupportedTensorL2Closure20261025a

/-- The cutoff is applied to the zero extension of the local L² representative. -/
def localTensorCutoff (Q : Set (ℝ × ℝ)) (f : (ℝ × ℝ) → ℂ)
    (g h : ℝ → ℝ) (p : ℝ × ℝ) : ℂ :=
  tensorTest g h p • Q.indicator f p

theorem localTensorCutoff_memLp {Q : Set (ℝ × ℝ)} (hQ : MeasurableSet Q)
    {f : (ℝ × ℝ) → ℂ} (hf : MemLp f 2 (volume.restrict Q))
    {g h : ℝ → ℝ} (hg : Continuous g) (hh : Continuous h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    MemLp (localTensorCutoff Q f g h) 2 volume := by
  have hfi : MemLp (Q.indicator f) 2 volume := (memLp_indicator_iff_restrict hQ).2 hf
  exact hfi.smul ((tensorTest_continuous hg hh).memLp_top_of_hasCompactSupport
    (tensorTest_hasCompactSupport hgc hhc) volume)

/-- Multiplication puts every global smooth tensor back into the exact local
support class of the weak equation. This is the missing localization step. -/
theorem localTensorCutoff_ae_zero {a b c d : ℝ} (hc : 0 ≤ c)
    {f : (ℝ × ℝ) → ℂ} (hf : MemLp f 2 (volume.restrict (openRectangle a b c d)))
    (hpair : ∀ u v : ℝ → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u ⊆ Ioo a b → ContDiff ℝ ∞ v → HasCompactSupport v →
      tsupport v ⊆ Ioo c d → tensorPairing (openRectangle a b c d) f u v = 0)
    {g h : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h)
    (hgs : tsupport g ⊆ Ioo a b) (hhs : tsupport h ⊆ Ioo c d) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), localTensorCutoff (openRectangle a b c d) f g h p = 0 := by
  let Q := openRectangle a b c d
  have hQ : MeasurableSet Q := measurableSet_Ioo.prod measurableSet_Ioo
  let F := localTensorCutoff Q f g h
  have hF : MemLp F 2 volume := localTensorCutoff_memLp hQ hf hg.continuous hh.continuous hgc hhc
  let G : PlaneL2 := hF.toLp F
  have hupper : G ∈ upperSupportedSubmodule := by
    change ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∉ upperChart → G p = 0
    filter_upwards [hF.coeFn_toLp] with p hp
    intro hout
    rw [hp]
    have hnQ : p ∉ Q := by
      intro hpQ
      exact hout (lt_of_le_of_lt hc hpQ.2.1)
    simp [F, localTensorCutoff, Set.indicator_of_notMem hnQ]
  have htest : ∀ T : SmoothPositiveTensor, inner ℂ (testL2 (toMaassTensor T)) G = 0 := by
    intro T
    have hT : MemLp (planeTensor T) 2 (volume : Measure (ℝ × ℝ)) :=
      (planeTensor_continuous T).memLp_of_hasCompactSupport (planeTensor_compact T)
    rw [← planeTensor_toLp_eq_actual_testL2 T hT, L2.inner_def]
    have he : (∫ p : ℝ × ℝ,
        inner ℂ ((hT.toLp (planeTensor T)) p) (G p)) =
        ∫ p : ℝ × ℝ, tensorTest (fun x => g x * T.horizontal x)
          (fun y => h y * T.vertical y) p • Q.indicator f p := by
      apply integral_congr_ae
      filter_upwards [hT.coeFn_toLp, hF.coeFn_toLp] with p hpT hpF
      rw [hpT, hpF]
      simp only [RCLike.inner_apply', planeTensor, F, localTensorCutoff,
        tensorTest, Complex.real_smul, Complex.ofReal_mul, star_mul, Complex.star_def,
        map_mul, Complex.conj_ofReal]
      ring
    rw [he]
    have hind : (fun p : ℝ × ℝ => tensorTest (fun x => g x * T.horizontal x)
        (fun y => h y * T.vertical y) p • Q.indicator f p) =
        Q.indicator (fun p => tensorTest (fun x => g x * T.horizontal x)
          (fun y => h y * T.vertical y) p • f p) := by
      funext p
      by_cases hp : p ∈ Q <;> simp [hp]
    rw [hind, integral_indicator hQ]
    exact hpair _ _ (hg.mul T.horizontal_smooth) hgc.mul_right
      (tsupport_mul_subset_left.trans hgs) (hh.mul T.vertical_smooth) hhc.mul_right
      (tsupport_mul_subset_left.trans hhs)
  have hspan : ∀ V ∈ smoothTensorL2Span, inner ℂ V G = 0 := by
    intro V hV
    change V ∈ Submodule.span ℂ (Set.range (fun T : SmoothPositiveTensor => testL2 (toMaassTensor T))) at hV
    induction hV using Submodule.span_induction with
    | mem V hV => obtain ⟨T, rfl⟩ := hV; exact htest T
    | zero => simp
    | add V W _ _ hV hW => simp only [inner_add_left, hV, hW, add_zero]
    | smul z V _ hV => simp only [inner_smul_left, hV, mul_zero]
  have hclosed : IsClosed {V : PlaneL2 | inner ℂ V G = 0} :=
    isClosed_eq (continuous_id.inner continuous_const) continuous_const
  have hGcl : G ∈ closure (smoothTensorL2Span : Set PlaneL2) := by
    change G ∈ smoothTensorL2Span.topologicalClosure
    rw [smoothTensorL2Span_topologicalClosure_eq_upperSupported]
    exact hupper
  have hzero : G = 0 := inner_self_eq_zero.mp (closure_minimal hspan hclosed hGcl)
  filter_upwards [hF.coeFn_toLp, Lp.coeFn_zero ℂ 2 (volume : Measure (ℝ × ℝ))] with p hp hp0
  rw [← hp]
  change G p = 0
  rw [hzero]
  exact hp0

/-- On any region where the chosen cutoff is one, the original representative
vanishes a.e. This conclusion concerns the original local function, not a
new regular representative. -/
theorem ae_zero_where_local_cutoff_one {a b c d : ℝ} (hc : 0 ≤ c)
    {f : (ℝ × ℝ) → ℂ} (hf : MemLp f 2 (volume.restrict (openRectangle a b c d)))
    (hpair : ∀ u v : ℝ → ℝ, ContDiff ℝ ∞ u → HasCompactSupport u →
      tsupport u ⊆ Ioo a b → ContDiff ℝ ∞ v → HasCompactSupport v →
      tsupport v ⊆ Ioo c d → tensorPairing (openRectangle a b c d) f u v = 0)
    {g h : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h)
    (hgs : tsupport g ⊆ Ioo a b) (hhs : tsupport h ⊆ Ioo c d) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      p ∈ openRectangle a b c d → g p.1 = 1 → h p.2 = 1 → f p = 0 := by
  filter_upwards [localTensorCutoff_ae_zero hc hf hpair hg hh hgc hhc hgs hhs] with p hp
  intro hpQ hpg hph
  simpa [localTensorCutoff, tensorTest, hpQ, hpg, hph] using hp

end
end ImbalancedChen.Part3.WeakGradientLocalTensorDetector20261026a
