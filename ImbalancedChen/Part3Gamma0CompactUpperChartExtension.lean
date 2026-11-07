import ImbalancedChen.Part3Gamma0SmoothTensorSpanRendering

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

An actual continuous compact H-function is zero extended to real positive
coordinates. Its topological support is contained in the compact coordinate
image of its ORIGINAL H-support. Continuity across y=0 follows from this
compact image staying at positive height, not from treating ofComplex as
globally continuous. If the original support is in the actual reduced
carrier, the entire extended support remains in that actual carrier chart.
-/

namespace ImbalancedChen.Part3.Gamma0CompactUpperChartExtension20261025a

noncomputable section
open Set Filter Topology
open scoped UpperHalfPlane
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CompactTensorPoincareC2Core20261025a
open ImbalancedChen.Part3.Gamma0SmoothCompactTensorCore20261025a

def coordinates (z : UpperHalfPlane) : ℝ×ℝ := (z.re,z.im)

theorem coordinates_continuous : Continuous coordinates :=
  UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im

theorem chartLift_coordinates (z : UpperHalfPlane) : chartLift (coordinates z)=z := by
  rw [chartLift_of_positive z.im_pos]
  apply UpperHalfPlane.ext
  ext <;> rfl

theorem extendUpper_positive (f : UpperHalfPlane→ℂ) {p : ℝ×ℝ} (hp : 0<p.2) :
    extendUpper f p=f (chartLift p) := by
  rw [extendUpper,dif_pos hp,chartLift_of_positive hp]

theorem extendUpper_support_image (f : UpperHalfPlane→ℂ)
    (hfc : HasCompactSupport f) :
    tsupport (extendUpper f)⊆coordinates '' tsupport f := by
  apply closure_minimal _ (hfc.image coordinates_continuous).isClosed
  intro p hp
  by_cases hy : 0<p.2
  · let z : UpperHalfPlane := ⟨⟨p.1,p.2⟩,hy⟩
    have hz : f z≠0 := by simpa only [extendUpper,dif_pos hy,z] using hp
    exact ⟨z,subset_tsupport _ hz,rfl⟩
  · exact (hp (by simp only [extendUpper,dif_neg hy])).elim

theorem extendUpper_hasCompactSupport (f : UpperHalfPlane→ℂ)
    (hfc : HasCompactSupport f) : HasCompactSupport (extendUpper f) :=
  (hfc.image coordinates_continuous).of_isClosed_subset isClosed_tsupport
    (extendUpper_support_image f hfc)

theorem extendUpper_continuous (f : UpperHalfPlane→ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f) : Continuous (extendUpper f) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hy : 0<p.2
  · have hchart : ContinuousAt chartLift p :=
      (UpperHalfPlane.contMDiffAt_ofComplex (n:=2) hy).continuousAt.comp
        complexOfPair_contDiff_infty.continuous.continuousAt
    have heq : extendUpper f =ᶠ[𝓝 p] (fun q => f (chartLift q)) := by
      filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hy] with q hq
      exact extendUpper_positive f hq
    exact (hf.continuousAt.comp p hchart).congr_of_eventuallyEq heq
  · have hout : p∉coordinates '' tsupport f := by
      rintro ⟨z,_,hz⟩
      have hh : z.im=p.2 := congrArg Prod.snd hz
      exact hy (hh ▸ z.im_pos)
    have heq : extendUpper f =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [(hfc.image coordinates_continuous).isClosed.isOpen_compl.mem_nhds hout]
        with q hq
      exact image_eq_zero_of_notMem_tsupport
        (fun ht => hq (extendUpper_support_image f hfc ht))
    exact continuousAt_const.congr_of_eventuallyEq heq

theorem extendUpper_support_inside_actual_chart (N : ℕ) [NeZero N]
    (f : UpperHalfPlane→ℂ) (hfc : HasCompactSupport f)
    (hsupp : tsupport f⊆reducedCarrier N) :
    ∀ p∈tsupport (extendUpper f),0<p.2 ∧ chartLift p∈reducedCarrier N := by
  intro p hp
  obtain ⟨z,hz,rfl⟩ := extendUpper_support_image f hfc hp
  exact ⟨z.im_pos,by rw [chartLift_coordinates]; exact hsupp hz⟩

end
end ImbalancedChen.Part3.Gamma0CompactUpperChartExtension20261025a
