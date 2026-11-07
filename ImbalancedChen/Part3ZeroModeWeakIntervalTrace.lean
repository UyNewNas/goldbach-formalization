import ImbalancedChen.Part3ZeroModeComplexPrimitiveWeak
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

An actual finite-interval distributional derivative pair has a continuous,
coordinatewise absolutely continuous representative. Its derivative is the
given weak derivative a.e.; its endpoint traces are determined uniquely by
the original a.e. function. No smooth graph approximation is assumed.
All imports are independent of the held tail-Hardy chain.
-/

namespace ImbalancedChen.Part3.ZeroModeWeakIntervalTrace20261026b
noncomputable section
open MeasureTheory Set Filter
open ZeroModeRealPrimitiveWeak20261026b ZeroModeComplexPrimitiveWeak20261026b
open WeakDerivativeIntervalRigidity20261026a

private theorem ac_congr_interval {F : Type*} [PseudoMetricSpace F]
    {a b : ℝ} {u v : ℝ → F} (hu : AbsolutelyContinuousOnInterval u a b)
    (heq : EqOn v u (uIcc a b)) : AbsolutelyContinuousOnInterval v a b := by
  rw [absolutelyContinuousOnInterval_iff] at hu ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδprop⟩ := hu ε hε
  refine ⟨δ, hδ, ?_⟩
  intro E hE hlen
  have hs : (∑ i ∈ Finset.range E.1, dist (v (E.2 i).1) (v (E.2 i).2)) =
      ∑ i ∈ Finset.range E.1, dist (u (E.2 i).1) (u (E.2 i).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hm := hE.1 i hi
    rw [heq hm.1, heq hm.2]
  rw [hs]
  exact hδprop E hE hlen

/-- A local weak derivative gives an actual indefinite-integral representative.
The additive constant is obtained by zero-weak-derivative rigidity. -/
theorem exists_integral_representative {a b : ℝ} (hab : a < b)
    {f g : ℝ → ℂ} (hf : LocallyIntegrableOn f (Ioo a b))
    (hg : IntervalIntegrable g volume a b)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
      (∫ x, deriv ψ x • f x) = -(∫ x, ψ x • g x)) :
    ∃ c : ℂ, ∀ᵐ x, x ∈ Ioo a b → f x = c + complexPrimitive a g x := by
  have hGc : ContinuousOn (complexPrimitive a g) (Ioo a b) :=
    (complexPrimitive_continuousOn hg).mono (by
      rw [uIcc_of_le hab.le]
      exact Ioo_subset_Icc_self)
  have hGloc := hGc.locallyIntegrableOn measurableSet_Ioo
  have hzero : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
      (∫ x, deriv ψ x • (f x - complexPrimitive a g x)) = 0 := by
    intro ψ hψ hψc hψs
    have hdψ : ContDiff ℝ ∞ (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
    have hdψs : tsupport (deriv ψ) ⊆ Ioo a b := tsupport_deriv_subset.trans hψs
    have hiF := integrable_local_test_smul hf hdψ.continuous hψc.deriv hdψs
    have hiG := integrable_local_test_smul hGloc hdψ.continuous hψc.deriv hdψs
    simp_rw [smul_sub]
    rw [integral_sub hiF hiG, hweak ψ hψ hψc hψs,
      complexPrimitive_weak_identity hab.le hg hψ hψc hψs, sub_self]
  obtain ⟨c, hc⟩ := ae_eq_const_of_zero_weak_derivative hab (hf.sub hGloc) hzero
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  intro hxi
  exact (sub_eq_iff_eq_add).mp (hx hxi)

/-- This object records a regular representative, not an assumed graph limit. -/
structure IntervalSobolevRepresentative (a b : ℝ) (f g : ℝ → ℂ) where
  function : ℝ → ℂ
  continuous : ContinuousOn function (Icc a b)
  re_ac : AbsolutelyContinuousOnInterval (fun x => (function x).re) a b
  im_ac : AbsolutelyContinuousOnInterval (fun x => (function x).im) a b
  value_ae : ∀ᵐ x, x ∈ Ioo a b → f x = function x
  derivative_ae : ∀ᵐ x, x ∈ Icc a b → HasDerivAt function (g x) x
  fundamental : ∀ x ∈ Icc a b, function x = function a + ∫ t in a..x, g t

/-- Constructed regular representative, including both endpoint traces and
the exact fundamental theorem of calculus with the supplied weak derivative. -/
theorem nonempty_intervalSobolevRepresentative {a b : ℝ} (hab : a < b)
    {f g : ℝ → ℂ} (hf : LocallyIntegrableOn f (Ioo a b))
    (hg : IntervalIntegrable g volume a b)
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
      (∫ x, deriv ψ x • f x) = -(∫ x, ψ x • g x)) :
    Nonempty (IntervalSobolevRepresentative a b f g) := by
  obtain ⟨c, hc⟩ := exists_integral_representative hab hf hg hweak
  let F : ℝ → ℂ := fun x => c + complexPrimitive a g x
  have hgre : IntervalIntegrable (fun x => (g x).re) volume a b := ⟨hg.1.re, hg.2.re⟩
  have hgim : IntervalIntegrable (fun x => (g x).im) volume a b := ⟨hg.1.im, hg.2.im⟩
  have hreconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c.re) a b :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c.re)).contDiffOn.absolutelyContinuousOnInterval
  have himconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c.im) a b :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => c.im)).contDiffOn.absolutelyContinuousOnInterval
  have hre : AbsolutelyContinuousOnInterval (fun x => (F x).re) a b := by
    apply ac_congr_interval
      (hreconst.add (hgre.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)))
    intro x hx
    simp only [F, Complex.add_re, complexPrimitive_re hg hx, realPrimitive, Pi.add_apply]
  have him : AbsolutelyContinuousOnInterval (fun x => (F x).im) a b := by
    apply ac_congr_interval
      (himconst.add (hgim.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)))
    intro x hx
    simp only [F, Complex.add_im, complexPrimitive_im hg hx, realPrimitive, Pi.add_apply]
  refine ⟨{
    function := F
    continuous := ?_
    re_ac := hre
    im_ac := him
    value_ae := hc
    derivative_ae := ?_
    fundamental := ?_ }⟩
  · have hcont : ContinuousOn F (uIcc a b) :=
      continuousOn_const.add (complexPrimitive_continuousOn hg)
    simpa only [uIcc_of_le hab.le] using hcont
  · filter_upwards [hg.ae_hasDerivAt_integral] with x hx hxi
    have hxu : x ∈ uIcc a b := by simpa only [uIcc_of_le hab.le] using hxi
    simpa only [zero_add] using
      (hasDerivAt_const x c).add (hx hxu a (by simp))
  · intro x hx
    simp [F, complexPrimitive]

/-- The continuous representative and hence both endpoint traces are unique
on the closed interval, even though the original data are only a.e. classes. -/
theorem IntervalSobolevRepresentative.unique_of_value_ae {a b : ℝ} (hab : a < b)
    {f g f' g' : ℝ → ℂ} (u : IntervalSobolevRepresentative a b f g)
    (v : IntervalSobolevRepresentative a b f' g')
    (hvalue : ∀ᵐ x, x ∈ Ioo a b → f x = f' x) :
    EqOn u.function v.function (Icc a b) := by
  have hae : u.function =ᵐ[volume.restrict (Ioo a b)] v.function := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [u.value_ae, v.value_ae, hvalue] with x hu hv hff hxi
    exact (hu hxi).symm.trans ((hff hxi).trans (hv hxi))
  rw [restrict_Ioo_eq_restrict_Icc] at hae
  exact Measure.eqOn_Icc_of_ae_eq hab.ne hae u.continuous v.continuous

theorem IntervalSobolevRepresentative.unique_on_closed_interval {a b : ℝ} (hab : a < b)
    {f g : ℝ → ℂ} (u v : IntervalSobolevRepresentative a b f g) :
    EqOn u.function v.function (Icc a b) :=
  IntervalSobolevRepresentative.unique_of_value_ae hab u v
    (Eventually.of_forall (fun _ _ => rfl))

theorem IntervalSobolevRepresentative.endpoint_traces_unique {a b : ℝ} (hab : a < b)
    {f g : ℝ → ℂ} (u v : IntervalSobolevRepresentative a b f g) :
    u.function a = v.function a ∧ u.function b = v.function b := by
  have h := IntervalSobolevRepresentative.unique_on_closed_interval hab u v
  exact ⟨h ⟨le_rfl, hab.le⟩, h ⟨hab.le, le_rfl⟩⟩

/-- Actual finite-interval L2 weak data suffice for the regular representative;
there is no regularity or approximation assumption beyond the weak identity. -/
theorem nonempty_intervalSobolevRepresentative_of_memLp {a b : ℝ} (hab : a < b)
    {f g : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
      (∫ x, deriv ψ x • f x) = -(∫ x, ψ x • g x)) :
    Nonempty (IntervalSobolevRepresentative a b f g) := by
  have hfi : IntegrableOn f (Ioo a b) := MemLp.integrable (by norm_num) hf
  have hgi : IntegrableOn g (Ioo a b) := MemLp.integrable (by norm_num) hg
  exact nonempty_intervalSobolevRepresentative hab hfi.locallyIntegrableOn
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mpr hgi) hweak

end
end ImbalancedChen.Part3.ZeroModeWeakIntervalTrace20261026b
