import ImbalancedChen.Part3ActualScatteringResidueReciprocity
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Symmetry of the continued cusp-pair scattering entries and Schwarz
reflection on the actual normalized native functions. All initial
identities come from their determinant-one rows or literal real seeds. -/
namespace ImbalancedChen.Part3.ActualCriticalScatteringReciprocity20261110

noncomputable section
open Set Filter Topology Complex Matrix Matrix.SpecialLinearGroup UpperHalfPlane MeasureTheory
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualScatteringResidueReciprocity20261110 ActualNativeScatteringConstant20261110
open ActualCriticalScatteringEntry20261110 ActualParabolicScatteringRows20261110
open ActualCharacterCuspExpansion20261110 ActualYoungCriticalCusps20261110
open NativeAllCuspEisenstein20261026b ActualCriticalCuspEvaluation20261110
open Gamma0GeneralCuspUnitPeriod20261025a ActualCompletedCurveMeans20261110
open ActualEisensteinFourierInterchange20261025a

/-- The meromorphic uniqueness step used for the physical reciprocal
entries and the forward original character expansion. -/
theorem eq_at_regular_of_initial {f g : ℂ → ℂ} (hf : MeromorphicOn f ({0,1} : Set ℂ)ᶜ)
    (hg : MeromorphicOn g ({0,1} : Set ℂ)ᶜ) (hu : ∀ w : ℂ, 1 < w.re → f w = g w)
    {s : ℂ} (hs : s ≠ 0) (hs1 : s ≠ 1) (hfc : ContinuousAt f s) (hgc : ContinuousAt g s) :
    f s = g s := by
  let U := ({0,1} : Set ℂ)ᶜ
  let F := fun w => f w - g w
  have HM : MeromorphicOn F U := hf.fun_sub hg
  have HU : IsPreconnected U := (Set.Countable.isConnected_compl_of_one_lt_rank
    (by simp [Complex.rank_real_complex] : 1 < Module.rank ℝ ℂ)
    (Set.finite_pair (0 : ℂ) 1).countable).isPreconnected
  have h₂ : (2 : ℂ) ∈ U := by norm_num [U]
  have hS : s ∈ U := by simpa [U] using And.intro hs hs1
  have ho : meromorphicOrderAt F 2 = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hhalf : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hhalf] with w hw using sub_eq_zero.mpr (hu w hw)
  have hord : meromorphicOrderAt F s = ⊤ := by
    by_contra h
    exact (HM.meromorphicOrderAt_ne_top_of_isPreconnected HU hS h₂ h) ho
  apply sub_eq_zero.mp
  exact tendsto_nhds_unique_of_eventuallyEq ((hfc.sub hgc).tendsto.mono_left nhdsWithin_le_nhds)
    tendsto_const_nhds (meromorphicOrderAt_eq_top_iff.mp hord)

theorem entries_symmetric (N : ℕ) [NeZero N] (hN : 0 < N) (g h : SL(2,ℤ))
    (s : ℂ) (hs : 1/2 ≤ s.re) (hs1 : s ≠ 1) :
    continuedEntry N hN g h s = continuedEntry N hN h g s := by
  obtain ⟨H,Hd⟩ := continuedEntry_regularity N hN g h
  obtain ⟨J,Jd⟩ := continuedEntry_regularity N hN h g
  apply eq_at_regular_of_initial H J _ (fun e => by simp [e] at hs) hs1 (Hd s hs hs1).continuousAt (Jd s hs hs1).continuousAt
  intro w hw
  simp only [continuedEntry_initial N hN _ _ w hw,initial_entry_symmetric N hN g h w]

private theorem reflected_meromorphic {F : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt F (conj a)) :
    MeromorphicAt (fun z => conj (F (conj z))) a := by
  obtain ⟨n,H⟩ := hf
  let B := fun z => (z-conj a)^n • F z
  have hB : ∀ᶠ w in 𝓝 (conj a), DifferentiableAt ℂ B w :=
    Complex.analyticAt_iff_eventually_differentiableAt.mp H
  have J : AnalyticAt ℂ (fun z => conj (B (conj z))) a := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [Complex.continuous_conj.continuousAt.preimage_mem_nhds hB] with z hz
    simpa only [Function.comp_apply,Complex.conj_conj] using hz.conj_conj
  refine ⟨n,?_⟩
  simpa only [B,smul_eq_mul,map_mul,map_pow,map_sub,Complex.conj_conj] using J

private theorem original_seed_conjugation (N : ℕ) (g : SL(2,ℤ)) (s : ℂ) (z : ℍ) :
    cuspEisenstein N g (conj s) z = conj (cuspEisenstein N g s z) := by
  have ht : conj (∑' v : AllowedPair N g, normalizedSeed N g z v.1 s) =
      ∑' v : AllowedPair N g, conj (normalizedSeed N g z v.1 s) := RCLike.conjCLE.map_tsum
  simp only [cuspEisenstein,map_mul,map_div₀,map_one,map_ofNat,ht]
  congr 1
  apply tsum_congr
  intro v
  rw [normalizedSeed,normalizedSeed,← Complex.exp_conj,map_mul,Complex.conj_ofReal]

/-- Native Schwarz reflection for each genuine continued parabolic cusp
function at physical z. In particular conjugation at t reverses t. -/
theorem original_cusp_conjugation (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (z : ℍ)
    (s : ℂ) (hs : 1/2 ≤ s.re) (hs1 : s ≠ 1) :
    cuspFamily N (nativeFrameOrbit N g) (conj s) z = conj (cuspFamily N (nativeFrameOrbit N g) s z) := by
  let F := fun w => cuspFamily N (nativeFrameOrbit N g) w z
  have HM := cuspFamily_meromorphic N (nativeFrameOrbit N g) z
  have H (w : ℂ) (hw : 1/2 ≤ w.re) (h1 : w ≠ 1) : DifferentiableAt ℂ F w :=
    parameterFamily_differentiable _ z w hw h1
  have hc1 : conj s ≠ 1 := by simpa using hs1
  have hrev : ContinuousAt (fun w => conj (F (conj w))) s := by
    exact (Complex.continuous_conj.continuousAt.comp
      ((H (conj s) (by simpa using hs) hc1).continuousAt.comp Complex.continuous_conj.continuousAt))
  have E : F s = conj (F (conj s)) := by
    apply eq_at_regular_of_initial (fun w _ => HM w) (fun w _ => reflected_meromorphic (HM (conj w))) _
      (fun e => by simp [e] at hs) hs1 (H s hs hs1).continuousAt hrev
    intro w hw
    have hwc : 1 < (conj w).re := by simpa using hw
    simp only [F,cuspFamily_initial N g w hw,cuspFamily_initial N g (conj w) hwc,
      original_seed_conjugation,Complex.conj_conj]
  simpa only [F,Complex.conj_conj] using (congrArg conj E).symm

/-- Schwarz reflection of the physical scattering amplitude, including
the center. Extraction at height one uses the genuine native family. -/
theorem entry_conjugation (N : ℕ) [NeZero N] (hN : 0 < N) (g h : SL(2,ℤ))
    (s : ℂ) (hs : 1/2 ≤ s.re) (hs1 : s ≠ 1) :
    continuedEntry N hN g h (conj s) = conj (continuedEntry N hN g h s) := by
  have hI : incoming N g h (conj s) 1 = conj (incoming N g h s 1) := by
    classical
    by_cases H : nativeFrameOrbit N h = nativeFrameOrbit N g <;> simp [incoming,H]
  have H : horocycleMean N hN g h 1 zero_lt_one (conj s) = conj (horocycleMean N hN g h 1 zero_lt_one s) := by
    simp only [horocycleMean,curveMean,intervalIntegral.integral_of_le zero_le_one,
      ← integral_conj]
    exact integral_congr_ae (Eventually.of_forall (fun x => original_cusp_conjugation N g _ s hs hs1))
  rw [continuedEntry,continuedEntry,map_sub,H,hI]

theorem critical_entry_adjoint (N : ℕ) [NeZero N] (hN : 0 < N) (g h : SL(2,ℤ)) (t : ℝ) :
    continuedEntry N hN g h (criticalPoint (-t)) = conj (continuedEntry N hN h g (criticalPoint t)) := by
  have hs : 1/2 ≤ (criticalPoint t).re := by norm_num [criticalPoint,Complex.mul_re]
  have h1 : criticalPoint t ≠ 1 := by
    intro e
    have H := congrArg Complex.re e
    norm_num [criticalPoint,Complex.mul_re] at H
  have hc : criticalPoint (-t) = conj (criticalPoint t) := by
    apply Complex.ext <;> simp [criticalPoint,Complex.mul_re,Complex.mul_im]
  rw [hc,entry_conjugation N hN g h _ hs h1,entries_symmetric N hN g h _ hs h1]

end
end ImbalancedChen.Part3.ActualCriticalScatteringReciprocity20261110
