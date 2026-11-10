import ImbalancedChen.Part3ActualNativeHorocycleParameter
import ImbalancedChen.Part3ActualNativeScatteringConstant
import Mathlib.Analysis.Normed.Module.Connected

/-! The continued scattering coefficient is determined by the original
Dirichlet series on the region of absolute convergence. Meromorphic
uniqueness propagates the native two-power constant term to all heights
on the critical line, even at t=0 where the two exponents coincide. -/
namespace ImbalancedChen.Part3.ActualCriticalScatteringEntry20261110

noncomputable section
open Set Filter Topology Complex Matrix Matrix.SpecialLinearGroup UpperHalfPlane MeasureTheory
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualCompletedCurveMeans20261110 ActualNativeHorocycleParameter20261110
open ActualParabolicScatteringRows20261110 ActualNativeScatteringConstant20261110
open ActualYoungCriticalCusps20261110 ActualCharacterCuspExpansion20261110
open ActualEisensteinFourierInterchange20261025a Gamma0GeneralCuspUnitPeriod20261025a
open ActualCriticalCuspEvaluation20261110

def horocycleMean (N : ℕ) [NeZero N] (hN : 0 < N) (g h : SL(2,ℤ))
    (y : ℝ) (hy : 0 < y) (s : ℂ) : ℂ :=
  curveMean (fun x => normalizedScaling N hN h • horizontalPoint y hy x)
    (cuspFamily N (nativeFrameOrbit N g)) s

def continuedEntry (N : ℕ) [NeZero N] (hN : 0 < N) (g h : SL(2,ℤ)) (s : ℂ) : ℂ :=
  horocycleMean N hN g h 1 zero_lt_one s - incoming N g h s 1

theorem continuedEntry_initial (N : ℕ) [NeZero N] (hN : 0 < N) (g h : SL(2,ℤ))
    (s : ℂ) (hs : 1 < s.re) : continuedEntry N hN g h s = scatteringEntry N g h s := by
  rw [continuedEntry,horocycleMean,curveMean,cuspFamily_initial_constant_term N hN g h s hs]
  simp

private theorem mean_reg (N : ℕ) [NeZero N] (hN : 0 < N) (g h : SL(2,ℤ))
    (y : ℝ) (hy : 0 < y) :
    MeromorphicOn (horocycleMean N hN g h y hy) ({0,1} : Set ℂ)ᶜ ∧
      ∀ s : ℂ, 1/2 ≤ s.re → s ≠ 1 → DifferentiableAt ℂ (horocycleMean N hN g h y hy) s := by
  apply native_curve_regularity
  change Continuous (fun x : ℝ => Matrix.SpecialLinearGroup.mapGL ℝ (normalizedScaling N hN h) •
    horizontalPoint y hy x)
  apply (continuous_const_smul _).comp
  unfold horizontalPoint
  fun_prop

private theorem incoming_entire (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (y : ℝ) (hy : 0 < y) :
    Differentiable ℂ (fun s => incoming N g h s y) := by
  classical
  by_cases H : nativeFrameOrbit N h = nativeFrameOrbit N g
  · simp only [incoming,if_pos H]
    exact fun _ => differentiableAt_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hy.ne'))
  · simp only [incoming,if_neg H]
    exact differentiable_const _

private theorem entire_merom {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    MeromorphicOn f ({0,1} : Set ℂ)ᶜ :=
  fun s _ => ((analyticOnNhd_univ_iff_differentiable.mpr hf) s (mem_univ s)).meromorphicAt

/-- An actual meromorphic continuation of the initial Gamma/Dirichlet
scattering entry, regular on the critical line and at the central point. -/
theorem continuedEntry_regularity (N : ℕ) [NeZero N] (hN : 0 < N) (g h : SL(2,ℤ)) :
    MeromorphicOn (continuedEntry N hN g h) ({0,1} : Set ℂ)ᶜ ∧
      ∀ s : ℂ, 1/2 ≤ s.re → s ≠ 1 → DifferentiableAt ℂ (continuedEntry N hN g h) s := by
  obtain ⟨hm,hd⟩ := mean_reg N hN g h 1 zero_lt_one
  have hi := incoming_entire N g h 1 zero_lt_one
  exact ⟨hm.fun_sub (entire_merom hi),fun s hs h1 => (hd s hs h1).sub (hi s)⟩

/-- At every physical height, the outgoing amplitude is the very same
continued initial entry. Meromorphic uniqueness takes place away from
the two completed poles; actual regularity gives pointwise equality at
the original s, so a choice of pole-representative cannot decide it. -/
theorem actual_constant_term (N : ℕ) [NeZero N] (hN : 0 < N) (g h : SL(2,ℤ))
    (u : ℂ) (hu : 1/2 ≤ u.re) (hu1 : u ≠ 1) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, cuspFamily N (nativeFrameOrbit N g) u
      (normalizedScaling N hN h • horizontalPoint y hy x)) =
        incoming N g h u y + continuedEntry N hN g h u*(y : ℂ)^(1-u) := by
  let U := ({0,1} : Set ℂ)ᶜ
  let F (s : ℂ) := horocycleMean N hN g h y hy s -
    (incoming N g h s y + continuedEntry N hN g h s*(y : ℂ)^(1-s))
  obtain ⟨hm,hd⟩ := mean_reg N hN g h y hy
  obtain ⟨hσ,hσd⟩ := continuedEntry_regularity N hN g h
  have hI := incoming_entire N g h y hy
  have hP : Differentiable ℂ (fun s : ℂ => (y : ℂ)^(1-s)) := fun s =>
    ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr hy.ne'))
  have hF : MeromorphicOn F U := hm.fun_sub ((entire_merom hI).fun_add
    (hσ.fun_mul (entire_merom hP)))
  have hU : IsPreconnected U :=
    (Set.Countable.isConnected_compl_of_one_lt_rank
      (by simp [Complex.rank_real_complex] : 1 < Module.rank ℝ ℂ)
      (Set.finite_pair (0 : ℂ) 1).countable).isPreconnected
  have h₂ : (2 : ℂ) ∈ U := by norm_num [U]
  have hu0 : u ≠ 0 := by intro e; simp [e] at hu
  have huU : u ∈ U := by simpa [U] using And.intro hu0 hu1
  have h2order : meromorphicOrderAt F (2 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hp : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hp] with s hs
    rw [F,horocycleMean,curveMean,cuspFamily_initial_constant_term N hN g h s hs,
      continuedEntry_initial N hN g h s hs,sub_self]
  have he : meromorphicOrderAt F u = ⊤ := by
    by_contra huord
    exact (hF.meromorphicOrderAt_ne_top_of_isPreconnected hU huU h₂ huord) h2order
  have hcont : ContinuousAt F u :=
    ((hd u hu hu1).sub ((hI u).add ((hσd u hu hu1).mul (hP u)))).continuousAt
  have hz : F u = 0 := tendsto_nhds_unique_of_eventuallyEq
    (hcont.tendsto.mono_left nhdsWithin_le_nhds) tendsto_const_nhds
    (meromorphicOrderAt_eq_top_iff.mp he)
  exact sub_eq_zero.mp hz

/-- Every member of the native continuous family used in the actual
four-spectrum packet now has the physical two-cusp constant row. -/
theorem critical_native_constant_term (N : ℕ) [NeZero N] (hN : 0 < N) (g h : SL(2,ℤ))
    (t y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, cuspFamily N (nativeFrameOrbit N g) (criticalPoint t)
      (normalizedScaling N hN h • horizontalPoint y hy x)) =
      incoming N g h (criticalPoint t) y + continuedEntry N hN g h (criticalPoint t)*
        (y : ℂ)^(1-criticalPoint t) := by
  apply actual_constant_term N hN g h
  · norm_num [criticalPoint,Complex.mul_re]
  · intro he
    have H := congrArg Complex.re he
    norm_num [criticalPoint,Complex.mul_re] at H

end
end ImbalancedChen.Part3.ActualCriticalScatteringEntry20261110
