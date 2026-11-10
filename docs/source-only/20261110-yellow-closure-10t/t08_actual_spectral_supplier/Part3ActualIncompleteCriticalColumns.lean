import ImbalancedChen.Part3ActualIncompleteMellinFactors
import ImbalancedChen.Part3AngularFourierUnitary

/-! Critical boundary values on the noncuspidal test generators. Every
entry is the physical spatial pairing testified by the native cusp
integral. Absolute convergence uses the actual unitary scattering matrix
and the Schwartz Mellin transforms of these same compact tests. -/
namespace ImbalancedChen.Part3.ActualIncompleteCriticalColumns20261110

noncomputable section
open Set Filter Topology MeasureTheory Matrix Complex UpperHalfPlane
open scoped UpperHalfPlane MatrixGroups FourierTransform SchwartzMap BigOperators Classical
open SmoothZeroHeightSeedProfiles20261026b CompactHeightMellinInversion20261027
open NativeCuspCompactMellinSynthesis20261027 ActualCharacterCuspExpansion20261110
open ActualCriticalCuspEvaluation20261110 ActualCriticalScatteringEntry20261110
open ActualCriticalScatteringReciprocity20261110 ActualCriticalScatteringUnitarity20261110
open ActualIncompleteEisensteinTransform20261110 ActualIncompleteEisensteinGram20261110
open ActualIncompleteMellinFactors20261110 ActualContinuousSpatialProfiles20261110
open ActualRegularEisensteinQuotient20261110 ActualYoungCriticalCusps20261110
open ActualParabolicScatteringRows20261110 Gamma0QuotientCellPushforward20261025a

def frameIndex (N : ℕ) [NeZero N] (h : SL(2,ℤ)) : CuspRowClass N :=
  (nativeCuspEquiv N).symm (nativeFrameOrbit N h)

@[simp] theorem frameIndex_classFrame {N : ℕ} [NeZero N] (b : CuspRowClass N) :
    frameIndex N (classFrame b) = b := (nativeCuspEquiv N).symm_apply_apply b

theorem critical_parameters (t : ℝ) : verticalParameter (1/2) t = criticalPoint t ∧
    1/2 ≤ (criticalPoint t).re ∧ criticalPoint t ≠ 0 ∧ criticalPoint t ≠ 1 := by
  have E : (criticalPoint t).re = 1/2 := by norm_num [criticalPoint,Complex.mul_re]
  refine ⟨by unfold verticalParameter criticalPoint; push_cast; ring,E.ge,?_,?_⟩ <;>
    intro e <;> rw [e] at E <;> norm_num at E

private theorem eq_source {N : ℕ} [NeZero N] {g g' : SL(2,ℤ)}
    (H : nativeFrameOrbit N g = nativeFrameOrbit N g') (h : SL(2,ℤ)) (s : ℂ) :
    continuedEntry N (NeZero.pos N) g h s = continuedEntry N (NeZero.pos N) g' h s := by
  simp only [continuedEntry,horocycleMean,ActualParabolicScatteringRows20261110.incoming,H]

theorem entry_eq_matrix (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (t : ℝ) :
    continuedEntry N (NeZero.pos N) g h (criticalPoint t) = scatteringMatrix N t (frameIndex N g) (frameIndex N h) := by
  have R (v : SL(2,ℤ)) : nativeFrameOrbit N (classFrame (frameIndex N v)) = nativeFrameOrbit N v :=
    (nativeCuspEquiv N).apply_symm_apply _
  have T := (critical_parameters t).2
  rw [scatteringMatrix,eq_source (R g) (classFrame (frameIndex N h)) _,
    entries_symmetric N _ g (classFrame (frameIndex N h)) _ T.1 T.2.2,eq_source (R h) g _,
    entries_symmetric N _ h g _ T.1 T.2.2]

theorem column_norm_sq (N : ℕ) [NeZero N] (t : ℝ) (b : CuspRowClass N) :
    ∑ a, ‖scatteringMatrix N t a b‖^2 = 1 := by
  let S := scatteringMatrix N t
  have H := congrArg (fun M : Matrix (CuspRowClass N) (CuspRowClass N) ℂ => M b b)
    (actual_critical_scattering_unitary N t).2
  have E : ∑ a, ((‖S a b‖^2 : ℝ) : ℂ) = 1 := by
    simpa only [S,Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.star_def,Complex.conj_mul',
      Complex.ofReal_pow,Matrix.one_apply_eq] using H
  exact_mod_cast E

theorem entry_norm_le (N : ℕ) [NeZero N] (t : ℝ) (a b : CuspRowClass N) :
    ‖scatteringMatrix N t a b‖ ≤ 1 := by
  have H : ‖scatteringMatrix N t a b‖^2 ≤ ∑ k, ‖scatteringMatrix N t k b‖^2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg ‖scatteringMatrix N t i b‖) (Finset.mem_univ a)
  rw [column_norm_sq] at H
  nlinarith [norm_nonneg (scatteringMatrix N t a b)]

def wave (ψ : SmoothHeightSeed) (t : ℝ) : ℂ := mellinAngular ψ (1/2) t

theorem wave_L2 (ψ : SmoothHeightSeed) : MemLp (wave ψ) 2 := by
  let C := (2*Real.pi)⁻¹
  let F := (𝓕 (logSchwartz ψ (1/2)) : 𝓢(ℝ,ℂ))
  have HC : C ≠ 0 := inv_ne_zero (by positivity)
  have H := (memLp_two_iff_integrable_sq_norm F.continuous.aestronglyMeasurable).mp (F.memLp 2)
  exact (memLp_two_iff_integrable_sq_norm
    (F.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable).mpr
    ((integrable_comp_mul_left_iff (fun ξ : ℝ => ‖F ξ‖^2) HC).mpr H)

def boundaryColumn (N : ℕ) [NeZero N] (h : SL(2,ℤ)) (ψ : SmoothHeightSeed)
    (a : CuspRowClass N) (t : ℝ) : ℂ :=
  (if a = frameIndex N h then star (wave ψ t) else 0) + scatteringMatrix N t a (frameIndex N h)*star (wave ψ (-t))

private theorem moments (ψ : SmoothHeightSeed) (t : ℝ) :
    moment ψ.toHeightSeed (criticalPoint t) = star (wave ψ t) ∧
    moment ψ.toHeightSeed (1-criticalPoint t) = star (wave ψ (-t)) := by
  have E : 1-star (criticalPoint t) = criticalPoint t := by
    simp [criticalPoint,Complex.star_def] <;> ring
  have J : 1-star (1-criticalPoint t) = criticalPoint (-t) := by
    simp [criticalPoint,Complex.star_def] <;> ring
  simp only [moment_conjugated,E,J,← (critical_parameters t).1,← (critical_parameters (-t)).1,
    heightMellin_angular,wave]

theorem physical_boundary (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ : SmoothHeightSeed) (t : ℝ) :
    let U := quotientProfile ((youngCuspEquiv N).symm (nativeFrameOrbit N g)) t
    Integrable (fun u => star (zeroPoincare N h ψ.toHeightSeed u)*U u) (carrierPushforward N) ∧
    (∫ u,star (zeroPoincare N h ψ.toHeightSeed u)*U u ∂carrierPushforward N) =
      boundaryColumn N h ψ (frameIndex N g) t := by
  classical
  have T := (critical_parameters t).2
  obtain ⟨I,E⟩ := physical_zero_transform N g h ψ.toHeightSeed (criticalPoint t) T.1 T.2.2
  rw [descended_critical] at I E
  refine ⟨I,E.trans ?_⟩
  have he : nativeFrameOrbit N h = nativeFrameOrbit N g ↔ frameIndex N g = frameIndex N h := by
    simp only [frameIndex,(nativeCuspEquiv N).symm.injective.eq_iff,eq_comm]
  rw [he,(moments ψ t).1,(moments ψ t).2,entry_eq_matrix]
  rfl

theorem boundaryColumn_L2 (N : ℕ) [NeZero N] (h : SL(2,ℤ)) (ψ : SmoothHeightSeed)
    (a : CuspRowClass N) : MemLp (boundaryColumn N h ψ a) 2 := by
  let b := frameIndex N h
  have hR : MemLp (fun t : ℝ => star (wave ψ (-t))) 2 :=
    ((wave_L2 ψ).comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))).star
  have hC : Continuous (fun t : ℝ => scatteringMatrix N t a b) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have T := (critical_parameters t).2
    exact ((continuedEntry_regularity N (NeZero.pos N) (classFrame a) (classFrame b)).2 _
      T.1 T.2.2).continuousAt.comp (show Continuous criticalPoint by unfold criticalPoint; fun_prop).continuousAt
  have hS : MemLp (fun t : ℝ => scatteringMatrix N t a b*star (wave ψ (-t))) 2 := by
    apply hR.of_le (hC.aestronglyMeasurable.mul hR.1)
    exact ae_of_all _ (fun t => by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (entry_norm_le N t a b))
  by_cases e : a = b
  · simpa only [boundaryColumn,b,e,if_true,Pi.add_apply] using (wave_L2 ψ).star.add hS
  · simpa only [boundaryColumn,b,e,if_false,zero_add] using hS

theorem gram_critical_eq (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) (t : ℝ) :
    gramIntegrand N g h ψ φ (1/2) t = wave φ t*boundaryColumn N h ψ (frameIndex N g) t := by
  have e : nativeFrameOrbit N h = nativeFrameOrbit N g ↔ frameIndex N g = frameIndex N h := by
    simp only [frameIndex,(nativeCuspEquiv N).symm.injective.eq_iff,eq_comm]
  simp only [gramIntegrand,(critical_parameters t).1,e,(moments ψ t).1,(moments ψ t).2,
    entry_eq_matrix,boundaryColumn,wave]

theorem gram_critical_integrable (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) :
    Integrable (gramIntegrand N g h ψ φ (1/2)) := by
  rw [show gramIntegrand N g h ψ φ (1/2) = (wave φ)*(boundaryColumn N h ψ (frameIndex N g))
    from funext (gram_critical_eq N g h ψ φ)]
  exact (wave_L2 φ).integrable_mul (boundaryColumn_L2 N h ψ _)

end
end ImbalancedChen.Part3.ActualIncompleteCriticalColumns20261110
