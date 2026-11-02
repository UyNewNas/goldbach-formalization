import ImbalancedChen.Part5OriginalH430FrozenTableRootMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Full U3/U4 root coefficient, including the continuous canonical upper
amplitude.  The P table theorem is reused, including its positive-measure
clamp branch.  The physical residual and complete root weight are kept;
there is no replacement of physical lambda by an analytic cover level.

The conclusions concern the two original continuous root integrals.
Arithmetic Theta and the entire descendant Member family remain separate.
-/

namespace ImbalancedChen.Part5OriginalH430FullRootAmplitude

noncomputable section
open Set MeasureTheory Filter Topology Classical
open P2EnhancedLowerPhysicalNode
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenPerturbation Part5OriginalH430PhysicalMassPerturbation
open Part5OriginalH430FrozenRootMass Part5OriginalH430FrozenTableRootMass
open Part5UpperTables Part5UpperTables.OriginalU34
open Part5OriginalUpsilon5CausalDictionary (a floorBound)

/-- A globally continuous extension used only to prove measurability.
Every actual root query below is proved to lie in its unchanged [2,6] part. -/
def clippedAmplitude (s : ℝ) : ℝ := upperAmplitude (max 2 (min 6 s))

theorem clip_mem (s : ℝ) : max 2 (min 6 s) ∈ Icc (2 : ℝ) 6 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem clippedAmplitude_eq {s : ℝ} (hs : s ∈ Icc (2 : ℝ) 6) :
    clippedAmplitude s = upperAmplitude s := by
  simp only [clippedAmplitude, min_eq_right hs.2, max_eq_right hs.1]

theorem continuous_clippedAmplitude : Continuous clippedAmplitude := by
  have hc : Continuous (fun s : ℝ => max 2 (min 6 s)) :=
    continuous_const.max (continuous_const.min continuous_id)
  have hh : ContinuousOn clippedAmplitude univ :=
    continuousOn_upperAmplitude.comp hc.continuousOn (fun s _ => clip_mem s)
  simpa only [continuousOn_univ] using hh

theorem exists_amplitude_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Icc (2 : ℝ) 6, |upperAmplitude s| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image continuousOn_upperAmplitude.norm
  refine ⟨max B 0, le_max_right _ _, fun s hs => ?_⟩
  simpa only [Real.norm_eq_abs] using
    (hB (mem_image_of_mem _ hs)).trans (le_max_left B 0)

theorem idealQuery_mem {k : Root} {t : ℝ} (ht : t ∈ rootBand k) :
    idealQuery k t ∈ Icc (2 : ℝ) 6 :=
  ⟨le_max_left _ _, (sourceRoot_argument (by norm_num) (by norm_num) ht).2⟩

/-- The upper query bound holds even before the positive-residual mesh
threshold: downward freezing cannot increase the clamped argument. -/
theorem frozenQuery_mem {n : ℕ} {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (ht : t ∈ rootBand k) :
    frozenQuery n k tau t ∈ Icc (2 : ℝ) 6 := by
  have hl := (frozenLevel_bounds (root_total_bounds htau htauhi ht) n).1
  have hr := (sourceResidual_bounds htau htauhi ht).2
  change frozenLevel n (t + sourceResidual k tau t) ≤ t + sourceResidual k tau t at hl
  change 2 ≤ max 2 ((frozenLevel n (t + sourceResidual k tau t)-t)/a) ∧ _
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  apply (div_le_iff₀ (by norm_num [a] : 0 < a)).mpr
  dsimp [a]
  linarith

private theorem amplitude_comp_aestronglyMeasurable {k : Root} {q : ℝ → ℝ}
    (hq : Measurable q) (hr : ∀ t ∈ rootBand k, q t ∈ Icc (2 : ℝ) 6) :
    AEStronglyMeasurable (fun t => upperAmplitude (q t)) (volume.restrict (rootBand k)) := by
  have hm : AEStronglyMeasurable (fun t => clippedAmplitude (q t))
      (volume.restrict (rootBand k)) :=
    (continuous_clippedAmplitude.measurable.comp hq).aestronglyMeasurable
  apply hm.congr
  filter_upwards [ae_restrict_mem (rootBand_measurable k)] with t ht
  exact clippedAmplitude_eq (hr t ht)

theorem frozenAmplitude_tendsto {k : Root} {t : ℝ} (ht : t ∈ rootBand k) :
    Tendsto (fun n => upperAmplitude (frozenQuery n k (finiteTau n) t)) atTop
      (𝓝 (upperAmplitude (idealQuery k t))) := by
  have hh := continuous_clippedAmplitude.continuousAt.tendsto.comp (frozenQuery_tendsto ht)
  have he : (fun n => clippedAmplitude (frozenQuery n k (finiteTau n) t)) =
      (fun n => upperAmplitude (frozenQuery n k (finiteTau n) t)) := by
    funext n
    exact clippedAmplitude_eq (frozenQuery_mem (finiteTau_pos n).le (finiteTau_le n) ht)
  rw [he, clippedAmplitude_eq (idealQuery_mem ht)] at hh
  exact hh

theorem eventually_fine_mesh : ∀ᶠ n : ℕ in atTop, meshError n ≤ 11/384 :=
  ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 11/384))).mono (fun _ h => h.le)

/-- Pointwise physical root weight convergence is derived from the old
explicit residual-loss bound, with no assumed weight approximation. -/
theorem frozenRootWeight_tendsto {k : Root} {t : ℝ} (ht : t ∈ rootBand k) :
    Tendsto (fun n => frozenRootWeight n k (finiteTau n) t) atTop
      (𝓝 (branchWeight (sourceResidual k 0) t)) := by
  apply Metric.tendsto_nhds.2
  intro epsilon he
  have hl : Tendsto (fun n => rootWeightConstant * levelError n (finiteTau n))
      atTop (𝓝 0) := by
    simpa using levelError_finiteTau_tendsto.const_mul rootWeightConstant
  filter_upwards [eventually_fine_mesh, hl.eventually (eventually_lt_nhds he)] with n hn hb
  rw [Real.dist_eq, abs_sub_comm]
  exact (rootWeight_error (finiteTau_pos n).le (finiteTau_le n) ht hn).trans_lt hb

def idealFullCoefficient (k : Root) (t : ℝ) : ℝ :=
  (upperAmplitude (idealQuery k t)-H430 (idealQuery k t)) *
    branchWeight (sourceResidual k 0) t

def frozenFullCoefficient (n : ℕ) (k : Root) (tau t : ℝ) : ℝ :=
  (upperAmplitude (frozenQuery n k tau t)-H430 (frozenQuery n k tau t)) *
    frozenRootWeight n k tau t

theorem idealFullCoefficient_eq_branch (k : Root) (t : ℝ) :
    idealFullCoefficient k t = branchCoefficient H430Numerators (sourceResidual k 0) t := rfl

theorem idealFullCoefficient_U3 (t : ℝ) : idealFullCoefficient .U3 t = U3H430Coefficient t := by
  rw [idealFullCoefficient_eq_branch]
  by_cases ht : t < tailCutoff
  · simp [sourceResidual, U3Residual, U3H430Coefficient, branchCoefficient,
      rootArgument, branchWeight, ht, not_le.mpr ht]
  · simp [sourceResidual, U3Residual, U3H430Coefficient, branchCoefficient,
      rootArgument, branchWeight, ht, le_of_not_gt ht]

theorem idealFullCoefficient_U4 (t : ℝ) : idealFullCoefficient .U4 t = U4H430Coefficient t := rfl

theorem original_U3_integral :
    (∫ t in rootBand .U3, idealFullCoefficient .U3 t) =
      ∫ t in Ico a (1/3 : ℝ), U3H430Coefficient t := by
  simp_rw [idealFullCoefficient_U3]
  exact integral_Icc_eq_integral_Ico

theorem original_U4_integral :
    (∫ t in rootBand .U4, idealFullCoefficient .U4 t) =
      ∫ t in Ico a (59/250 : ℝ), U4H430Coefficient t := by
  simp_rw [idealFullCoefficient_U4]
  exact integral_Icc_eq_integral_Ico

theorem idealFullCoefficient_aestronglyMeasurable (k : Root) :
    AEStronglyMeasurable (idealFullCoefficient k) (volume.restrict (rootBand k)) :=
  ((amplitude_comp_aestronglyMeasurable (idealQuery_measurable k) (fun _ => idealQuery_mem)).sub
    (measurable_H430.comp (idealQuery_measurable k)).aestronglyMeasurable).mul
      (sourceWeight_measurable k 0).aestronglyMeasurable

theorem frozenFullCoefficient_aestronglyMeasurable {n : ℕ} (k : Root) {tau : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) :
    AEStronglyMeasurable (frozenFullCoefficient n k tau) (volume.restrict (rootBand k)) :=
  ((amplitude_comp_aestronglyMeasurable (frozenQuery_measurable n k tau)
      (fun _ => frozenQuery_mem htau htauhi)).sub
    (measurable_H430.comp (frozenQuery_measurable n k tau)).aestronglyMeasurable).mul
      (frozenRootWeight_measurable n k tau).aestronglyMeasurable

private theorem full_pointwise_bound {q W B : ℝ}
    (hA : |upperAmplitude q| ≤ B) (hW : |W| ≤ weightEnvelope) :
    |(upperAmplitude q-H430 q)*W| ≤ (B+floorBound H430Numerators)*weightEnvelope := by
  have hH : |H430 q| ≤ floorBound H430Numerators := by
    simpa only [Real.norm_eq_abs] using norm_H430_le q
  rw [abs_mul]
  exact mul_le_mul ((abs_sub _ _).trans (add_le_add hA hH)) hW (abs_nonneg _)
    ((abs_nonneg (upperAmplitude q-H430 q)).trans
      ((abs_sub _ _).trans (add_le_add hA hH)))

theorem idealFullCoefficient_bound {k : Root} {t B : ℝ}
    (hB : ∀ s ∈ Icc (2 : ℝ) 6, |upperAmplitude s| ≤ B) (ht : t ∈ rootBand k) :
    |idealFullCoefficient k t| ≤ (B+floorBound H430Numerators)*weightEnvelope := by
  apply full_pointwise_bound (hB _ (idealQuery_mem ht))
  exact weight_bound ((by norm_num : (11/384 : ℝ) ≤ 11/192).trans
    (sourceResidual_bounds (by norm_num) (by norm_num) ht).1) (rootBand_subset k ht).1

theorem frozenFullCoefficient_bound {n : ℕ} {k : Root} {tau t B : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (hn : meshError n ≤ 11/384)
    (hB : ∀ s ∈ Icc (2 : ℝ) 6, |upperAmplitude s| ≤ B) (ht : t ∈ rootBand k) :
    |frozenFullCoefficient n k tau t| ≤ (B+floorBound H430Numerators)*weightEnvelope := by
  apply full_pointwise_bound (hB _ (frozenQuery_mem htau htauhi ht))
  rw [frozenRootWeight_eq]
  simpa only [mul_comm] using weight_bound
    (frozenRoot_residual_bounds htau htauhi ht hn).1 (rootBand_subset k ht).1

theorem idealFullCoefficient_integrable (k : Root) :
    IntegrableOn (idealFullCoefficient k) (rootBand k) := by
  obtain ⟨B, _, hB⟩ := exists_amplitude_bound
  have hi : IntegrableOn (fun _ : ℝ => (B+floorBound H430Numerators)*weightEnvelope)
      (rootBand k) := integrableOn_const (rootBand_volume_lt_top k).ne
  apply hi.mono' (idealFullCoefficient_aestronglyMeasurable k)
  filter_upwards [ae_restrict_mem (rootBand_measurable k)] with t ht
  simpa only [Real.norm_eq_abs] using idealFullCoefficient_bound hB ht

theorem frozenFullCoefficient_integrable {n : ℕ} (k : Root) {tau : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (hn : meshError n ≤ 11/384) :
    IntegrableOn (frozenFullCoefficient n k tau) (rootBand k) := by
  obtain ⟨B, _, hB⟩ := exists_amplitude_bound
  have hi : IntegrableOn (fun _ : ℝ => (B+floorBound H430Numerators)*weightEnvelope)
      (rootBand k) := integrableOn_const (rootBand_volume_lt_top k).ne
  apply hi.mono' (frozenFullCoefficient_aestronglyMeasurable k htau htauhi)
  filter_upwards [ae_restrict_mem (rootBand_measurable k)] with t ht
  simpa only [Real.norm_eq_abs] using frozenFullCoefficient_bound htau htauhi hn hB ht

/-- P's genuine H430 convergence includes the entire preserved clamp.
Only its proper non-clamp knot fibres were removed there. -/
theorem ae_frozenFullCoefficient_tendsto (k : Root) :
    ∀ᵐ t : ℝ ∂volume.restrict (rootBand k),
      Tendsto (fun n => frozenFullCoefficient n k (finiteTau n) t) atTop
        (𝓝 (idealFullCoefficient k t)) := by
  filter_upwards [ae_frozen_H430_tendsto k, ae_restrict_mem (rootBand_measurable k)] with t hH ht
  exact ((frozenAmplitude_tendsto ht).sub hH).mul (frozenRootWeight_tendsto ht)

def rootFullAbsoluteError (n : ℕ) (k : Root) (tau : ℝ) : ℝ :=
  ∫ t in rootBand k, |idealFullCoefficient k t-frozenFullCoefficient n k tau t|

/-- Actual full weighted absolute error, including continuous amplitude.
The auxiliary zero at coarse mesh indices is eventually absent and is
used only to obtain a uniform dominating function for all indices. -/
theorem rootFullAbsoluteError_tendsto (k : Root) :
    Tendsto (fun n => rootFullAbsoluteError n k (finiteTau n)) atTop (𝓝 0) := by
  obtain ⟨B, hB0, hB⟩ := exists_amplitude_bound
  let C := (B+floorBound H430Numerators)*weightEnvelope
  have hF : 0 ≤ floorBound H430Numerators := (norm_nonneg (H430 2)).trans (norm_H430_le 2)
  have hW : 0 ≤ weightEnvelope := by norm_num [weightEnvelope, a]
  have hC : 0 ≤ C := mul_nonneg (add_nonneg hB0 hF) hW
  let f : ℕ → ℝ → ℝ := fun n t => if meshError n ≤ 11/384 then
    |idealFullCoefficient k t-frozenFullCoefficient n k (finiteTau n) t| else 0
  have hf (n : ℕ) : AEStronglyMeasurable (f n) (volume.restrict (rootBand k)) := by
    by_cases hn : meshError n ≤ 11/384
    · simpa only [f, if_pos hn] using
        ((idealFullCoefficient_aestronglyMeasurable k).sub
          (frozenFullCoefficient_aestronglyMeasurable k (finiteTau_pos n).le (finiteTau_le n))).abs
    · simp only [f, if_neg hn]
      exact aestronglyMeasurable_const
  have hb (n : ℕ) : ∀ᵐ t : ℝ ∂volume.restrict (rootBand k), ‖f n t‖ ≤ 2*C := by
    filter_upwards [ae_restrict_mem (rootBand_measurable k)] with t ht
    by_cases hn : meshError n ≤ 11/384
    · simp only [f, if_pos hn, Real.norm_eq_abs, abs_abs]
      exact (abs_sub _ _).trans (by
        have hi := idealFullCoefficient_bound hB ht
        have hf := frozenFullCoefficient_bound (finiteTau_pos n).le (finiteTau_le n) hn hB ht
        change |idealFullCoefficient k t| + |frozenFullCoefficient n k (finiteTau n) t| ≤ 2*C
        change |idealFullCoefficient k t| ≤ C at hi
        change |frozenFullCoefficient n k (finiteTau n) t| ≤ C at hf
        linarith)
    · simp only [f, if_neg hn, norm_zero]
      exact mul_nonneg (by norm_num) hC
  have hlim : ∀ᵐ t : ℝ ∂volume.restrict (rootBand k),
      Tendsto (fun n => f n t) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_frozenFullCoefficient_tendsto k] with t ht
    have hh : Tendsto (fun n => |idealFullCoefficient k t-frozenFullCoefficient n k (finiteTau n) t|)
        atTop (𝓝 (0 : ℝ)) := by simpa using (tendsto_const_nhds.sub ht).abs
    apply hh.congr'
    exact eventually_fine_mesh.mono (fun n hn => by simp [f, hn])
  have hi : IntegrableOn (fun _ : ℝ => 2*C) (rootBand k) :=
    integrableOn_const (rootBand_volume_lt_top k).ne
  have hd := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (rootBand k)) (f := fun _ : ℝ => (0 : ℝ))
    (fun _ : ℝ => 2*C) hf hi hb hlim
  have hd' : Tendsto (fun n => ∫ t in rootBand k, f n t) atTop (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero] using hd
  apply hd'.congr'
  exact eventually_fine_mesh.mono (fun n hn => by simp only [rootFullAbsoluteError, f, if_pos hn])

theorem actual_root_full_mass_difference {n : ℕ} (k : Root) {tau : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (hn : meshError n ≤ 11/384) :
    |(∫ t in rootBand k, idealFullCoefficient k t) -
      (∫ t in rootBand k, frozenFullCoefficient n k tau t)| ≤ rootFullAbsoluteError n k tau := by
  rw [← integral_sub (idealFullCoefficient_integrable k)
    (frozenFullCoefficient_integrable k htau htauhi hn)]
  exact abs_integral_le_integral_abs

/-- The non-null root clamp is represented exactly for every finite mesh.
Its amplitude is constant; the surviving error is solely the real weight error. -/
theorem full_clamp_error {n : ℕ} {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (ht : t ∈ rootBand k)
    (hc : idealQuery k t = 2) :
    |idealFullCoefficient k t-frozenFullCoefficient n k tau t| =
      |upperAmplitude 2-H430 2| *
        |branchWeight (sourceResidual k 0) t-frozenRootWeight n k tau t| := by
  have hf := ideal_clamp_preserved htau htauhi ht hc
  simp only [idealFullCoefficient, frozenFullCoefficient, hc, hf, ← mul_sub, abs_mul]

/-- One common finite mesh and positive tau for BOTH complete U3/U4 roots,
chosen before N.  This does not quantify over 441 descendant generations. -/
theorem exists_common_full_root_precision {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ n : ℕ, 0 < finiteTau n ∧ finiteTau n ≤ 1/12 ∧ meshError n ≤ 11/384 ∧
      ∀ k : Root, rootFullAbsoluteError n k (finiteTau n) < epsilon := by
  have hh := Filter.eventually_all.mpr (fun k : Root =>
    (rootFullAbsoluteError_tendsto k).eventually (eventually_lt_nhds he))
  obtain ⟨n, hn, hroots⟩ := (eventually_fine_mesh.and hh).exists
  exact ⟨n, finiteTau_pos n, finiteTau_le n, hn, hroots⟩

end
end ImbalancedChen.Part5OriginalH430FullRootAmplitude
