import ImbalancedChen.Part5OriginalH430PhysicalMassPerturbation
import ImbalancedChen.Part5OriginalH430CellMeasurability

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual composition with the O smooth-causal-box peer's implemented
measurability theorem. The root primitive mass estimates below are
unweighted by a discontinuous table. Table crossing and moving descendant
admission errors remain separate obligations.
-/

namespace ImbalancedChen.Part5OriginalH430FrozenRootMass

noncomputable section
open Set MeasureTheory Filter Topology
open P2EnhancedLowerPhysicalNode
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenPerturbation Part5OriginalH430PhysicalMassPerturbation
open Part5OriginalH430CellMeasurability
open Part5UpperTables Part5UpperTables.OriginalU34
open Part5OriginalUpsilon5CausalDictionary (a floorValue)

theorem sourceResidual_measurable (k : Root) (tau : ℝ) : Measurable (sourceResidual k tau) := by
  cases k with
  | U3 =>
      exact Measurable.ite measurableSet_Iio continuous_mainResidual.measurable
        (continuous_tailResidual.measurable.sub measurable_const)
  | U4 => exact continuous_mainResidual.measurable

theorem frozenResidual_measurable (n : ℕ) (k : Root) (tau : ℝ) :
    Measurable (fun t => residual (frozenRoot n k tau t).physical) := by
  simp only [frozenRoot_residual]
  exact ((measurable_frozenLevel n).comp
    (measurable_id.add (sourceResidual_measurable k tau))).sub measurable_id

theorem frozenRootWeight_measurable (n : ℕ) (k : Root) (tau : ℝ) :
    Measurable (frozenRootWeight n k tau) := by
  have he : frozenRootWeight n k tau =
      fun t => 4/(t*residual (frozenRoot n k tau t).physical) :=
    funext (frozenRootWeight_eq n k tau)
  rw [he]
  exact measurable_const.div (measurable_id.mul (frozenResidual_measurable n k tau))

theorem sourceWeight_measurable (k : Root) (tau : ℝ) :
    Measurable (branchWeight (sourceResidual k tau)) :=
  measurable_const.div ((sourceResidual_measurable k tau).mul measurable_id)

theorem rootBand_measurable (k : Root) : MeasurableSet (rootBand k) := by
  cases k <;> exact measurableSet_Icc

def weightEnvelope : ℝ := 4 / ((11/384 : ℝ)*a)

theorem weight_bound {R t : ℝ} (hR : (11/384 : ℝ) ≤ R) (ht : a ≤ t) :
    |4/(R*t)| ≤ weightEnvelope := by
  have hR0 : 0 < R := (by norm_num : (0 : ℝ) < 11/384).trans_le hR
  have ht0 : 0 < t := (by norm_num [a] : (0 : ℝ) < a).trans_le ht
  rw [abs_of_pos (div_pos (by norm_num) (mul_pos hR0 ht0))]
  apply div_le_div_of_nonneg_left (by norm_num)
    (mul_pos (by norm_num) (by norm_num [a]))
  exact mul_le_mul hR ht (by norm_num [a]) hR0.le

theorem sourceWeight_integrable (k : Root) {tau : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) :
    IntegrableOn (branchWeight (sourceResidual k tau)) (rootBand k) := by
  have hi : IntegrableOn (fun _ : ℝ => weightEnvelope) (rootBand k) :=
    integrableOn_const (rootBand_volume_lt_top k).ne
  apply hi.mono' (sourceWeight_measurable k tau).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (rootBand_measurable k)] with t ht
  simpa only [Real.norm_eq_abs, branchWeight] using weight_bound
    (le_trans (by norm_num) (sourceResidual_bounds htau htauhi ht).1)
    (rootBand_subset k ht).1

theorem frozenRootWeight_integrable {n : ℕ} (k : Root) {tau : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (hn : meshError n ≤ 11/384) :
    IntegrableOn (frozenRootWeight n k tau) (rootBand k) := by
  have hi : IntegrableOn (fun _ : ℝ => weightEnvelope) (rootBand k) :=
    integrableOn_const (rootBand_volume_lt_top k).ne
  apply hi.mono' (frozenRootWeight_measurable n k tau).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (rootBand_measurable k)] with t ht
  have hb := weight_bound (frozenRoot_residual_bounds htau htauhi ht hn).1
    (rootBand_subset k ht).1
  rw [frozenRootWeight_eq]
  simpa only [Real.norm_eq_abs, mul_comm] using hb

/-- Both masses are bona fide integrable physical root weights. -/
theorem actual_root_mass_difference {n : ℕ} (k : Root) {tau : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (hn : meshError n ≤ 11/384) :
    |(∫ t in rootBand k, branchWeight (sourceResidual k 0) t) -
        (∫ t in rootBand k, frozenRootWeight n k tau t)| ≤
      rootWeightConstant*levelError n tau := by
  rw [← integral_sub (sourceWeight_integrable k (by norm_num) (by norm_num))
    (frozenRootWeight_integrable k htau htauhi hn)]
  have hi := norm_integral_le_integral_norm
    (μ := volume.restrict (rootBand k))
    (fun t => branchWeight (sourceResidual k 0) t-frozenRootWeight n k tau t)
  have h := (rootAbsoluteError_bound k htau htauhi hn).2
  exact (by simpa only [Real.norm_eq_abs] using hi).trans h

/-- Positive finite half-level reserve, tending to zero with the same
root precision. No convergence premise is introduced. -/
def finiteTau (n : ℕ) : ℝ := min (1/12) (meshError n)

theorem finiteTau_pos (n : ℕ) : 0 < finiteTau n := lt_min (by norm_num) (meshError_pos n)
theorem finiteTau_le (n : ℕ) : finiteTau n ≤ 1/12 := min_le_left _ _

theorem levelError_finiteTau_tendsto :
    Tendsto (fun n => levelError n (finiteTau n)) atTop (𝓝 0) := by
  have hm : Tendsto meshError atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto finiteTau atTop (𝓝 0) := by
    simpa [finiteTau] using (tendsto_const_nhds (x := (1/12 : ℝ))).min hm
  simpa [levelError] using ht.add hm

theorem actual_root_absolute_error_tendsto (k : Root) :
    Tendsto (fun n => rootAbsoluteError n k (finiteTau n)) atTop (𝓝 0) := by
  have hn : ∀ᶠ n : ℕ in atTop, meshError n ≤ 11/384 :=
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 11/384))).mono (fun _ h => h.le)
  apply squeeze_zero'
    (hn.mono (fun n hn => (rootAbsoluteError_bound k (finiteTau_pos n).le (finiteTau_le n) hn).1))
    (hn.mono (fun n hn => (rootAbsoluteError_bound k (finiteTau_pos n).le (finiteTau_le n) hn).2))
  simpa using tendsto_const_nhds.mul levelError_finiteTau_tendsto

theorem actual_root_mass_error_tendsto (k : Root) :
    Tendsto (fun n => |(∫ t in rootBand k, branchWeight (sourceResidual k 0) t) -
      (∫ t in rootBand k, frozenRootWeight n k (finiteTau n) t)|) atTop (𝓝 0) := by
  have hn : ∀ᶠ n : ℕ in atTop, meshError n ≤ 11/384 :=
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 11/384))).mono (fun _ h => h.le)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
    (hn.mono (fun n hn => actual_root_mass_difference k (finiteTau_pos n).le (finiteTau_le n) hn))
  simpa using tendsto_const_nhds.mul levelError_finiteTau_tendsto

def clampValue : ℝ := min (floorValue H430Numerators 49) (floorValue H430Numerators 50)

/-- Retain the actual table-weighted positive-measure clamp. This is not
a punctured tube and no assertion that its volume vanishes is made. -/
def clampTableAbsoluteError (n : ℕ) (tau : ℝ) : ℝ :=
  ∫ t in Icc clampStart (1/3 : ℝ),
    |H430 ((sourceRoot .U3 0 t).physical.argument)*branchWeight (sourceResidual .U3 0) t -
      H430 ((frozenRoot n .U3 tau t).physical.argument)*frozenRootWeight n .U3 tau t|

theorem clampTableAbsoluteError_bound {n : ℕ} {tau : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (hn : meshError n ≤ 11/384) :
    0 ≤ clampTableAbsoluteError n tau ∧
      clampTableAbsoluteError n tau ≤ |clampValue|*rootWeightConstant*levelError n tau := by
  have h0 : 0 ≤ clampTableAbsoluteError n tau := integral_nonneg (fun _ => abs_nonneg _)
  have hC : 0 ≤ |clampValue|*rootWeightConstant*levelError n tau :=
    mul_nonneg (mul_nonneg (abs_nonneg _) rootWeightConstant_pos.le)
      (add_nonneg htau (meshError_pos n).le)
  have hm : volume (Icc clampStart (1/3 : ℝ)) < ⊤ := by simp [Real.volume_Icc]
  have hv : volume.real (Icc clampStart (1/3 : ℝ)) ≤ 1 := by
    norm_num [Real.volume_real_Icc, clampStart]
  have hpoint (t : ℝ) (ht : t ∈ Icc clampStart (1/3 : ℝ)) :
      |H430 ((sourceRoot .U3 0 t).physical.argument)*branchWeight (sourceResidual .U3 0) t -
        H430 ((frozenRoot n .U3 tau t).physical.argument)*frozenRootWeight n .U3 tau t| ≤
        |clampValue|*rootWeightConstant*levelError n tau := by
    have hroot : t ∈ rootBand .U3 :=
      ⟨(by norm_num [a, clampStart] : a ≤ clampStart).trans ht.1, ht.2⟩
    rw [(actual_U3_clamp ht.1).2, (finite_frozen_U3_clamp htau htauhi hroot ht.1).2]
    change |clampValue*branchWeight (sourceResidual .U3 0) t -
      clampValue*frozenRootWeight n .U3 tau t| ≤ _
    rw [← mul_sub, abs_mul]
    have h := mul_le_mul_of_nonneg_left (rootWeight_error htau htauhi hroot hn)
      (abs_nonneg clampValue)
    simpa only [mul_assoc] using h
  have hi := norm_setIntegral_le_of_norm_le_const hm
    (f := fun t => |H430 ((sourceRoot .U3 0 t).physical.argument)*
      branchWeight (sourceResidual .U3 0) t -
      H430 ((frozenRoot n .U3 tau t).physical.argument)*frozenRootWeight n .U3 tau t|)
    (C := |clampValue|*rootWeightConstant*levelError n tau)
    (fun t ht => by simpa only [Real.norm_eq_abs, abs_abs] using hpoint t ht)
  rw [Real.norm_eq_abs, abs_of_nonneg h0] at hi
  exact ⟨h0, hi.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv hC)⟩

theorem actual_clamp_table_error_tendsto :
    Tendsto (fun n => clampTableAbsoluteError n (finiteTau n)) atTop (𝓝 0) := by
  have hn : ∀ᶠ n : ℕ in atTop, meshError n ≤ 11/384 :=
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 11/384))).mono (fun _ h => h.le)
  apply squeeze_zero'
    (hn.mono (fun n hn => (clampTableAbsoluteError_bound (finiteTau_pos n).le (finiteTau_le n) hn).1))
    (hn.mono (fun n hn => (clampTableAbsoluteError_bound (finiteTau_pos n).le (finiteTau_le n) hn).2))
  simpa using tendsto_const_nhds.mul levelError_finiteTau_tendsto

end
end ImbalancedChen.Part5OriginalH430FrozenRootMass
