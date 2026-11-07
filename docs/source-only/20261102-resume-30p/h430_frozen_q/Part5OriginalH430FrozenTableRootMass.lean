import ImbalancedChen.Part5OriginalH430FrozenRootMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The missing non-clamp H430 root-table term.  Proper root knot fibres are
computed from the literal two affine main branches and half-level tail.
The entire max-two stratum is retained exactly.  No continuity of H430,
mass-closeness premise, numerical table evaluation, or count licence is
assumed.  The descendant moving-admission problem is NOT solved here.
-/

namespace ImbalancedChen.Part5OriginalH430FrozenTableRootMass

noncomputable section
open Set MeasureTheory Filter Topology Classical
open scoped BigOperators
open P2EnhancedLowerPhysicalNode
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenPerturbation Part5OriginalH430PhysicalMassPerturbation
open Part5OriginalH430FrozenRootMass
open Part5UpperTables Part5UpperTables.OriginalU34
open Part5OriginalUpsilon5CausalDictionary (a FloorAtom floorGrid floorBound)

def idealQuery (k : Root) (t : ℝ) : ℝ := (sourceRoot k 0 t).physical.argument
def frozenQuery (n : ℕ) (k : Root) (tau t : ℝ) : ℝ :=
  (frozenRoot n k tau t).physical.argument

theorem idealQuery_measurable (k : Root) : Measurable (idealQuery k) :=
  measurable_const.max ((sourceResidual_measurable k 0).div_const a)

theorem frozenQuery_measurable (n : ℕ) (k : Root) (tau : ℝ) :
    Measurable (frozenQuery n k tau) := by
  have he : frozenQuery n k tau = fun t =>
      max 2 (residual (frozenRoot n k tau t).physical / a) := by
    ext t
    rw [frozenRoot_residual]
    rfl
  rw [he]
  exact measurable_const.max ((frozenResidual_measurable n k tau).div_const a)

/-- For an arbitrary target value c, a proper (non-clamp) root fibre
has at most these three points.  No hypothesis about a table entry occurs. -/
theorem proper_root_fibre {k : Root} {t c : ℝ}
    (hproper : idealQuery k t ≠ 2) (hc : idealQuery k t = c) :
    t = 1 - 2*a*c ∨ t = (57/64-a*c)*2/5 ∨ t = 1/2-a*c := by
  have ha : a ≠ 0 := by norm_num [a]
  have hres : sourceResidual k 0 t = a*c := by
    have hmax : max 2 (sourceResidual k 0 t/a) = c := hc
    have hnot : ¬ sourceResidual k 0 t/a ≤ 2 := by
      intro h
      exact hproper (max_eq_left h)
    rw [max_eq_right (le_of_lt (lt_of_not_ge hnot))] at hmax
    have h := (div_eq_iff ha).mp hmax
    simpa only [mul_comm] using h
  have hmain (h : mainResidual t = a*c) :
      t = 1-2*a*c ∨ t = (57/64-a*c)*2/5 := by
    unfold mainResidual at h
    rw [VariableEnvelope.v_eq_min] at h
    by_cases hAC : VariableEnvelope.A t ≤ VariableEnvelope.C t
    · rw [min_eq_left hAC] at h
      left
      dsimp [VariableEnvelope.A] at h
      linarith
    · rw [min_eq_right (le_of_not_ge hAC)] at h
      right
      dsimp [VariableEnvelope.C] at h
      linarith
  cases k with
  | U3 =>
      by_cases ht : t < tailCutoff
      · have h : mainResidual t = a*c := by
          simpa [sourceResidual, U3Residual, ht] using hres
        exact (hmain h).elim Or.inl (fun h => Or.inr (Or.inl h))
      · right; right
        simp only [sourceResidual, U3Residual, if_neg ht, sub_zero, tailResidual] at hres
        linarith
  | U4 =>
      exact (hmain hres).elim Or.inl (fun h => Or.inr (Or.inl h))

private theorem ae_ne_point (c : ℝ) : ∀ᵐ t : ℝ, t ≠ c := by
  rw [ae_iff]
  simp

/-- Equality at two is deliberately not removed.  Only the finitely
many proper affine knot fibres are null. -/
theorem ae_root_clamp_or_off_knots (k : Root) :
    ∀ᵐ t : ℝ, idealQuery k t = 2 ∨
      ∀ j : Fin 201, idealQuery k t ≠ floorGrid j.val := by
  have hj (j : Fin 201) : ∀ᵐ t : ℝ,
      idealQuery k t = 2 ∨ idealQuery k t ≠ floorGrid j.val := by
    filter_upwards [ae_ne_point (1-2*a*floorGrid j.val),
      ae_ne_point ((57/64-a*floorGrid j.val)*2/5),
      ae_ne_point (1/2-a*floorGrid j.val)] with t hA hC hT
    by_cases htwo : idealQuery k t = 2
    · exact Or.inl htwo
    · right
      intro he
      exact (proper_root_fibre htwo he).elim hA (fun h => h.elim hC hT)
  filter_upwards [Filter.eventually_all.mpr hj] with t ht
  by_cases htwo : idealQuery k t = 2
  · exact Or.inl htwo
  · exact Or.inr (fun j => (ht j).resolve_left htwo)

/-- Lowering the actual total cannot move a root out of its ideal clamp.
This extends the O U3 clamp calculation to the common two-root interface. -/
theorem ideal_clamp_preserved {n : ℕ} {k : Root} {tau t : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (ht : t ∈ rootBand k)
    (hclamp : idealQuery k t = 2) : frozenQuery n k tau t = 2 := by
  have hq : sourceResidual k 0 t/a ≤ 2 := (le_max_right _ _).trans_eq hclamp
  have hl := sourceResidual_tau_loss k (t := t) htau
  have hq' : sourceResidual k tau t/a ≤ 2 :=
    (div_le_div_of_nonneg_right (by linarith [hl.1]) (by norm_num [a])).trans hq
  exact frozenRoot_keeps_clamp htau htauhi ht (max_eq_left hq')

theorem frozenQuery_tendsto {k : Root} {t : ℝ} (ht : t ∈ rootBand k) :
    Tendsto (fun n => frozenQuery n k (finiteTau n) t) atTop (𝓝 (idealQuery k t)) := by
  apply Metric.tendsto_nhds.2
  intro epsilon he
  have hlim : Tendsto (fun n => levelError n (finiteTau n)/a) atTop (𝓝 0) := by
    simpa using levelError_finiteTau_tendsto.div_const a
  filter_upwards [hlim.eventually (eventually_lt_nhds he)] with n hn
  rw [Real.dist_eq, abs_sub_comm]
  exact (root_argument_error (finiteTau_pos n).le (finiteTau_le n) ht).trans_lt hn

private theorem eventually_comparisons {f : ℕ → ℝ} {s c : ℝ}
    (hf : Tendsto f atTop (𝓝 s)) (hne : s ≠ c) :
    ∀ᶠ n in atTop,
      (c ≤ f n ↔ c ≤ s) ∧ (f n ≤ c ↔ s ≤ c) ∧
      (c < f n ↔ c < s) ∧ (f n < c ↔ s < c) ∧ (f n = c ↔ s = c) := by
  rcases lt_or_gt_of_ne hne with h | h
  · filter_upwards [hf.eventually (eventually_lt_nhds h)] with n hn
    simp [hn, h, hn.le, h.le, not_le_of_gt hn, not_le_of_gt h,
      not_lt_of_ge hn.le, not_lt_of_ge h.le, ne_of_lt hn, hne]
  · filter_upwards [hf.eventually (eventually_gt_nhds h)] with n hn
    simp [hn, h, hn.le, h.le, not_le_of_gt hn, not_le_of_gt h,
      not_lt_of_ge hn.le, not_lt_of_ge h.le, ne_of_gt hn, hne]

/-- Literal finite closed lookup, eventually identical off its 201 knots.
Knot values remain the stored adjacent minima; no table is replayed. -/
theorem eventually_upperFloor_eq {f : ℕ → ℝ} {s : ℝ}
    (hf : Tendsto f atTop (𝓝 s)) (hne : ∀ j : Fin 201, s ≠ floorGrid j.val)
    (nums : Fin 200 → ℤ) :
    ∀ᶠ n in atTop, upperFloor nums (f n) = upperFloor nums s := by
  have hj := Filter.eventually_all.mpr
    (fun j : Fin 201 => eventually_comparisons hf (hne j))
  filter_upwards [hj] with n hn
  have hzero := hn ⟨0, by norm_num⟩
  have hlast := hn ⟨200, by norm_num⟩
  norm_num [floorGrid] at hzero hlast
  have hmem (b : FloorAtom) : f n ∈ upperAtomSet b ↔ s ∈ upperAtomSet b := by
    cases b with
    | inl i =>
        have hlo := hn ⟨i.val, by omega⟩
        have hhi := hn ⟨i.val+1, by omega⟩
        simp only [upperAtomSet, mem_inter_iff, mem_Icc, mem_Ioo,
          hzero.1, hlast.2.1, hlo.2.2.1, hhi.2.2.2.1]
    | inr j =>
        simp only [upperAtomSet, mem_inter_iff, mem_Icc, mem_singleton_iff,
          hzero.1, hlast.2.1, (hn j).2.2.2.2]
  unfold upperFloor
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : s ∈ upperAtomSet b
  · rw [indicator_of_mem hb, indicator_of_mem ((hmem b).mpr hb)]
  · rw [indicator_of_notMem hb, indicator_of_notMem (fun h => hb ((hmem b).mp h))]

theorem ae_frozen_H430_tendsto (k : Root) :
    ∀ᵐ t : ℝ ∂volume.restrict (rootBand k),
      Tendsto (fun n => H430 (frozenQuery n k (finiteTau n) t)) atTop
        (𝓝 (H430 (idealQuery k t))) := by
  filter_upwards [ae_restrict_of_ae (ae_root_clamp_or_off_knots k),
    ae_restrict_mem (rootBand_measurable k)] with t hcase ht
  rcases hcase with hc | hk
  · have he (n : ℕ) := ideal_clamp_preserved (finiteTau_pos n).le (finiteTau_le n) ht hc
    simpa only [hc, he] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => H430 2) atTop (𝓝 (H430 2)))
  · apply tendsto_const_nhds.congr'
    exact (eventually_upperFloor_eq (frozenQuery_tendsto ht) hk H430Numerators).symm

def tableDiscrepancy (n : ℕ) (k : Root) (tau : ℝ) : ℝ :=
  ∫ t in rootBand k, |H430 (idealQuery k t)-H430 (frozenQuery n k tau t)|

theorem tableDiscrepancy_tendsto (k : Root) :
    Tendsto (fun n => tableDiscrepancy n k (finiteTau n)) atTop (𝓝 0) := by
  have hi : IntegrableOn (fun _ : ℝ => 2*floorBound H430Numerators) (rootBand k) :=
    integrableOn_const (rootBand_volume_lt_top k).ne
  have hbound (n : ℕ) (t : ℝ) :
      ‖|H430 (idealQuery k t)-H430 (frozenQuery n k (finiteTau n) t)|‖ ≤
        2*floorBound H430Numerators := by
    rw [Real.norm_eq_abs, abs_abs]
    exact (abs_sub _ _).trans (by
      have h1 := norm_H430_le (idealQuery k t)
      have h2 := norm_H430_le (frozenQuery n k (finiteTau n) t)
      rw [Real.norm_eq_abs] at h1 h2
      linarith)
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (rootBand k)) (f := fun _ : ℝ => (0 : ℝ))
    (fun _ : ℝ => 2*floorBound H430Numerators)
    (fun n => (((measurable_H430.comp (idealQuery_measurable k)).sub
      (measurable_H430.comp (frozenQuery_measurable n k (finiteTau n)))).abs).aestronglyMeasurable)
    hi (fun n => Filter.Eventually.of_forall (hbound n))
    ((ae_frozen_H430_tendsto k).mono (fun t ht => by
      simpa using (tendsto_const_nhds.sub ht).abs))
  simpa [tableDiscrepancy] using h

theorem tableDiscrepancy_integrable (n : ℕ) (k : Root) (tau : ℝ) :
    IntegrableOn (fun t => |H430 (idealQuery k t)-H430 (frozenQuery n k tau t)|)
      (rootBand k) := by
  have hi : IntegrableOn (fun _ : ℝ => 2*floorBound H430Numerators) (rootBand k) :=
    integrableOn_const (rootBand_volume_lt_top k).ne
  apply hi.mono' (((measurable_H430.comp (idealQuery_measurable k)).sub
    (measurable_H430.comp (frozenQuery_measurable n k tau))).abs).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs, abs_abs]
    exact (abs_sub _ _).trans (by
      have h1 := norm_H430_le (idealQuery k t)
      have h2 := norm_H430_le (frozenQuery n k tau t)
      rw [Real.norm_eq_abs] at h1 h2
      linarith))

theorem idealTableWeight_integrable (k : Root) :
    IntegrableOn (fun t => H430 (idealQuery k t)*branchWeight (sourceResidual k 0) t)
      (rootBand k) :=
  integrableOn_upperRoot_mul H430Numerators
    ((sourceResidual_measurable k 0).div_const a) (rootBand_measurable k)
    (sourceWeight_integrable k (by norm_num) (by norm_num))

theorem frozenTableWeight_integrable {n : ℕ} (k : Root) {tau : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (hn : meshError n ≤ 11/384) :
    IntegrableOn (fun t => H430 (frozenQuery n k tau t)*frozenRootWeight n k tau t)
      (rootBand k) := by
  have he (t : ℝ) : H430 (frozenQuery n k tau t) =
      upperRoot H430Numerators (residual (frozenRoot n k tau t).physical/a) := by
    rw [frozenRoot_residual]
    rfl
  simp_rw [he]
  exact integrableOn_upperRoot_mul H430Numerators
    ((frozenResidual_measurable n k tau).div_const a) (rootBand_measurable k)
    (frozenRootWeight_integrable k htau htauhi hn)

/-- The explicit absolute error for the ACTUAL H430-weighted root mass. -/
def rootTableAbsoluteError (n : ℕ) (k : Root) (tau : ℝ) : ℝ :=
  ∫ t in rootBand k,
    |H430 (idealQuery k t)*branchWeight (sourceResidual k 0) t -
      H430 (frozenQuery n k tau t)*frozenRootWeight n k tau t|

theorem rootTableAbsoluteError_bound {n : ℕ} (k : Root) {tau : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (hn : meshError n ≤ 11/384) :
    0 ≤ rootTableAbsoluteError n k tau ∧
      rootTableAbsoluteError n k tau ≤
        floorBound H430Numerators*rootAbsoluteError n k tau +
          weightEnvelope*tableDiscrepancy n k tau := by
  have hpoint (t : ℝ) (ht : t ∈ rootBand k) :
      |H430 (idealQuery k t)*branchWeight (sourceResidual k 0) t -
        H430 (frozenQuery n k tau t)*frozenRootWeight n k tau t| ≤
      floorBound H430Numerators*|branchWeight (sourceResidual k 0) t-frozenRootWeight n k tau t| +
        weightEnvelope*|H430 (idealQuery k t)-H430 (frozenQuery n k tau t)| := by
    have hw : |frozenRootWeight n k tau t| ≤ weightEnvelope := by
      rw [frozenRootWeight_eq]
      simpa only [mul_comm] using weight_bound
        (frozenRoot_residual_bounds htau htauhi ht hn).1 (rootBand_subset k ht).1
    have hH : |H430 (idealQuery k t)| ≤ floorBound H430Numerators := by
      simpa only [Real.norm_eq_abs] using norm_H430_le (idealQuery k t)
    have heq : H430 (idealQuery k t)*branchWeight (sourceResidual k 0) t -
        H430 (frozenQuery n k tau t)*frozenRootWeight n k tau t =
      H430 (idealQuery k t)*(branchWeight (sourceResidual k 0) t-frozenRootWeight n k tau t) +
      (H430 (idealQuery k t)-H430 (frozenQuery n k tau t))*frozenRootWeight n k tau t := by ring
    rw [heq]
    calc
      _ ≤ |H430 (idealQuery k t)|*|branchWeight (sourceResidual k 0) t-frozenRootWeight n k tau t| +
          |H430 (idealQuery k t)-H430 (frozenQuery n k tau t)|*|frozenRootWeight n k tau t| := by
        simpa only [abs_mul] using abs_add
          (H430 (idealQuery k t)*(branchWeight (sourceResidual k 0) t-frozenRootWeight n k tau t))
          ((H430 (idealQuery k t)-H430 (frozenQuery n k tau t))*frozenRootWeight n k tau t)
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hH (abs_nonneg _))
        (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hw
          (abs_nonneg (H430 (idealQuery k t)-H430 (frozenQuery n k tau t))))
  have hraw := (sourceWeight_integrable k (by norm_num) (by norm_num)).sub
    (frozenRootWeight_integrable k htau htauhi hn)
  have htable := (idealTableWeight_integrable k).sub
    (frozenTableWeight_integrable k htau htauhi hn)
  have hrawAbs : IntegrableOn
      (fun t => |branchWeight (sourceResidual k 0) t-frozenRootWeight n k tau t|) (rootBand k) := by
    simpa only [Real.norm_eq_abs] using hraw.norm
  have htableAbs : IntegrableOn
      (fun t => |H430 (idealQuery k t)*branchWeight (sourceResidual k 0) t -
        H430 (frozenQuery n k tau t)*frozenRootWeight n k tau t|) (rootBand k) := by
    simpa only [Real.norm_eq_abs] using htable.norm
  have hright := (hrawAbs.const_mul (floorBound H430Numerators)).add
    ((tableDiscrepancy_integrable n k tau).const_mul weightEnvelope)
  refine ⟨integral_nonneg (fun _ => abs_nonneg _), ?_⟩
  have hb := integral_mono_ae htableAbs hright
    ((ae_restrict_mem (rootBand_measurable k)).mono (fun t ht => hpoint t ht))
  rw [integral_add (hrawAbs.const_mul _) ((tableDiscrepancy_integrable n k tau).const_mul _),
    integral_const_mul, integral_const_mul] at hb
  exact hb

theorem rootTableAbsoluteError_tendsto (k : Root) :
    Tendsto (fun n => rootTableAbsoluteError n k (finiteTau n)) atTop (𝓝 0) := by
  have hn : ∀ᶠ n : ℕ in atTop, meshError n ≤ 11/384 :=
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 11/384))).mono (fun _ h => h.le)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _)))
    (hn.mono (fun n hn => (rootTableAbsoluteError_bound k (finiteTau_pos n).le (finiteTau_le n) hn).2))
  simpa using ((actual_root_absolute_error_tendsto k).const_mul (floorBound H430Numerators)).add
    ((tableDiscrepancy_tendsto k).const_mul weightEnvelope)

theorem actual_root_table_mass_difference {n : ℕ} (k : Root) {tau : ℝ}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12) (hn : meshError n ≤ 11/384) :
    |(∫ t in rootBand k, H430 (idealQuery k t)*branchWeight (sourceResidual k 0) t) -
      (∫ t in rootBand k, H430 (frozenQuery n k tau t)*frozenRootWeight n k tau t)| ≤
        rootTableAbsoluteError n k tau := by
  rw [← integral_sub (idealTableWeight_integrable k) (frozenTableWeight_integrable k htau htauhi hn)]
  simpa only [Real.norm_eq_abs, rootTableAbsoluteError] using
    norm_integral_le_integral_norm
      (μ := volume.restrict (rootBand k))
      (fun t => H430 (idealQuery k t)*branchWeight (sourceResidual k 0) t -
        H430 (frozenQuery n k tau t)*frozenRootWeight n k tau t)

/-- One finite positive tau and one common precision for BOTH original
root table masses, chosen before arithmetic N.  This is not a choice for
every descendant admission domain or all 441 graph generations. -/
theorem exists_common_root_table_precision {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ n : ℕ, 0 < finiteTau n ∧ finiteTau n ≤ 1/12 ∧ meshError n ≤ 11/384 ∧
      ∀ k : Root, rootTableAbsoluteError n k (finiteTau n) < epsilon := by
  have hmass := Filter.eventually_all.mpr (fun k : Root =>
    (rootTableAbsoluteError_tendsto k).eventually (eventually_lt_nhds he))
  have hn : ∀ᶠ n : ℕ in atTop, meshError n ≤ 11/384 :=
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 11/384))).mono (fun _ h => h.le)
  obtain ⟨n, hn, hm⟩ := (hn.and hmass).exists
  exact ⟨n, finiteTau_pos n, finiteTau_le n, hn, hm⟩

end
end ImbalancedChen.Part5OriginalH430FrozenTableRootMass
