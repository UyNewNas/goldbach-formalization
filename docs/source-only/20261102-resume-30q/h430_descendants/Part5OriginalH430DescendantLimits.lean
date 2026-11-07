import ImbalancedChen.Part5OriginalH430FrozenTableRootMass
import ImbalancedChen.Part5OriginalH430NativeQueryPaths

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Limits at the SAME physical Program and appended coordinates.  Only the
ideal path is assumed admitted.  In particular frozen Member, equality of
admission indicators, and a physical-mass convergence estimate are NOT
premises.  The limit preserves the full marked word and the true alpha.
These pointwise limits do not themselves prove moving-domain L1 convergence.
-/

namespace ImbalancedChen.Part5OriginalH430DescendantLimits

noncomputable section
open Set Filter Topology
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph P5OriginalActionMassBound
open P5OriginalFeedbackDomains
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenPerturbation Part5OriginalH430PhysicalMassPerturbation
open Part5OriginalH430FrozenRootMass Part5OriginalH430FrozenTableRootMass

theorem perform_residual_tendsto {p : ℕ → PhysicalNode} {q : PhysicalNode}
    (hL : Tendsto (fun n => residual (p n)) atTop (𝓝 (residual q)))
    (shape : StepShape) (z : Point) :
    Tendsto (fun n => residual (perform (p n) shape z)) atTop
      (𝓝 (residual (perform q shape z))) := by
  cases shape with
  | retain => exact hL
  | transport i => exact hL
  | buchstabUpper =>
      simpa only [perform, residual_appendOne] using hL.sub_const (z 0)
  | buchstabLower =>
      simpa only [perform, residual_appendOne] using hL.sub_const (z 0)
  | w1Fixed i j => exact hL
  | w1Singleton i j =>
      simpa only [perform, residual_appendOne] using hL.sub_const (z 0)
  | w2Fixed i j => exact hL
  | w2Singleton i j =>
      simpa only [perform, residual_appendOne] using hL.sub_const (z 0)
  | w2Pair i j =>
      simpa only [perform, residual_appendPair] using (hL.sub_const (z 1)).sub_const (z 0)

/-- Every literal child formula is continuous at a positive parent
residual.  Constants and inherited arguments are handled exactly. -/
theorem perform_argument_tendsto {p : ℕ → PhysicalNode} {q : PhysicalNode}
    (hL : Tendsto (fun n => residual (p n)) atTop (𝓝 (residual q)))
    (hs : Tendsto (fun n => (p n).argument) atTop (𝓝 q.argument))
    (hLq : 0 < residual q) (shape : StepShape) (z : Point) :
    Tendsto (fun n => (perform (p n) shape z).argument) atTop
      (𝓝 (perform q shape z).argument) := by
  have hu (i : Fin 2) : Tendsto (fun n => normalized (p n) z i) atTop
      (𝓝 (normalized q z i)) :=
    tendsto_const_nhds.div hL hLq.ne'
  cases shape with
  | retain => exact hs
  | transport i => exact tendsto_const_nhds
  | buchstabUpper => exact (hL.div_const (z 0)).sub_const 1
  | buchstabLower => exact (hL.div_const (z 0)).sub_const 1
  | w1Fixed i j => exact tendsto_const_nhds
  | w1Singleton i j =>
      exact tendsto_const_nhds.mul (tendsto_const_nhds.sub (hu 0))
  | w2Fixed i j => exact tendsto_const_nhds
  | w2Singleton i j =>
      exact tendsto_const_nhds.mul (tendsto_const_nhds.sub (hu 0))
  | w2Pair i j =>
      by_cases hj : j.val < 2
      · simpa only [perform, appendPair, pairProfile, hj, if_true, fixedPairProfile]
          using tendsto_const_nhds.mul ((tendsto_const_nhds.sub (hu 0)).sub (hu 1))
      · by_cases hz : z 0 = 0
        · simpa only [perform, appendPair, pairProfile, hj, if_false,
            movingPairProfile, normalized, hz, zero_div, div_zero]
            using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
        · have hden : normalized q z 0 ≠ 0 := div_ne_zero hz hLq.ne'
          simpa only [perform, appendPair, pairProfile, hj, if_false, movingPairProfile]
            using ((tendsto_const_nhds.sub (hu 0)).sub (hu 1)).div (hu 0) hden

/-- The induction reads the original ideal local filters.  No frozen
admission assumption is introduced in order to prove convergence. -/
theorem realize_argument_tendsto {mesh depth : ℕ} {lo hi : ℝ}
    {p : ℕ → TypedNode} {q : TypedNode}
    {code : Program mesh depth} {z : Coordinates depth}
    (hL : Tendsto (fun n => residual (p n).physical) atTop (𝓝 (residual q.physical)))
    (hs : Tendsto (fun n => (p n).physical.argument) atTop (𝓝 q.physical.argument))
    (hz : Member lo hi depth q code z) :
    Tendsto (fun n => (realize depth (p n) code z).physical.argument) atTop
      (𝓝 (realize depth q code z).physical.argument) := by
  induction depth generalizing p q with
  | zero => exact hs
  | succ depth ih =>
      apply ih (p := fun n => advance (p n) (code 0).1 (z 0))
        (q := advance q (code 0).1 (z 0))
      · exact perform_residual_tendsto hL (code 0).1 (z 0)
      · exact perform_argument_tendsto hL hs hz.2.2.1.1 (code 0).1 (z 0)
      · exact hz.2.2.2

def idealDescendant (k : Root) (t : ℝ) {mesh depth : ℕ}
    (code : Program mesh depth) (z : Coordinates depth) : PhysicalNode :=
  (realize depth (sourceRoot k 0 t) code z).physical

def frozenDescendant (n : ℕ) (k : Root) (t : ℝ) {mesh depth : ℕ}
    (code : Program mesh depth) (z : Coordinates depth) : PhysicalNode :=
  (realize depth (frozenRoot n k (finiteTau n) t) code z).physical

@[simp] theorem frozenDescendant_slots (n : ℕ) (k : Root) (t : ℝ)
    {mesh depth : ℕ} (code : Program mesh depth) (z : Coordinates depth) :
    (frozenDescendant n k t code z).slots = (idealDescendant k t code z).slots :=
  realize_slots_eq rfl code z

@[simp] theorem frozenDescendant_ceiling (n : ℕ) (k : Root) (t : ℝ)
    {mesh depth : ℕ} (code : Program mesh depth) (z : Coordinates depth) :
    (frozenDescendant n k t code z).ceiling = (idealDescendant k t code z).ceiling :=
  realize_ceiling_eq rfl code z

/-- Residual convergence holds for every Program, including paths which
fail the frozen admission test at infinitely many precisions. -/
theorem frozenDescendant_residual_tendsto {k : Root} {t : ℝ}
    (ht : t ∈ rootBand k) {mesh depth : ℕ}
    (code : Program mesh depth) (z : Coordinates depth) :
    Tendsto (fun n => residual (frozenDescendant n k t code z)) atTop
      (𝓝 (residual (idealDescendant k t code z))) := by
  apply Metric.tendsto_nhds.2
  intro epsilon he
  filter_upwards [levelError_finiteTau_tendsto.eventually (eventually_lt_nhds he)] with n hn
  have hl := rootLoss_bounds (n := n) (finiteTau_pos n).le (finiteTau_le n) ht
  have hd := actual_descendant_residual_loss n k (finiteTau n) t code z
  rw [Real.dist_eq, abs_sub_comm]
  change |residual (idealDescendant k t code z) -
    residual (frozenDescendant n k t code z)| < epsilon
  rw [hd, abs_of_nonneg hl.1]
  exact hl.2.trans_lt hn

theorem frozenDescendant_argument_tendsto {k : Root} {t lo hi : ℝ}
    (ht : t ∈ rootBand k) {mesh depth : ℕ}
    {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (sourceRoot k 0 t) code z) :
    Tendsto (fun n => (frozenDescendant n k t code z).argument) atTop
      (𝓝 (idealDescendant k t code z).argument) := by
  apply realize_argument_tendsto (q := sourceRoot k 0 t)
    (p := fun n => frozenRoot n k (finiteTau n) t) _ (frozenQuery_tendsto ht) hz
  let emptyCode : Program mesh 0 := Fin.elim0
  let emptyZ : Coordinates 0 := Fin.elim0
  exact frozenDescendant_residual_tendsto ht emptyCode emptyZ

theorem idealDescendant_residual_pos {k : Root} {t lo hi : ℝ}
    (ht : t ∈ rootBand k) {mesh depth : ℕ}
    {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (sourceRoot k 0 t) code z) :
    0 < residual (idealDescendant k t code z) := by
  have hroot : 0 < residual (sourceRoot k 0 t).physical := by
    rw [sourceRoot_residual]
    exact (by norm_num : (0 : ℝ) < 11/192).trans_le
      (sourceResidual_bounds (by norm_num) (by norm_num) ht).1
  exact (div_pos hroot (pow_pos (by norm_num : (0 : ℝ) < 101) depth)).trans_le
    (realize_residual_bound hz)

theorem perform_ceiling_pos {p : PhysicalNode} {shape : StepShape} {z : Point}
    (hC : 0 < p.ceiling) (hz : LocalDomain p shape z) :
    0 < (perform p shape z).ceiling := by
  cases shape with
  | retain => exact hC
  | transport i => exact hC
  | buchstabUpper => exact hz.2.1.1
  | buchstabLower => exact hz.2.2.1.1
  | w1Fixed i j => exact hC
  | w1Singleton i j => exact hz.2.1.1
  | w2Fixed i j => exact hC
  | w2Singleton i j => exact hz.2.1.1
  | w2Pair i j => exact hz.2.1.1

theorem realize_ceiling_pos {lo hi : ℝ} {mesh depth : ℕ} {p : TypedNode}
    {code : Program mesh depth} {z : Coordinates depth}
    (hC : 0 < p.physical.ceiling) (hz : Member lo hi depth p code z) :
    0 < (realize depth p code z).physical.ceiling := by
  induction depth generalizing p with
  | zero => exact hC
  | succ depth ih => exact ih (perform_ceiling_pos hC hz.2.2.1) hz.2.2.2

theorem idealDescendant_ceiling_pos {k : Root} {t lo hi : ℝ}
    (ht : t ∈ rootBand k) {mesh depth : ℕ}
    {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (sourceRoot k 0 t) code z) :
    0 < (idealDescendant k t code z).ceiling := by
  apply realize_ceiling_pos _ hz
  exact (by norm_num [Part5OriginalUpsilon5CausalDictionary.a] :
    (0 : ℝ) < Part5OriginalUpsilon5CausalDictionary.a).trans_le (rootBand_subset k ht).1

/-- True alpha has the original physical numerator.  No alpha=2 reset
and no re-normalization of a zero-mass cell is used. -/
theorem frozenDescendant_alpha_tendsto {k : Root} {t lo hi : ℝ}
    (ht : t ∈ rootBand k) {mesh depth : ℕ}
    {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (sourceRoot k 0 t) code z) :
    Tendsto (fun n => alpha (frozenDescendant n k t code z)) atTop
      (𝓝 (alpha (idealDescendant k t code z))) := by
  have hw (n : ℕ) : word (frozenDescendant n k t code z) =
      word (idealDescendant k t code z) :=
    congrArg (List.map Slot.exponent) (frozenDescendant_slots n k t code z)
  simpa only [alpha, hw] using
    (tendsto_const_nhds (x := 1-(word (idealDescendant k t code z)).sum)).div
      (frozenDescendant_residual_tendsto ht code z) (idealDescendant_residual_pos ht hz).ne'

/-- The real complete-prefix weight converges even when its product is
zero in Lean's totalized division.  Arithmetic membership is not inferred. -/
theorem frozenDescendant_weight_tendsto {k : Root} {t lo hi : ℝ}
    (ht : t ∈ rootBand k) {mesh depth : ℕ}
    {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member lo hi depth (sourceRoot k 0 t) code z) :
    Tendsto (fun n => physicalWeight (frozenDescendant n k t code z)) atTop
      (𝓝 (physicalWeight (idealDescendant k t code z))) := by
  have hw (n : ℕ) : word (frozenDescendant n k t code z) =
      word (idealDescendant k t code z) :=
    congrArg (List.map Slot.exponent) (frozenDescendant_slots n k t code z)
  have he (P L : ℝ) : 4/(P*L) = (4/P)*(1/L) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simpa only [physicalWeight, hw, he] using
    (tendsto_const_nhds (x := 4/(word (idealDescendant k t code z)).prod)).mul
      (tendsto_const_nhds.div (frozenDescendant_residual_tendsto ht code z)
        (idealDescendant_residual_pos ht hz).ne')

/-- Inherit/constant comparisons have exact argument strata.  They are
not classified as proper walls, even if their value is a table knot. -/
theorem constant_child_arguments (p q : PhysicalNode) (z : Point) :
    (∀ i, (perform p (.transport i) z).argument = (perform q (.transport i) z).argument) ∧
    (∀ i j, (perform p (.w1Fixed i j) z).argument = (perform q (.w1Fixed i j) z).argument) ∧
    (∀ i j, (perform p (.w2Fixed i j) z).argument = (perform q (.w2Fixed i j) z).argument) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

end
end ImbalancedChen.Part5OriginalH430DescendantLimits
