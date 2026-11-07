import ImbalancedChen.P2OriginalMixedThirdSignedFrontier
import ImbalancedChen.FrozenRosserPolicy

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The rank3-only mixed plan actually keeps its computed cap on every later
history. This proves the frozen TOTAL level and its exact quotient before
any ordinary-Rosser continuation identification is used.
-/
namespace ImbalancedChen.P2OriginalI3ActualFrozenTraceLevel
noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalLowerSelectedCapConstructor (Code)
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalMixedThirdBranchTableTrace
open P2OriginalMixedThirdSignedFrontier

theorem thirdPlan_non3_inherits {mesh : ℕ} (D : ThirdStage mesh)
    (rank : Fin 6) (code : Code mesh) (hr : rank.val ≠ 3) :
    D.thirdPlan.choose rank code = .inherit 2 := by
  fin_cases rank <;>
    simp_all [ThirdStage.thirdPlan, mixedPlan, compactPlan, checkedChoice,
      mixedThirdRows, emptyRows]

/-- After rank3, each later actual step inherits the preceding cap. -/
theorem thirdPlan_trace_cons_frozen {mesh : ℕ} (D : ThirdStage mesh)
    (N p : ℕ) (pre : List ℕ) (hlen : 3 ≤ pre.length) :
    (integerTrace D.thirdPlan (D.start.epsilon : ℝ)
      (startCutoff D.start.start : ℝ) (baselineCap D.rho) N (p::pre)).cap =
    (integerTrace D.thirdPlan (D.start.epsilon : ℝ)
      (startCutoff D.start.start : ℝ) (baselineCap D.rho) N pre).cap := by
  let H := integerTrace D.thirdPlan (D.start.epsilon : ℝ)
    (startCutoff D.start.start : ℝ) (baselineCap D.rho) N pre
  have hl : (H.word ++ [coordinate N p]).length = pre.length + 1 := by
    rw [integerTrace_word]
    simp [physicalWord]
  rw [integerTrace_cons]
  change (planChoice D.thirdPlan (D.start.epsilon : ℝ)
    (startCutoff D.start.start : ℝ) (H.word ++ [coordinate N p])).freeze H.cap = H.cap
  unfold planChoice
  split_ifs with hactive
  · unfold incomingChoice
    have hr : min (H.word ++ [coordinate N p]).length 5 ≠ 3 := by
      rw [hl]
      omega
    rw [thirdPlan_non3_inherits D _ _ hr]
    rfl
  · rfl

/-- An arbitrary later selected prime word keeps the same actual rank3
cap. It is not an assumption that the new plan reads the old ancestor. -/
theorem thirdPlan_trace_append_frozen {mesh : ℕ} (D : ThirdStage mesh)
    (N : ℕ) (pre later : List ℕ) (hlen : 3 ≤ pre.length) :
    (integerTrace D.thirdPlan (D.start.epsilon : ℝ)
      (startCutoff D.start.start : ℝ) (baselineCap D.rho) N (later++pre)).cap =
    (integerTrace D.thirdPlan (D.start.epsilon : ℝ)
      (startCutoff D.start.start : ℝ) (baselineCap D.rho) N pre).cap := by
  induction later with
  | nil => rfl
  | cons p ps ih =>
    rw [List.cons_append, thirdPlan_trace_cons_frozen D N p (ps++pre)
      (by simp only [List.length_append]; omega)]
    exact ih

/-- The unchanged total level is divided by the ENTIRE actual selected
product. No new buffer, ideal parent or rounded natural level is inserted. -/
theorem thirdPlan_actual_quotient_level {mesh : ℕ} (D : ThirdStage mesh)
    (N : ℕ) (pre later : List ℕ) (hlen : 3 ≤ pre.length)
    (hN : 1 < (N : ℝ)) (hpos : ∀ p ∈ later++pre, 0 < p) :
    (N : ℝ) ^ (integerTrace D.thirdPlan (D.start.epsilon : ℝ)
        (startCutoff D.start.start : ℝ) (baselineCap D.rho) N (later++pre)).cap /
        ((later++pre).prod : ℝ) =
      (N : ℝ) ^ ((integerTrace D.thirdPlan (D.start.epsilon : ℝ)
        (startCutoff D.start.start : ℝ) (baselineCap D.rho) N pre).cap -
          (physicalWord N (later++pre)).sum) := by
  rw [thirdPlan_trace_append_frozen D N pre later hlen,
    Real.rpow_sub (zero_lt_one.trans hN), physicalWord_power hN (later++pre) hpos]

end
end ImbalancedChen.P2OriginalI3ActualFrozenTraceLevel
