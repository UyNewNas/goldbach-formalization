import ImbalancedChen.P2OriginalMixedThirdWTentSelector
import ImbalancedChen.P2OriginalCommonActualWMesh
import ImbalancedChen.P2OriginalLowerPrefixTrimmedChamberCover

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A single mesh threshold transfers independent strict point winners of the
ACTUAL screened mixed tent/W bank to its inherited-first finite selector.
The winner need not be W. All row forms have a proved uniform slope bound;
mesh-width premises are derived rather than supplied per point/row. Actual
screened membership and original strict point margins remain visible. This
does not construct the missing arithmetic factorization licence or a global
adopted bank from an arbitrary ideal point.
-/

namespace ImbalancedChen.P2OriginalUniformMixedTentWChoice

noncomputable section
open scoped Classical BigOperators Topology
open Set Filter
open P2OriginalLowerSelectedCapConstructor (Code prefixCode)
open P2OriginalLowerAffineTieSelector
open P2OriginalLowerBufferedAffineBoxes (RationalBox inBox affineValue)
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalLowerWholeBoxBranchSelect
open P2OriginalLowerFiniteAffineMeshWidth
open P2OriginalLowerPrefixTrimmedChamberCover
open P2OriginalStartSpecificTentParentBank
open P2OriginalMixedThirdWTentSelector
open P2OriginalCommonActualWMesh

-- Every literal SourceForm slope is 0, 1/2, -3/2, or -3/8.
theorem source_slopeNorm_le (b : SelectedBranchData) :
    slopeNorm b.cap.slope ≤ 15 / 2 := by
  have hterm (i : Fin 5) : |(b.cap.slope i : ℝ)| ≤ 3 / 2 := by
    cases h : b.form <;>
      simp only [SelectedBranchData.cap, SourceForm.affine, h] <;>
      split_ifs <;> norm_num
  calc
    _ ≤ ∑ _i : Fin 5, (3 / 2 : ℝ) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = 15 / 2 := by norm_num

theorem source_difference_norm_le (b c : SelectedBranchData) :
    slopeNorm (fun i => b.cap.slope i - c.cap.slope i) ≤ 15 := by
  have hs : slopeNorm (fun i => b.cap.slope i - c.cap.slope i) ≤
      slopeNorm b.cap.slope + slopeNorm c.cap.slope := by
    unfold slopeNorm
    simp only [Rat.cast_sub, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => abs_sub_le _ _)
  linarith [source_slopeNorm_le b, source_slopeNorm_le c]

def point5 (S : CompactStart) (x : P2OriginalStrictWLocalRationalCover.Point) : Fin 5 → ℝ :=
  fun i => if hi : i.val < 3 then x ⟨i.val, hi⟩ else startCutoff S.start

theorem point5_in_actual_box (S : CompactStart) (mesh : ℕ)
    (x : P2OriginalStrictWLocalRationalCover.Point)
    (hx : ∀ i, x i ∈ Icc (S.epsilon : ℝ) (startCutoff S.start : ℝ)) :
    inBox (boxOfCode S (canonicalThirdCode S mesh x)) (point5 S x) := by
  apply inBox_of_exponentCodes
  intro i
  by_cases hi : i.val < 3
  · simpa [point5, canonicalThirdCode, hi] using
      (P2PhysicalIncomingPrefixCells.exponentCode_membership
        (m := mesh) (hx ⟨i.val, hi⟩))
  · simp [point5, canonicalThirdCode, hi, P2PhysicalIncomingPrefixCells.exponentCell]

private theorem gap_pos_from_point
    (S : CompactStart) {mesh : ℕ} (code : Code mesh)
    (a b : AffineBranch 5) (x : Fin 5 → ℝ)
    (hx : inBox (boxOfCode S code) x) (margin : ℝ)
    (hpoint : margin ≤ a.eval x - b.eval x)
    (hmesh : slopeNorm (fun i => a.slope i - b.slope i) *
      logPrimeMeshStep (S.epsilon : ℝ) (startCutoff S.start : ℝ) mesh < margin) :
    0 < gapLower a b (boxOfCode S code) := by
  have hloss := affine_point_minus_box_infimum_le_step S code
    (a.constant - b.constant) (fun i => a.slope i - b.slope i) x hx
  have heval : affineValue (a.constant - b.constant)
      (fun i => a.slope i - b.slope i) x = a.eval x - b.eval x := by
    simp [affineValue, AffineBranch.eval, Rat.cast_sub,
      sub_mul, Finset.sum_sub_distrib]
    ring
  rw [heval] at hloss
  have hreal : (0 : ℝ) < gapLower a b (boxOfCode S code) := by
    change (0 : ℝ) < P2OriginalLowerBufferedAffineBoxes.wholeBoxInfimum
      (a.constant - b.constant) (fun i => a.slope i - b.slope i) (boxOfCode S code)
    linarith
  exact_mod_cast hreal

private theorem firstStable_unique {rows : List SelectedBranchData}
    {P : SelectedBranchData → Prop} {b : SelectedBranchData}
    (hb : b ∈ rows) (hPb : P b) (hu : ∀ c ∈ rows, P c → c = b) :
    firstStable P rows = some b := by
  induction rows with
  | nil => cases hb
  | cons c cs ih =>
      by_cases hc : P c
      · have hcb := hu c List.mem_cons_self hc
        subst c
        simp [firstStable, hPb]
      · have hbt : b ∈ cs := by
          rcases List.mem_cons.mp hb with heq | ht
          · subst c
            exact False.elim (hc hPb)
          · exact ht
        simpa [firstStable, hc] using ih hbt
          (fun d hd hPd => hu d (List.mem_cons_of_mem _ hd) hPd)

-- rho and parent are the original rational baseline. A proper trimmed
-- point winner has a margin over inherit and each genuinely different row;
-- no successful mixedWinner equation is an input. Equal affine rows require
-- the original first-label merge/uniqueness, made explicit by row equality.
theorem exists_common_mesh_for_strict_mixed_point_winners
    (S : CompactStart) (rho : ℚ) (margin : ℝ) (hmargin : 0 < margin) :
    ∃ M : ℕ, ∀ mesh : ℕ, M ≤ mesh →
      ∀ screen buffer delta : ℚ,
      ∀ argument : Fin 6 → Code mesh → SourceForm → ℚ,
      ∀ x : P2OriginalStrictWLocalRationalCover.Point,
      (∀ i, x i ∈ Icc (S.epsilon : ℝ) (startCutoff S.start : ℝ)) →
      ∀ b : SelectedBranchData,
      b ∈ mixedRows S rho screen buffer delta argument (canonicalThirdCode S mesh x) →
      margin ≤ b.cap.eval (point5 S x) - (249 / 448 - (rho : ℝ)) →
      (∀ c ∈ mixedRows S rho screen buffer delta argument (canonicalThirdCode S mesh x),
        c = b ∨ margin ≤ b.cap.eval (point5 S x) - c.cap.eval (point5 S x)) →
      mixedWinner S rho screen buffer delta
        (fun _ => inheritedConstant (249 / 448 - rho)) argument
        (canonicalThirdCode S mesh x) = some b := by
  have hsmall := (tendsto_logPrimeMeshStep (S.epsilon : ℝ)
    (startCutoff S.start : ℝ)).eventually (gt_mem_nhds (show 0 < margin / 16 by positivity))
  obtain ⟨M, hM⟩ := eventually_atTop.mp hsmall
  refine ⟨M, ?_⟩
  intro mesh hmesh screen buffer delta argument x hx b hb hbase hrows
  let code := canonicalThirdCode S mesh x
  let box := boxOfCode S code
  let base := inheritedConstant (249 / 448 - rho)
  let rows := mixedRows S (rho : ℝ) screen buffer delta argument code
  let X := point5 S x
  have hX : inBox box X := point5_in_actual_box S mesh x hx
  have hstep0 : 0 ≤ logPrimeMeshStep (S.epsilon : ℝ) (startCutoff S.start : ℝ) mesh :=
    (logPrimeMeshStep_pos
      (show (S.epsilon : ℝ) < startCutoff S.start by exact_mod_cast S.epsilon_lt_start) mesh).le
  have hstep := hM mesh hmesh
  have hbaseNorm : slopeNorm (fun i => b.cap.slope i - base.cap.slope i) ≤ 15 := by
    simpa [base, inheritedConstant] using (source_slopeNorm_le b).trans (by norm_num : (15 : ℝ) / 2 ≤ 15)
  have hgapbase : 0 < gapLower b.cap base.cap box := by
    apply gap_pos_from_point S code b.cap base.cap X hX margin
    · simpa [base, inheritedConstant, AffineBranch.eval] using hbase
    · have hmul := mul_le_mul_of_nonneg_right hbaseNorm hstep0
      linarith
  have hgaprow (c : SelectedBranchData) (hc : c ∈ rows) (hne : c ≠ b) :
      0 < gapLower b.cap c.cap box := by
    rcases hrows c hc with heq | hpoint
    · exact False.elim (hne heq)
    · apply gap_pos_from_point S code b.cap c.cap X hX margin hpoint
      have hmul := mul_le_mul_of_nonneg_right (source_difference_norm_le b c) hstep0
      linarith
  have hdom : dominates box base rows b := by
    refine ⟨Or.inr hgapbase, ?_⟩
    intro c hc
    by_cases heq : c = b
    · exact Or.inl (congrArg SelectedBranchData.cap heq.symm)
    · exact Or.inr (hgaprow c hc heq)
  have hnotbase : ¬ stableBase box base rows := by
    intro hstable
    rcases hstable b hb with heq | hg
    · have hv := congrArg (fun a : AffineBranch 5 => a.eval X) heq
      have hbpoint : margin ≤ b.cap.eval X - base.cap.eval X := by
        simpa [base, inheritedConstant, AffineBranch.eval] using hbase
      linarith
    · have hbound := gapLower_le_eval_gap base.cap b.cap box X hX
      have hgR : (0 : ℝ) < gapLower base.cap b.cap box := by exact_mod_cast hg
      have hbpoint : margin ≤ b.cap.eval X - base.cap.eval X := by
        simpa [base, inheritedConstant, AffineBranch.eval] using hbase
      linarith
  have hunique : ∀ c ∈ rows, dominates box base rows c → c = b := by
    intro c hc hstable
    by_contra hne
    have hpoint : margin ≤ b.cap.eval X - c.cap.eval X := by
      rcases hrows c hc with heq | hpoint
      · exact False.elim (hne heq)
      · exact hpoint
    rcases hstable.2 b hb with heq | hg
    · have hv := congrArg (fun a : AffineBranch 5 => a.eval X) heq
      linarith
    · have hbound := gapLower_le_eval_gap c.cap b.cap box X hX
      have hgR : (0 : ℝ) < gapLower c.cap b.cap box := by exact_mod_cast hg
      linarith
  have hfirst := firstStable_unique hb hdom hunique
  have hcanon : prefixCode 3 code = code := (canonicalThirdCode_prefix S mesh x).symm
  simpa only [mixedWinner, hcanon, if_neg hnotbase] using hfirst

end
end ImbalancedChen.P2OriginalUniformMixedTentWChoice
