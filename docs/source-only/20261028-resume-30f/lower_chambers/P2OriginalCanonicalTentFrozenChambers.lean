import ImbalancedChen.P2OriginalIdealTentCanonicalScreen

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual point decoding and a mesh threshold shared by all ranks feed the
independent canonical tent producer. The fourth/fifth local chamber tests
use its own COMPUTED cap3/cap4 as parent. In particular rank five receives
no invented new cube, and inherited fourth states remain available.
This remains the tent subbank; W and global adopted coverage stay open.
-/

namespace ImbalancedChen.P2OriginalCanonicalTentFrozenChambers

noncomputable section
open scoped Classical Topology
open Set Filter
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2EnhancedLowerPhysicalNode
open P2OriginalLowerSelectedCapConstructor (Code strictSquareGates)
open P2OriginalLowerAffineTieSelector
open P2OriginalLowerBufferedAffineBoxes
open P2OriginalLowerWholeBoxBranchSelect
open P2OriginalLowerFiniteAffineMeshWidth (slopeNorm)
open P2OriginalUniformMixedTentWChoice (source_slopeNorm_le)
open P2OriginalPairSourceReceiver
open P2OriginalCanonicalPairTentBank
open P2OriginalIdealTentCanonicalScreen

private theorem range_lt (R : PairRange) : (R.epsilon : ℝ) < (ceiling : ℝ) := by
  exact_mod_cast (lt_trans R.epsilon_lt_a (by norm_num [ceiling] : (417:ℚ)/5000 < ceiling))

private theorem qPoint_cast (R : PairRange) (mesh j : ℕ) :
    (qPoint R mesh j : ℝ) = logPrimeMeshPoint (R.epsilon : ℝ) (ceiling : ℝ) mesh j := by
  unfold qPoint logPrimeMeshPoint logPrimeMeshStep
  push_cast
  ring

private theorem scalar_code_bounds (R : PairRange) (mesh : ℕ) (z : ℝ)
    (hz : z ∈ Icc (R.epsilon : ℝ) (ceiling : ℝ)) :
    (qLo R mesh (exponentCode (R.epsilon : ℝ) (ceiling : ℝ) mesh z) : ℝ) ≤ z ∧
      z ≤ (qHi R mesh (exponentCode (R.epsilon : ℝ) (ceiling : ℝ) mesh z) : ℝ) := by
  have hm := exponentCode_membership (m:=mesh) hz
  cases hc : exponentCode (R.epsilon : ℝ) (ceiling : ℝ) mesh z with
  | none =>
      have heq : z = (ceiling : ℝ) := by simpa [hc, exponentCell] using hm
      simp [hc, qLo, qHi, heq]
  | some j =>
      have hm' : logPrimeMeshPoint (R.epsilon : ℝ) (ceiling : ℝ) mesh j.val ≤ z ∧
          z < logPrimeMeshPoint (R.epsilon : ℝ) (ceiling : ℝ) mesh (j.val+1) := by
        simpa [hc, exponentCell] using hm
      simpa [hc, qLo, qHi, qPoint_cast] using And.intro hm'.1 hm'.2.le

def actualPoint (rank : Fin 6) (x : Fin 5 → ℝ) : Fin 5 → ℝ :=
  fun i => if i.val < rank.val then x i else (ceiling : ℝ)

def actualCode (R : PairRange) (mesh : ℕ) (rank : Fin 6) (x : Fin 5 → ℝ) : Code mesh :=
  codeAt R mesh rank.val [x 0,x 1,x 2,x 3,x 4]

theorem actualCode_at (R : PairRange) (mesh : ℕ) (rank : Fin 6)
    (x : Fin 5 → ℝ) (i : Fin 5) :
    actualCode R mesh rank x i =
      if i.val < rank.val then
        (exponentCode (R.epsilon : ℝ) (ceiling : ℝ) mesh (x i), false)
      else (none, false) := by
  fin_cases rank <;> fin_cases i <;>
    simp [actualCode, codeAt, incomingCode, physicalCode, marked, exponentCode]

theorem actualCode_point_in_box (R : PairRange) (mesh : ℕ) (rank : Fin 6)
    (x : Fin 5 → ℝ)
    (hx : ∀ i, x i ∈ Icc (R.epsilon : ℝ) (ceiling : ℝ)) :
    inBox (box R (actualCode R mesh rank x)) (actualPoint rank x) := by
  intro i
  by_cases hi : i.val < rank.val
  · simpa [box, actualCode_at, actualPoint, hi] using scalar_code_bounds R mesh (x i) (hx i)
  · simp [box, actualCode_at, actualPoint, hi, qLo, qHi]

-- One explicit step condition suffices for both the source screen and the
-- actual-parent gates. All ranks3/4/5 share this threshold, before points/N.
theorem exists_uniform_canonical_tent_mesh (R : PairRange)
    (buffer : ℚ) (hbuffer : 0 ≤ buffer) (margin : ℝ)
    (hgap : (buffer : ℝ) < margin) :
    ∃ M : ℕ, ∀ mesh : ℕ, M ≤ mesh →
      16 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer < margin := by
  have he : 0 < (margin - buffer) / 16 := by positivity
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    ((tendsto_logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ)).eventually (gt_mem_nhds he))
  exact ⟨M, fun mesh hm => by have h := hM mesh hm; linarith⟩

-- The point tests of the original selected source give actual membership
-- in the literal rank alphabet; canonical decoding is now supplied here.
theorem original_point_enters_actual_canonical_bank
    (R : PairRange) (mesh : ℕ) (rank : Fin 6) (x : Fin 5 → ℝ)
    (hx : ∀ i, x i ∈ Icc (R.epsilon : ℝ) (ceiling : ℝ))
    (mask : Finset (Fin 5))
    (hm : mask ∈ P2OriginalFiniteTentBankSelectorMargins.tentMasks rank)
    (right : Bool) (buffer seed : ℚ) (hbuffer : 0 ≤ buffer)
    (margin : ℝ) (hmargin : 0 < margin)
    (hbudget : 16 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer < margin)
    (hside : margin ≤
      (otherRow R (actualCode R mesh rank x) mask right).cap.eval (actualPoint rank x) -
      (chosenRow R (actualCode R mesh rank x) mask right).cap.eval (actualPoint rank x))
    (hfull : strictSquareGates
      ((chosenRow R (actualCode R mesh rank x) mask right).cap.eval (actualPoint rank x) - margin) 0
      ((pointSlots rank (actualCode R mesh rank x) mask (actualPoint rank x)).map Slot.exponent))
    (hselected : strictSquareGates
      ((chosenRow R (actualCode R mesh rank x) mask right).cap.eval (actualPoint rank x) - margin)
      (selectedWord (pointSlots rank (actualCode R mesh rank x) mask (actualPoint rank x))).sum
      (remainingWord (pointSlots rank (actualCode R mesh rank x) mask (actualPoint rank x)))) :
    chosenRow R (actualCode R mesh rank x) mask right ∈
      (bank R mesh buffer seed).alternatives rank (actualCode R mesh rank x) := by
  exact ideal_tent_occurs_in_canonical_bank R mesh _ rank _
    (actualCode_point_in_box R mesh rank x hx) mask hm right buffer seed hbuffer
    margin hmargin hbudget hside hfull hselected

private theorem actual_parent_fresh_from_point (R : PairRange) {mesh : ℕ}
    (code : Code mesh) (rank : Fin 6) (x : Fin 5 → ℝ)
    (hx : inBox (box R code) x) (b : SelectedBranchData)
    (buffer : ℚ) (hbuffer : 0 ≤ buffer) (margin : ℝ)
    (hbudget : 16 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer < margin)
    (parent : ℝ) (hparent : parent + margin ≤ b.cap.eval x)
    (htop : b.cap.eval x ≤ (153:ℝ)/256)
    (harrival : rank.val = 4 → x 0+x 1+x 2+3*x 3+margin ≤ parent) :
    freshCheck R rank code buffer parent b := by
  let h := logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh
  have hh := (logPrimeMeshStep_pos (range_lt R) mesh).le
  have hb : (0:ℝ) ≤ buffer := by exact_mod_cast hbuffer
  have hloss := ideal_minus_boxInf_le_step R code x hx b.cap.constant b.cap.slope
  have hnorm := mul_le_mul_of_nonneg_right (source_slopeNorm_le b) hh
  have heval : affineValue b.cap.constant b.cap.slope x = b.cap.eval x := rfl
  rw [heval] at hloss
  have hrow : (rowCap R code buffer b : ℝ) =
      (wholeBoxInfimum b.cap.constant b.cap.slope (box R code) : ℝ) - buffer := by
    unfold rowCap
    push_cast
    rfl
  have hinf := wholeBoxInfimum_le_affine b.cap.constant b.cap.slope (box R code) x hx
  rw [heval] at hinf
  refine ⟨?_, ?_, ?_⟩
  · rw [hrow]
    linarith
  · rw [hrow]
    linarith
  · unfold arrivalGate
    split_ifs with hr
    · have hp := harrival hr
      have hu (i : Fin 5) : (qHi R mesh (code i).1 : ℝ) ≤ x i + h := by
        have hw : ((box R code).hi i : ℝ) - (box R code).lo i ≤ h := by
          -- Same-code endpoints differ by at most the actual step.
          cases hc : (code i).1 with
          | none => simpa [box,qLo,qHi,hc] using hh
          | some j =>
              simp only [box,hc,qLo,qHi,qPoint_cast,logPrimeMeshPoint_succ]
              dsimp [h]
              linarith
        have hl := (hx i).1
        change (qLo R mesh (code i).1 : ℝ) ≤ x i at hl
        dsimp [box] at hw
        linarith
      have h0 := hu 0
      have h1 := hu 1
      have h2 := hu 2
      have h3 := hu 3
      dsimp [h] at *
      linarith
    · trivial

-- Ranking floor and genuine physical root are distinct. These chamber
-- hypotheses mention cap3 computed from root:Real with the concrete bank
-- ranked at floor:Rat, never the ideal C3 or the rational ranking floor.
-- The physical L5/L6 root supplier is consumed downstream by the warm plan;
-- no successful branch selection is supplied as a premise here.
theorem rank4_actual_frozen_parent_chamber (R : PairRange) (mesh : ℕ)
    (buffer floor : ℚ) (root : ℝ) (hbuffer : 0 ≤ buffer) (code : Code mesh)
    (x : Fin 5 → ℝ) (hx : inBox (box R code) x) (b : SelectedBranchData)
    (margin : ℝ)
    (hbudget : 16 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer < margin)
    (hparent : cap3 R (bank R mesh buffer floor) buffer root code + margin ≤ b.cap.eval x)
    (htop : b.cap.eval x ≤ (153:ℝ)/256)
    (hcube : x 0+x 1+x 2+3*x 3+margin ≤ cap3 R (bank R mesh buffer floor) buffer root code) :
    freshCheck R 4 code buffer (cap3 R (bank R mesh buffer floor) buffer root code) b := by
  exact actual_parent_fresh_from_point R code 4 x hx b buffer hbuffer margin
    hbudget _ hparent htop (fun _ => hcube)

-- The actual fourth cap may be inherited unchanged. The genuine real
-- root stays distinct from the rational ranking floor. No strict fourth
-- improvement or invented S4+3t5 gate is required to license a fifth action.
theorem rank5_actual_frozen_parent_chamber (R : PairRange) (mesh : ℕ)
    (buffer floor : ℚ) (root : ℝ) (hbuffer : 0 ≤ buffer) (code : Code mesh)
    (x : Fin 5 → ℝ) (hx : inBox (box R code) x) (b : SelectedBranchData)
    (margin : ℝ)
    (hbudget : 16 * logPrimeMeshStep (R.epsilon : ℝ) (ceiling : ℝ) mesh + buffer < margin)
    (hparent : cap4 R (bank R mesh buffer floor) buffer root code + margin ≤ b.cap.eval x)
    (htop : b.cap.eval x ≤ (153:ℝ)/256) :
    freshCheck R 5 code buffer (cap4 R (bank R mesh buffer floor) buffer root code) b := by
  exact actual_parent_fresh_from_point R code 5 x hx b buffer hbuffer margin
    hbudget _ hparent htop (by intro h; norm_num at h)

end
end ImbalancedChen.P2OriginalCanonicalTentFrozenChambers
