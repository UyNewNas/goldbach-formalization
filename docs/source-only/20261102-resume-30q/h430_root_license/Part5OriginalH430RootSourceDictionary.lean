import ImbalancedChen.Part5OriginalH430FrozenRootRefinement

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The source discriminator is computed from the original U3/U4 occurrence
and its strict t<57/224 split.  It is not a field containing a count
licence.  Analytic squares have their own ell_aux; physical total,
residual, alpha, cutoff and the actual Program are never changed.

The cover transition below reuses the existing physical gate theorem on
a proof-only record.  That record is not returned as an arithmetic node.
No factorization, signed-distribution, positive seed or H430 count
estimate is inferred from these geometric statements.
-/

namespace ImbalancedChen.Part5OriginalH430RootSourceDictionary

noncomputable section
open Set
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5UpperTables.OriginalU34

inductive SourceBranch where
  | enhanced
  | classicalBelowHalf
  deriving DecidableEq

def rootSource : Root → ℝ → SourceBranch
  | .U3, t => if t < tailCutoff then .enhanced else .classicalBelowHalf
  | .U4, _ => .enhanced

theorem U3_source_split (t : ℝ) :
    (rootSource .U3 t = .enhanced ↔ t < tailCutoff) ∧
    (rootSource .U3 t = .classicalBelowHalf ↔ tailCutoff ≤ t) := by
  by_cases h : t < tailCutoff
  · simp [rootSource, h, not_le.mpr h]
  · simp [rootSource, h, le_of_not_gt h]

/-- Both square lists are the original complete lists. Only their analytic
right-hand side is a separate datum. This definition has no density. -/
def coverGates (ell_aux : ℝ) (n : PhysicalNode) : Prop :=
  SquareGates ell_aux 0 (word n) ∧
    SquareGates ell_aux (selectedWord n.slots).sum (remainingWord n.slots)

theorem coverGates_at_physical (n : PhysicalNode) :
    coverGates n.total n ↔ fullGates n ∧ selectedGates n := Iff.rfl

theorem appendOne_coverGates {ell_aux x s : ℝ} {n : PhysicalNode}
    (hcap : n.total ≤ ell_aux) (hg : coverGates ell_aux n)
    (hx : 2*x ≤ residual n) : coverGates ell_aux (appendOne n x s) := by
  let a : PhysicalNode := { n with total := ell_aux }
  have hx' : 2*x ≤ residual a := by
    dsimp [a, residual, word] at *
    linarith only [hx, hcap]
  exact appendOne_gates (n := a) hg.1 hg.2 hx'

theorem appendPair_coverGates {ell_aux x y s : ℝ} {n : PhysicalNode}
    (hcap : n.total ≤ ell_aux) (hg : coverGates ell_aux n)
    (hy : 2*y ≤ residual n) (hx : y+2*x ≤ residual n) :
    coverGates ell_aux (appendPair n x y s) := by
  let a : PhysicalNode := { n with total := ell_aux }
  have hy' : 2*y ≤ residual a := by
    dsimp [a, residual, word] at *
    linarith only [hy, hcap]
  have hx' : y+2*x ≤ residual a := by
    dsimp [a, residual, word] at *
    linarith only [hx, hcap]
  exact appendPair_gates (n := a) hg.1 hg.2 hy' hx'

/-- LocalDomain is evaluated at the actual physical lambda, not ell_aux. -/
theorem perform_coverGates {ell_aux : ℝ} {n : PhysicalNode}
    {shape : StepShape} {z : Point} (hcap : n.total ≤ ell_aux)
    (hg : coverGates ell_aux n) (hz : LocalDomain n shape z) :
    coverGates ell_aux (perform n shape z) := by
  cases shape with
  | retain => exact hg
  | transport cell => exact hg
  | buchstabUpper => exact appendOne_coverGates hcap hg hz.2.1.2.2
  | buchstabLower => exact appendOne_coverGates hcap hg hz.2.2.1.2.2
  | w1Fixed i j => exact hg
  | w1Singleton i j => exact appendOne_coverGates hcap hg hz.2.1.2.2
  | w2Fixed bank anchor => exact hg
  | w2Singleton bank piece => exact appendOne_coverGates hcap hg hz.2.1.2.2
  | w2Pair bank piece =>
      exact appendPair_coverGates hcap hg hz.2.1.2.2.2.1 hz.2.1.2.2.2.2

theorem realize_coverGates {lo hi ell_aux : ℝ} {mesh depth : ℕ}
    {n : TypedNode} {code : Program mesh depth} {z : Coordinates depth}
    (hcap : n.physical.total ≤ ell_aux) (hg : coverGates ell_aux n.physical)
    (hz : Member lo hi depth n code z) :
    coverGates ell_aux (realize depth n code z).physical := by
  induction depth generalizing n with
  | zero => exact hg
  | succ depth ih =>
      apply ih (n := advance n (code 0).1 (z 0))
      · simpa only [advance, perform_total] using hcap
      · exact perform_coverGates hcap hg hz.2.2.1
      · exact hz.2.2.2

theorem enhanced_root_coordinate {k : Root} {t : ℝ}
    (hbranch : rootSource k t = .enhanced) (ht : t ∈ rootBand k) :
    t < tailCutoff := by
  cases k with
  | U3 => exact (U3_source_split t).1.mp hbranch
  | U4 => exact ht.2.trans_lt (by norm_num [tailCutoff])

/-- The enhanced-root full square is derived from the actual tent. The
strict e boundary goes to the classical branch, including t=e itself. -/
theorem enhanced_root_square {t : ℝ} (ht : t < tailCutoff) :
    2*t < VariableEnvelope.v t := by
  rw [VariableEnvelope.v_eq_min]
  apply lt_min <;> dsimp [VariableEnvelope.A, VariableEnvelope.C] <;>
    dsimp [tailCutoff] at ht <;> linarith

theorem enhanced_root_total {k : Root} {tau t : ℝ}
    (hbranch : rootSource k t = .enhanced) :
    (sourceRoot k tau t).physical.total = VariableEnvelope.v t := by
  cases k with
  | U3 =>
      have ht := (U3_source_split t).1.mp hbranch
      change t + U3Residual tau t = VariableEnvelope.v t
      simp only [U3Residual, if_pos ht, mainResidual]
      ring
  | U4 =>
      change t + mainResidual t = VariableEnvelope.v t
      unfold mainResidual
      ring

theorem enhanced_root_coverGates {k : Root} {tau t ell_aux : ℝ}
    (hbranch : rootSource k t = .enhanced) (ht : t ∈ rootBand k)
    (hcover : VariableEnvelope.v t ≤ ell_aux) :
    coverGates ell_aux (sourceRoot k tau t).physical := by
  have hs := (enhanced_root_square (enhanced_root_coordinate hbranch ht)).le.trans hcover
  simpa [coverGates, sourceRoot, word, selectedWord, remainingWord, SquareGates] using hs

/-- Frozen physical lambda may be below the external square. The same
root word passes its separate analytic cover, without changing lambda. -/
theorem enhanced_frozen_root_coverGates {k : Root} {tau t ell_aux : ℝ}
    (n : ℕ) (hbranch : rootSource k t = .enhanced) (ht : t ∈ rootBand k)
    (hcover : VariableEnvelope.v t ≤ ell_aux) :
    coverGates ell_aux (frozenRoot n k tau t).physical := by
  exact enhanced_root_coverGates hbranch ht hcover

/-- Concrete Q14 entry: no root fullGates or root licence hypothesis.
The original Member, native coordinates, total, word and labels survive. -/
theorem enhanced_frozen_descendant_coverGates
    {lo hi tau t ell_aux : ℝ} {k : Root} {n mesh depth : ℕ}
    {code : Program mesh depth} {z : Coordinates depth}
    (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hbranch : rootSource k t = .enhanced) (ht : t ∈ rootBand k)
    (hcover : VariableEnvelope.v t ≤ ell_aux)
    (hz : Member lo hi depth (frozenRoot n k tau t) code z) :
    coverGates ell_aux (realize depth (frozenRoot n k tau t) code z).physical ∧
    (realize depth (frozenRoot n k tau t) code z).physical.total =
      (frozenRoot n k tau t).physical.total := by
  have hlow := (frozenLevel_bounds (root_total_bounds htau htauhi ht) n).1
  have hcap : (frozenRoot n k tau t).physical.total ≤ ell_aux := by
    change frozenLevel n (sourceRoot k tau t).physical.total ≤ ell_aux
    exact hlow.trans (by rwa [enhanced_root_total hbranch])
  exact ⟨realize_coverGates hcap (enhanced_frozen_root_coverGates n hbranch ht hcover) hz,
    realize_total _ _ _⟩

/-- A concrete cover inside the original singleton tent. It is computed
from the already frozen physical lambda; it is not a replacement lambda. -/
def bufferedRootCover (t lambda : ℝ) : ℝ :=
  (max lambda (2*t) + VariableEnvelope.v t)/2

theorem bufferedRootCover_bounds {t lambda : ℝ}
    (ht : t < tailCutoff) (hlambda : lambda < VariableEnvelope.v t) :
    lambda < bufferedRootCover t lambda ∧ 2*t < bufferedRootCover t lambda ∧
    bufferedRootCover t lambda < VariableEnvelope.v t := by
  have hsq := enhanced_root_square ht
  have hm : max lambda (2*t) < VariableEnvelope.v t := max_lt hlambda hsq
  have hl := le_max_left lambda (2*t)
  have hr := le_max_right lambda (2*t)
  dsimp [bufferedRootCover]
  constructor
  · linarith only [hm, hl]
  constructor <;> linarith only [hm, hr]

/-- Actual frozen roots with positive buffer have an explicit cover below
the original endpoint and above every old full square. Equality/no-loss
roots are not claimed to have a strict reserve by this theorem. -/
theorem enhanced_frozen_descendant_buffered_cover
    {lo hi tau t : ℝ} {k : Root} {n mesh depth : ℕ}
    {code : Program mesh depth} {z : Coordinates depth}
    (hbranch : rootSource k t = .enhanced) (ht : t ∈ rootBand k)
    (hbuffer : (frozenRoot n k tau t).physical.total < VariableEnvelope.v t)
    (hz : Member lo hi depth (frozenRoot n k tau t) code z) :
    let ell_aux := bufferedRootCover t (frozenRoot n k tau t).physical.total
    (frozenRoot n k tau t).physical.total < ell_aux ∧
    ell_aux < VariableEnvelope.v t ∧
    coverGates ell_aux (realize depth (frozenRoot n k tau t) code z).physical := by
  dsimp only
  have hb := bufferedRootCover_bounds (enhanced_root_coordinate hbranch ht) hbuffer
  refine ⟨hb.1, hb.2.2, realize_coverGates hb.1.le ?_ hz⟩
  simpa [coverGates, frozenRoot, sourceRoot, word, selectedWord, remainingWord,
    SquareGates] using hb.2.1.le

theorem classical_tail_total {tau t : ℝ} (ht : tailCutoff ≤ t) :
    (sourceRoot .U3 tau t).physical.total = 1/2-tau := by
  change t + U3Residual tau t = 1/2-tau
  simp only [U3Residual, if_neg (not_lt.mpr ht), tailResidual]
  ring

/-- This is the classical complete-level gap, not a full-square claim. -/
theorem classical_frozen_descendant_level {tau t : ℝ} {n mesh depth : ℕ}
    (htau : 0 < tau) (htauhi : tau ≤ 1/12)
    (ht : t ∈ rootBand .U3) (htail : tailCutoff ≤ t)
    (code : Program mesh depth) (z : Coordinates depth) :
    (realize depth (frozenRoot n .U3 tau t) code z).physical.total ≤ 1/2-tau ∧
    (realize depth (frozenRoot n .U3 tau t) code z).physical.total < 1/2 := by
  have hlow := (frozenLevel_bounds (root_total_bounds htau.le htauhi ht) n).1
  have hlevel : (realize depth (frozenRoot n .U3 tau t) code z).physical.total ≤
      1/2-tau := by
    rw [realize_total]
    exact hlow.trans_eq (classical_tail_total htail)
  exact ⟨hlevel, lt_of_le_of_lt hlevel (by linarith only [htau])⟩

end
end ImbalancedChen.Part5OriginalH430RootSourceDictionary
