import ImbalancedChen.Part3OriginalOppositeBlockHighV
import ImbalancedChen.Part3OriginalCommonPoissonLanes
import Mathlib.Data.Nat.Log

/-! SOURCE ONLY / UNCOMPILED / UNEVALUATED.
Exact intersection of the high-V restriction with the original global
ceiling cutoff and half-open common dyadic blocks. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHighVActualCutoff20261120
open Finset
open OriginalCompletedReciprocalSource20261102
open OriginalCommonPoissonLanes20261102 (blockIndices commonMBlock globalCutoff)
open OriginalTwoZSourceAssembly20261102 (fixedZ)
open ImbalancedChen.P3ZActualPrimaryShortEndpoint
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly

/-- The last dyadic block is genuinely occupied iff its left endpoint is
at most the original inclusive integer cutoff J. -/
theorem common_block_nonempty_iff (J j : ℕ) :
    (commonMBlock J j).Nonempty ↔ 2^j ≤ J := by
  constructor
  · rintro ⟨p,hp⟩
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hp
    have hcut := (lt_min_iff.mp hhi).2
    omega
  · intro h
    refine ⟨2^j,Finset.mem_Ico.mpr ⟨le_rfl,lt_min_iff.mpr ⟨?_,?_⟩⟩⟩
    · exact Nat.pow_lt_pow_right (by norm_num : 1 < (2:ℕ)) (Nat.lt_succ_self j)
    · omega

/-- Exact existence criterion for an occupied high-V block, including
the dyadic discretization and the actual original blockIndices carrier. -/
theorem highV_global_cutoff_iff (D : OriginalData) (x ε : ℝ) :
    (∃ j ∈ blockIndices (globalCutoff D x ε),
      (commonMBlock (globalCutoff D x ε) j).Nonempty ∧
        fixedZ D true ≤ (((2:ℕ)^j : ℕ):ℝ)) ↔
    0 < globalCutoff D x ε ∧
      fixedZ D true ≤ (((2:ℕ)^(Nat.log 2 (globalCutoff D x ε)) : ℕ):ℝ) := by
  let J := globalCutoff D x ε
  change (∃ j ∈ blockIndices J, (commonMBlock J j).Nonempty ∧
    fixedZ D true ≤ (((2:ℕ)^j : ℕ):ℝ)) ↔
      0 < J ∧ fixedZ D true ≤ (((2:ℕ)^(Nat.log 2 J) : ℕ):ℝ)
  constructor
  · rintro ⟨j,_,hblock,hZ⟩
    have hpow : 2^j ≤ J := (common_block_nonempty_iff J j).mp hblock
    have hJ : 0 < J := (pow_pos (by norm_num : 0 < (2:ℕ)) j).trans_le hpow
    have hlog : j ≤ Nat.log 2 J := Nat.le_log_of_pow_le (by norm_num) hpow
    have hpow' : (2:ℕ)^j ≤ 2^(Nat.log 2 J) :=
      Nat.pow_le_pow_right (by norm_num) hlog
    have hreal : (((2:ℕ)^j : ℕ):ℝ) ≤ (((2:ℕ)^(Nat.log 2 J) : ℕ):ℝ) := by
      exact_mod_cast hpow'
    exact ⟨hJ,hZ.trans hreal⟩
  · rintro ⟨hJ,hZ⟩
    refine ⟨Nat.log 2 J, ?_, ?_, hZ⟩
    · exact Finset.mem_range.mpr (Nat.lt_succ_self _)
    · exact (common_block_nonempty_iff J _).mpr (Nat.pow_log_le_self 2 hJ.ne')

/-- The exact ceiling contributes a strict +1 in the necessary physical
cutoff condition; neither endpoint nor a dyadic factor is suppressed. -/
theorem highV_requires_real_cutoff (D : OriginalData) {x ε : ℝ} (hx : 0 < x)
    (hhigh : ∃ j ∈ blockIndices (globalCutoff D x ε),
      (commonMBlock (globalCutoff D x ε) j).Nonempty ∧
        fixedZ D true ≤ (((2:ℕ)^j : ℕ):ℝ)) :
    2*(scaleS D.key)^2 < (scaleS D.key)*x^ε + 1 := by
  obtain ⟨j,_,hblock,hZ⟩ := hhigh
  have hpow : (2:ℕ)^j ≤ globalCutoff D x ε :=
    (common_block_nonempty_iff _ _).mp hblock
  have hpowR : (((2:ℕ)^j : ℕ):ℝ) ≤ (globalCutoff D x ε : ℝ) := by
    exact_mod_cast hpow
  have hS : 0 < scaleS D.key := scaleS_pos D.key
  have hratio : D.cScale/D.bScale = scaleS D.key := by
    unfold OriginalData.cScale
    field_simp [D.bScale_pos.ne'] <;> ring
  have hT : 0 ≤ (scaleS D.key)*x^ε :=
    mul_nonneg hS.le (Real.rpow_nonneg hx.le _)
  have hceil : (globalCutoff D x ε : ℝ) < (scaleS D.key)*x^ε+1 := by
    simpa only [globalCutoff,hratio] using (Nat.ceil_lt_add_one hT)
  have hupper : 2*(scaleS D.key)^2 ≤ (((2:ℕ)^j : ℕ):ℝ) := by
    simpa only [fixedZ,if_true] using hZ
  exact (hupper.trans hpowR).trans_lt hceil

/-- Contrapositive: when the actual real cutoff cannot reach 2S^2 even
after the ceiling's strict unit allowance, no retained block is high-V. -/
theorem no_highV_if_real_cutoff_small (D : OriginalData) {x ε : ℝ} (hx : 0 < x)
    (hsmall : (scaleS D.key)*x^ε+1 ≤ 2*(scaleS D.key)^2) :
    ¬ ∃ j ∈ blockIndices (globalCutoff D x ε),
      (commonMBlock (globalCutoff D x ε) j).Nonempty ∧
        fixedZ D true ≤ (((2:ℕ)^j : ℕ):ℝ) := by
  intro h
  exact (not_lt_of_ge hsmall) (highV_requires_real_cutoff D hx h)

end ImbalancedChen.Part3.OriginalHighVActualCutoff20261120
end
