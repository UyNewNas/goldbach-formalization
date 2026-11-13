import ImbalancedChen.Part3OriginalSwitchedNativePrefixEnergy

/-! The lower-order X=1 price for every shorter common interval in a
native positive block, with no Mellin-frequency cost. -/
namespace ImbalancedChen.Part3.OriginalSwitchedIntervalUnit20261113
noncomputable section
open Finset Complex
open scoped BigOperators MatrixGroups
open OriginalSwitchedNativePrefixEnergy20261113 (intervalEnergy)
open OriginalSwitchedMellinRows20261113 (twistedRow nativeRow wave wave_norm)
open OriginalExceptionalJNativeCompletion20261110 (exceptional classicalLevels mem_classicalLevels mem_full_classical_block)
open OriginalExceptionalJInitialAverage20261113 (signed_row)
open private card_levels from ImbalancedChen.Part3OriginalExceptionalJInitialAverage
open ActualCuspBasisWhittakerCoefficients20261102 (basisR basisR_eq_half_native)
open ActualIntervalGeometricSumSourceOnly (phaseAt)
open private phaseAt_norm from ImbalancedChen.Part3ActualIntervalGeometricSum
open ActualContinuousPoincarePairing20261110 (originalFrame)
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant sieveConstant_pos)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)

theorem short_unit {B : ℝ} (bp : 0<B) (j a b : ℕ) (lo : 2^j≤a) (hi : b≤2^(j+1)) (ω t : ℝ) :
    intervalEnergy (classicalLevels B) 1 ω a b t≤32*sieveConstant*(B+classicalMScale j)*classicalMScale j := by
  let M := classicalMScale j
  let S := Ico a b
  let w := fun m : ℕ => phaseAt ω m*wave (m:ℝ) t
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have mem (m : ℕ) (hm : m∈S) : m∈dyadicWindow j := Finset.mem_Ico.mpr
    ⟨lo.trans (Finset.mem_Ico.mp hm).1,lt_of_lt_of_le (Finset.mem_Ico.mp hm).2 hi⟩
  have mass : (∑ m∈S,‖w m‖^2)≤2*M := by
    have id : (∑ m∈S,‖w m‖^2)=(S.card:ℝ) := by simp [w,phaseAt_norm]
    rw [id]
    have len : S.card≤2^j := by
      dsimp only [S]
      rw [Nat.card_Ico]
      rw [pow_succ] at hi
      omega
    have lr : (S.card:ℝ)≤((2^j:ℕ):ℝ) := by exact_mod_cast len
    exact lr.trans (by dsimp only [M];linarith only [(classicalMScale_bounds j).2.1])
  have cp := sieveConstant_pos
  have pt (z : ℕ+) (hz : z∈classicalLevels B) :
      (∑ i : ↥(exceptional z),‖twistedRow S (nativeRow z i.val ω) t‖^2)≤
      8*sieveConstant*(1+M/B)*(2*M) := by
    have line (i : ↥(exceptional z)) : twistedRow S (nativeRow z i.val ω) t=
        2*∑ m∈S,w m*basisR z z.property i.val 1 (m:ℤ) := by
      rw [twistedRow,Finset.mul_sum]
      apply sum_congr rfl
      intro m hm
      have pos := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le (Finset.mem_Ico.mp (mem m hm)).1
      have nz : (m:ℤ)≠0 := (show (0:ℤ)<m by exact_mod_cast pos).ne'
      rw [basisR_eq_half_native z.val z.property i.val 1 nz]
      dsimp only [w,nativeRow];ring
    have h := signed_row z false (A:=1) mp (by norm_num : (0:ℝ)<1)
      (by simpa only [one_mul] using le_max_left (1:ℝ) ((z.val:ℝ)/M)) S w 1 (Or.inl rfl)
      (fun m hm => (mem_full_classical_block j m).mp (mem m hm))
    simp only [Real.one_rpow,one_mul,originalFrame,Bool.false_eq_true,if_false,max_self] at h
    simp_rw [line,norm_mul,mul_pow,Complex.norm_ofNat]
    rw [←Finset.mul_sum]
    have l := ((mem_classicalLevels B z).mp hz).1.le
    have q := mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (div_le_div_of_nonneg_left mp.le bp l)) (by positivity : 0≤sieveConstant*(1+1))) mass
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity : 0≤sieveConstant*(1+1)*(1+M/B))
    exact (mul_le_mul_of_nonneg_left (h.trans q) (by norm_num : (0:ℝ)≤2^2)).trans_eq (by ring)
  simp only [intervalEnergy,Real.one_rpow,one_mul]
  have sum := Finset.sum_le_sum (s:=classicalLevels B) (fun z hz => pt z hz)
  simp only [Finset.sum_const,nsmul_eq_mul] at sum
  have cnt := mul_le_mul_of_nonneg_right (card_levels bp) (by positivity : 0≤8*sieveConstant*(1+M/B)*(2*M))
  exact sum.trans (cnt.trans_eq (by dsimp only [M];field_simp [bp.ne'] <;> ring))

end
end ImbalancedChen.Part3.OriginalSwitchedIntervalUnit20261113
