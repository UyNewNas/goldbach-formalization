import ImbalancedChen.Part3OriginalExceptionalJInitialAverage
import ImbalancedChen.Part3OriginalSwitchedMellinRows

/-! Pay the lower-order additive term of the switched estimate at X=1.
The complete Mellin factor is included in the physical coefficient vector. -/
namespace ImbalancedChen.Part3.OriginalSwitchedTwistedBaseline20261113
noncomputable section
open Finset MeasureTheory Complex
open scoped BigOperators MatrixGroups Classical
open OriginalExceptionalJNativeCompletion20261110
open OriginalExceptionalJInitialAverage20261113 (signed_row)
open OriginalSwitchedMellinRows20261113
open ActualCuspBasisWhittakerCoefficients20261102
open ActualIntervalGeometricSumSourceOnly (phaseAt)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open ActualContinuousPoincarePairing20261110 (originalFrame)
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant sieveConstant_pos)
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open private phaseAt_norm from ImbalancedChen.Part3ActualIntervalGeometricSum
open private card_levels from ImbalancedChen.Part3OriginalExceptionalJInitialAverage

local instance (z : ℕ+) : NeZero z.val := ⟨z.property.ne'⟩

def energy (S : Finset ℕ+) (X : ℝ) (j : ℕ) (ω t : ℝ) :=
  ∑ z ∈ S,∑ i : ↥(exceptional z),X^(tau z i.val)*
    ‖twistedRow (dyadicWindow j) (nativeRow z i.val ω) t‖^2

@[simp] theorem zero_frequency (S : Finset ℕ+) (X : ℝ) (j : ℕ) (ω : ℝ) :
    energy S X j ω 0=pascadiJ S X j ω := by simp only [energy,pascadiJ,twistedRow,nativeRow,wave_zero,mul_one]

/-- An arbitrary fixed list of frequency phases of modulus one is
permitted by the fixed-level sieve. For the stated application the
twist is m^(it), common to every level and slot, with no factor in t. -/
theorem unit_average {Q : ℝ} (qp : 0<Q) (j : ℕ) (ω t : ℝ) :
    energy (classicalLevels Q) 1 j ω t≤32*sieveConstant*(Q+classicalMScale j)*classicalMScale j := by
  let M := classicalMScale j
  let S := dyadicWindow j
  let w := fun m : ℕ => phaseAt ω m*wave (m:ℝ) t
  have cp := sieveConstant_pos
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have wmass : (∑ m ∈ S,‖w m‖^2)≤2*M := by
    have id : (∑ m ∈ S,‖w m‖^2)=(S.card:ℝ) := by simp [w,phaseAt_norm]
    rw [id]
    have card : S.card=2^j := by
      change (Finset.Ico (2^j) (2^(j+1)) : Finset ℕ).card=2^j
      rw [Nat.card_Ico,pow_succ];omega
    rw [card]
    linarith only [(classicalMScale_bounds j).2.1]
  have point (z : ℕ+) (hz : z∈classicalLevels Q) :
      (∑ i : ↥(exceptional z),‖twistedRow S (nativeRow z i.val ω) t‖^2)≤
        (8*sieveConstant)*(1+M/Q)*(2*M) := by
    have raw := signed_row z false (A:=1) mp (show (0:ℝ)<1 by norm_num)
      (by simpa only [one_mul] using le_max_left (1:ℝ) ((z.val:ℝ)/M)) S w 1 (Or.inl rfl)
      (fun m hm => (mem_full_classical_block j m).mp hm)
    simp only [Real.one_rpow,one_mul,originalFrame,Bool.false_eq_true,if_false,max_self] at raw
    have line (i : ↥(exceptional z)) :
        twistedRow S (nativeRow z i.val ω) t=2*∑ m ∈ S,w m*basisR z z.property i.val 1 (m:ℤ) := by
      rw [twistedRow,mul_sum]
      apply sum_congr rfl
      intro m hm
      have pos := ((mem_full_classical_block j m).mp hm).1
      have mp' : (0:ℝ)<m := mp.trans pos
      have nz : (m:ℤ)≠0 := (show (0:ℤ)<m by exact_mod_cast mp').ne'
      rw [basisR_eq_half_native z z.property i.val (1:SL(2,ℤ)) nz]
      dsimp only [w,nativeRow];ring
    simp_rw [line,norm_mul,mul_pow,Complex.norm_ofNat]
    rw [←mul_sum]
    have base := mul_le_mul_of_nonneg_left raw (by norm_num : (0:ℝ)≤2^2)
    have l := ((mem_classicalLevels Q z).mp hz).1.le
    have norm := mul_le_mul (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (div_le_div_of_nonneg_left mp.le qp l))
      (by positivity : 0≤sieveConstant*(1+1))) wmass
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity : 0≤sieveConstant*(1+1)*(1+M/Q))
    exact base.trans ((mul_le_mul_of_nonneg_left norm (by norm_num : (0:ℝ)≤2^2)).trans_eq (by ring))
  simp only [energy,Real.one_rpow,one_mul]
  have sum := Finset.sum_le_sum (fun z hz => point z hz)
  simp only [Finset.sum_const,nsmul_eq_mul] at sum
  have tail := mul_le_mul_of_nonneg_right (card_levels qp)
    (by positivity : 0≤8*sieveConstant*(1+M/Q)*(2*M))
  exact sum.trans (tail.trans_eq (by dsimp only [M];field_simp [qp.ne'] <;> ring))

/-- Both signs from the reflected half-frequency decomposition are
paid by the same untwisted X=1 bound after averaging their squares. -/
theorem integrated_unit {Q : ℝ} (qp : 0<Q) (j : ℕ) (ω : ℝ) :
    (∫ t : ℝ,‖density t‖*(energy (classicalLevels Q) 1 j ω (-(t/2))+
      energy (classicalLevels Q) 1 j ω (t/2))) ≤
      (∫ t : ℝ,‖density t‖)*(64*sieveConstant*(Q+classicalMScale j)*classicalMScale j) := by
  let L := 32*sieveConstant*(Q+classicalMScale j)*classicalMScale j
  have major (t : ℝ) := add_le_add (unit_average qp j ω (-(t/2))) (unit_average qp j ω (t/2))
  let G := fun t : ℝ => energy (classicalLevels Q) 1 j ω (-(t/2))+energy (classicalLevels Q) 1 j ω (t/2)
  have nn (t : ℝ) : 0≤G t := by
    simp only [G,energy,Real.one_rpow,one_mul];positivity
  have I : Integrable (fun t : ℝ => ‖density t‖*G t) := by
    apply density_integrable.norm.mul_bdd (c:=L+L)
    · simp only [G,energy,Real.one_rpow,one_mul,twistedRow,wave]
      fun_prop
    · exact ae_of_all _ (fun t => by rw [Real.norm_of_nonneg (nn t)];exact major t)
  apply (integral_mono I (density_integrable.norm.mul_const (L+L))
    (fun t => mul_le_mul_of_nonneg_left (major t) (norm_nonneg _))).trans_eq
  rw [integral_mul_const]
  dsimp [L];ring

end
end ImbalancedChen.Part3.OriginalSwitchedTwistedBaseline20261113
