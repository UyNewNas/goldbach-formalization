import ImbalancedChen.Part3OriginalRowPhysicalScalar
import ImbalancedChen.Part3OriginalAdditionalSpectralCosts
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual arithmetic support qualifications for the printed classical A/J
theorems.  The original Poisson block is [V,min(2V,J+1)), not (V,2V].
It is kept unchanged and placed in (V-1/2,2(V-1/2)].  Likewise the original
closed level plateau [Z,2Z] is covered by (Z/2,Z] and (Z,2Z].  Every
classical length is at least 1/2, including m=1 and the lower level boundary.
The phase and its original physical denominator V are not changed.

No spectral coefficient, trace identity, large sieve, gap, or energy estimate
is a premise or a conclusion.  In particular this is not an A/J instance.
-/

namespace ImbalancedChen.Part3.OriginalClassicalSpectralSupports20261102

noncomputable section
open Classical Finset
open OriginalCompletedReciprocalSource20261102
open OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalRowPhysicalScalar20261102
open OriginalCommonPoissonLanes20261102 OriginalAdditionalSpectralCosts20261102
open OriginalMaskedOuterEnergy20261102 MediumGlobalDyadicOwnership20261028
open ImbalancedChen.P3ZActualPrimaryShortEndpoint
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly
open P3ActualLiteralPacketIntegralSourceOnly

/-- This scale is only for the classical support theorem.  The normalized
physical amplitude and common phase still use V=2^j. -/
def classicalMScale (j : ℕ) : ℝ := ((2 : ℕ)^j : ℝ) - 1/2

theorem classicalMScale_bounds (j : ℕ) :
    (1 : ℝ)/2 ≤ classicalMScale j ∧
      ((2 : ℕ)^j : ℝ)/2 ≤ classicalMScale j ∧
      classicalMScale j ≤ ((2 : ℕ)^j : ℝ) := by
  have hvN : 1 ≤ (2 : ℕ)^j := pow_pos (by norm_num) _
  have hv : (1 : ℝ) ≤ ((2 : ℕ)^j : ℝ) := by exact_mod_cast hvN
  unfold classicalMScale
  constructor
  · linarith
  constructor <;> linarith

/-- The entire original clipped interval, including its left endpoint,
belongs to the same printed dyadic interval at every level. -/
theorem commonMBlock_classical_support (J j : ℕ) {m : ℕ}
    (hm : m ∈ commonMBlock J j) :
    classicalMScale j < (m : ℝ) ∧
      (m : ℝ) ≤ 2*classicalMScale j := by
  obtain ⟨hlo, hhi⟩ := mem_Ico.mp hm
  have hupper : m < 2*(2 : ℕ)^j := by
    simpa only [pow_succ, Nat.mul_comm] using (lt_min_iff.mp hhi).1
  have hupper' : m+1 ≤ 2*(2 : ℕ)^j := by omega
  have hloR : ((2 : ℕ)^j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hlo
  have hhiR : (m : ℝ)+1 ≤ 2*((2 : ℕ)^j : ℝ) := by exact_mod_cast hupper'
  unfold classicalMScale
  constructor <;> linarith

/-- The same frozen interval/phase object is retained at the changed
classical support scale: no level-dependent mask or phase is introduced. -/
theorem commonPoissonCompleted_classical_support (J j : ℕ) (k1 : ℤ) {m : ℕ}
    (hm : m ∈ commonMBlock J j) :
    (1 : ℝ)/2 ≤ classicalMScale j ∧
      (m : ℝ) ∈ Set.Ioc (classicalMScale j) (2*classicalMScale j) ∧
      (commonPoissonCompleted J j k1).weight m =
        Complex.exp (2*(Real.pi : ℂ)*Complex.I*
          ((k1 : ℝ)/(64*(2^j : ℕ)) : ℝ)*(m : ℂ)) := by
  exact ⟨(classicalMScale_bounds j).1, commonMBlock_classical_support J j hm,
    commonPoissonCompleted_weight J j k1 m hm⟩

/-- Reuse the existing nonempty endpoint theorem on the actual row beta.
The nonzero coefficient is the proper eligibility condition for a norm
estimate; no artificial nonempty spectrum is asserted. -/
theorem original_nonzero_row_classical_length (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k) (n : ℕ)
    (hb : signedCoefficient k.2.2 (rowPacket D r k z) n ≠ 0) :
    (1 : ℝ)/2 ≤ dyadicScale k.2.1/(k.1 : ℝ) := by
  have hblock : blockBeta D r k (decode k z.val n) ≠ 0 := by
    intro hz
    apply hb
    rw [rowCoefficient_eq, hz, zero_mul]
  have hbeta : dyadicBeta D.block.atom.residue (originalSource D) k.1
      (dyadicScale k.2.1) k.2.2 (D.lambda r) D.omega (k.1*n) z.val ≠ 0 := by
    change (rowPacket D r k z).beta (k.1*n) z.val ≠ 0
    rw [rowPacket_beta]
    exact hblock
  exact (nonempty_endpoint_bounds (dyadicScale_pos k.2.1) hbeta).2.2.2

/-- Pascadi A is used at the original level z.  Its sufficient allowed
range max(1,z/L) contains X0=1+Z/L up to the absolute constant two. -/
theorem original_fixed_level_A_range (D : OriginalData)
    (r : ZMod (prefixPeriod D.key)) (k : BlockKey) (z : Row D k) (n : ℕ)
    (hb : signedCoefficient k.2.2 (rowPacket D r k z) n ≠ 0) :
    1 + levelChart D z.val/(dyadicScale k.2.1/(k.1 : ℝ)) ≤
      2*max 1 ((z.val : ℝ)/(dyadicScale k.2.1/(k.1 : ℝ))) := by
  have hL : 0 < dyadicScale k.2.1/(k.1 : ℝ) :=
    lt_of_lt_of_le (by norm_num) (original_nonzero_row_classical_length D r k z n hb)
  have hZ : 0 < levelChart D z.val := levelChart_pos D z.val
  have hZz : levelChart D z.val ≤ (z.val : ℝ) := by
    have hh := (le_div_iff₀ hZ).mp (levelCarrier_normalized D k z.property).1
    simpa only [one_mul] using hh
  have hratio := div_le_div_of_nonneg_right hZz hL.le
  have h1 := le_max_left (1 : ℝ) ((z.val : ℝ)/(dyadicScale k.2.1/(k.1 : ℝ)))
  have h2 := le_max_right (1 : ℝ) ((z.val : ℝ)/(dyadicScale k.2.1/(k.1 : ℝ)))
  linarith only [hratio, h1, h2]

/-- The two possible scales are fixed after a physical Z chart is fixed. -/
def classicalLevelScale (Z : ℝ) (lower : Bool) : ℝ := if lower then Z/2 else Z

theorem classicalLevelScale_bounds {Z : ℝ} (hZ : 1 ≤ Z) (lower : Bool) :
    (1 : ℝ)/2 ≤ classicalLevelScale Z lower ∧
      Z/2 ≤ classicalLevelScale Z lower ∧ classicalLevelScale Z lower ≤ Z := by
  cases lower <;> simp only [classicalLevelScale, Bool.false_eq_true, if_false, if_true]
  · constructor
    · linarith
    exact ⟨by linarith, le_rfl⟩
  · exact ⟨by linarith, le_rfl, by linarith⟩

theorem original_levelChart_one_le (D : OriginalData) (z : ℕ) :
    1 ≤ levelChart D z := by
  have hS := scaleS_one_le D.key
  have hS2 : (1 : ℝ) ≤ (scaleS D.key)^2 := by nlinarith only [hS]
  unfold levelChart
  split_ifs <;> linarith only [hS2]

/-- The lower boundary is kept.  This is a two-interval cover for a
positive level norm, not an equality changing the original row partition. -/
theorem original_level_classical_cover (D : OriginalData) (k : BlockKey)
    (z : Row D k) :
    (z.val : ℝ) ∈ Set.Ioc (levelChart D z.val/2) (levelChart D z.val) ∨
      (z.val : ℝ) ∈ Set.Ioc (levelChart D z.val) (2*levelChart D z.val) := by
  have hZ := levelChart_pos D z.val
  have hbounds := levelCarrier_normalized D k z.property
  have hlo : levelChart D z.val ≤ (z.val : ℝ) := by
    simpa only [one_mul] using (le_div_iff₀ hZ).mp hbounds.1
  have hhi : (z.val : ℝ) ≤ 2*levelChart D z.val := (div_le_iff₀ hZ).mp hbounds.2
  by_cases he : (z.val : ℝ) = levelChart D z.val
  · exact Or.inl ⟨by rw [he]; linarith, he.le⟩
  · exact Or.inr ⟨lt_of_le_of_ne hlo (Ne.symm he), hhi⟩

/-- The classical J threshold at the endpoint-corrected scales is
comparable to the original physical threshold, uniformly in both level
intervals.  The constant four is independent of the source and frequency. -/
theorem original_J_threshold_comparison (D : OriginalData) (z : ℕ)
    (j : ℕ) (lower : Bool) :
    max (((2 : ℕ)^j : ℝ)) ((levelChart D z)^2/((2 : ℕ)^j : ℝ)) ≤
      4*max (classicalMScale j)
        ((classicalLevelScale (levelChart D z) lower)^2/classicalMScale j) := by
  let V : ℝ := ((2 : ℕ)^j : ℝ)
  let Z : ℝ := levelChart D z
  let M : ℝ := classicalMScale j
  let Q : ℝ := classicalLevelScale Z lower
  change max V (Z^2/V) ≤ 4*max M (Q^2/M)
  have hmb := classicalMScale_bounds j
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) hmb.1
  have hV : 0 < V := hM.trans_le hmb.2.2
  have hMV : M ≤ V := hmb.2.2
  have hVM : V ≤ 2*M := by linarith only [hmb.2.1]
  have hZQ : Z^2 ≤ 4*Q^2 := by
    cases lower
    · change Z^2 ≤ 4*Z^2
      nlinarith only [sq_nonneg Z]
    · change Z^2 ≤ 4*(Z/2)^2
      nlinarith only []
  have hratio : Z^2/V ≤ 4*(Q^2/M) := by
    have hnum : Z^2*M ≤ (4*Q^2)*V :=
      (mul_le_mul_of_nonneg_right hZQ hM.le).trans
        (mul_le_mul_of_nonneg_left hMV (by positivity))
    have hh : Z^2/V ≤ (4*Q^2)/M := (div_le_div_iff₀ hV hM).mpr hnum
    exact hh.trans_eq (by ring)
  have hmaxM : M ≤ max M (Q^2/M) := le_max_left _ _
  have hmaxQ : Q^2/M ≤ max M (Q^2/M) := le_max_right _ _
  apply max_le
  · linarith only [hVM, hmaxM, hM]
  · linarith only [hratio, hmaxQ]

end
end ImbalancedChen.Part3.OriginalClassicalSpectralSupports20261102
