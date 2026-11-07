import ImbalancedChen.P5OriginalPresievedDeltaAttachment
import ImbalancedChen.P5OriginalOrdinaryPresievedActiveRange

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An ACTUAL nonzero explicitly-new ordinary15 presievedSigma supplies the
same original tuple and real e,d. Its rough d is active in the original
native row; e is taken from this very coefficient at the unchanged COMMON
physical beta level. The actual e is attached only to the third actual
factor, with the complete physical q and positive delta-scale reserves.
No factorability, desired monomial or old-sigma licence is assumed.
-/

namespace ImbalancedChen.P5Z.OriginalPresievedActiveDeltaFactors

noncomputable section
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler (selectedPolicy ownerBox boxPolicy_certificate tupleTag)
open U1011OriginalSixteenNearCapBoxProfiles (delta)
open U1011OriginalFifteenJointSmallBeta (attachedFactors)
open OriginalOrdinaryBetaRegroup OriginalOrdinaryResidualArithmeticFactor
open OriginalOrdinaryCommonBetaModel OriginalOrdinaryPresievedSigma
open OriginalOrdinaryPresievedActiveRange OriginalPresievedDeltaAttachment
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

/-- The rough factor displayed by an actual ordinary retained tree is a
nonzero original native divisor, not merely a member of a larger carrier. -/
theorem ordinary_rough_supported_native_active {N cap d : ℕ} {w Z L : ℝ}
    (hL : 1 < L) (hwZ : w ≤ Z)
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z) :
    actualSmallRosserPlus N cap Z L d ≠ 0 := by
  have hsf := fixedRoughSupport_squarefree (ordinaryRetainOdd L) N cap w Z hd
  have hmu : ArithmeticFunction.moebius d ≠ 0 :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsf
  have hdc : fixedRoughCoefficient (ordinaryRetainOdd L) N cap w Z d ≠ 0 := by
    change ((if d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z
      then ArithmeticFunction.moebius d else 0 : ℤ) : ℝ) ≠ 0
    rw [if_pos hd]
    exact_mod_cast hmu
  have hdW : roughWeight N cap w Z L d ≠ 0 := by
    rw [← ordinary_rough_coefficient N cap w Z L hL d]
    exact hdc
  have hda := upperWeight_active hdW
  have he1 : 1 ∈ actualSmallRosserSupport N cap w :=
    Nat.mem_divisors.mpr ⟨one_dvd _, actualSmallPrimeProduct_ne_zero N cap w⟩
  have hdM : d ∈ actualSmallRosserSupport N cap Z := by
    rw [nativeSupport_eq_products N cap hwZ]
    exact Finset.mem_image.mpr ⟨(1,d), Finset.mem_product.mpr ⟨he1,hda.1⟩, one_mul d⟩
  change upperWeight (actualSmallPrimeProduct N cap Z) L d ≠ 0
  rw [upperWeight_apply, if_pos ⟨hdM,hda.2.1,hda.2.2⟩]
  exact pow_ne_zero _ (by norm_num)

/-- Every nonzero NEW physical presieved coefficient has SAME original15
natural factors after attaching its actual common beta integer to group3.
The original w=N^(nu0*betaEta^2), B=N^(nu0*betaEta) are unchanged. Every
original A query and every 0<=kappa<=delta/64 is covered. -/
theorem active_original_presieved_delta_factors {n N q : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop) (nu0 betaEta : ℝ)
    (hw : ∀ t ∈ tuples n N E,
      (N : ℝ) ^ (nu0 * betaEta ^ 2) ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (hell : ∀ t ∈ tuples n N E,
      nu0 * betaEta ≤ (delta (selectedPolicy n N t) (ownerBox n N t) eta : ℝ) / 8)
    (hq : presievedSigma n N eta ((N : ℝ) ^ (nu0 * betaEta ^ 2))
      ((N : ℝ) ^ (nu0 * betaEta)) E q ≠ 0) :
    ∃ t ∈ tuples n N E,
      ∃ e ∈ actualSmallRosserSupport N
          (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
          ((N : ℝ) ^ (nu0 * betaEta ^ 2)),
        ∃ d ∈ fixedRoughSupport
            (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
            (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
            ((N : ℝ) ^ (nu0 * betaEta ^ 2)) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t),
          (e : ℝ) < (N : ℝ) ^ (nu0 * betaEta) ∧ q = fullPrefix t * (e * d) ∧
          U1011OriginalSixteenJointNearCapCompiler.coefficient n N eta t d ≠ 0 ∧
          ∀ A : ℝ, 1 ≤ A → A ≤ (N : ℝ) ^ (1 / 3 : ℝ) →
            ∀ kappa : ℝ, 0 ≤ kappa →
              kappa ≤ (delta (selectedPolicy n N t) (ownerBox n N t) eta : ℝ) / 64 →
              let abc := attachedFactors (selectedPolicy n N t) (ownerBox n N t) eta N A t d e
              let delt := (delta (selectedPolicy n N t) (ownerBox n N t) eta : ℝ)
              abc.1 * abc.2.1 * abc.2.2 = q ∧
                0 < abc.1 ∧ 0 < abc.2.1 ∧ 0 < abc.2.2 ∧ (abc.1 : ℝ) ≤ A ∧
                A ^ 2 * (abc.2.1 : ℝ) * (abc.2.2 : ℝ) ^ 2 ≤ (N : ℝ) ^ (1 - 3 * delt / 2) ∧
                (N : ℝ) ^ (7 * (1 + 3 * kappa) / 32) * A * (abc.1 : ℝ) *
                  (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 - delt) ∧
                (A * (abc.2.2 : ℝ) / (abc.2.1 : ℝ)) ^ (7 / 16 : ℝ) * A *
                  (abc.1 : ℝ) * (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤
                    (N : ℝ) ^ (2 - 117 * delt / 64) := by
  obtain ⟨t,ht,r,hr,hqr,e,he,d,hd,her,heB,hfull,hphysical⟩ :=
    active_physical_factors hN heta E hw hq
  have htOrd := (Finset.mem_filter.mp ht).1
  have hp := (Finset.mem_filter.mp ht).2
  have hs := (Finset.mem_filter.mp htOrd).1
  have htag := (Finset.mem_filter.mp htOrd).2
  have hlegal := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta htOrd
  have hdNative : U1011OriginalSixteenJointNearCapCompiler.coefficient n N eta t d ≠ 0 := by
    change actualSmallRosserPlus N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
      (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
      (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) d ≠ 0
    exact ordinary_rough_supported_native_active hlegal.2.1 (hw t ht) hd
  have hcell := owner_mem n (U1011OriginalFifteenJointNativeRows.joint_coordinates_cube hN hs)
  have hbox := cell_subset_closed_box n _ hcell
  have hvalid : (ownerBox n N t).Valid := gridBox_valid n _
  have hpositive : 0 < (ownerBox n N t).lo 3 := gridBox_lower_positive n _ 3
  have hcert := (boxPolicy_certificate (ownerBox n N t) htag).2
  have hqed : q = fullPrefix t * (e * d) := by rw [hqr,her]
  refine ⟨t,ht,e,he,d,hd,heB,hqed,hdNative,?_⟩
  intro A hA hAupper kappa hk0 hk
  have ha := actual_beta_attached_delta_monomials hN hs
    (selectedPolicy n N t) hp (ownerBox n N t) eta heta hvalid hpositive hcert hbox
    hdNative A hA hAupper hk0 hk he heB (hell t ht)
  dsimp only at ha ⊢
  refine ⟨?_,ha.2⟩
  calc
    _ = e * (fullPrefix t * d) := ha.1
    _ = q := by rw [hqed]; ring

end
end ImbalancedChen.P5Z.OriginalPresievedActiveDeltaFactors
