import ImbalancedChen.P5OriginalOrdinaryResidualArithmeticFactor
import ImbalancedChen.OrdinaryRosserFirstExitPolicy
import ImbalancedChen.ActualUpperPolicyFiniteBridge

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The manuscript attaches a common small beta pair to the rough ordinary
tree. That construction is already defined by actualSmallRoughRho. Here
its rough coefficient is identified with the literal rough upper Rosser
arithmetic function, and its difference from the existing all-prime
native coefficient is derived exactly. The same difference is identified
at the existing JOINT sigma. No sigma is redefined and no zero-defect or
fixed-beta identification premise occurs in these theorems.
-/

namespace ImbalancedChen.P5Z.OriginalOrdinaryCommonBetaModel

noncomputable section
open scoped BigOperators
open Classical
open OriginalOrdinaryBetaRegroup OriginalOrdinaryResidualArithmeticFactor
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

def ordinaryRetainOdd (L : ℝ) : List ℕ → Bool :=
  ordinaryParityRosserPolicy false L false

/-- The common beta level B is separate from the original rough level L.
This is the already-defined physical sign-sensitive construction. -/
def presievedCoefficient (N cap : ℕ) (w Z L B : ℝ) : ℕ → ℝ :=
  actualSmallRoughRho (ordinaryRetainOdd L) N cap w Z B

def commonSmallWeight (N cap : ℕ) (w Z L B : ℝ) (d e : ℕ) : ℝ :=
  if 0≤roughWeight N cap w Z L d then actualSmallRosserPlus N cap w B e
  else actualSmallRosserMinus N cap w B e

theorem roughProduct_eq_universe_prod (N cap : ℕ) (w Z : ℝ) :
    roughProduct N cap w Z=(roughPrimeUniverse N cap w Z).prod := by
  unfold roughProduct
  rw [←roughPrimeUniverse_toFinset N cap w Z]
  simpa using List.prod_toFinset (fun p : ℕ=>p) (roughPrimeUniverse_nodup N cap w Z)

/-- The actual ordinary ROUGH tree has the literal rough upper weight at
all arguments, including zero and arguments outside its retained carrier. -/
theorem ordinary_rough_coefficient (N cap : ℕ) (w Z L : ℝ) (hL : 1<L) (d : ℕ) :
    fixedRoughCoefficient (ordinaryRetainOdd L) N cap w Z d=
      roughWeight N cap w Z L d := by
  calc
    fixedRoughCoefficient (ordinaryRetainOdd L) N cap w Z d =
        (firstExitRetainedCoefficient (ordinaryParityRosserPolicy false L)
          (roughPrimeUniverse N cap w Z) d:ℝ) :=
      UpperPolicyFiniteBridge.fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
        (ordinaryParityRosserPolicy false L) (ordinaryParityRosserPolicy_upper_even L) N cap w Z d
    _ = ordinaryRosserWeight false (roughPrimeUniverse N cap w Z).prod L d :=
      firstExitRetainedCoefficient_ordinaryParityRosser false L hL _
        (roughPrimeUniverse_pairwise_gt N cap w Z)
        (fun _ hp=>mem_roughPrimeUniverse_prime hp) (by simp) d
    _ = roughWeight N cap w Z L d := by
      simp only [ordinaryRosserWeight,Bool.false_eq_true,if_false,roughWeight,
        roughProduct_eq_universe_prod]

/-- Every retained ordinary rough row belongs to the exact whole rough
divisor carrier used by the conditional native split. -/
theorem ordinary_rough_support_subset {N cap d : ℕ} {w Z L : ℝ} (hL : 1<L)
    (hd : d∈fixedRoughSupport (ordinaryRetainOdd L) N cap w Z) :
    d∈roughSupport N cap w Z := by
  have hs := UpperPolicyFiniteBridge.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    (ordinaryParityRosserPolicy false L) (ordinaryParityRosserPolicy_upper_even L) N cap w Z
  change d∈fixedRoughSupport (ordinaryParityRosserPolicy false L false) N cap w Z at hd
  rw [hs,ordinaryParityRosserRetainedModuli_eq false L hL _
    (roughPrimeUniverse_pairwise_gt N cap w Z)
    (fun _ hp=>mem_roughPrimeUniverse_prime hp) (by simp)] at hd
  have hmem := (mem_ordinaryRosserRetainedModuli_iff false L hL _
    (roughPrimeUniverse_pairwise_gt N cap w Z)
    (fun _ hp=>mem_roughPrimeUniverse_prime hp) d).mp hd
  change d∈(roughProduct N cap w Z).divisors
  rw [roughProduct_eq_universe_prod]
  exact hmem.1

/-- Exact value of the genuine presieved coefficient. The small level B
is common across d, while the sign is that of this actual rough row. -/
theorem presieved_coefficient_value {N cap e d : ℕ} {w Z L B : ℝ}
    (hL : 1<L) (he : e∈actualSmallRosserSupport N cap w)
    (hd : d∈fixedRoughSupport (ordinaryRetainOdd L) N cap w Z) :
    presievedCoefficient N cap w Z L B (e*d)=
      roughWeight N cap w Z L d * commonSmallWeight N cap w Z L B d e := by
  change smallRoughRho (actualSmallRosserSupport N cap w)
    (fixedRoughSupport (ordinaryRetainOdd L) N cap w Z)
    (fixedRoughCoefficient (ordinaryRetainOdd L) N cap w Z)
    (actualSmallRosserMinus N cap w B) (actualSmallRosserPlus N cap w B) (e*d)=_
  rw [smallRoughRho_mul
    (fun _ hp=>actualSmallRosserSupport_smallPrimeSupportedAt N cap w hp)
    (fun _ hp=>fixedRoughSupport_roughPrimeSupportedAt (ordinaryRetainOdd L) N cap w Z hp)
    (fixedRoughCoefficient (ordinaryRetainOdd L) N cap w Z)
    (actualSmallRosserMinus N cap w B) (actualSmallRosserPlus N cap w B) he hd]
  change signAttachedCoefficient (fixedRoughCoefficient (ordinaryRetainOdd L) N cap w Z d)
    (actualSmallRosserMinus N cap w B e) (actualSmallRosserPlus N cap w B e)=_
  rw [ordinary_rough_coefficient N cap w Z L hL d]
  rfl

/-- The precise model difference, derived from both actual constructions.
It must be controlled before the common beta coefficient can be used in
an argument already proved for the all-prime native arithmetic function. -/
theorem native_sub_presieved_coefficient {N cap e d : ℕ} {w Z L B : ℝ}
    (hwZ : w≤Z) (hL : 1<L) (he : e∈actualSmallRosserSupport N cap w)
    (hd : d∈fixedRoughSupport (ordinaryRetainOdd L) N cap w Z) :
    actualSmallRosserPlus N cap Z L (e*d)-presievedCoefficient N cap w Z L B (e*d)=
      roughWeight N cap w Z L d *
        (residualSmallWeight N cap w L d e-commonSmallWeight N cap w Z L B d e) := by
  rw [native_upper_residual_factor_on_support hwZ he (ordinary_rough_support_subset hL hd),
    presieved_coefficient_value hL he hd]
  ring

/-- In particular the exact already-defined JOINT sigma retains this
same explicit model difference at each actual ordinary branch. The full
physical four-prime prefix is unchanged. No new sigma is introduced. -/
theorem ordinary_same_sigma_presieved_difference {n N e d : ℕ} {eta : ℚ}
    (hN : 1<N) (heta : 0<eta) {E : ℕ×ℕ→Prop}
    {t : U1011OriginalSixteenArithmeticProducts.Four}
    (ht : t∈U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hp : (U1011OriginalSixteenStaticNativeCompiler.selectedPolicy n N t).val<15)
    {w B : ℝ} (hwZ : w≤U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (hL : 1<U1011OriginalSixteenJointNearCapCompiler.D n N eta t)
    (he : e∈actualSmallRosserSupport N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w)
    (hd : d∈fixedRoughSupport
      (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w
      (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) :
    U1011OriginalSixteenJointNearCapModulusConvolution.sigma n N eta E
        (U1011OriginalSixteenArithmeticProducts.fullPrefix t*(e*d)) -
      presievedCoefficient N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
        w (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
        (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) B (e*d) =
    roughWeight N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w
      (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
      (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) d *
      (residualSmallWeight N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
        w (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) d e -
       commonSmallWeight N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) w
        (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
        (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) B d e) := by
  have hdM := ordinary_rough_support_subset hL hd
  have hprod : e*d∈U1011OriginalSixteenJointNearCapCompiler.support n N eta t := by
    change e*d∈actualSmallRosserSupport N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
      (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    rw [nativeSupport_eq_products N _ hwZ]
    exact Finset.mem_image.mpr ⟨(e,d),Finset.mem_product.mpr ⟨he,hdM⟩,rfl⟩
  have hs := ordinary_sigma_on_native_support hN heta ht hp hprod
  change U1011OriginalSixteenJointNearCapModulusConvolution.sigma n N eta E
    (U1011OriginalSixteenArithmeticProducts.fullPrefix t*(e*d)) =
      actualSmallRosserPlus N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
        (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
        (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) (e*d) at hs
  rw [hs]
  exact native_sub_presieved_coefficient hwZ hL he hd

end
end ImbalancedChen.P5Z.OriginalOrdinaryCommonBetaModel
