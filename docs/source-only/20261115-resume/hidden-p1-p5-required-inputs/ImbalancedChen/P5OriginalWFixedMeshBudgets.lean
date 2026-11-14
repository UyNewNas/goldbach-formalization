import ImbalancedChen.P5OriginalWOwnerOccurrenceBinding
import ImbalancedChen.P5OriginalJointCommonBetaModel
import ImbalancedChen.P5ZU1011OriginalSixteenNearCapCommonSmallParameters

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Choose one rough fine-mesh precision after the finite prefix bank and
common beta are fixed, but before N, any physical mark, or any signed
discrepancy. The existing finite-bank ellMax pays the original W delta.
-/
namespace ImbalancedChen.P5Z.OriginalWFixedMeshBudgets
noncomputable section
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler
open U1011OriginalSixteenCommonSmallParameters (owner_mem_selected)
open U1011OriginalSixteenNearCapCommonSmallParameters
open OriginalCommonBetaActualParameters
open OriginalPresievedRoughRank
open OriginalJointPresievedArithmeticSupport
open OriginalOrdinaryCommonBetaModel
open OriginalWOwnerOccurrenceBinding

/-- This number depends on the fixed prefix bank, eta and the common beta
parameters only. It does not depend on N, the W owner, or the rough rank. -/
def roughMeshPrecision (n : ℕ) (eta : ℚ) (nu0 epsilon : ℝ) : ℕ :=
  Nat.ceil ((((rankBound nu0 epsilon : ℕ) : ℝ) + 3) * (59 / 250 : ℝ) /
    (ellMax n eta : ℝ))

/-- Every rank up to the common rank bound and every actual rough cutoff
under the original 59/250 wall fits the same mesh width budget. -/
theorem roughMeshPrecision_width {n r : ℕ} {eta : ℚ}
    (heta : 0 < eta) {nu0 epsilon rho zeta : ℝ}
    (hnu0 : 0 < nu0) (heps : 0 < epsilon)
    (hrank : r ≤ rankBound nu0 epsilon)
    (hrho : 0 ≤ rho) (hzeta : zeta ≤ (59 / 250 : ℝ)) :
    ((r : ℝ) + 3) *
      logPrimeMeshStep rho zeta (roughMeshPrecision n eta nu0 epsilon) ≤
        (ellMax n eta : ℝ) := by
  have he : (0 : ℝ) < (ellMax n eta : ℝ) := by
    exact_mod_cast ellMax_pos n eta heta
  have hrc : (r : ℝ) ≤ (rankBound nu0 epsilon : ℝ) := by exact_mod_cast hrank
  have hceil : (((rankBound nu0 epsilon : ℕ) : ℝ) + 3) * (59 / 250 : ℝ) /
      (ellMax n eta : ℝ) ≤ roughMeshPrecision n eta nu0 epsilon := by
    exact Nat.le_ceil _
  have hwidth : zeta - rho ≤ (59 / 250 : ℝ) := by linarith
  have hden : (0 : ℝ) < (roughMeshPrecision n eta nu0 epsilon : ℝ) + 1 := by positivity
  unfold logPrimeMeshStep
  apply (div_le_iff₀ hden).mpr
  have hnum : ((r : ℝ) + 3) * (zeta - rho) ≤
      ((rankBound nu0 epsilon : ℕ) : ℝ) * (59 / 250 : ℝ) + 3 * (59 / 250 : ℝ) := by
    calc
      _ ≤ ((r : ℝ) + 3) * (59 / 250 : ℝ) :=
        mul_le_mul_of_nonneg_left hwidth (by positivity)
      _ ≤ (((rankBound nu0 epsilon : ℕ) : ℝ) + 3) * (59 / 250 : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith [hrc]) (by norm_num)
      _ = _ := by ring
  have hcap : (((rankBound nu0 epsilon : ℕ) : ℝ) + 3) * (59 / 250 : ℝ) ≤
      (roughMeshPrecision n eta nu0 epsilon : ℝ) * (ellMax n eta : ℝ) := by
    exact (div_le_iff₀ he).mp hceil
  nlinarith

/-- The strict rho<zeta comparison follows from the actual epsilonBudget
and the selected finite-bank cutoff, including the distinct W branch. -/
theorem active_W_rho_lt_zeta {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) {nu0 epsilon : ℝ}
    (hnu0 : 0 < nu0) (heps : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu0)
    {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hW : selectedPolicy n N t = wPolicy) :
    nu0 * epsilon ^ 2 <
      (U1011OriginalW16NearCapNative.cutoffExponent (ownerBox n N t) eta : ℝ) := by
  have htag := (Finset.mem_filter.mp ht).2
  have hj := owner_mem_selected htag
  have hcut : (cutoffMin n eta : ℝ) ≤
      (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
        (selectedPolicy n N t) (ownerBox n N t) eta : ℝ) := by
    exact_mod_cast cutoffMin_le_cell eta _ hj
  rw [hW] at hcut
  have hnative : (U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent
      wPolicy (ownerBox n N t) eta : ℝ) =
      (U1011OriginalW16NearCapNative.cutoffExponent (ownerBox n N t) eta : ℝ) := by
    simp [U1011OriginalSixteenNearCapBoxProfiles.cutoffExponent,
      U1011OriginalSixteenNearCapBoxProfiles.physicalResidual,
      U1011OriginalSixteenNearCapBoxProfiles.nu,
      U1011OriginalSixteenNearCapBoxProfiles.delta,
      U1011OriginalSixteenNearCapBoxProfiles.xi,
      U1011OriginalSixteenNearCapBoxProfiles.rho,
      U1011OriginalSixteenNearCapBoxProfiles.G,
      U1011OriginalW16NearCapNative.cutoffExponent,
      U1011OriginalW16NearCapNative.residualExponent,
      U1011OriginalW16NearCapNative.nu,
      U1011OriginalW16NearCapNative.delta,
      U1011OriginalW16NearCapNative.xi,
      U1011OriginalW16NearCapNative.rho,
      U1011OriginalSixteenNearCapBoxProfiles.Tplus,
      U1011OriginalW16FixedCellNative.Tplus,
      U1011OriginalFifteenFixedCellNative.Tplus, wPolicy]
  rw [hnative] at hcut
  have he8 : epsilon < 1 / 8 := heBudget.trans_le (min_le_left _ _)
  have hecut : epsilon < (cutoffMin n eta : ℝ) / nu0 :=
    heBudget.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hlinear : nu0 * epsilon < (cutoffMin n eta : ℝ) :=
    (lt_div_iff₀ hnu0).mp hecut
  have hsquare : epsilon ^ 2 < epsilon := by nlinarith
  nlinarith

/-- The same precision is small against the actual selected W delta,
not a fabricated second cell parameter. -/
theorem active_W_mesh_width_le_delta {n N r : ℕ} {eta : ℚ}
    (heta : 0 < eta) {nu0 epsilon rho zeta : ℝ}
    (hnu0 : 0 < nu0) (heps : 0 < epsilon)
    (hrank : r ≤ rankBound nu0 epsilon)
    (hrho : 0 ≤ rho) (hzeta : zeta ≤ (59 / 250 : ℝ))
    {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hW : selectedPolicy n N t = wPolicy) :
    ((r : ℝ) + 3) *
      logPrimeMeshStep rho zeta (roughMeshPrecision n eta nu0 epsilon) ≤
        (U1011OriginalSixteenNearCapBoxProfiles.delta wPolicy
          (ownerBox n N t) eta : ℝ) := by
  have htag := (Finset.mem_filter.mp ht).2
  have hj := owner_mem_selected htag
  have hdelta : (ellMax n eta : ℝ) ≤
      (U1011OriginalSixteenNearCapBoxProfiles.delta wPolicy
        (ownerBox n N t) eta : ℝ) / 2 := by
    have h := ellMax_le_cell eta _ hj
    rw [show cellDelta n eta (owner n (coordinates N t)) =
      U1011OriginalSixteenNearCapBoxProfiles.delta wPolicy
        (ownerBox n N t) eta by
          simp [cellDelta, selectedPolicy, ownerBox, hW]] at h
    exact_mod_cast h
  have hw := roughMeshPrecision_width heta hnu0 heps hrank hrho hzeta
  linarith

/-- The native W prime ceiling is below the third padded upper prefix
coordinate. This uses the actual fourth prefix prime and fixed owner order. -/
theorem active_W_cutoff_le_u2 {n N : ℕ} (hN : 1 < N)
    {eta : ℚ} (heta : 0 < eta) {E : ℕ × ℕ → Prop}
    {t : Four} (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hW : selectedPolicy n N t = wPolicy) :
    (U1011OriginalW16NearCapNative.cutoffExponent (ownerBox n N t) eta : ℝ) ≤
      paddedOwnerCorner (ownerBox n N t) eta 2 := by
  have hlegal := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht
  have hZ : U1011OriginalSixteenJointNearCapCompiler.Z n N eta t =
      U1011OriginalW16NearCapNative.Z (ownerBox n N t) eta N := by
    change U1011OriginalSixteenJointNearCapCompiler.rowZ
      (selectedPolicy n N t) (ownerBox n N t) eta N = _
    rw [hW]
    exact (U1011OriginalSixteenJointNearCapCompiler.W_native_binding
      (ownerBox n N t) eta N).1
  obtain ⟨_,_,_,_,_,_,_,hu32,hsize⟩ :=
    active_W_owner_padded_corner hN heta ht hW
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hpow : (N : ℝ) ^
      (U1011OriginalW16NearCapNative.cutoffExponent (ownerBox n N t) eta : ℝ) ≤
      (N : ℝ) ^ (paddedOwnerCorner (ownerBox n N t) eta 3) := by
    exact (by simpa only [U1011OriginalW16NearCapNative.Z] using
      (hZ ▸ hlegal.2.2.1)).trans (hsize 3)
  exact ((Real.rpow_le_rpow_left_iff hn).mp hpow).trans hu32

/-- The rank belongs to the same active joint mark and same retained d.
It is obtained from the physical 153/256 modulus cap and the rough
small-prime floor, without selecting a possibly different mark preimage. -/
theorem active_joint_mark_rough_rank {n N r e d : ℕ} {eta : ℚ}
    {nu0 epsilon : ℝ} (hN : 1 < N) (heta : 0 < eta)
    (hnu0 : 0 < nu0) (heps : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu0)
    (E : ℕ × ℕ → Prop) {t : Four}
    (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (her : r = e * d) (hepos : 0 < e)
    (hd : d ∈ fixedRoughSupport
      (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
      ((N : ℝ) ^ (nu0 * epsilon ^ 2))
      (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
    (hq : ImbalancedChen.P5Z.OriginalJointPresievedCompiler.jointPresievedSigma n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2))
      ((N : ℝ) ^ (nu0 * epsilon)) E (fullPrefix t * r) ≠ 0) :
    d.primeFactors.card ≤ rankBound nu0 epsilon := by
  have hs := (Finset.mem_filter.mp ht).1
  have hprefix : 0 < fullPrefix t := by
    rw [fullPrefix_eq_multiplier]
    exact joint_multiplier_pos hs
  have hdq : d ≤ fullPrefix t * r := by
    rw [her]
    nlinarith
  have hsupport := actual_joint_arithmetic_support hN heta hnu0 heps
    heBudget E hq
  have hrough := P4ASpliceDifferenceLowerModulus.retained_pow_primeFactors_card_le
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
    (Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le N) : (0 : ℝ) ≤ N) _)
    (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) hd
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := zero_lt_one.trans hn
  have hrho : 0 < nu0 * epsilon ^ 2 := mul_pos hnu0 (sq_pos_of_pos heps)
  have hpow : (N : ℝ) ^ ((nu0 * epsilon ^ 2) * (d.primeFactors.card : ℝ)) ≤
      (N : ℝ) ^ (5 / 8 : ℝ) := by
    rw [Real.rpow_mul hn0.le, Real.rpow_natCast]
    have hdreal : (d : ℝ) ≤ fullPrefix t * r := by exact_mod_cast hdq
    exact hrough.trans (hdreal.trans (hsupport.2.2.2.2.le.trans
      (Real.rpow_le_rpow_of_exponent_le hn.le (by norm_num))))
  have hc := (Real.rpow_le_rpow_left_iff hn).mp hpow
  unfold rankBound actualRoughVectorRankBound
  apply (Nat.le_floor_iff (div_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 8) hrho.le)).mpr
  apply (le_div_iff₀ hrho).mpr
  simpa only [mul_comm] using hc

end
end ImbalancedChen.P5Z.OriginalWFixedMeshBudgets
