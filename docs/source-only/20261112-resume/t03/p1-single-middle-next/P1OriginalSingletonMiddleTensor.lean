import ImbalancedChen.P1OriginalSingletonMiddleWeight
import ImbalancedChen.P4BOriginalCollisionThirdFactor
import ImbalancedChen.P5OriginalPrimeAtlasReserveBranches

/-! Physical rectangular single-prime discrepancy. The free three-factor
coefficient is used only in the discrepancy. Each prime gives precisely
one original source point. The outer operator carries the full primitive
mean and the original moving residue. -/
namespace ImbalancedChen.P1OriginalSingletonMiddleTensor
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalCollisionWords (Params)
open P4AHeldTaggedCompilerSupport (J0)
open P4BOriginalFiniteSmoothCount (Q)
open P1OriginalSharpFiniteReceiver (middle)
open P4BOriginalCollisionTensor (products free bad)
open P4BOriginalCollisionThirdFactor (tensor tensor_eq)
open P4BOriginalCollisionKernel (row bound reindex Y full_difference kernel_power)
open P4BArbitraryWidthUpperBlockGeometry (countingScale scaleFactor scaleFactor_one_le target_le_countingScale)
open PrimeProducts.MellinInsertion20261028 (residueKernel exactDiscrepancy)
open P5CanonicalTentNarrowSingletonTransfer (smoothNatural fullSmoothWeight actualLicence)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy P5Z.OriginalPrimeAtlasReserveBranches
open P5Z.ExactOriginalSmoothDyadicPartition

private theorem prime_row (K N d : ℕ) (W : ℕ → ℝ) :
    row (chenPrimePrefix K) id (fun p => (W p:ℂ)) N d =
      (finitePrimitiveDiscrepancy (chenPrimePrefix K) W N d:ℂ) := by
  rw [finitePrimitiveDiscrepancy_eq_sum,Complex.ofReal_sum]
  unfold row
  apply Finset.sum_congr rfl
  intro p hp
  by_cases ha : p%d=N%d <;> by_cases hc : p.Coprime d <;>
    simp [id,residueKernel,Nat.ModEq,ha,hc,div_eq_mul_inv] <;> ring

private theorem real_pp (K N : ℕ) (S : Finset ℕ) (c W : ℕ→ℝ) :
    exactDiscrepancy (chenPrimePrefix K) S (fun d => (c d:ℂ)) id N (fun p => (W p:ℂ)) =
      (Part3.primeProductSignedError 1 K N S c (P5S1SingletonPP.singletonWeight K W):ℂ) := by
  rw [reindex,P5S1SingletonPP.primeProductSignedError_singleton_eq,Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun d _ => by rw [prime_row,Complex.ofReal_mul])

/-- The original prime at its own integer p, with its two-sided smooth
profile. Each nonempty fibre has one term, even at shared dyadic endpoints. -/
private theorem one_prime_fibre (kappa : ℝ) (N n : ℕ) :
    (∑ p ∈ (chenPrimePrefix (2*N)).filter (fun t => id t=n),
      ‖(smoothNatural kappa 6 N p:ℂ)‖) ≤ 1 := by
  simp only [id_eq,Finset.filter_eq']
  split_ifs
  · obtain ⟨h0,h1⟩ := P5CanonicalTentNarrowSingletonTransfer.smooth_range kappa 6 N n
    simpa only [Finset.sum_singleton,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg h0] using h1
  · simp

/-- Remove the true global square restriction for this independent smooth
prime itself. Omega and accuracy are fixed before the target. All
rectangular policy fields stay uniform after omega is fixed. -/
theorem eventually_singleton_collision (omega eta : ℝ) (ho : 0<omega) (hu : 0<eta) :
    ∀ᶠ N : ℕ in atTop, ∀ P : Params, P.N=N → P.omega=omega → 0≤P.e →
      P.ell+P.T*(J0 P.omega:ℝ)<1/1000 → ∀ kappa : ℝ,
      |Part3.primeProductSignedError 1 (2*N) N (products P) (free P) (fullSmoothWeight kappa 6 N)-
        Part3.primeProductSignedError 1 (2*N) N P.S P.rho (fullSmoothWeight kappa 6 N)| ≤
        eta*singularNormalization N := by
  let J := ((J0 omega).factorial : ℝ)
  let C := 2*(1+6*scaleFactor)
  have hJ : 0≤J := Nat.cast_nonneg _
  filter_upwards [kernel_power omega (omega/2) ho (half_pos ho),
    eventually_powerLog_le_singularNormalization (J*C) (1+omega/2-omega) 0 (by linarith) eta hu,
    eventually_ge_atTop (2:ℕ)] with N hK hscale hN
  intro P hPN hm he ht kappa
  subst N
  let W := smoothNatural kappa 6 P.N
  have hn : 0<(P.N:ℝ) := by exact_mod_cast (show 0<P.N by omega)
  have cap : 2*P.N≤Y P.N := by
    apply Nat.le_floor
    push_cast
    have hsc := target_le_countingScale P.N
    linarith
  have HH := full_difference P (by omega) he (by rwa [hm]) ht
    (chenPrimePrefix (2*P.N)) id (fun p => (W p:ℂ)) (Y P.N)
    (fun p hp => Finset.mem_Icc.mpr ⟨(mem_chenPrimePrefix.mp hp).2.pos,(mem_chenPrimePrefix.mp hp).1.trans cap⟩)
    (show (0:ℝ)≤1 by norm_num) (fun p _ => one_prime_fibre kappa P.N p)
  rw [real_pp,real_pp,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,hm,mul_one] at HH
  have hpow : (P.N:ℝ)*(P.N:ℝ)^(omega/2-omega) = (P.N:ℝ)^(1+omega/2-omega) := by
    conv_lhs => lhs; rw [←Real.rpow_one (P.N:ℝ)]
    rw [←Real.rpow_add hn]
    congr 1; ring
  have hk' := hK P rfl hm
  apply HH.trans
  calc
    _ ≤ J*(C*(P.N:ℝ)*(P.N:ℝ)^(omega/2-omega)) := mul_le_mul_of_nonneg_left hk' hJ
    _ = (J*C)*(P.N:ℝ)^(1+omega/2-omega) := by rw [←hpow]; ring
    _ ≤ _ := by simpa only [pow_zero,mul_one] using hscale

/-- Evaluate the three independent one-bounded arithmetic factors of the
current bank against the singleton's own primitive discrepancy.
The product a*b*t is the modulus in both terms of that discrepancy. -/
def singletonTensor (P : Params) (kappa x U eta : ℝ) :=
  tensor P x U eta (fun d => finitePrimitiveDiscrepancy (chenPrimePrefix (2*P.N))
    (smoothNatural kappa 6 P.N) P.N d)

theorem tensor_original_free (P : Params) (hN : 1<P.N) (kappa x U eta : ℝ) :
    singletonTensor P kappa x U eta =
      Part3.primeProductSignedError 1 (2*P.N) P.N (products P) (free P) (fullSmoothWeight kappa 6 P.N) := by
  rw [singletonTensor,tensor_eq P hN]
  exact (P5S1SingletonPP.primeProductSignedError_singleton_eq _ _ _ _ _).symm

/-- The complete modulus height is absent from the new factors. The
sharp signed receiver keeps the original complete modulus limits on
the left. The genuine collision and singleton smoothing each occur once. -/
theorem actual_middle_to_tensor (omega kappa eta : ℝ) (ho : 0<omega)
    (hk : 0<kappa) (hk1 : kappa<1) (hu : 0<eta) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ P : Params,P.N=N → P.omega=omega → 0≤P.e →
      P.ell<1/1000 → P.ell+P.T*(J0 P.omega:ℝ)<1/1000 → ∀ x U eps : ℝ,
      |middle N (Q P.omega N) P.rho-singletonTensor P kappa x U eps| ≤ eta*singularNormalization N := by
  filter_upwards [P1OriginalSingletonMiddleWeight.eventually_smooth kappa (eta/2) hk hk1 (half_pos hu),
    eventually_singleton_collision omega (eta/2) ho (half_pos hu),eventually_ge_atTop (2:ℕ)]
    with N hSm hC hN
  intro hev P hPN hm he hell ht x U eps
  subst N
  rw [tensor_original_free P (by omega)]
  have hs := hSm hev P rfl he (by rwa [hm]) hell ht
  have hc := hC P rfl hm he ht kappa
  apply (abs_sub_le _ (Part3.primeProductSignedError 1 (2*P.N) P.N P.S P.rho
    (fullSmoothWeight kappa 6 P.N)) _).trans
  rw [abs_sub_comm _ (Part3.primeProductSignedError 1 (2*P.N) P.N (products P) (free P) _)]
  linarith only [hs,hc]

/-- Use the independently constructed original one-group Heath--Brown
chart bank. K is the fixed rank bound, and every proper-power, chart
roughness and complete-product trim sign is retained. -/
def singletonAtlas (P : Params) (kappa : ℝ) (K : ℕ) (kappa0 zeta : ℝ) : ℂ :=
  let L := actualLicence kappa 6 P.N
  let S := products P
  let c := fun d => (free P d:ℂ)
  trimReserve L (2*P.N) P.N kappa0 S c +
    ∑ js ∈ chartBank (2*P.N) 1,
      (mediumAtlas L K (2*P.N) P.N kappa0 (originalMediumLow zeta js) (originalMediumHigh zeta js) S c js+
       noMediumAtlas L K (2*P.N) P.N kappa0 (originalMediumLow zeta js) (originalMediumHigh zeta js) S c js-
       properPowerReserve L K (2*P.N) P.N kappa0 S c js+
       roughPrimeReserve L K (2*P.N) P.N kappa0 S c js)

theorem tensor_to_singleton_atlas (P : Params) (hN : 1<P.N) (kappa x U eps : ℝ)
    (K : ℕ) (kappa0 zeta : ℝ) :
    (singletonTensor P kappa x U eps : ℂ)=singletonAtlas P kappa K kappa0 zeta := by
  rw [tensor_original_free P hN]
  exact original_prime_discrepancy_mode_carriers (actualLicence kappa 6 P.N) K (2*P.N) P.N kappa0 zeta
    (products P) (free P)

end
end ImbalancedChen.P1OriginalSingletonMiddleTensor
