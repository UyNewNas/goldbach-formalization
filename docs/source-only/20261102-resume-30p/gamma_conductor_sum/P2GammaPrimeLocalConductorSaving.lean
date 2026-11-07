import ImbalancedChen.P2GammaPrimitiveScaleThreshold
import ImbalancedChen.P2GammaSmallConductorIntervalBridge

/-!
SOURCE ONLY. UNCOMPILED. ZERO FORMAL CREDIT.

This consumes O's implemented variable-profile prime supplier. It never
assumes a Gamma discrepancy, an SW estimate or a low-conductor bound.
The complementary mass and both original L2 estimates remain physical
source obligations. No assertion about the full coupled Gamma weight or
its boundary/trim residuals is made here.
-/

namespace ImbalancedChen.P2GammaPrimeLocalConductorSaving
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set MeasureTheory
open P2GammaConvolutionLargeConductor P2GammaExactConductorRegrouping
open P2GammaDyadicConductorSum P2GammaConductorScaleThreshold
open P2GammaPrimitiveScaleThreshold P2GammaSmallConductorIntervalBridge
open P2GammaPrimeCharacterSW P2GammaPrimeTargetDeletion
open P2GammaVariablePrimeProfile P2GammaVariablePrimeSmallConductor
open P2GammaPrimeSmallConductorSum
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The SAME dyadic cutoff used by the high ledger lies in one fixed
logarithmic conductor range. This loss is paid before requesting prime
accuracy. H, and therefore the threshold, precedes every row and target. -/
theorem cutoff_le_log_power (H : ℕ) {x : ℝ}
    (hlog : (2 : ℝ)^(H+1)≤Real.log x) :
    (((2^(cutoffExponent (1+Real.log x) H) : ℕ) : ℝ))≤
      (Real.log x)^(H+1) := by
  have htwo : (1 : ℝ)≤2^(H+1) := one_le_pow₀ (by norm_num)
  have hl : 1≤Real.log x := htwo.trans hlog
  have hcut := (cutoffExponent_bounds (1+Real.log x) (by linarith) H).2
  have hcut' : (((2^(cutoffExponent (1+Real.log x) H) : ℕ) : ℝ))≤
      2*(1+Real.log x)^H := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hcut
  calc
    _ ≤ 2*(1+Real.log x)^H := hcut'
    _ ≤ 2*(2*Real.log x)^H := by gcongr; linarith
    _ = (2 : ℝ)^(H+1)*(Real.log x)^H := by rw [mul_pow,pow_succ]; ring
    _ ≤ Real.log x*(Real.log x)^H :=
      mul_le_mul_of_nonneg_right hlog (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- Complete local logarithmic saving at every real accuracy A for a
target-deleted original prime profile times a complementary row. Set
An=ceil(A). The real prime theorem is called at accuracy An+Hmass, AFTER
fixing the high cutoff H=An+C+3 and its conductor range B=H+1. Its internal
prime accuracy is consequently An+Hmass+2B+2.
One threshold precedes x,M,N, endpoints, profile, target, rows, Q and z.

This theorem deliberately displays the two original L2 bounds and the
complement's original L1 bound. They are not renamed discrepancy estimates.
No lower bound is imposed on the prime interval length v-u. -/
theorem exists_actual_prime_local_conductor_saving
    (A : ℝ) (C Hmass : ℕ) (eta epsilon J W Ctarget ea eb c em : ℝ)
    (heta : 0<eta) (hepsilon : 0<epsilon)
    (hW : 0≤W) (hCtarget : 0≤Ctarget)
    (hea : 0≤ea) (heb : 0≤eb) (hc : 0≤c) (hem : 0≤em) :
    ∃ K : ℝ,0<K ∧ ∃ x0 : ℝ,1<x0 ∧
      ∀ x M N u v : ℝ,x0≤x → M*N=x → x^eta≤M → x^eta≤N →
      M≤u → u≤v → v≤2*M →
      ∀ f : ℝ → ℂ,
      (∀ y∈Icc u v,DifferentiableAt ℝ f y) →
      IntegrableOn (deriv f) (Icc u v) →
      profileAbelNorm f u v≤W*Real.log x^J →
      (∀ y∈Icc u v,‖f y‖≤W*Real.log x^J) →
      ∀ target : ℕ,0<target → (target : ℝ)≤x^Ctarget →
      ∀ P V Q : ℕ,∀ T : Finset ℕ,∀ b : ℕ → ℂ,
      primeSWInterval u v⊆Finset.Icc 1 P → T⊆Finset.Icc 1 V →
      ∀ z : (q : ℕ) → ZMod q,
      let a := paddedRow (primeSWInterval u v)
        (targetDeleted target (profilePrimeCoefficient f))
      let beta := paddedRow T b
      rowEnergy a 0 P≤ea^2*M*(Real.log x)^C →
      rowEnergy beta 0 V≤eb^2*N*(Real.log x)^C →
      rowMass T b≤em*N*(Real.log x)^Hmass →
      (P : ℝ)≤c^2*M → (V : ℝ)≤c^2*N →
      (Q : ℝ)≤x^((1 : ℝ)/2-epsilon) →
      (∑ q ∈ Finset.Icc 1 Q,
        ‖rectangleCharacterDiscrepancy a beta 0 0 P V q (z q)‖)≤
        K*x/(Real.log x)^A := by
  let An : ℕ := Nat.ceil A
  obtain ⟨xh,hxh,hhigh⟩ := exists_primitive_high_conductor_threshold
    An C eta epsilon ea eb c heta hepsilon hea heb hc
  obtain ⟨Cs,hCs,xs,hxs,hsmall⟩ := variable_profile_small_conductors_logSaving
    heta hW hCtarget (by norm_num : (0 : ℝ)≤1)
    (J:=J) (A:=((An+Hmass : ℕ) : ℝ)) (B:=((An+C+4 : ℕ) : ℝ)) (D:=1)
  have hlogLarge : ∀ᶠ x : ℝ in atTop,(2 : ℝ)^(An+C+3+1)≤Real.log x :=
    tendsto_log_atTop.eventually_ge_atTop _
  obtain ⟨xc,hxc⟩ := eventually_atTop.mp hlogLarge
  let K := Cs*em+highCoefficient ea eb c+1
  have hK : 0<K := by
    have := highCoefficient_nonneg hea heb hc
    have := mul_nonneg hCs.le hem
    dsimp [K]
    linarith
  refine ⟨K,hK,max xh (max xs xc),hxh.trans_le (le_max_left _ _),?_⟩
  intro x M N u v hx hMN hMpower hNpower hlu huv hhi f hfd hfi hvar hsize
    target ht htarget P V Q T b hS hT z
  dsimp only
  intro hEa hEb hmass hP hV hQ
  let a := paddedRow (primeSWInterval u v)
    (targetDeleted target (profilePrimeCoefficient f))
  let beta := paddedRow T b
  let b0 := cutoffExponent (1+Real.log x) (An+C+3)
  have hxh' : xh≤x := (le_max_left _ _).trans hx
  have hxs' : xs≤x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxc' : xc≤x := (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hxgt : 1<x := hxh.trans_le hxh'
  have hxpos : 0<x := zero_lt_one.trans hxgt
  have hlog := hxc x hxc'
  have hL1 : 1≤Real.log x :=
    (one_le_pow₀ (by norm_num : (1 : ℝ)≤2)).trans hlog
  have hLpos : 0<Real.log x := zero_lt_one.trans_le hL1
  have hM : 1≤M := (Real.one_le_rpow hxgt.le heta.le).trans hMpower
  have hMpos : 0<M := zero_lt_one.trans_le hM
  have hNpos := (Real.rpow_pos_of_pos hxpos eta).trans_le hNpower
  have hcut : (((2^b0 : ℕ) : ℝ))≤Real.log x^((An+C+4 : ℕ) : ℝ) := by
    simpa only [b0,Real.rpow_natCast,show An+C+3+1=An+C+4 by omega] using
      cutoff_le_log_power (An+C+3) hlog
  have hQx : (Q : ℝ)≤x^((1 : ℝ)) := hQ.trans
    (Real.rpow_le_rpow_of_exponent_le hxgt.le (by linarith))
  have hlow0 := hsmall x M u v hxs' hMpower hM hlu huv hhi f hfd hfi hvar hsize
    target ht htarget (2^b0) Q hcut hQx T b
  have hlow : lowConductorTotal a beta 0 0 P V Q b0≤
      Cs*M*rowMass T b/(Real.log x)^(An+Hmass) := by
    rw [lowConductorTotal_eq_smallConductorContribution _ _ _ _ _ _ _ _ hS hT]
    simpa only [Real.rpow_natCast] using hlow0
  have hlowPaid : lowConductorTotal a beta 0 0 P V Q b0≤
      (Cs*em)*x/(Real.log x)^An := by
    refine hlow.trans ?_
    calc
      _ ≤ Cs*M*(em*N*(Real.log x)^Hmass)/(Real.log x)^(An+Hmass) := by gcongr
      _ = _ := by
        rw [pow_add,← hMN]
        field_simp [(pow_pos hLpos An).ne',(pow_pos hLpos Hmass).ne']
        <;> ring
  have hhighPaid : highConductorTotal a beta 0 0 P V Q b0≤
      highCoefficient ea eb c*x/(Real.log x)^An :=
    hhigh x hxh' M N hMN hMpower hNpower a beta 0 0 P V Q hP hV hEa hEb hQ
  have hsum := sum_rectangleCharacterDiscrepancy_norm_le a beta 0 0 P V Q z
  rw [allNonprincipalMajorant_eq_inducedTotal a beta 0 0 (by norm_num) (by norm_num),
    inducedTotal_eq_low_add_high a beta 0 0 P V Q b0] at hsum
  change (∑ q ∈ Finset.Icc 1 Q,
    ‖rectangleCharacterDiscrepancy a beta 0 0 P V q (z q)‖)≤K*x/(Real.log x)^A
  calc
    _ ≤ lowConductorTotal a beta 0 0 P V Q b0+
        highConductorTotal a beta 0 0 P V Q b0 := hsum
    _ ≤ (Cs*em)*x/(Real.log x)^An+
        highCoefficient ea eb c*x/(Real.log x)^An := add_le_add hlowPaid hhighPaid
    _ ≤ K*x/(Real.log x)^An := by
      have hbase : 0≤x/(Real.log x)^An := by positivity
      calc
        _ ≤ (Cs*em)*x/(Real.log x)^An+
            highCoefficient ea eb c*x/(Real.log x)^An+x/(Real.log x)^An :=
          le_add_of_nonneg_right hbase
        _ = _ := by dsimp [K]; ring
    _ ≤ K*x/(Real.log x)^A := by
      apply div_le_div_of_nonneg_left (mul_nonneg hK.le hxpos.le)
        (Real.rpow_pos_of_pos hLpos A)
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le hL1 (Nat.le_ceil A)

end
end ImbalancedChen.P2GammaPrimeLocalConductorSaving
