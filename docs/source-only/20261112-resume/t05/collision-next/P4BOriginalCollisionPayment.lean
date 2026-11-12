import ImbalancedChen.P4BOriginalCollisionRetained
import ImbalancedChen.P4BOriginalCollisionThirdFactor

/-! Original (T) and (C) for the signed, retained medium/no-medium sum.
The physical density is evaluated on the original squarefree coefficient.
Only its discrepancy is replaced by an unrestricted three-factor tensor.
The positive presieve exponent is fixed before the eventual target. -/
namespace ImbalancedChen.P4BOriginalCollisionPayment
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionTensor (products free)
open P4BOriginalCollisionRetained (exists_band_power)
open P4BOriginalHighRankScheduledCount (outerWidth eventually_width)
open P4BOriginalHighRankPostModulusCount (band exists_trimmed_RealB_le_band)
open P4BOriginalFiniteSmoothCount (mass Q)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BArbitraryWidthUpperBlockGeometry (countingScale countingScale_one_le)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P4AHeldTaggedCompilerSupport (J0)
open P4BOuterRampRoughness (baseline)

/-- The existing extra margin of the Fine common coefficient can be set
to 1/2000 before beta and k. That single choice suffices also for the
unrestricted tensor boxes, including their nonsquarefree points. -/
theorem fine_budget (P : Params) (hell : P.ell<(1/2000:ℝ)/32)
    (ht : P.T*((J0 P.omega:ℝ)+1)≤1/2000) : P.ell+P.T*(J0 P.omega:ℝ)<1/1000 := by
  have hp := P.T_pos
  linarith only [hell,ht,hp,mul_add P.T (J0 P.omega:ℝ) 1,mul_one P.T]

/-- The total debit on the fixed full band is arbitrary in the singular
normalisation. Accuracy A affects the common frequency cube. -/
theorem eventually_collision_paid (omega : ℝ) (ho : 0<omega) {b kap : ℝ}
    (hb : 0<b) (hb1 : b≤1) (hk : 0<kap) (hg : 19/96<baseline b kap)
    (eta : ℝ) (heta : 0<eta) :
    ∀ᶠ N : ℕ in atTop,∀ P : Params,P.N=N → P.omega=omega → 0≤P.e →
    P.ell+P.T*(J0 P.omega:ℝ)<1/1000 → ∀ (K A : ℕ) (kap0 zeta : ℝ),
      ‖band b kap N K A kap0 zeta (products P) (free P)-band b kap N K A kap0 zeta P.S P.rho‖≤
        eta*singularNormalization N := by
  obtain ⟨C,hC,H⟩ := exists_band_power omega (omega/2) ho (half_pos ho)
  have hz : 1-omega+omega/2<1 := by linarith
  filter_upwards [H hb hb1 hk hg,eventually_width 1 (by norm_num),
    eventually_powerLog_le_singularNormalization (C*2^51) (1-omega+omega/2) 51 hz eta heta] with N hbnd hw hfee
  intro P hp hom he ht K A kap0 zeta
  have hl := logScale_one_le (countingScale_one_le (N:=N) (by have := hw.1; omega))
  apply (hbnd P hp hom he ht K A kap0 zeta).trans
  have hpow := pow_le_pow_left₀ (zero_le_one.trans hl) hw.2.2.2.2 51
  apply (mul_le_mul_of_nonneg_left hpow
    (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg N) _))).trans
  rw [mul_pow]
  calc
    _=(C*2^51)*(N:ℝ)^(1-omega+omega/2)*Real.log (N:ℝ)^51 := by ring
    _≤_ := hfee

/-- This is the actual counted inequality after globally removing all
rough-square collisions. No arithmetic estimate for the remaining
unrestricted band is an input. -/
theorem exists_RealB_le_free_band {b kappa : ℝ} (hb : (1:ℝ)/2<b) (hb1 : b<1)
    (hk : 0<kappa) (cap : ℝ) (hcap : 0<cap) :
    ∃ kap0 : ℝ,0<kap0 ∧ kap0<cap ∧ kap0<1 ∧ kap0<kappa/(4*(1+kappa)) ∧ 19/96<baseline b kap0 ∧
    ∀ (K : ℕ),2≤K → ∀ (eta nu beta : ℝ),0<eta → 0<nu → 0<beta → beta≤1 →
    nu*beta^2≤19/96 → nu*beta<(1/2000:ℝ)/32 →
    ∀ᶠ N : ℕ in atTop,Even N →
      0≤mass b kap0 (outerWidth N) N ∧
      |mass b kap0 (outerWidth N) N/((N:ℝ)/Real.log (N:ℝ))-Real.log (1/b)|<eta ∧
      ∀ (zeta : ℝ) (m r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (k : ℕ),0≤e →
      let omega := nu*beta^2
      let P : Params := ⟨m,r,n,e,q,a,omega,k,N,nu*beta⟩
      P.T*((J0 omega:ℝ)+1)≤1/2000 →
        (RealB b N:ℝ)≤mass b kap0 (outerWidth N) N*physicalDensitySum (Q omega N) P.rho+
          (band b kap0 N K 0 kap0 zeta (products P) (free P)).re+eta*singularNormalization N := by
  obtain ⟨kap0,ht,hcap',h1,hk0,hg,H⟩ := exists_trimmed_RealB_le_band hb hb1 hk cap hcap
  refine ⟨kap0,ht,hcap',h1,hk0,hg,?_⟩
  intro K hK eta nu beta heta hnu hb0 hb2 hrough hbeta
  let omega := nu*beta^2
  have ho : 0<omega := by dsimp [omega]; positivity
  filter_upwards [H K hK (eta/2) (half_pos heta),eventually_collision_paid omega ho
    (by linarith : 0<b) hb1.le ht hg (eta/2) (half_pos heta),eventually_ge_atTop (2:ℕ)] with N Hc Hf hN
  intro hev
  obtain ⟨hn,happ,hcount⟩ := Hc hev
  refine ⟨hn,happ.trans (by linarith),?_⟩
  intro zeta m r n e q a k he
  let P : Params := ⟨m,r,n,e,q,a,omega,k,N,nu*beta⟩
  change P.T*((J0 omega:ℝ)+1)≤1/2000 → _
  intro hmesh
  have hbudget := fine_budget P hbeta hmesh
  have hclass (d : ℕ) (hd : P.rho d≠0) : (d:ℝ)<(N:ℝ)^modulusExponent :=
    P4BOriginalCollisionPhysical.supported_physical P (by change 1<N; omega) he ho (by change nu*beta<1/1000; linarith) hbudget hd
  have hp := Hf P rfl rfl he hbudget K 0 kap0 zeta
  let old := band b kap0 N K 0 kap0 zeta P.S P.rho
  let new := band b kap0 N K 0 kap0 zeta (products P) (free P)
  have hnorm : ‖old-new‖≤eta/2*singularNormalization N := (norm_sub_rev old new).le.trans hp
  have hs : old.re-new.re≤eta/2*singularNormalization N := (Complex.re_le_norm (old-new)).trans hnorm
  have hc := hcount zeta m r n e q a k nu beta hnu hb0 hb2 hrough (by linarith) hclass
  change (RealB b N:ℝ)≤mass b kap0 (outerWidth N) N*physicalDensitySum (Q omega N) P.rho+
    old.re+eta/2*singularNormalization N at hc
  change (RealB b N:ℝ)≤mass b kap0 (outerWidth N) N*physicalDensitySum (Q omega N) P.rho+
    new.re+eta*singularNormalization N
  linarith only [hs,hc]

end
end ImbalancedChen.P4BOriginalCollisionPayment
