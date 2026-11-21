import ImbalancedChen.P4BOriginalActualNativeLocalPayment

/-! SOURCE ONLY / UNCOMPILED. Transfer the actual complete scale to N.
Only the proved live geometry is used; the fixed local constant is paid
later, after the actual mother norm and HB scalar mass have been fixed. -/
namespace ImbalancedChen.P4BOriginalNativeTargetPayment
noncomputable section
open Classical Filter Set
open P4BOriginalNoMediumPairRows
open P4BOriginalActualNativeLocalPayment
open P4BOriginalSharpNativeRow (nativeMode)
open P4BOriginalTwoLongExpandedCore (rho)
open P4BOriginalHighRankMotherScale (completeScale live_geometry)
open P4BOriginalHighRankPostModulusRow (H)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BUpperPairOrderedRowGeometry
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle)
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCutoff)
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff)
open P5Z.AllRankCauchyCubeTail (outsideCube)
open P4BOuterRampRoughness (baseline)

def localConstant (A : ℕ) : ℝ := Real.exp 1*2^A

theorem localConstant_nonneg (A : ℕ) : 0≤localConstant A := by unfold localConstant; positivity

theorem complete_to_target (A N : ℕ) {x kappa : ℝ} (hN : 1<(N:ℝ))
    (hx : 1<x) (hk : kappa≤1) (hNx : (N:ℝ)≤x^(1+kappa)) (hxN : x≤Real.exp 1*N) :
    x/(Real.log x)^A≤localConstant A*N/(Real.log (N:ℝ))^A := by
  have hlN := Real.log_pos hN
  have hlx := Real.log_pos hx
  have hlog : Real.log (N:ℝ)≤2*Real.log x := by
    have H := Real.log_le_log (zero_lt_one.trans hN) hNx
    rw [Real.log_rpow (zero_lt_one.trans hx)] at H
    exact H.trans (mul_le_mul_of_nonneg_right (by linarith) hlx.le)
  calc
    _≤(Real.exp 1*N)/(Real.log x)^A := div_le_div_of_nonneg_right hxN (pow_nonneg hlx.le _)
    _=(Real.exp 1*N*2^A)/(2*Real.log x)^A := by rw [mul_pow]; field_simp [hlx.ne']; ring
    _≤(Real.exp 1*N*2^A)/(Real.log (N:ℝ))^A :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hlN _)
        (pow_le_pow_left₀ hlN.le hlog A)
    _=_ := by unfold localConstant; ring

theorem eventually_native_target_paid (K A0 A : ℕ)
    {zeta kappa kap0 : ℝ} (hz : 0<zeta) (hz1 : zeta≤1/400)
    (hk : 0<kappa) (hkz : kappa≤zeta/10000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop,∀ {b kap s : ℝ},0<b → 0<kap → 0<s → 2*s≤baseline b kap-19/96 →
      ∀ (j l cj ck : ℕ),j∈Finset.range 3 → l∈Finset.range 3 →
      ∀ (bs : Fin (2*(j+1))→Block) (cs : Fin (2*(l+1))→Block),
      noMedium zeta cj ck (Fin.append bs cs) →
      live b kap s N kap0 cj ck (Fin.append bs cs) (beforeHBCutoff K [cj,ck])
        (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
        (Fin.append (rowRoles j) (rowRoles l)) →
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ),
      (∀ d,coefficient m r n e q a omega k N ((N:ℝ)^ell) d≠0 →
        (d:ℝ)<(N:ℝ)^modulusExponent) →
      ∀ S : Finset ℕ,S⊆Q omega N →
      ∀ xi : Fin (2*(j+1)+2*(l+1))→ℝ,xi∈(outsideCube _ (H N A0))ᶜ →
      ‖nativeMode (Fin.append bs cs) (beforeHBCutoff K [cj,ck])
        (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck)) xi
        (Fin.append (rowRoles j) (rowRoles l)) N S (rho m r n e q a omega k N ((N:ℝ)^ell))‖≤
          localConstant A*N/(Real.log (N:ℝ))^A := by
  have hk1 : kappa≤1 := by linarith
  filter_upwards [eventually_actual_native_mode_paid K A0 A hz hz1 hk hkz ht ht1,
    eventually_ge_atTop (2:ℕ)] with N Hlocal hN
  intro b kap s hb hkap hs hg j l cj ck hj hl bs cs hnone hlive
  obtain ⟨i1,i2,hchoose1,hchoose2,y,hy,hactive,hik,hcard,hrole1,hrole2,hx,hNx,
    hU,hV,hprod,hUmin,hVmin,hpaid⟩ := Hlocal hb hkap hs hg j l cj ck hj hl bs cs hnone hlive
  have hw : integerProfile (a:=2*(j+1)) (d:=2*(l+1)) b kap s N kap0 cj ck y≠0 := by
    intro hzero
    exact (mul_ne_zero_iff.mp hactive).2 (by rw [hzero]; rfl)
  have hgeom := live_geometry (show 0<N by omega) hb hkap hs hg cj ck (Fin.append bs cs) y
    (Fin.castAdd (2*(l+1)) i1) hy hw
  have hscale := complete_to_target A N (by exact_mod_cast (show 1<N by omega)) hx hk1 hNx hgeom.2.1
  intro m r n e q a omega k ell hRange S hS xi hxi
  exact ((hpaid m r n e q a omega k ell hRange S hS xi hxi).2.2).trans hscale

end
end ImbalancedChen.P4BOriginalNativeTargetPayment
