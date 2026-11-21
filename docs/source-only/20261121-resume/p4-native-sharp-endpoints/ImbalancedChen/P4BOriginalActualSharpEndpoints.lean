import ImbalancedChen.P4BOriginalSharpEndpointPrices

/-! SOURCE ONLY / UNCOMPILED. The native two-mother sharp row minus
the upper/upper rough-smooth row, with the original q, signed rho,
before-HB Z and actual Brun order. Accuracy fixes B=A+40 before N.
This is only the two local endpoint errors; no mother integration. -/
namespace ImbalancedChen.P4BOriginalActualSharpEndpoints
noncomputable section
open Classical Filter Set
open scoped BigOperators
open P4BOriginalNoMediumPairRows
open P4BOriginalTwoLongActualScales
open P4BOriginalTwoLongActualAssignment (eventually_actual_pair_assignment)
open P4BOriginalPairMeanGeometry (actual_MUV eventually_native_long_lengths)
open P4BOriginalSharpEndpointPrices (endpointOrder eventually_endpoint_invoice_paid)
open P4BOriginalSharpPairComparison (sharpDifference finite_endpoint_invoice)
open P4BOriginalSharpNativeRow (nativeMode nativeMode_eq_sharpSum)
open P4BOriginalRoughE3Assembly (roughSum)
open P4BOriginalTwoLongExpandedCore (rho)
open P4BOriginalHighRankLocalLevel (theta)
open P4BOriginalHighRankMotherScale (completeScale)
open P4BOriginalHighRankPostModulusRow (H)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BUpperPairOrderedRowGeometry
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle)
open P5Z.ActualHBPostModulusLogCutoff (hbSlots)
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCutoff)
open P5Z.ExactOriginalSmoothDyadicPartition (R beforeHBCutoff)
open P5Z.ActualHBRoughBrunRates (halfOrder)
open P5Z.AllRankCauchyCubeTail (outsideCube)
open Part3.TwoLongActualHBShortMass (ShortPositions shortScale shortSupport shortSequence shortSequence_mass)
open Part3.TwoLongTransitionMellinN2 (profile)
open P4BOuterRampRoughness (baseline)

/-- Local endpoint payment for the two actual full right-closed HB blocks.
The independent outer mother smoothing order is not an argument here;
`A` is the requested local accuracy and fixes the inner order before N.
No arbitrary subinterval or integrated mother estimate is asserted. -/
theorem eventually_actual_sharp_endpoints_paid (K A0 A : ℕ)
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
      ∃ i1 : Fin (2*(j+1)),∃ i2 : Fin (2*(l+1)),
      i1=chooseLong (by omega) ((R cj*R ck)^(1/3+zeta/4:ℝ)) bs ∧
      i2=chooseLong (by omega) ((R cj*R ck)^(1/3+zeta/4:ℝ)) cs ∧
      ∃ y∈rectangle (Fin.append bs cs),
      hbSlots (beforeHBCutoff K [cj,ck])
        (Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck))
        (Fin.append (rowRoles j) (rowRoles l)) y *
        (integerProfile (a:=2*(j+1)) (d:=2*(l+1)) b kap s N kap0 cj ck y:ℂ)≠0 ∧
      let blocks := Fin.append bs cs
      let i := Fin.castAdd (2*(l+1)) i1
      let t := Fin.natAdd (2*(j+1)) i2
      let x := completeScale blocks y i
      let U := (lower (blocks i):ℝ)
      let V := (lower (blocks t):ℝ)
      let Z := beforeHBCutoff K [cj,ck]
      let allY := Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck)
      let roles := Fin.append (rowRoles j) (rowRoles l)
      let bS := fun a : ShortPositions i t => blocks a.val
      let ys := fun a : ShortPositions i t => allY a.val
      let rs := fun a : ShortPositions i t => roles a.val
      i≠t ∧ Fintype.card (ShortPositions i t)≤10 ∧
      (roles i=.one ∨ roles i=.logarithm) ∧ (roles t=.one ∨ roles t=.logarithm) ∧
      1<U ∧ 1<V ∧ (shortScale bS:ℝ)*U*V≤4*x ∧ x^(1/3:ℝ)≤U ∧ x^(1/3:ℝ)≤V ∧
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ),
      (∀ d,coefficient m r n e q a omega k N ((N:ℝ)^ell) d≠0 →
        (d:ℝ)<(N:ℝ)^modulusExponent) →
      ∀ S : Finset ℕ,S⊆Q omega N →
      ∀ xi : Fin (2*(j+1)+2*(l+1))→ℝ,xi∈(outsideCube _ (H N A0))ᶜ →
      let delta := ((Real.log x)^(endpointOrder A))⁻¹
      let fLog := decide (roles i=.logarithm)
      let gLog := decide (roles t=.logarithm)
      ‖nativeMode blocks Z allY xi roles N S (rho m r n e q a omega k N ((N:ℝ)^ell))-
        roughSum (profile false fLog delta U (xi i)) (profile false gLog delta V (xi t))
          U V Z (shortSupport bS) (shortSequence bS Z ys (fun a => xi a.val) rs)
          m r n e q a omega k N ((N:ℝ)^ell) S‖≤x/(Real.log x)^A := by
  let B := endpointOrder A
  have hB : 1≤B := by dsimp [B,endpointOrder]; omega
  have hX := (eventually_endpoint_invoice_paid A hz1).and
    ((Part3.TwoLongMellinLogBudget.eventually_schedule B hB).and
      (Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)))
  obtain ⟨x0,Hx⟩ := eventually_atTop.mp hX
  filter_upwards [eventually_actual_pair_assignment K B A0 0 hB hz hz1 hk hkz ht ht1,
    eventually_native_long_lengths hz hz1 ht1,eventually_live_large ht1 x0]
    with N hassign hlong hlarge
  intro b kap s hb hkap hs hg j l cj ck hj hl bs cs hnone hLive
  obtain ⟨i1,i2,hchoose1,hchoose2,y,hy,hactive,hik,hcard,hrole1,hrole2,hx,hD,hDx,hZ,hMpow,
      hyPower,hends,hU,hV,hUx,hVx,hcaller⟩ := hassign hb hkap hs hg j l cj ck hj hl bs cs hnone hLive
  let blocks := Fin.append bs cs
  let i := Fin.castAdd (2*(l+1)) i1
  let t := Fin.natAdd (2*(j+1)) i2
  let x := completeScale blocks y i
  let U : ℝ := lower (blocks i)
  let V : ℝ := lower (blocks t)
  let Z := beforeHBCutoff K [cj,ck]
  let D := Nat.floor (x^theta)
  let allY := Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck)
  let roles := Fin.append (rowRoles j) (rowRoles l)
  let bS := fun a : ShortPositions i t => blocks a.val
  let ys := fun a : ShortPositions i t => allY a.val
  let rs := fun a : ShortPositions i t => roles a.val
  let M : ℝ := shortScale bS
  let Y := Z^(2*halfOrder x+1)
  have hw : integerProfile (a:=2*(j+1)) (d:=2*(l+1)) b kap s N kap0 cj ck y≠0 := by
    intro hzero
    exact (mul_ne_zero_iff.mp hactive).2 (by rw [hzero]; rfl)
  have hlongs := hlong hb hkap hs hg j l cj ck hj hl bs cs y hy hw hnone i1 i2 hchoose1 hchoose2
  have hprod := actual_MUV blocks y hy i t hik
  have hxl := (hlarge hb hkap hs hg _ _ cj ck blocks y i hy hw).1
  obtain ⟨hpay,hSched,hlog⟩ := Hx x hxl
  have hroot : 1<x^(1/3:ℝ) := Real.one_lt_rpow hx (by norm_num)
  have hU1 : 1<U := hroot.trans hlongs.1
  have hV1 : 1<V := hroot.trans hlongs.2
  have hM : 0≤M := Nat.cast_nonneg _
  have hY : 0≤Y := pow_nonneg (zero_le_one.trans hZ) _
  have hYx : Y≤x := hyPower.trans (by simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hx.le (show brunEpsilon≤1 by norm_num [brunEpsilon]))
  refine ⟨i1,i2,hchoose1,hchoose2,y,hy,hactive,hik,hcard,hrole1,hrole2,hU1,hV1,hprod,hlongs.1.le,hlongs.2.le,?_⟩
  intro m r n e q a omega k ell hRange S hS xi hxi
  obtain ⟨hDlevel,_⟩ := hcaller m r n e q a omega k ell hRange S hS
  let alpha := shortSequence bS Z ys (fun a => xi a.val) rs
  let mu := ∑ short∈shortSupport bS,‖alpha short‖
  let delta := ((Real.log x)^B)⁻¹
  have hmu : 0≤mu := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hmub : mu≤4096*M*(Real.log x)^12 := by
    have H0 := shortSequence_mass bS Z ys (fun a => xi a.val) rs hx.le hends
    have H1 := P4BOriginalTwoLongExpandedCore.short_log_budget
      (by omega : Fintype.card (ShortPositions i t)≤12) hlog
    exact H0.trans ((mul_le_mul_of_nonneg_left H1 hM).trans_eq (by dsimp [M]; ring))
  let fLog := decide (roles i=.logarithm)
  let gLog := decide (roles t=.logarithm)
  have hfinite := finite_endpoint_invoice fLog gLog hSched.2.1 hSched.2.2
    (zero_lt_one.trans_le hU) (zero_lt_one.trans_le hV) hZ hx.le (xi i) (xi t) (halfOrder x) hYx
    (shortSupport bS) alpha m r n e q a omega k N D ((N:ℝ)^ell) S hS hDlevel
  have hpaid := hpay U V Y M mu D hU hV hUx hVx hD hDx hM hMpow hY hyPower hmu hmub
    hprod hlongs.1.le hlongs.2.le hSched.2.1 hSched.2.2
  have H := hfinite.trans hpaid
  change ‖nativeMode blocks Z allY xi roles N S (rho m r n e q a omega k N ((N:ℝ)^ell))-
    roughSum (profile false fLog delta U (xi i)) (profile false gLog delta V (xi t))
      U V Z (shortSupport bS) alpha m r n e q a omega k N ((N:ℝ)^ell) S‖≤_
  rw [nativeMode_eq_sharpSum blocks Z allY xi roles i t hik hU1 hV1
    (zero_le_one.trans hZ) hrole1 hrole2 m r n e q a omega k N ((N:ℝ)^ell) S]
  exact H

end
end ImbalancedChen.P4BOriginalActualSharpEndpoints
