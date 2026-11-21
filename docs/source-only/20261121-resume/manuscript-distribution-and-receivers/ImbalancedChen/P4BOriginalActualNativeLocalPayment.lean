import ImbalancedChen.P4BOriginalActualSharpEndpoints

/-! SOURCE ONLY / UNCOMPILED. Common-witness assembly of source69 and
source72. Their two existential terminal statements cannot be combined
by choosing unrelated witnesses: completeScale, hence delta, uses y.
We extract the common actual assignment ONCE and instantiate the already
proved rough and endpoint invoices on that same row. No E1/E3/P2/strip
estimate is reproved. Outer amplitude choices must precede local accuracy. -/
namespace ImbalancedChen.P4BOriginalActualNativeLocalPayment
noncomputable section
open Classical Filter Set
open scoped BigOperators
open P4BOriginalNoMediumPairRows
open P4BOriginalTwoLongActualScales
open P4BOriginalTwoLongActualAssignment (eventually_actual_pair_assignment)
open P4BOriginalPairMeanGeometry (actual_MUV eventually_native_long_lengths)
open P4BOriginalE3LocalPayment
open P4BOriginalE3LogPrices (decay decay_bounds)
open P4BOriginalRoughE3Assembly (roughSum finite_rough_invoice)
open P4BOriginalActualChartCoprimeE1 (eventually_gap_density)
open P4BOriginalSharpEndpointPrices (endpointOrder eventually_endpoint_invoice_paid)
open P4BOriginalSharpPairComparison (sharpDifference finite_endpoint_invoice)
open P4BOriginalSharpNativeRow (nativeMode nativeMode_eq_sharpSum)
open P4BOriginalTwoLongExpandedCore (rho)
open P4BOriginalHighRankLocalLevel (theta eventually_live_level)
open P4BOriginalHighRankMotherScale (completeScale)
open P4BOriginalHighRankComplementBlocks (fibre complement same_scale)
open P4BOriginalHighRankPostModulusRow (H bandwidthOrder eventually_local_twists)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BUpperPairOrderedRowGeometry
open P5Z.HBRightClosedDyadicRoles (Block owner)
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

/-- Both component bounds use local accuracy A+1, one inner order
endpointOrder (A+1), and one actual source witness. The final native mode
has no smoothing parameter. The original Q/rho and retained cube stay fixed. -/
theorem eventually_actual_native_mode_paid (K A0 A : ℕ)
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
      1<x ∧ (N:ℝ)≤x^(1+kappa) ∧ 1<U ∧ 1<V ∧
      (shortScale bS:ℝ)*U*V≤4*x ∧ x^(1/3:ℝ)≤U ∧ x^(1/3:ℝ)≤V ∧
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ),
      (∀ d,coefficient m r n e q a omega k N ((N:ℝ)^ell) d≠0 →
        (d:ℝ)<(N:ℝ)^modulusExponent) →
      ∀ S : Finset ℕ,S⊆Q omega N →
      ∀ xi : Fin (2*(j+1)+2*(l+1))→ℝ,xi∈(outsideCube _ (H N A0))ᶜ →
      let delta := ((Real.log x)^(endpointOrder (A+1)))⁻¹
      let fLog := decide (roles i=.logarithm)
      let gLog := decide (roles t=.logarithm)
      let smooth := roughSum (profile false fLog delta U (xi i)) (profile false gLog delta V (xi t))
        U V Z (shortSupport bS) (shortSequence bS Z ys (fun a => xi a.val) rs)
        m r n e q a omega k N ((N:ℝ)^ell) S
      let native := nativeMode blocks Z allY xi roles N S (rho m r n e q a omega k N ((N:ℝ)^ell))
      ‖smooth‖≤x/(Real.log x)^(A+1) ∧ ‖native-smooth‖≤x/(Real.log x)^(A+1) ∧
        ‖native‖≤x/(Real.log x)^A := by
  let B := endpointOrder (A+1)
  have hB : 1≤B := by dsimp [B,endpointOrder]; omega
  have hk1 : kappa≤1 := by linarith
  have hX := (((eventually_polynomialBill_paid B (bandwidthOrder A0+1) (A+2) hB hz1).and
    (eventually_meanBill_paid B (A+2))).and (eventually_endpoint_invoice_paid (A+1) hz1)).and
    ((eventually_gap_density.and (Part3.TwoLongMellinLogBudget.eventually_schedule B hB)).and
      (Real.tendsto_log_atTop.eventually_ge_atTop (3:ℝ)))
  obtain ⟨x0,Hx⟩ := eventually_atTop.mp hX
  filter_upwards [eventually_actual_pair_assignment K B A0 0 hB hz hz1 hk hkz ht ht1,
    eventually_native_long_lengths hz hz1 ht1,eventually_live_large ht1 x0,
    eventually_live_level hz hz1 hk hkz ht,eventually_local_twists A0 hk1]
    with N hassign hlong hlarge hlevel htwists
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
  obtain ⟨⟨⟨hpolyPay,hmeanPay⟩,hendpointPay⟩,⟨hgap,hSched⟩,hlog⟩ := Hx x hxl
  have hDx' : (D:ℝ)≤x := hDx.trans (by simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hx.le (show theta≤1 by norm_num [theta]))
  have hM : 0≤M := Nat.cast_nonneg _
  have hY : 0≤Y := pow_nonneg (zero_le_one.trans hZ) _
  have hMp : M≤x^(1/10:ℝ) := hMpow.trans
    (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith : 40*zeta≤1/10))
  have hYx : Y≤x := hyPower.trans (by simpa only [Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hx.le (show brunEpsilon≤1 by norm_num [brunEpsilon]))
  have hZx : Z≤x := (show Z≤Y by
    calc Z=Z^1 := (pow_one _).symm
         _≤Z^(2*halfOrder x+1) := pow_le_pow_right₀ hZ (by omega)).trans hYx
  let C := owner (complement i y)
  have hfy : y∈fibre blocks i C := Finset.mem_filter.mpr ⟨hy,rfl⟩
  have hlev := hlevel hb hkap hs hg _ _ cj ck blocks i C ⟨y,hfy,hw⟩
  rw [←same_scale hfy] at hlev
  have hNx := hlev.2.2.1
  have hroot : 1<x^(1/3:ℝ) := Real.one_lt_rpow hx (by norm_num)
  have hU1 : 1<U := hroot.trans hlongs.1
  have hV1 : 1<V := hroot.trans hlongs.2
  refine ⟨i1,i2,hchoose1,hchoose2,y,hy,hactive,hik,hcard,hrole1,hrole2,hx,hNx,hU1,hV1,hprod,hlongs.1.le,hlongs.2.le,?_⟩
  intro m r n e q a omega k ell hRange S hS xi hxi
  obtain ⟨hDlevel,_⟩ := hcaller m r n e q a omega k ell hRange S hS
  let alpha := shortSequence bS Z ys (fun a => xi a.val) rs
  let mu := ∑ short∈shortSupport bS,‖alpha short‖
  let delta := ((Real.log x)^B)⁻¹
  have hmu : 0≤mu := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hmub : mu≤4096*M*(Real.log x)^12 := by
    have H0 := shortSequence_mass bS Z ys (fun a => xi a.val) rs hx.le hends
    have H1 := P4BOriginalTwoLongExpandedCore.short_log_budget (by omega : Fintype.card (ShortPositions i t)≤12)
      (by linarith : 1≤Real.log x)
    exact H0.trans ((mul_le_mul_of_nonneg_left H1 hM).trans_eq (by dsimp [M]; ring))
  have ht1' := htwists x hx hNx _ xi hxi i
  have ht2' := htwists x hx hNx _ xi hxi t
  let fLog := decide (roles i=.logarithm)
  let gLog := decide (roles t=.logarithm)
  let smooth := roughSum (profile false fLog delta U (xi i)) (profile false gLog delta V (xi t))
    U V Z (shortSupport bS) alpha m r n e q a omega k N ((N:ℝ)^ell) S
  let native := nativeMode blocks Z allY xi roles N S (rho m r n e q a omega k N ((N:ℝ)^ell))
  have hfinite := finite_rough_invoice false fLog false gLog
    hSched.2.1 hSched.2.2 (zero_lt_one.trans_le hU) (zero_lt_one.trans_le hV) hZ hx.le
    (decay_bounds x).1 (decay_bounds x).2 (xi i) (xi t) (halfOrder x) hYx
    (shortSupport bS) alpha m r n e q a omega k N D ((N:ℝ)^ell) S hS
    (fun v hv => hgap Z hZ hZx v 1) hDlevel
  have hp := hpolyPay U V Y M mu (xi i) (xi t) D hU hV hUx hVx hD hDx hM hMpow hY hyPower hmu hmub ht1' ht2'
    false fLog false gLog hSched.2.1 hSched.2.2
  have hm := hmeanPay U V Y M mu D hU hV hUx hVx hD hDx' hY hM hmu hmub hprod hlongs.1.le hlongs.2.le hMp hyPower
  have hrough0 : ‖smooth‖≤2*x/(Real.log x)^(A+2) := by
    dsimp only at hfinite hp
    change ‖smooth‖≤_ at hfinite
    change meanBill delta U V x Y mu D≤_ at hm
    unfold meanBill at hm
    nlinarith only [hfinite,hp,hm]
  have hl0 : 0<Real.log x := by linarith
  have hrough : ‖smooth‖≤x/(Real.log x)^(A+1) := hrough0.trans (by
    calc
      2*x/(Real.log x)^(A+2)=(2/Real.log x)*(x/(Real.log x)^(A+1)) := by
        rw [show A+2=(A+1)+1 by omega,pow_succ]; field_simp [hl0.ne']; ring
      _≤1*(x/(Real.log x)^(A+1)) := mul_le_mul_of_nonneg_right
        ((div_le_one hl0).mpr (by linarith)) (by positivity)
      _=_ := one_mul _)
  have hsfinite := finite_endpoint_invoice fLog gLog hSched.2.1 hSched.2.2
    (zero_lt_one.trans_le hU) (zero_lt_one.trans_le hV) hZ hx.le (xi i) (xi t) (halfOrder x) hYx
    (shortSupport bS) alpha m r n e q a omega k N D ((N:ℝ)^ell) S hS hDlevel
  have hspaid := hendpointPay U V Y M mu D hU hV hUx hVx hD hDx hM hMpow hY hyPower hmu hmub
    hprod hlongs.1.le hlongs.2.le hSched.2.1 hSched.2.2
  have hsharp : ‖native-smooth‖≤x/(Real.log x)^(A+1) := by
    dsimp only [native]
    rw [nativeMode_eq_sharpSum blocks Z allY xi roles i t hik hU1 hV1
      (zero_le_one.trans hZ) hrole1 hrole2 m r n e q a omega k N ((N:ℝ)^ell) S]
    exact hsfinite.trans hspaid
  refine ⟨hrough,hsharp,?_⟩
  calc
    ‖native‖=‖(native-smooth)+smooth‖ := by rw [sub_add_cancel]
    _≤‖native-smooth‖+‖smooth‖ := norm_add_le _ _
    _≤2*x/(Real.log x)^(A+1) := by linarith
    _=(2/Real.log x)*(x/(Real.log x)^A) := by rw [pow_succ]; field_simp [hl0.ne']; ring
    _≤1*(x/(Real.log x)^A) := mul_le_mul_of_nonneg_right ((div_le_one hl0).mpr (by linarith)) (by positivity)
    _=_ := one_mul _

end
end ImbalancedChen.P4BOriginalActualNativeLocalPayment
