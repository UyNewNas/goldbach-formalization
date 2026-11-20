import ImbalancedChen.P4BOriginalTwoLongActualScales
import ImbalancedChen.P4BOriginalTwoLongActualDictionary

/-! SOURCE ONLY / UNCOMPILED. The actual block-only no-medium pair row
is assigned to the already-paid expanded core with its original rho.
All scalar and local error thresholds precede N. No rough E1/E3,
endpoint strip, mother integral or H_N restoration is asserted. -/
namespace ImbalancedChen.P4BOriginalTwoLongActualAssignment
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalNoMediumPairRows
open P4BOriginalTwoLongActualScales
open P4BOriginalTwoLongActualDictionary (polynomialRow polynomialRow_eq_core)
open P4BOriginalTwoLongExpandedCore (eventually_actual_upper_core_paid)
open P4BOriginalHighRankLocalLevel (theta eventually_live_level)
open P4BOriginalHighRankMotherScale (completeScale live_geometry tuple_scale)
open P4BOriginalHighRankComplementBlocks (fibre complement same_scale)
open P4BOriginalHighRankPostModulusRow (H bandwidthOrder eventually_local_twists)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BUpperPairOrderedRowGeometry
open P5Z.HBRightClosedDyadicRoles (Block owner)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos owns_bounds)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle mem_rectangle owns_pos)
open P5Z.ActualHBPostModulusLogCutoff (hbSlots completeProduct)
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCutoff)
open P5Z.ExactOriginalSmoothDyadicPartition (R R_pos beforeHBCutoff)
open P5Z.ActualHBRoughBrunRates (halfOrder)
open P5Z.AllRankCauchyCubeTail (outsideCube)
open Part3.TwoLongActualHBShortMass (ShortPositions shortScale)
open P4BOuterRampRoughness (baseline)

/-- A true source theorem for the two rows occurring in rowBank/modeBank.
`S` may be Q or its actual wholeHigh subset. The displayed global support
gate is the unchanged FineDensity .599 theorem, not a new error premise.
The selected long positions are fixed from blocks before xi or rho. -/
theorem eventually_actual_pair_assignment (K B A0 A : ℕ) (hB : 1≤B)
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
        (integerProfile (a:=2*(j+1)) (d:=2*(l+1)) b kap s N kap0 cj ck y : ℂ)≠0 ∧
      let blocks := Fin.append bs cs
      let i := Fin.castAdd (2*(l+1)) i1
      let k := Fin.natAdd (2*(j+1)) i2
      let x := completeScale blocks y i
      let U := (lower (blocks i):ℝ)
      let V := (lower (blocks k):ℝ)
      let Z := beforeHBCutoff K [cj,ck]
      let D := Nat.floor (x^theta)
      i≠k ∧ Fintype.card (ShortPositions i k)≤10 ∧
      (Fin.append (rowRoles j) (rowRoles l) i=.one ∨ Fin.append (rowRoles j) (rowRoles l) i=.logarithm) ∧
      (Fin.append (rowRoles j) (rowRoles l) k=.one ∨ Fin.append (rowRoles j) (rowRoles l) k=.logarithm) ∧
      1<x ∧ 1≤D ∧ (D:ℝ)≤x^theta ∧ 1≤Z ∧
      (shortScale (fun t : ShortPositions i k => blocks t.val):ℝ)≤x^(40*zeta) ∧
      Z^(2*halfOrder x+1)≤x^brunEpsilon ∧
      (∀ t : ShortPositions i k,2*(lower (blocks t.val):ℝ)≤x) ∧
      1≤U ∧ 1≤V ∧ U≤4*x ∧ V≤4*x ∧
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (index : ℕ) (ell : ℝ),
      (∀ v,coefficient m r n e q a omega index N ((N:ℝ)^ell) v≠0 →
        (v:ℝ)<(N:ℝ)^modulusExponent) →
      ∀ S : Finset ℕ,S⊆Q omega N →
      (∀ v∈S,coefficient m r n e q a omega index N ((N:ℝ)^ell) v≠0 → v≤D) ∧
      ∀ xi : Fin (2*(j+1)+2*(l+1))→ℝ,xi∈(outsideCube _ (H N A0))ᶜ →
      ∀ (gap1 gap2 : Bool) (label : Fin 3),
      ‖polynomialRow m r n e q a omega index N ((N:ℝ)^ell) Z S (halfOrder x)
        gap1 gap2 ((Real.log x)^B)⁻¹ U V (xi i) (xi k) label
        (decide (Fin.append (rowRoles j) (rowRoles l) i=.logarithm))
        (decide (Fin.append (rowRoles j) (rowRoles l) k=.logarithm))
        (fun t : ShortPositions i k => blocks t.val)
        (fun t => Fin.append (fun _ => hbCutoff cj) (fun _ => hbCutoff ck) t.val)
        (fun t => xi t.val)
        (fun t => Fin.append (rowRoles j) (rowRoles l) t.val)‖≤x/(Real.log x)^A := by
  obtain ⟨heps,htheta,_,hmargin⟩ := fixed_margin hz1
  have hkapOne : kappa≤1 := by linarith
  have hpay := eventually_actual_upper_core_paid B (bandwidthOrder A0+1) A hB 4
    (by norm_num) zeta theta brunEpsilon heps htheta hmargin
  have hscalar := (hpay.and (eventually_short_transport hz hz1)).and
    ((eventually_chart_brun K brunEpsilon heps).and
      (Part3.TwoLongMellinLogBudget.eventually_schedule B hB))
  obtain ⟨x0,Hx⟩ := eventually_atTop.mp hscalar
  obtain ⟨X0,HX⟩ := eventually_atTop.mp (eventually_X_gates hz)
  filter_upwards [eventually_live_large ht1 (max x0 X0),
    eventually_mother_short_gap (kap0:=kap0) hz hz1,
    eventually_live_level hz hz1 hk hkz ht,eventually_local_twists A0 hkapOne,
    eventually_ge_atTop (2:ℕ)] with N hlarge hshort hlevel htwists hN
  intro b kap s hb hkap hs hg j l cj ck hj hl bs cs hnone hLive
  obtain ⟨y,hy,hactive⟩ := hLive
  have hslots := (mul_ne_zero_iff.mp hactive).1
  have hw : integerProfile (a:=2*(j+1)) (d:=2*(l+1)) b kap s N kap0 cj ck y≠0 := by
    intro hzero
    exact (mul_ne_zero_iff.mp hactive).2 (by rw [hzero]; rfl)
  let blocks := Fin.append bs cs
  let i0 : Fin (2*(j+1)+2*(l+1)) := ⟨0,by omega⟩
  have hbase := hlarge hb hkap hs hg _ _ cj ck blocks y i0 hy hw
  have hXlarge : X0≤R cj*R ck := (le_max_right _ _).trans hbase.2
  obtain ⟨hthree,hcut⟩ := HX _ hXlarge
  obtain ⟨i1,i2,hchoose1,hchoose2,hik,hlong1,hlong2,hcard,hrest,hMbase⟩ :=
    select_actual_pair hj hl hb hs hg hz cj ck bs cs y hy hw hnone
      (hshort hb hkap hs hg _ _ cj ck blocks y i0 hy hw) hthree
  let i := Fin.castAdd (2*(l+1)) i1
  let k := Fin.natAdd (2*(j+1)) i2
  let x := completeScale blocks y i
  let U : ℝ := lower (blocks i)
  let V : ℝ := lower (blocks k)
  let Z := beforeHBCutoff K [cj,ck]
  let D := Nat.floor (x^theta)
  let C := owner (complement i y)
  have hfy : y∈fibre blocks i C := Finset.mem_filter.mpr ⟨hy,rfl⟩
  have hlev := hlevel hb hkap hs hg _ _ cj ck blocks i C ⟨y,hfy,hw⟩
  rw [←same_scale hfy] at hlev
  obtain ⟨hx,hxN,hNx,_,_,_,hlevels⟩ := hlev
  have hxl := (hlarge hb hkap hs hg _ _ cj ck blocks y i hy hw).1
  obtain ⟨⟨hpaid,htrans⟩,hBrun,hschedule⟩ := Hx x ((le_max_left _ _).trans hxl)
  obtain ⟨_,_,hXx,hxX⟩ := live_geometry (by omega) hb hkap hs hg cj ck blocks y i hy hw
  have hXp : 0<R cj*R ck := mul_pos (R_pos cj) (R_pos ck)
  obtain ⟨hM,hend⟩ := htrans (R cj*R ck) _ hXp hXx hMbase
  have hZpair := hBrun (R cj*R ck) hXp hXx hxX
  rw [←actual_cutoff_formula K cj ck] at hZpair
  obtain ⟨hZ,hyPower⟩ := hZpair
  have hD : 1≤D := Nat.le_floor (Real.one_le_rpow hx.le (by norm_num [theta]))
  have hDx : (D:ℝ)≤x^theta := Nat.floor_le (Real.rpow_nonneg (zero_lt_one.trans hx).le _)
  have hends (t : ShortPositions i k) : 2*(lower (blocks t.val):ℝ)≤x :=
    hend _ (hrest t).le
  have hprodPos : 0<completeProduct y := Finset.prod_pos (fun t _ => owns_pos ((mem_rectangle _ _).mp hy t))
  have hprodUpper := (tuple_scale blocks y i hy).2
  have coordinate (t : Fin (2*(j+1)+2*(l+1))) :
      1≤(lower (blocks t):ℝ) ∧ (lower (blocks t):ℝ)≤4*x := by
    have ho := owns_bounds ((mem_rectangle _ _).mp hy t)
    have hdiv : y t∣completeProduct y := Finset.dvd_prod_of_mem y (Finset.mem_univ t)
    have htle := Nat.le_of_dvd hprodPos hdiv
    constructor
    · exact_mod_cast (Nat.succ_le_of_lt (lower_pos (blocks t)))
    · have H : (lower (blocks t):ℝ)≤completeProduct y := by exact_mod_cast ho.1.trans htle
      exact H.trans hprodUpper
  have hUV := And.intro (coordinate i) (coordinate k)
  have hcuts := hcut cj ck rfl
  have hrole1 := selected_long_role cj ck Z _ bs cs y hy hslots hcuts i hlong1
  have hrole2 := selected_long_role cj ck Z _ bs cs y hy hslots hcuts k hlong2
  refine ⟨i1,i2,hchoose1,hchoose2,y,hy,hactive,hik,hcard,hrole1,hrole2,hx,hD,hDx,hZ,hM,
    hyPower,hends,hUV.1.1,hUV.2.1,hUV.1.2,hUV.2.2,?_⟩
  intro m r n e q a omega index ell hRange S hS
  have hDlevel (v : ℕ) (hv : v∈S)
      (hc : coefficient m r n e q a omega index N ((N:ℝ)^ell) v≠0) : v≤D :=
    Nat.le_floor (hlevels m r n e q a omega index ell hRange v (hS hv) hc).le
  refine ⟨hDlevel,?_⟩
  intro xi hxi gap1 gap2 label
  have htwi := htwists x hx hNx _ xi hxi i
  have htwk := htwists x hx hNx _ xi hxi k
  rw [polynomialRow_eq_core m r n e q a omega index N ((N:ℝ)^ell) S hZ
    hschedule.2.1 hschedule.2.2 (zero_lt_one.trans_le hUV.1.1) (zero_lt_one.trans_le hUV.2.1)]
  exact hpaid (ShortPositions i k) m r n e q a omega index N D ((N:ℝ)^ell) S Z U V
    (xi i) (xi k) (halfOrder x) gap1 gap2 label _ _ _ _ _ _
    (by omega) hS hD hZ hDlevel hDx hM hyPower hends hUV.1.1 hUV.2.1 hUV.1.2 hUV.2.2 htwi htwk

end
end ImbalancedChen.P4BOriginalTwoLongActualAssignment
