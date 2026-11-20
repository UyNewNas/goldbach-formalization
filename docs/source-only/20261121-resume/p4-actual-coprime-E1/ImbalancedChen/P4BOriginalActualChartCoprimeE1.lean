import ImbalancedChen.P4BOriginalSameRhoCoprimeE1
import ImbalancedChen.P4BOriginalTwoLongActualAssignment

/-! SOURCE ONLY / UNCOMPILED. Original pre-HB Z, growing Brun order,
retained frequency cube and final same-rho family in the E1 mean.
All thresholds precede N, chart labels, row, mode and short product.
No E3 twice-mean or endpoint/mother-integration payment is claimed. -/
namespace ImbalancedChen.P4BOriginalActualChartCoprimeE1
noncomputable section
open Classical Filter Set
open scoped BigOperators
open P4BOriginalCoprimeSmoothE1 (price price_nonneg)
open P4BOriginalBrunCoprimeE1 (density profilePrice profile_price gap_density_B2)
open P4BOriginalSameRhoCoprimeE1 (signedError same_rho_actual_profile_E1)
open P4BOriginalTwoLongActualScales (brunEpsilon actual_cutoff_formula eventually_chart_brun eventually_live_large)
open P4BOriginalHighRankLocalLevel (theta eventually_live_level)
open P4BOriginalHighRankMotherScale (completeScale live_geometry)
open P4BOriginalHighRankComplementBlocks (fibre complement same_scale)
open P4BOriginalHighRankPostModulusRow (H bandwidthOrder eventually_local_twists)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BUpperPairOrderedRowGeometry (integerProfile)
open P4BOuterRampRoughness (baseline)
open P5Z.HBRightClosedDyadicRoles (Block owner)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle)
open P5Z.ExactOriginalSmoothDyadicPartition (R R_pos beforeHBCutoff)
open P5Z.ActualHBRoughBrunRates (halfOrder nextOrder loglog nextOrder_bounds tendsto_loglog eventually_real_chart_harmonic)
open P5Z.AllRankCauchyCubeTail (outsideCube)
open Part3.TwoLongTransitionMellinN2 (profile profileSchwartz)
open Part3.RoughSlotCharacterLift20261026b (smallPrimes smallPrimes_prime mem_smallPrimes)

/-- The old actual harmonic and factorial suppliers apply to every
actual Z<=x alphabet, rather than only to the smaller roughZ(x).
Both q-deletion and the nonunit short gate stay in density. -/
theorem eventually_gap_density :
    ∀ᶠ x : ℝ in atTop,∀ Z : ℝ,1≤Z → Z≤x → ∀ q short : ℕ,
      ‖density Z (halfOrder x) true q short‖≤Real.exp (-((loglog x)^2)) := by
  filter_upwards [eventually_real_chart_harmonic,
    tendsto_loglog.eventually_ge_atTop (max 1 (2*Real.exp 2))] with x hH hL
  intro Z hZ hZx q short
  let P := smallPrimes Z
  let h := Part3.BrunFactorialRecurrenceE1.chartHarmonic P
  have h0 : 0≤h := by dsimp [h,Part3.BrunFactorialRecurrenceE1.chartHarmonic]; positivity
  have hh : h≤2*loglog x := hH P (fun p hp => smallPrimes_prime hp) (fun p hp =>
    (((mem_smallPrimes (by linarith : 0≤Z)).mp hp).2).trans hZx)
  have hL1 : 1≤loglog x := (le_max_left _ _).trans hL
  have hLe : 2*Real.exp 2≤loglog x := (le_max_right _ _).trans hL
  have hr := (nextOrder_bounds x hL1).1
  have hf := OriginalOneLongExplicitBrunRates.factorial_gap_le_exp h (nextOrder x) h0
  have hB := gap_density_B2 Z (halfOrder x) q short
  change ‖density Z (halfOrder x) true q short‖≤h^(nextOrder x)/(Nat.factorial (nextOrder x):ℝ) at hB
  apply hB.trans (hf.trans _)
  apply Real.exp_le_exp.mpr
  have H1 := mul_le_mul_of_nonneg_left hh (Real.exp_pos 2).le
  have H2 := mul_le_mul_of_nonneg_right hLe (zero_le_one.trans hL1)
  nlinarith only [H1,H2,hr]

/-- The local E1 error is for the original actual profile and same Q/rho.
No q-to-N coprimality premise is added: generic E1 includes every q>0,
and the reciprocal moment uses the proved actual Q structural support.
The full source-preserved mean/main remains inside signedError. -/
theorem eventually_live_same_rho_E1 (K B A0 : ℕ) (hB : 1≤B)
    {zeta kappa kap0 : ℝ} (hz : 0<zeta) (hz1 : zeta≤1/400)
    (hk : 0<kappa) (hkz : kappa≤zeta/10000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop,∀ {b kap s : ℝ},0<b → 0<kap → 0<s → 2*s≤baseline b kap-19/96 →
      ∀ (u v cj ck : ℕ) (blocks : Fin (u+v)→Block) (y : Fin (u+v)→ℕ) (i : Fin (u+v)),
      y∈rectangle blocks → integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y≠0 →
      let x := completeScale blocks y i
      let U := (lower (blocks i):ℝ)
      let Z := beforeHBCutoff K [cj,ck]
      let D := Nat.floor (x^theta)
      let delta := ((Real.log x)^B)⁻¹
      let freq := (Real.log x)^(bandwidthOrder A0+1)
      1≤Z ∧ Z^(2*halfOrder x+1)≤x^brunEpsilon ∧ 0<delta ∧ delta≤1/4 ∧
      (∀ q short : ℕ,‖density Z (halfOrder x) true q short‖≤Real.exp (-((loglog x)^2))) ∧
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ),
      (∀ d,coefficient m r n e q a omega k N ((N:ℝ)^ell) d≠0 →
        (d:ℝ)<(N:ℝ)^modulusExponent) →
      ∀ S : Finset ℕ,S⊆Q omega N →
      ∀ xi : Fin (u+v)→ℝ,xi∈(outsideCube _ (H N A0))ᶜ →
      ∀ (isGap isLog gap : Bool) (short : ℕ),
      ‖signedError (profile isGap isLog delta U (xi i)) U Z (halfOrder x) gap short
        m r n e q a omega k N ((N:ℝ)^ell) S‖≤
        profilePrice delta U freq*x^brunEpsilon*(4*(1+Real.log (max 1 (D:ℝ))))^16 := by
  have heps : 0<brunEpsilon := by norm_num [brunEpsilon]
  have hkapOne : kappa≤1 := by linarith
  have hscalar := ((eventually_chart_brun K brunEpsilon heps).and
    (Part3.TwoLongMellinLogBudget.eventually_schedule B hB)).and eventually_gap_density
  obtain ⟨x0,Hx⟩ := eventually_atTop.mp hscalar
  filter_upwards [eventually_live_large ht1 x0,eventually_live_level hz hz1 hk hkz ht,
    eventually_local_twists A0 hkapOne,eventually_ge_atTop (2:ℕ)] with N hlarge hlevel htwists hN
  intro b kap s hb hkap hs hg u v cj ck blocks y i hy hw
  let x := completeScale blocks y i
  let U : ℝ := lower (blocks i)
  let Z := beforeHBCutoff K [cj,ck]
  let D := Nat.floor (x^theta)
  let delta := ((Real.log x)^B)⁻¹
  let freq := (Real.log x)^(bandwidthOrder A0+1)
  let C := owner (complement i y)
  have hfy : y∈fibre blocks i C := Finset.mem_filter.mpr ⟨hy,rfl⟩
  have HL := hlevel hb hkap hs hg u v cj ck blocks i C ⟨y,hfy,hw⟩
  rw [←same_scale hfy] at HL
  obtain ⟨hx,_,hNx,_,_,_,hlevels⟩ := HL
  obtain ⟨⟨hBrun,hSched⟩,hGap⟩ := Hx x ((hlarge hb hkap hs hg u v cj ck blocks y i hy hw).1)
  obtain ⟨_,_,hXx,hxX⟩ := live_geometry (by omega) hb hkap hs hg cj ck blocks y i hy hw
  have hZpair := hBrun (R cj*R ck) (mul_pos (R_pos cj) (R_pos ck)) hXx hxX
  rw [←actual_cutoff_formula K cj ck] at hZpair
  obtain ⟨hZ,hY⟩ := hZpair
  have hZx : Z≤x := by
    calc
      Z=Z^1 := (pow_one _).symm
      _≤Z^(2*halfOrder x+1) := pow_le_pow_right₀ hZ (by omega)
      _≤x^brunEpsilon := hY
      _≤x := by simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hx.le (show brunEpsilon≤1 by norm_num [brunEpsilon])
  refine ⟨hZ,hY,hSched.2.1,hSched.2.2,hGap Z hZ hZx,?_⟩
  intro m r n e q a omega k ell hRange S hS xi hxi isGap isLog gap short
  have hDlevel (d : ℕ) (hd : d∈S)
      (hc : coefficient m r n e q a omega k N ((N:ℝ)^ell) d≠0) : d≤D :=
    Nat.le_floor (hlevels m r n e q a omega k ell hRange d (hS hd) hc).le
  have hU : 0<U := by exact_mod_cast lower_pos (blocks i)
  have hFreq : 0≤freq := pow_nonneg (Real.log_pos hx).le _
  have htw := htwists x hx hNx (u+v) xi hxi i
  have hp := same_rho_actual_profile_E1 isGap isLog gap hSched.2.1 hSched.2.2 hU hFreq htw
    hZ (halfOrder x) short m r n e q a omega k N D ((N:ℝ)^ell) S hS hDlevel
  have hprice0 : 0≤profilePrice delta U freq :=
    (price_nonneg (profileSchwartz isGap isLog hSched.2.1 hSched.2.2 U (xi i))).trans
      (profile_price isGap isLog hSched.2.1 hSched.2.2 hFreq htw)
  exact hp.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hY hprice0) (by positivity))

end
end ImbalancedChen.P4BOriginalActualChartCoprimeE1
