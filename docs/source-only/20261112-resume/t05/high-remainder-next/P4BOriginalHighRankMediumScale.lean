import ImbalancedChen.P4BOriginalHighRankMotherScale
import ImbalancedChen.P5OriginalChartRoughCutoff

/-! Uniform local (S) for the original first-medium coordinate on each live
pair mother, including its whole complement and its original pre-HB cutoff. -/
namespace ImbalancedChen.P4BOriginalHighRankMediumScale
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle)
open P5Z.ExactOriginalSmoothDyadicPartition (R R_pos beforeHBCutoff scales)
open P5Z.OriginalChartRoughCutoff (roughF roughF_mono roughF_upper)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P5Z.ActualHBMediumBranchPartition (firstMedium)
open P4BUpperPairOrderedRowGeometry (integerProfile)
open P4BOriginalRankTwoChartScales (eventually_power)
open P4BOriginalHighRankMotherScale (completeScale live_geometry selected_window)
open P4BOuterRampRoughness (baseline)

private theorem geometry (K : ℕ) {zeta kappa kap0 : ℝ}
    (hz : 0<zeta) (hz1 : zeta≤1/400) (hk : 0<kappa) (hkz : kappa≤zeta)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop,∀ (x X U : ℝ),
      (1/4:ℝ)*(N:ℝ)^(1-kap0)≤x → x≤Real.exp 1*N →
      X≤16*x → x≤4*X → X^(3*zeta)≤U → U≤X^(1/3+zeta/4:ℝ) →
      let v := (2:ℝ)^(6*K+2)*(4*X)
      1<x ∧ x^(1-zeta)≤N ∧ (N:ℝ)≤x^(1+kappa) ∧
      x^(2*zeta)≤U ∧ U≤x^(1/3+zeta/2:ℝ) ∧
      roughF x≤roughF v ∧ roughF v≤x^(2/(Real.log (Real.log x))^3) := by
  let C := (2:ℝ)^(6*K+2)
  have hC : 1≤C := one_le_pow₀ (by norm_num)
  have htX : ∀ᶠ x : ℝ in atTop,Real.exp (Real.exp 3)≤x ∧ 64*C≤x ∧
      4≤x^(1/3:ℝ) ∧ 16≤x^(zeta/4) ∧ Real.exp 1≤x^zeta := by
    filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 3)),eventually_ge_atTop (64*C),
      (Real.tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).eventually_ge_atTop 4,
      (Real.tendsto_rpow_atTop (by linarith : 0<zeta/4)).eventually_ge_atTop 16,
      (Real.tendsto_rpow_atTop hz).eventually_ge_atTop (Real.exp 1)] with x h1 h2 h3 h4 h5
    exact ⟨h1,h2,h3,h4,h5⟩
  obtain ⟨x0,Hx⟩ := eventually_atTop.mp htX
  obtain ⟨_,N0,_,HN⟩ := exists_manuscript_restrictedResidueScale_threshold
    (by norm_num : (0:ℝ)<1/4) (Real.exp_pos 1) hk ht
  filter_upwards [eventually_ge_atTop N0,eventually_power (4*x0) (1-kap0) (by linarith)]
    with N hN hsize
  intro x X U hlo hhi hX hxX hU hU'
  obtain ⟨hx,rlo,rhi⟩ := HN N hN x hlo hhi
  have hxp := zero_lt_one.trans hx
  have hXp : 0<X := by linarith
  obtain ⟨hlarge,hcx,hfour,hsixteen,hex⟩ := Hx x (by linarith)
  have lowerRes : x^(1-zeta)≤N := by
    have h : Real.exp 1*x^(1-zeta)≤x := by
      calc
        _≤x^zeta*x^(1-zeta) := mul_le_mul_of_nonneg_right hex (Real.rpow_nonneg hxp.le _)
        _=x := by rw [←Real.rpow_add hxp,show zeta+(1-zeta)=1 by ring,Real.rpow_one]
    exact (le_of_mul_le_mul_left (h.trans hhi) (Real.exp_pos 1))
  have hXlower : x^(2/3:ℝ)≤X := by
    have hmul := mul_le_mul_of_nonneg_left hfour (Real.rpow_nonneg hxp.le (2/3:ℝ))
    rw [←Real.rpow_add hxp,show (2/3:ℝ)+1/3=1 by norm_num,Real.rpow_one] at hmul
    linarith
  have hUlo : x^(2*zeta)≤U := by
    calc
      _=(x^(2/3:ℝ))^(3*zeta) := by
        rw [←Real.rpow_mul hxp.le]; congr 1; ring
      _≤X^(3*zeta) := Real.rpow_le_rpow (Real.rpow_nonneg hxp.le _) hXlower (by linarith)
      _≤U := hU
  let g : ℝ := 1/3+zeta/4
  have hg : 0≤g := by dsimp [g]; linarith
  have h16 : (16:ℝ)^g≤16 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ)≤16) (show g≤1 by dsimp [g]; linarith)
  have hUhi : U≤x^(1/3+zeta/2:ℝ) := by
    calc
      U≤X^g := hU'
      _≤(16*x)^g := Real.rpow_le_rpow hXp.le hX hg
      _=16^g*x^g := Real.mul_rpow (by norm_num) hxp.le
      _≤x^(zeta/4)*x^g :=
        mul_le_mul_of_nonneg_right (h16.trans hsixteen) (Real.rpow_nonneg hxp.le _)
      _=_ := by rw [←Real.rpow_add hxp]; congr 1; dsimp [g]; ring
  let v := C*(4*X)
  have hxv : x≤v := hxX.trans (by
    dsimp [v]; simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (by positivity : 0≤4*X))
  have hvx : v≤x^2 := by
    have hscaled := mul_le_mul_of_nonneg_left hX (show 0≤4*C by linarith)
    have hlast := mul_le_mul_of_nonneg_right hcx hxp.le
    dsimp [v]; nlinarith only [hscaled,hlast]
  have hl3 : Real.exp 3≤Real.log x := (Real.le_log_iff_exp_le hxp).mpr hlarge
  have hloglog : 3≤Real.log (Real.log x) := (Real.le_log_iff_exp_le (Real.log_pos hx)).mpr hl3
  exact ⟨hx,lowerRes,rhi,hUlo,hUhi,roughF_mono hx hloglog hxv,roughF_upper hx hloglog hxv hvx⟩

/-- The nonzero tuple and literal first-medium selector produce all length
and cutoff comparisons. The threshold precedes every chart, width, tuple,
selected position and complementary dyadic label. -/
theorem eventually_live_medium (K : ℕ) {zeta kappa kap0 : ℝ}
    (hz : 0<zeta) (hz1 : zeta≤1/400) (hk : 0<kappa) (hkz : kappa≤zeta)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop,∀ {b kap s : ℝ},0<b → 0<kap → 0<s → 2*s≤baseline b kap-19/96 →
      ∀ (u v cj ck : ℕ) (bs : Fin (u+v)→Block) (n : Fin (u+v)→ℕ) (i : Fin (u+v)),
      n∈rectangle bs → integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck n≠0 →
      firstMedium (originalMediumLow zeta [cj,ck]) (originalMediumHigh zeta [cj,ck])
        (List.ofFn bs)=some i.val →
      let x := completeScale bs n i
      let U := (lower (bs i):ℝ)
      1<x ∧ x^(1-zeta)≤N ∧ (N:ℝ)≤x^(1+kappa) ∧ x^(2*zeta)≤U ∧ U≤x^(1/3+zeta/2:ℝ) ∧
      roughF x≤beforeHBCutoff K [cj,ck] ∧ beforeHBCutoff K [cj,ck]≤x^(2/(Real.log (Real.log x))^3) := by
  filter_upwards [geometry K hz hz1 hk hkz ht ht1,eventually_ge_atTop (1:ℕ)] with N H hN
  intro b kap s hb hkap hs hg u v cj ck bs n i hn hw hi
  obtain ⟨hlo,hhi,hX,hxX⟩ := live_geometry (by omega) hb hkap hs hg cj ck bs n i hn hw
  obtain ⟨hU,hU'⟩ := selected_window bs i cj ck zeta hi
  have J := H (completeScale bs n i) (R cj*R ck) (lower (bs i):ℝ) hlo hhi hX hxX hU hU'
  have harg : P5Z.OriginalChartRoughCutoff.argument K (scales [cj,ck])=
      (2:ℝ)^(6*K+2)*(4*(R cj*R ck)) := by
    norm_num [P5Z.OriginalChartRoughCutoff.argument,scales]
  simpa only [beforeHBCutoff,P5Z.OriginalChartRoughCutoff.chartCutoff,harg] using J

end
end ImbalancedChen.P4BOriginalHighRankMediumScale
