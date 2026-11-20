import ImbalancedChen.P4BOriginalRoughE3Assembly
import ImbalancedChen.P4BOriginalTwoLongActualAssignment

/-! SOURCE ONLY / UNCOMPILED. Current live-row geometry for the
twice-mean invoice. M is the product of remaining block lowers, not
an integer-product owner. The long positions are the existing block-only choices. -/
namespace ImbalancedChen.P4BOriginalPairMeanGeometry
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalNoMediumPairRows
open P4BOriginalTwoLongActualScales
open P4BOriginalHighRankMotherScale (completeScale tuple_scale live_geometry)
open P4BUpperPairOrderedRowGeometry
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower owns_bounds)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle mem_rectangle)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open P5Z.ExactOriginalSmoothDyadicPartition (R R_pos)
open Part3.TwoLongActualHBShortMass (ShortPositions shortScale product_two_positions)
open P4BOuterRampRoughness (baseline)

theorem actual_MUV {r : ℕ} (bs : Fin r→Block) (y : Fin r→ℕ)
    (hy : y∈rectangle bs) (i k : Fin r) (hik : i≠k) :
    (shortScale (fun t : ShortPositions i k => bs t.val):ℝ)*(lower (bs i):ℝ)*(lower (bs k):ℝ)≤
      4*completeScale bs y i := by
  have hprod : (∏ t,lower (bs t))≤completeProduct y :=
    Finset.prod_le_prod' (fun t _ => (owns_bounds ((mem_rectangle bs y).mp hy t)).1)
  have he := product_two_positions i k hik (fun t => lower (bs t))
  have hreal : (shortScale (fun t : ShortPositions i k => bs t.val):ℝ)*
      (lower (bs i):ℝ)*(lower (bs k):ℝ)=(∏ t,lower (bs t):ℕ) := by
    rw [he]
    simp only [shortScale,Nat.cast_mul,Nat.cast_prod]
    ring
  rw [hreal]
  exact (show ((∏ t,lower (bs t):ℕ):ℝ)≤(completeProduct y:ℝ) by exact_mod_cast hprod).trans
    (tuple_scale bs y i hy).2

theorem eventually_native_long_lengths {zeta kap0 : ℝ}
    (hz : 0<zeta) (hz1 : zeta≤1/400) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop,∀ {b kap s : ℝ},0<b → 0<kap → 0<s → 2*s≤baseline b kap-19/96 →
      ∀ (j l cj ck : ℕ),j∈Finset.range 3 → l∈Finset.range 3 →
      ∀ (bs : Fin (2*(j+1))→Block) (cs : Fin (2*(l+1))→Block)
        (y : Fin (2*(j+1)+2*(l+1))→ℕ),
      y∈rectangle (Fin.append bs cs) →
      integerProfile (a:=2*(j+1)) (d:=2*(l+1)) b kap s N kap0 cj ck y≠0 →
      noMedium zeta cj ck (Fin.append bs cs) →
      ∀ i1 i2,
      i1=chooseLong (by omega) ((R cj*R ck)^(1/3+zeta/4:ℝ)) bs →
      i2=chooseLong (by omega) ((R cj*R ck)^(1/3+zeta/4:ℝ)) cs →
      let i := Fin.castAdd (2*(l+1)) i1
      let k := Fin.natAdd (2*(j+1)) i2
      let x := completeScale (Fin.append bs cs) y i
      x^(1/3:ℝ)<(lower (Fin.append bs cs i):ℝ) ∧
        x^(1/3:ℝ)<(lower (Fin.append bs cs k):ℝ) := by
  have hX : ∀ᶠ X : ℝ in atTop,1≤X ∧ 4<X^(3*zeta/4) ∧ (4:ℝ)^(1/3:ℝ)≤X^(zeta/4) := by
    filter_upwards [eventually_ge_atTop (1:ℝ),
      (Real.tendsto_rpow_atTop (by linarith : 0<3*zeta/4)).eventually_gt_atTop 4,
      (Real.tendsto_rpow_atTop (by linarith : 0<zeta/4)).eventually_ge_atTop ((4:ℝ)^(1/3:ℝ))]
      with X h1 h2 h3
    exact ⟨h1,h2,h3⟩
  obtain ⟨X0,HX⟩ := eventually_atTop.mp hX
  filter_upwards [eventually_live_large ht1 (max 1 X0),
    eventually_mother_short_gap (kap0:=kap0) hz hz1,eventually_ge_atTop (1:ℕ)] with N hlarge hshort hN
  intro b kap s hb hk hs hg j l cj ck hj hl bs cs y hy hw hnone i1 i2 hi1 hi2
  let i := Fin.castAdd (2*(l+1)) i1
  let k := Fin.natAdd (2*(j+1)) i2
  have hbig := hlarge hb hk hs hg _ _ cj ck (Fin.append bs cs) y i hy hw
  obtain ⟨hX1,hthree,hXroot⟩ := HX _ ((le_max_right _ _).trans hbig.2)
  obtain ⟨leftChoice,rightChoice,ha,hb',_,hlong1,hlong2,_⟩ := select_actual_pair hj hl hb hs hg hz cj ck bs cs y hy hw hnone
    (hshort hb hk hs hg _ _ cj ck (Fin.append bs cs) y i hy hw) hthree
  have ea : leftChoice=i1 := ha.trans hi1.symm
  have eb : rightChoice=i2 := hb'.trans hi2.symm
  subst leftChoice
  subst rightChoice
  obtain ⟨_,_,_,hxX⟩ := live_geometry (by omega) hb hk hs hg cj ck (Fin.append bs cs) y i hy hw
  have hx1 : 1≤completeScale (Fin.append bs cs) y i := (le_max_left _ _).trans hbig.1
  exact ⟨P5Z.SmoothChartPhysicalHBBranch.original_long_local_length hx1 hX1 (by norm_num)
    hxX hXroot hlong1,
    P5Z.SmoothChartPhysicalHBBranch.original_long_local_length hx1 hX1 (by norm_num)
      hxX hXroot hlong2⟩

theorem mean_power_terms {x M U V y : ℝ} (hx : 1<x)
    (hM : 0≤M) (hU : 0≤U) (hV : 0≤V) (hy : 0≤y)
    (hprod : M*U*V≤4*x) (hUmin : x^(1/3:ℝ)≤U) (hVmin : x^(1/3:ℝ)≤V)
    (hMpow : M≤x^(1/10:ℝ)) (hypow : y≤x^brunEpsilon) :
    M*(U+V)*y≤8*x^(2/3+brunEpsilon:ℝ) ∧ M*y^2≤x^(1/10+2*brunEpsilon:ℝ) := by
  have hx0 := zero_lt_one.trans hx
  have hp : 0<x^(1/3:ℝ) := Real.rpow_pos_of_pos hx0 _
  have hid : x^(2/3:ℝ)*x^(1/3:ℝ)=x := by
    rw [←Real.rpow_add hx0,show (2/3:ℝ)+1/3=1 by norm_num,Real.rpow_one]
  have hMU : M*U≤4*x^(2/3:ℝ) := by
    apply (mul_le_mul_right hp).mp
    rw [mul_assoc,hid]
    simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hVmin (mul_nonneg hM hU)).trans hprod
  have hMV : M*V≤4*x^(2/3:ℝ) := by
    apply (mul_le_mul_right hp).mp
    rw [mul_assoc,hid]
    have H := mul_le_mul_of_nonneg_left hUmin (mul_nonneg hM hV)
    nlinarith only [H,hprod]
  constructor
  · calc
      _≤(8*x^(2/3:ℝ))*y := mul_le_mul_of_nonneg_right (by nlinarith only [hMU,hMV]) hy
      _≤(8*x^(2/3:ℝ))*x^brunEpsilon := mul_le_mul_of_nonneg_left hypow (by positivity)
      _=_ := by rw [mul_assoc,←Real.rpow_add hx0]
  · calc
      _≤x^(1/10:ℝ)*(x^brunEpsilon)^2 := by gcongr
      _=_ := by rw [←Real.rpow_natCast,←Real.rpow_mul hx0.le,←Real.rpow_add hx0]; congr 1; ring

end
end ImbalancedChen.P4BOriginalPairMeanGeometry
