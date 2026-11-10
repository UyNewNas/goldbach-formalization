import ImbalancedChen.P5ActualMultiGroupHBChartScale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- Fixed rank and strict exponent margins supply ONE threshold. Original
-- size/trim hypotheses are the manuscript geometric support conditions,
-- not an R/128 bound, scale-comparability oracle or distribution estimate.
namespace ImbalancedChen.P5Z.ActualHBChartEventualClosure
noncomputable section
open Classical Filter
open scoped BigOperators
open LiteralHeathBrownOccurrenceWords ActualRoughHeathBrownWords
open HBRightClosedDyadicRoles ActualHBDyadicOccurrenceFamily
open ActualHBDyadicProductWindow ActualHBMediumBranchPartition
open SmoothChartHBDyadicPartition SmoothChartPhysicalHBBranch
open ActualMultiGroupHBChartScale

theorem fixed_reserves (K : ℕ) {a zeta : ℝ}
    (hzeta : 0 < zeta) (ha : 18*zeta < a) :
    ∃ L : ℝ, 1 < L ∧ ∀ X x : ℝ, L ≤ X → X ≤ scaleConstant K*x →
      1 < X ∧ 1 < x ∧ 1 < originalLower X zeta ∧
      8192 < X^(a-18*zeta) ∧ 4 < X^(3*zeta/4) ∧
      (scaleConstant K)^(2*zeta) ≤ X^zeta ∧
      (scaleConstant K)^(1/3+zeta/4) ≤ x^(zeta/4) ∧
      (scaleConstant K)^(1/3 : ℝ) ≤ X^(zeta/4) ∧
      (2 : ℝ)^K < X^(3*zeta/4) := by
  have he : ∀ᶠ t : ℝ in atTop,
      1 < t ∧ 8192 < t^(a-18*zeta) ∧ 4 < t^(3*zeta/4) ∧
      (scaleConstant K)^(2*zeta) ≤ t^zeta ∧
      (scaleConstant K)^(1/3+zeta/4) ≤ t^(zeta/4) ∧
      (scaleConstant K)^(1/3 : ℝ) ≤ t^(zeta/4) ∧
      (2 : ℝ)^K < t^(3*zeta/4) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      (_root_.tendsto_rpow_atTop (by linarith : 0 < a-18*zeta)).eventually
        (eventually_gt_atTop (8192 : ℝ)),
      (_root_.tendsto_rpow_atTop (by linarith : 0 < 3*zeta/4)).eventually
        (eventually_gt_atTop (4 : ℝ)),
      (_root_.tendsto_rpow_atTop hzeta).eventually
        (eventually_ge_atTop ((scaleConstant K)^(2*zeta))),
      (_root_.tendsto_rpow_atTop (by linarith : 0 < zeta/4)).eventually
        (eventually_ge_atTop ((scaleConstant K)^(1/3+zeta/4))),
      (_root_.tendsto_rpow_atTop (by linarith : 0 < zeta/4)).eventually
        (eventually_ge_atTop ((scaleConstant K)^(1/3 : ℝ))),
      (_root_.tendsto_rpow_atTop (by linarith : 0 < 3*zeta/4)).eventually
        (eventually_gt_atTop ((2 : ℝ)^K))]
      with t h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨B,hB⟩ := eventually_atTop.mp he
  let b : ℝ := max 1 B
  let L : ℝ := scaleConstant K*b
  have hb : 1 ≤ b := le_max_left _ _
  have hBb : B ≤ b := le_max_right _ _
  have hS := scaleConstant_ge_two K
  have hSp := scaleConstant_pos K
  have hL : 1 < L := by dsimp [L]; nlinarith
  refine ⟨L,hL,?_⟩
  intro X x hLX hXx
  have hbX : b ≤ X := by dsimp [L] at hLX; nlinarith
  have hbx : b ≤ x := by dsimp [L] at hLX; nlinarith
  obtain ⟨hX1,hXshort,hXlong,hXlow,hXupper,hXlongLocal,hXglobal⟩ := hB X (hBb.trans hbX)
  obtain ⟨hx1,hxshort,hxlong,hxlow,hxupper,hxlongLocal,hxglobal⟩ := hB x (hBb.trans hbx)
  have hA : 1 < originalLower X zeta :=
    Real.one_lt_rpow hX1 (by linarith : 0 < 3*zeta)
  exact ⟨hX1,hx1,hA,hXshort,hXlong,hXlow,hxupper,hXlongLocal,hXglobal⟩

-- Supply X^a<=R from the ORIGINAL individual polynomial cutoff,
-- complete smooth trim, and fixed upper complete-product support.
theorem original_sizes_eventually (K : ℕ) {c C astar a kappa0 L : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (ha0 : 0 ≤ a) (ha : a < astar)
    (hkappa : kappa0 < 1) :
    ∃ T0 : ℝ, 1 < T0 ∧ ∀ T : ℝ, T0 ≤ T → ∀ gs : List Group,
      gs.length ≤ K →
      (∀ g ∈ gs, c*T^astar ≤ (g.n : ℝ)) →
      T^(1-kappa0) ≤ chartN gs → chartN gs ≤ C*T →
      L ≤ chartX gs ∧ ∀ g ∈ gs, 1 ≤ g.R ∧ (chartX gs)^a ≤ g.R := by
  let D : ℝ := (2 : ℝ)^K*C
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hastar : 0 < astar := lt_of_le_of_lt ha0 ha
  have he : ∀ᶠ T : ℝ in atTop,
      1 < T ∧ 2/c ≤ T^astar ∧ (2/c)*D^a ≤ T^(astar-a) ∧
      (2 : ℝ)^K*L ≤ T^(1-kappa0) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      (_root_.tendsto_rpow_atTop hastar).eventually (eventually_ge_atTop (2/c)),
      (_root_.tendsto_rpow_atTop (sub_pos.mpr ha)).eventually
        (eventually_ge_atTop ((2/c)*D^a)),
      (_root_.tendsto_rpow_atTop (by linarith : 0 < 1-kappa0)).eventually
        (eventually_ge_atTop ((2 : ℝ)^K*L))] with T h1 h2 h3 h4
    exact ⟨h1,h2,h3,h4⟩
  obtain ⟨B,hB⟩ := eventually_atTop.mp he
  let T0 : ℝ := max 2 B
  refine ⟨T0,by dsimp [T0]; linarith [le_max_left (2 : ℝ) B],?_⟩
  intro T hT gs hrank hindividual htrim hupper
  have hBT : B ≤ T := (le_max_right (2 : ℝ) B).trans hT
  obtain ⟨hT1,hunit,hgap,htrimLarge⟩ := hB T hBT
  have hTp : 0 < T := by linarith
  obtain ⟨hNp,hNX,hXN⟩ := original_product_geometry gs
  have hXp := (whole_geometry gs).1
  have h2pow : (2 : ℝ)^gs.length ≤ 2^K :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hrank
  have hXupper : chartX gs ≤ D*T := by
    calc
      chartX gs ≤ (2 : ℝ)^gs.length*chartN gs := hXN
      _ ≤ (2 : ℝ)^K*chartN gs := mul_le_mul_of_nonneg_right h2pow hNp.le
      _ ≤ (2 : ℝ)^K*(C*T) := mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = D*T := by dsimp [D]; ring
  have hXL : L ≤ chartX gs := by
    have hh : (2 : ℝ)^K*L ≤ (2 : ℝ)^K*chartX gs := by
      calc
        (2 : ℝ)^K*L ≤ T^(1-kappa0) := htrimLarge
        _ ≤ chartN gs := htrim
        _ ≤ (2 : ℝ)^gs.length*chartX gs := hNX
        _ ≤ (2 : ℝ)^K*chartX gs := mul_le_mul_of_nonneg_right h2pow hXp.le
    exact (mul_le_mul_left (by positivity : (0 : ℝ) < 2^K)).mp hh
  refine ⟨hXL,?_⟩
  intro g hg
  have hs := smooth_group_support g.positive g.lower_support g.upper_support
    g.w (mul_ne_zero_iff.mp g.active).1
  have hsize := hindividual g hg
  have hRfloor : c*T^astar/2 ≤ g.R := by linarith
  have hRone : 1 ≤ g.R := by
    have hh := mul_le_mul_of_nonneg_left hunit hc.le
    have hcancel : c*(2/c) = 2 := by field_simp [ne_of_gt hc]
    rw [hcancel] at hh
    linarith
  have hscaled : D^a ≤ (c/2)*T^(astar-a) := by
    have hh := mul_le_mul_of_nonneg_left hgap (by linarith : 0 ≤ c/2)
    have hcancel : (c/2)*((2/c)*D^a) = D^a := by field_simp [ne_of_gt hc]; ring
    rw [hcancel] at hh
    exact hh
  have hpowid : T^(astar-a)*T^a = T^astar := by
    rw [← Real.rpow_add hTp]
    congr 1
    ring
  have hRa : (chartX gs)^a ≤ g.R := by
    calc
      (chartX gs)^a ≤ (D*T)^a := Real.rpow_le_rpow hXp.le hXupper ha0
      _ = D^a*T^a := Real.mul_rpow hD hTp.le
      _ ≤ ((c/2)*T^(astar-a))*T^a :=
        mul_le_mul_of_nonneg_right hscaled (Real.rpow_nonneg hTp.le _)
      _ = c*T^astar/2 := by rw [mul_assoc,hpowid]; ring
      _ ≤ g.R := hRfloor
  exact ⟨hRone,hRa⟩

-- This predicate records ACTUAL branch data, never a premise. Its proof
-- below instantiates the physical Phase2 theorem with derived parameters.
def Assigned (g : Group) (X x zeta : ℝ) : Prop :=
  (∃ i : ℕ, firstMedium (originalLower X zeta) (originalUpper X zeta) g.bs = some i ∧
    ∃ ps ∈ factorTuples (2*(g.j+1)) g.n,
      assignedWeight g.z g.y (roles g.j) g.bs ps ≠ 0 ∧
      ∃ hi : i < g.bs.length, ∃ hp : i < ps.length,
        x^(2*zeta) ≤ (lower g.bs[i] : ℝ) ∧
        (lower g.bs[i] : ℝ) ≤ x^(1/3+zeta/2) ∧
        (lower g.bs[i] : ℝ) < (ps[i] : ℝ) ∧
        (ps[i] : ℝ) ≤ 2*(lower g.bs[i] : ℝ) ∧
        0 < ps[i] ∧ ps[i] ≤ g.n ∧
        (∀ p ∈ ps.take (g.j+1), (p : ℝ) ≤ g.y)) ∨
  (firstMedium (originalLower X zeta) (originalUpper X zeta) g.bs = none ∧
    ((longBlocks (originalUpper X zeta) g.bs).length = 1 ∨
      (longBlocks (originalUpper X zeta) g.bs).length = 2) ∧
    (∀ rb ∈ (roles g.j).zip g.bs,
      originalUpper X zeta < (lower rb.2 : ℝ) →
        rb.1 = .one ∨ rb.1 = .logarithm))

theorem actual_family_eventual_closure (K : ℕ) {c C astar a kappa0 zeta : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hzeta : 0 < zeta)
    (haShort : 18*zeta < a) (haPrime : a < astar) (hkappa : kappa0 < 1) :
    ∃ T0 : ℝ, 1 < T0 ∧ ∀ T : ℝ, T0 ≤ T → ∀ gs : List Group,
      gs.length ≤ K →
      (∀ g ∈ gs, c*T^astar ≤ (g.n : ℝ)) →
      T^(1-kappa0) ≤ chartN gs → chartN gs ≤ C*T →
      ∀ (left right : List Block) (b : Block), blocks gs = left++b::right →
        ∃ pl p pr, integers gs = pl++p::pr ∧
          let x : ℝ := (lower b : ℝ)*(lower (owner (pl++pr).prod) : ℝ)
          1 < x ∧ chartX gs ≤ scaleConstant K*x ∧
          x ≤ scaleConstant K*chartX gs ∧
          (∀ g ∈ gs, Assigned g (chartX gs) x zeta) ∧
          (firstMedium (originalLower (chartX gs) zeta) (originalUpper (chartX gs) zeta)
              (blocks gs) = none →
            (longBlocks (originalUpper (chartX gs) zeta) (blocks gs)).length = 1 ∨
              (longBlocks (originalUpper (chartX gs) zeta) (blocks gs)).length = 2) ∧
          (∀ U : ℝ, originalUpper (chartX gs) zeta < U → x^(1/3 : ℝ) < U) := by
  obtain ⟨L,hL,hres⟩ := fixed_reserves K hzeta haShort
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨T0,hT0,hsizes⟩ := original_sizes_eventually (L:=L) K hc hC ha0 haPrime hkappa
  refine ⟨T0,hT0,?_⟩
  intro T hT gs hrank hindividual htrim hupper left right b hsplit
  obtain ⟨hXL,hmember⟩ := hsizes T hT gs hrank hindividual htrim hupper
  obtain ⟨pl,p,pr,hints,hl,hp,hr,howner,hxp,hXx,hSupper,hxX⟩ :=
    actual_complementary_scale gs left right b hsplit
  let x : ℝ := (lower b : ℝ)*(lower (owner (pl++pr).prod) : ℝ)
  have hXp := (whole_geometry gs).1
  have hscale := scaleConstant_mono hrank
  have hXxK : chartX gs ≤ scaleConstant K*x :=
    hXx.trans (mul_le_mul_of_nonneg_right hscale hxp.le)
  have hxXK : x ≤ scaleConstant K*chartX gs :=
    hxX.trans (mul_le_mul_of_nonneg_right hscale hXp.le)
  obtain ⟨hX1,hx1,hA,hshort,hlong,hlowerRes,hupperRes,hlongRes,hglobalLong⟩ :=
    hres (chartX gs) x hXL hXxK
  have hmemberX := (member_scale_le gs (fun g hg => (hmember g hg).1)).2
  have hassigned : ∀ g ∈ gs, Assigned g (chartX gs) x zeta := by
    intro g hg
    have hR2 : 2*g.R ≤ 2*chartX gs := by linarith [hmemberX g hg]
    exact physical_original_branch_assignment (C:=2) (Cscale:=scaleConstant K)
      g.positive g.rough_nonneg g.hb_nonneg
      g.lower_support g.upper_support hX1.le hx1.le hzeta.le (by norm_num)
      (hmember g hg).2 hR2 g.hb_cube hshort hlong hA (scaleConstant_pos K).le
      hxXK hXxK hlowerRes hupperRes g.w g.order g.active
  have hglobalCount :
      firstMedium (originalLower (chartX gs) zeta) (originalUpper (chartX gs) zeta)
          (blocks gs) = none →
        (longBlocks (originalUpper (chartX gs) zeta) (blocks gs)).length = 1 ∨
          (longBlocks (originalUpper (chartX gs) zeta) (blocks gs)).length = 2 := by
    intro hnone
    obtain ⟨g,tail,hgs⟩ : ∃ g tail, gs = g::tail := by
      cases he : gs with
      | nil =>
        have hlen := congrArg List.length hsplit
        simp only [he,blocks,List.length_nil,List.length_append,List.length_cons] at hlen
        omega
      | cons g tail => exact ⟨g,tail,he⟩
    have hg : g ∈ gs := by simp [hgs]
    have hgNone : firstMedium (originalLower (chartX gs) zeta)
        (originalUpper (chartX gs) zeta) g.bs = none := by
      apply firstMedium_none.mpr
      intro bb hbb
      apply firstMedium_none.mp hnone bb
      rw [hgs,blocks]
      exact List.mem_append.mpr (Or.inl hbb)
    have hs := smooth_group_support g.positive g.lower_support g.upper_support
      g.w (mul_ne_zero_iff.mp g.active).1
    have hR2 : 2*g.R ≤ 2*chartX gs := by linarith [hmemberX g hg]
    have hnX : (g.n : ℝ) ≤ 2*chartX gs := hs.2.trans hR2
    obtain ⟨hAr,hBr,hshortn,hcompn,hyB⟩ :=
      OriginalHBMediumChartReserves.original_chart_numeric_reserves (C:=2)
        hX1.le hzeta.le (by norm_num) (hmember g hg).2
        (by linarith : g.R ≤ 2*chartX gs) (by linarith : g.R/128 ≤ (g.n : ℝ))
        hnX g.hb_nonneg g.hb_cube hshort hlong
    obtain ⟨bb,hbb,hblong⟩ := actual_noMedium_has_long g.rough_nonneg hAr
      g.order (mul_ne_zero_iff.mp g.active).2 hgNone hshortn
    have hbfull : bb ∈ blocks gs := by
      rw [hgs,blocks]
      exact List.mem_append.mpr (Or.inl hbb)
    have hlongmem : bb ∈ longBlocks (originalUpper (chartX gs) zeta) (blocks gs) := by
      simp [longBlocks,hbfull,hblong]
    have hpos : 0 < (longBlocks (originalUpper (chartX gs) zeta) (blocks gs)).length :=
      List.length_pos.mpr (by intro he; simpa [he] using hlongmem)
    have hB3 : (originalUpper (chartX gs) zeta)^3 =
        chartX gs*(chartX gs)^(3*zeta/4) := by
      unfold originalUpper
      rw [← Real.rpow_natCast,← Real.rpow_mul hXp.le]
      have he : (1/3+zeta/4)*(3 : ℝ) = 1+3*zeta/4 := by ring
      rw [he,Real.rpow_add hXp,Real.rpow_one]
    have hrawBelow : rawProduct (blocks gs) < (originalUpper (chartX gs) zeta)^3 := by
      rw [hB3]
      calc
        rawProduct (blocks gs) ≤ chartXplus gs := (whole_geometry gs).2.2.2
        _ ≤ (2 : ℝ)^K*chartX gs := by
          unfold chartXplus
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hrank) hXp.le
        _ < chartX gs*(chartX gs)^(3*zeta/4) := by
          simpa only [mul_comm] using mul_lt_mul_of_pos_right hglobalLong hXp
    have htwo := atMostTwoLong hBr hrawBelow
    omega
  exact ⟨pl,p,pr,hints,hx1,hXxK,hxXK,hassigned,hglobalCount,
    fun U hU => original_long_local_length hx1.le hX1.le
      (scaleConstant_pos K).le hxXK hlongRes hU⟩

-- The manuscript's stricter kappa0 margin also supplies the actual
-- local shift range c0*x<=T<=x^(1+kappa), without a shift-range premise.
theorem actual_shift_range_eventually (K : ℕ) {C kappa kappa0 : ℝ}
    (hC : 0 ≤ C) (hkappa : 0 < kappa)
    (hkappa0 : kappa0 < kappa/(4*(1+kappa))) :
    ∃ c0 : ℝ, 0 < c0 ∧ ∃ T0 : ℝ, 1 < T0 ∧
      ∀ T : ℝ, T0 ≤ T → ∀ gs : List Group, gs.length ≤ K →
        T^(1-kappa0) ≤ chartN gs → chartN gs ≤ C*T →
        ∀ (left right : List Block) (b : Block), blocks gs = left++b::right →
          ∃ pl p pr, integers gs = pl++p::pr ∧
            let x : ℝ := (lower b : ℝ)*(lower (owner (pl++pr).prod) : ℝ)
            c0*x ≤ T ∧ T ≤ x^(1+kappa) := by
  let A : ℝ := (2 : ℝ)^K*scaleConstant K
  let B : ℝ := A*(C+1)
  let gap : ℝ := (1-kappa0)*(1+kappa)-1
  let c0 : ℝ := 1/B
  have hA : 0 < A := by dsimp [A]; exact mul_pos (by positivity) (scaleConstant_pos K)
  have hB : 0 < B := by dsimp [B]; positivity
  have hb : 0 < 1+kappa := by linarith
  have hkbound := (lt_div_iff₀ (by positivity : 0 < 4*(1+kappa))).mp hkappa0
  have hgap : 0 < gap := by dsimp [gap]; nlinarith
  have he : ∀ᶠ T : ℝ in atTop, 1 < T ∧ A^(1+kappa) ≤ T^gap := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      (_root_.tendsto_rpow_atTop hgap).eventually
        (eventually_ge_atTop (A^(1+kappa)))] with T h1 h2
    exact ⟨h1,h2⟩
  obtain ⟨Q,hQ⟩ := eventually_atTop.mp he
  let T0 : ℝ := max 2 Q
  refine ⟨c0,by dsimp [c0]; positivity,T0,by dsimp [T0]; linarith [le_max_left (2 : ℝ) Q],?_⟩
  intro T hT gs hrank htrim hupper left right b hsplit
  obtain ⟨hT1,hlarge⟩ := hQ T ((le_max_right (2 : ℝ) Q).trans hT)
  have hTp : 0 < T := by linarith
  obtain ⟨pl,p,pr,hints,hl,hp,hr,howner,hxp,hXx,hSupper,hxX⟩ :=
    actual_complementary_scale gs left right b hsplit
  let x : ℝ := (lower b : ℝ)*(lower (owner (pl++pr).prod) : ℝ)
  have hXp := (whole_geometry gs).1
  have hscale := scaleConstant_mono hrank
  have hXxK : chartX gs ≤ scaleConstant K*x :=
    hXx.trans (mul_le_mul_of_nonneg_right hscale hxp.le)
  have hxXK : x ≤ scaleConstant K*chartX gs :=
    hxX.trans (mul_le_mul_of_nonneg_right hscale hXp.le)
  obtain ⟨hNp,hNX,hXN⟩ := original_product_geometry gs
  have h2pow : (2 : ℝ)^gs.length ≤ 2^K :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hrank
  have hLower : T^(1-kappa0) ≤ A*x := by
    calc
      T^(1-kappa0) ≤ chartN gs := htrim
      _ ≤ (2 : ℝ)^gs.length*chartX gs := hNX
      _ ≤ (2 : ℝ)^K*chartX gs := mul_le_mul_of_nonneg_right h2pow hXp.le
      _ ≤ (2 : ℝ)^K*(scaleConstant K*x) :=
        mul_le_mul_of_nonneg_left hXxK (by positivity)
      _ = A*x := by dsimp [A]; ring
  have hxUpper : x ≤ B*T := by
    calc
      x ≤ scaleConstant K*chartX gs := hxXK
      _ ≤ scaleConstant K*((2 : ℝ)^gs.length*chartN gs) :=
        mul_le_mul_of_nonneg_left hXN (scaleConstant_pos K).le
      _ ≤ scaleConstant K*((2 : ℝ)^K*chartN gs) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2pow hNp.le)
          (scaleConstant_pos K).le
      _ ≤ scaleConstant K*((2 : ℝ)^K*(C*T)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hupper (by positivity)) (scaleConstant_pos K).le
      _ ≤ B*T := by
        have heq : scaleConstant K*((2 : ℝ)^K*(C*T)) = A*C*T := by dsimp [A]; ring
        rw [heq]
        have hnonneg : 0 ≤ A*T := mul_nonneg hA.le hTp.le
        dsimp [B]
        nlinarith
  have hc0 : c0*x ≤ T := by
    have hh : x/B ≤ T := (div_le_iff₀ hB).mpr (by simpa only [mul_comm] using hxUpper)
    simpa [c0,div_eq_mul_inv,mul_comm] using hh
  have hraise := Real.rpow_le_rpow (Real.rpow_nonneg hTp.le (1-kappa0)) hLower hb.le
  rw [← Real.rpow_mul hTp.le,Real.mul_rpow hA.le hxp.le] at hraise
  have hidentity : T^((1-kappa0)*(1+kappa)) = T*T^gap := by
    have hexp : (1-kappa0)*(1+kappa) = 1+gap := by dsimp [gap]; ring
    rw [hexp,Real.rpow_add hTp,Real.rpow_one]
  rw [hidentity] at hraise
  have hpay := mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hxp.le (1+kappa))
  have hfin : T^gap*T ≤ T^gap*x^(1+kappa) := by
    simpa only [mul_comm] using hraise.trans hpay
  have hshift : T ≤ x^(1+kappa) :=
    (mul_le_mul_left (Real.rpow_pos_of_pos hTp gap)).mp hfin
  exact ⟨pl,p,pr,hints,hc0,hshift⟩

end
end ImbalancedChen.P5Z.ActualHBChartEventualClosure
