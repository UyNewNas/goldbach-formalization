import ImbalancedChen.P5ActualSelectedRoughSlotAPDictionary
import ImbalancedChen.P5ActualHBChartEventualClosure

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- Original finite prime-product HB charts, not an arbitrary SW family.
-- The chart cutoff is fixed BEFORE HB at f(2^(6K+2)*Xplus). The selected
-- slot and local scale come from the actual block word and complementary
-- integer product. One threshold precedes every actual chart and interval.

namespace ImbalancedChen.P5Z.ActualPrimeProductChartRoughSW
noncomputable section
open Classical Filter
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.ActualRoughContourParameters20261026b
open ImbalancedChen.Part3.ActualRoughIntervalAllModuliSW20261028
open ImbalancedChen.Part3.RoughAPTwistAverage20261027
open ActualRoughHeathBrownWords HBRightClosedDyadicRoles ActualHBDyadicProductWindow
open ActualHBMediumBranchPartition SmoothChartPhysicalHBBranch
open ActualMultiGroupHBChartScale ActualHBChartEventualClosure
open ActualSelectedRoughSlotAPDictionary

def originalChartArgument (K : ℕ) (gs : List Group) : ℝ :=
  (2 : ℝ)^(6*K+2)*chartXplus gs

def originalChartCutoff (K : ℕ) (gs : List Group) : ℝ :=
  roughZ (originalChartArgument K gs)

def chartComparison (K : ℕ) : ℝ :=
  (2 : ℝ)^(6*K+2)*2^K*scaleConstant K

theorem chartComparison_pos (K : ℕ) : 0 < chartComparison K := by
  unfold chartComparison
  exact mul_pos (by positivity) (scaleConstant_pos K)

-- This uses the exact (S) upper endpoint from the actual integer-product
-- owner. The coarser symmetric scaleConstant would lose the lower v>=x.
theorem original_chart_argument_bounds {K : ℕ} (gs : List Group)
    (hrank : gs.length ≤ K) {x : ℝ} (hxp : 0 < x)
    (hXx : chartX gs ≤ scaleConstant K*x)
    (hS : x ≤ (2 : ℝ)^(6*gs.length-1)*chartXplus gs) :
    x ≤ originalChartArgument K gs ∧
      originalChartArgument K gs ≤ chartComparison K*x := by
  have hXp := (whole_geometry gs).1
  have hXplus : 0 ≤ chartXplus gs := by unfold chartXplus; positivity
  have hpow : (2 : ℝ)^(6*gs.length-1) ≤ 2^(6*K+2) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hk : (2 : ℝ)^gs.length ≤ 2^K :=
    pow_le_pow_right₀ (by norm_num) hrank
  refine ⟨hS.trans (mul_le_mul_of_nonneg_right hpow hXplus),?_⟩
  calc
    originalChartArgument K gs = (2 : ℝ)^(6*K+2)*(2^gs.length*chartX gs) := rfl
    _ ≤ (2 : ℝ)^(6*K+2)*(2^K*chartX gs) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk hXp.le) (by positivity)
    _ ≤ (2 : ℝ)^(6*K+2)*(2^K*(scaleConstant K*x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXx (by positivity)) (by positivity)
    _ = chartComparison K*x := by unfold chartComparison; ring

theorem selected_split_medium {X zeta : ℝ} {gs : List Group}
    (left right : List Block) (b : Block)
    (hsplit : blocks gs = left++b::right)
    (hselect : firstMedium (originalLower X zeta) (originalUpper X zeta)
      (blocks gs) = some left.length) :
    Medium (originalLower X zeta) (originalUpper X zeta) b := by
  obtain ⟨hi,hm,hbefore⟩ := firstMedium_some hselect
  have he : (blocks gs)[left.length]'hi = b := by simp [hsplit]
  simpa only [he] using hm

-- Exact original source parameters: K is the finite original rank bound;
-- c*T^astar is the original individual prime support, and the complete
-- smooth trim is T^(1-kappa0)<=chartN<=C*T. No SW output is a premise.
theorem actual_selected_prime_product_chart_auxiliary_SW
    (K : ℕ) {c C astar a kappa0 zeta A L : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hzeta : 0 < zeta) (hzetaSmall : zeta < 1/100)
    (haShort : 18*zeta < a) (haPrime : a < astar) (hkappa : kappa0 < 1)
    (hA : 0 ≤ A) (hL : 0 ≤ L) :
    ∃ CSW : ℝ, 0 < CSW ∧ ∃ T0 : ℝ, 1 < T0 ∧
      ∀ T : ℝ, T0 ≤ T → ∀ gs : List Group, gs.length ≤ K →
      (∀ g ∈ gs, c*T^astar ≤ (g.n : ℝ)) →
      T^(1-kappa0) ≤ chartN gs → chartN gs ≤ C*T →
      (∀ g ∈ gs, g.z = originalChartCutoff K gs) →
      ∀ (left right : List Block) (b : Block), blocks gs = left++b::right →
      firstMedium (originalLower (chartX gs) zeta) (originalUpper (chartX gs) zeta)
        (blocks gs) = some left.length →
      ∃ pl p pr, integers gs = pl++p::pr ∧
        let x : ℝ := (lower b : ℝ)*(lower (owner (pl++pr).prod) : ℝ)
        ∀ g ∈ gs, ∀ useMu : Bool,
        (roughRole useMu,b) ∈ (roles g.j).zip g.bs →
        ∀ k q residue : ℕ, 0 < k → 0 < q → residue.Coprime q →
        ∀ τ lo hi : ℝ, |τ| ≤ (Real.log x)^L →
        (lower b : ℝ) ≤ lo → lo ≤ hi → hi ≤ 2*(lower b : ℝ) →
        ‖auxiliarySWError (intervalCarrier lo hi)
          (selectedCoefficient b useMu g.z g.y τ) k q residue‖ ≤
          CSW*(lower b : ℝ)*(k.divisors.card : ℝ)/(Real.log x)^A := by
  obtain ⟨CSW,hCSW,xSW,hxSW,hSW⟩ :=
    exists_original_chart_rough_AP_all_moduli A L (2*zeta) hA hL (by linarith)
  obtain ⟨Lgeo,hLgeo,hres⟩ := fixed_reserves K hzeta haShort
  let e : ℝ := 1/3+zeta/2
  have he : 0 < 1-e := by dsimp [e]; linarith
  obtain ⟨R,hR⟩ := eventually_atTop.mp
    ((_root_.tendsto_rpow_atTop he).eventually (eventually_ge_atTop (2 : ℝ)))
  let B : ℝ := max xSW (max (chartComparison K) (max R 2))
  let Lall : ℝ := max Lgeo (scaleConstant K*B)
  have ha0 : 0 ≤ a := by linarith
  obtain ⟨T0,hT0,hsizes⟩ := original_sizes_eventually (L:=Lall) K hc hC ha0 haPrime hkappa
  refine ⟨CSW,hCSW,T0,hT0,?_⟩
  intro T hT gs hrank hindividual htrim hupper hcutoff left right b hsplit hselect
  obtain ⟨hXL,hmember⟩ := hsizes T hT gs hrank hindividual htrim hupper
  obtain ⟨pl,p,pr,hints,hl,hp,hr,howner,hxp,hXx,hS,hxX⟩ :=
    actual_complementary_scale gs left right b hsplit
  let x : ℝ := (lower b : ℝ)*(lower (owner (pl++pr).prod) : ℝ)
  let U : ℝ := lower b
  have hXp := (whole_geometry gs).1
  have hSmono := scaleConstant_mono hrank
  have hXxK : chartX gs ≤ scaleConstant K*x :=
    hXx.trans (mul_le_mul_of_nonneg_right hSmono hxp.le)
  have hxXK : x ≤ scaleConstant K*chartX gs :=
    hxX.trans (mul_le_mul_of_nonneg_right hSmono hXp.le)
  have hBx : B ≤ x := by
    have hh : scaleConstant K*B ≤ chartX gs := (le_max_right _ _).trans hXL
    exact (mul_le_mul_left (scaleConstant_pos K)).mp (hh.trans hXxK)
  have hxAnal : xSW ≤ x := (le_max_left _ _).trans hBx
  have hxD : chartComparison K ≤ x :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hBx)
  have hxR : R ≤ x := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hBx))
  have hx2 : 2 ≤ x := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hBx))
  have hXLgeo : Lgeo ≤ chartX gs := (le_max_left _ _).trans hXL
  obtain ⟨hX1,hx1,hAlow,hshort,hlong,hlower,hupperRes,hLongLocal,hGlobal⟩ :=
    hres (chartX gs) x hXLgeo hXxK
  have hm := selected_split_medium left right b hsplit hselect
  have hlocal := original_to_local_medium hx1.le hX1.le (scaleConstant_pos K).le
    hzeta.le hxXK hXxK hlower hupperRes hm
  have hUp : 0 < U := by dsimp [U]; exact_mod_cast lower_pos b
  have hU1 : 1 < U :=
    (Real.one_lt_rpow hx1 (by linarith : 0 < 2*zeta)).trans_le hlocal.1
  have hUhi : 2*U ≤ x := by
    have hh : 2 ≤ x^(1-e) := hR x hxR
    have hpaid := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hxp.le e)
    have hpowers : x^(1-e)*x^e = x := by
      rw [← Real.rpow_add hxp]
      have heq : 1-e+e = (1 : ℝ) := by ring
      rw [heq,Real.rpow_one]
    rw [hpowers] at hpaid
    have hbound : U ≤ x^e := hlocal.2
    linarith
  have hv := original_chart_argument_bounds gs hrank hxp hXxK hS
  have hvSquare : originalChartArgument K gs ≤ x^2 := by
    have hh := mul_le_mul_of_nonneg_right hxD hxp.le
    exact hv.2.trans (by simpa only [pow_two] using hh)
  refine ⟨pl,p,pr,hints,?_⟩
  intro g hg useMu hrole k q residue hk hq hb τ lo hi hτ hlo hlohi hhi
  have hgcut := hcutoff g hg
  have hhiX : hi ≤ x := hhi.trans hUhi
  have hLp : 0 < Real.log x := Real.log_pos hx1
  have hRHS : 0 ≤ CSW*U*(k.divisors.card : ℝ)/(Real.log x)^A := by positivity
  by_cases hempty : useMu = true ∧ g.y ≤ lo
  · rcases hempty with ⟨rfl,hy⟩
    rw [selected_error_zero_of_cutoff_before_interval b g.z g.y τ lo hi hU1 hlo hy]
    simpa only [norm_zero] using hRHS
  · have hclipLo : lo ≤ clippedUpper useMu g.y hi := by
      cases useMu with
      | false => simpa [clippedUpper] using hlohi
      | true =>
        have hy : lo < g.y := lt_of_not_ge (fun h => hempty ⟨rfl,h⟩)
        simpa [clippedUpper] using le_min hlohi hy.le
    have hclipHi : clippedUpper useMu g.y hi ≤ hi := by
      cases useMu <;> simp [clippedUpper]
    rw [selected_error_eq_clipped b useMu g.z g.y τ lo hi hU1 hlo hhi,
      hgcut]
    exact hSW x hxAnal (originalChartArgument K gs) hv.1 hvSquare
      k q residue hk hq hb useMu τ U lo (clippedUpper useMu g.y hi)
      hτ hUp hlocal.1 hlo hclipLo (hclipHi.trans hhi) (hclipHi.trans hhiX)

end
end ImbalancedChen.P5Z.ActualPrimeProductChartRoughSW
