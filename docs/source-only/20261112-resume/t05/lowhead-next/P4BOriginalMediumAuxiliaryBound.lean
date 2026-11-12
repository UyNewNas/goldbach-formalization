import ImbalancedChen.P4BOriginalMediumHBHead

/-! Exact auxiliary-coprime SW for the selected occurrence of the actual
retained two-group mother. Its real Mobius cutoff, original rough
projector, Mellin phase and right-closed endpoints are used in both sums. -/
namespace ImbalancedChen.P4BOriginalMediumAuxiliaryBound
noncomputable section
open Classical Filter Set MeasureTheory
open scoped BigOperators Topology
open Part3 (auxiliarySWError)
open Part3.ActualRoughContourParameters20261026b (roughZ)
open Part3.ActualRoughIntervalAllModuliSW20261028 (exists_original_chart_rough_AP_all_moduli)
open P5Z.ActualSelectedRoughSlotAPDictionary (intervalCarrier clippedUpper selectedCoefficient
  selected_error_eq_clipped selected_error_zero_of_cutoff_before_interval)
open P5Z.FixedProfileNormalizedLogVariation (retainedProfile profileVariationConstant
  retainedProfile_variation_le retainedProfile_hasDerivAt retainedProfile_contDiffOn)
open P5Z.RoughExactMeanComplexAbel (complex_Abel_auxiliary_error_norm_le)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualRoughHeathBrownWords (Role)
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff)
open P5Z.OriginalChartRoughCutoff (roughF)
open P5Z.AllRankCauchyCubeTail (outsideCube)
open P4BOriginalHighRankComplementBlocks (fibre)
open P4BOriginalHighRankPostModulusFibres (first)
open P4BOriginalHighRankPostModulusRow (bandwidthOrder H)
open P4BUpperPairOrderedRowGeometry (integerProfile)
open P4BOuterRampRoughness (baseline)
open P4BOriginalMediumHBHead (alpha muRole logRole)

private theorem normalized_rough_window (A L θ : ℝ) (hA : 0≤A) (hL : 0≤L) (hθ : 0<θ) :
    ∃ C : ℝ,0<C ∧ ∃ x0 : ℝ,1<x0 ∧
    ∀ {x v : ℝ},x0≤x → x≤v → v≤x^2 → ∀ (b : Block),1<(lower b:ℝ) →
    x^θ≤(lower b:ℝ) → 2*(lower b:ℝ)≤x → ∀ (r : Role) (Y τ lo hi : ℝ),
    |τ|≤(Real.log x)^L → (lower b:ℝ)≤lo → lo≤hi → hi≤2*(lower b:ℝ) →
    ∀ k q residue : ℕ,0<k → 0<q → residue.Coprime q →
    ‖auxiliarySWError (intervalCarrier lo hi) (alpha b (roughZ v) Y r τ) k q residue‖≤
      C*(lower b:ℝ)*(k.divisors.card:ℝ)/(Real.log x)^A := by
  obtain ⟨C,hC,x0,hx0,Hraw⟩ := exists_original_chart_rough_AP_all_moduli A L θ hA hL hθ
  let V := profileVariationConstant 1 0
  have hV : 0<V := by
    have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
    dsimp [V,profileVariationConstant]
    positivity
  refine ⟨C*V,mul_pos hC hV,x0,hx0,?_⟩
  intro x v hx hxv hvx b hU1 hU htop r Y τ lo hi hτ hlo hlh hhi k q residue hk hq hres
  let U := (lower b:ℝ)
  let useMu := muRole r
  let E := C*U*(k.divisors.card:ℝ)/(Real.log x)^A
  have hUp : 0<U := zero_lt_one.trans hU1
  have hlog : 0<Real.log x := Real.log_pos (hx0.trans_le hx)
  have hE : 0≤E := by dsimp only [E]; positivity
  have prefix (t : ℝ) (ht : t∈Icc lo hi) :
      ‖auxiliarySWError (intervalCarrier lo t) (selectedCoefficient b useMu (roughZ v) Y τ)
        k q residue‖≤E := by
    by_cases empty : useMu=true ∧ Y≤lo
    · rw [empty.1,selected_error_zero_of_cutoff_before_interval b (roughZ v) Y τ lo t
        hU1 hlo empty.2,norm_zero]
      exact hE
    · have hclip : lo≤clippedUpper useMu Y t := by
        cases hμ : useMu with
        | false => simpa [hμ,clippedUpper] using ht.1
        | true =>
          have hy : lo<Y := lt_of_not_ge (fun h => empty ⟨hμ,h⟩)
          exact le_min ht.1 hy.le
      have hc : clippedUpper useMu Y t≤t := by cases useMu <;> simp [clippedUpper]
      rw [selected_error_eq_clipped b useMu (roughZ v) Y τ lo t hU1 hlo (ht.2.trans hhi)]
      exact Hraw x hx v hxv hvx k q residue hk hq hres useMu τ U lo
        (clippedUpper useMu Y t) hτ hUp hU hlo hclip (hc.trans (ht.2.trans hhi))
          (hc.trans (ht.2.trans (hhi.trans htop)))
  let f := retainedProfile (fun _ : ℝ => (1:ℂ)) (logRole r) U
  have hΦ : ContDiff ℝ 1 (fun _ : ℝ => (1:ℂ)) := contDiff_const
  have hd : ∀ t∈Icc lo hi,DifferentiableAt ℝ f t := fun t ht =>
    (retainedProfile_hasDerivAt hΦ (logRole r) (hUp.trans_le (hlo.trans ht.1))).differentiableAt
  have hf : IntegrableOn (deriv f) (Icc lo hi) :=
    (((retainedProfile_contDiffOn hΦ (logRole r) U).continuousOn_deriv_of_isOpen
      isOpen_Ioi (by norm_num)).mono (fun t ht => hUp.trans_le (hlo.trans ht.1))).integrableOn_Icc
  have ab := complex_Abel_auxiliary_error_norm_le _ k q residue
    (hUp.le.trans hlo) hlh hE f hd hf prefix
  have var := retainedProfile_variation_le hΦ (by norm_num : (0:ℝ)≤1) (le_refl (0:ℝ))
    (fun _ _ => by simp) (fun _ _ => by simp) hU1.le hlo hlh hhi (logRole r)
  change ‖auxiliarySWError (intervalCarrier lo hi)
    (fun n => selectedCoefficient b useMu (roughZ v) Y τ n*f n) k q residue‖≤_
  calc
    _≤E*(‖f hi‖+∫ t in Ioc lo hi,‖deriv f t‖) := ab
    _≤E*V := mul_le_mul_of_nonneg_left var hE
    _=(C*V)*U*(k.divisors.card:ℝ)/(Real.log x)^A := by dsimp [E]; ring

/-- All three actual roles, all retained frequencies and all auxiliary
integers on their real fibre. The same N threshold works for every legal
outer width and every physical choice of the modulus coefficients. -/
theorem eventually_original_selected (K modeOrder : ℕ) (A : ℝ) (hA : 0≤A)
    {zeta kappa kap0 : ℝ} (hz : 0<zeta) (hz1 : zeta≤1/400) (hk : 0<kappa)
    (hkz : kappa≤zeta) (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∃ Csw : ℝ,0<Csw ∧ ∀ᶠ N : ℕ in atTop,
    ∀ {b kap s : ℝ},0<b → 0<kap → 0<s → 2*s≤baseline b kap-19/96 →
    ∀ (u v cj ck : ℕ) (bs : Fin (u+v)→Block) (i : Fin (u+v)) (C : Block),
    (∃ y∈fibre bs i C,integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y≠0) →
    first cj ck zeta bs=some i →
    let U := (lower (bs i):ℝ)
    let x := U*(lower C:ℝ)
    let Z := beforeHBCutoff K [cj,ck]
    ∀ (r : Role) (Y : ℝ) (ξ : Fin (u+v)→ℝ),ξ∈(outsideCube (u+v) (H N modeOrder))ᶜ →
    (∀ n,‖alpha (bs i) Z Y r (ξ i) n‖≤1) ∧
    (∀ n,alpha (bs i) Z Y r (ξ i) n≠0 → ∀ p : ℕ,p.Prime → p∣n → roughF x<(p:ℝ)) ∧
    ∀ lo hi : ℝ,U≤lo → lo≤hi → hi≤2*U →
    ∀ k q residue : ℕ,0<k → 0<q → residue.Coprime q →
    ‖auxiliarySWError (intervalCarrier lo hi) (alpha (bs i) Z Y r (ξ i)) k q residue‖≤
      Csw*U*(k.divisors.card:ℝ)/(Real.log x)^A := by
  let L : ℝ := ((bandwidthOrder modeOrder+1:ℕ):ℝ)
  obtain ⟨Csw,hC,x0,_,Hraw⟩ := normalized_rough_window A L (2*zeta) hA
    (by dsimp [L]; positivity) (by linarith)
  refine ⟨Csw,hC,?_⟩
  filter_upwards [P4BOriginalMediumFibreSWWindow.eventually_window K modeOrder x0 hz hz1 hk hkz ht ht1]
    with N Hwin
  intro b kap s hb hkap hs hg u v cj ck bs i C alive hi r Y ξ hξ
  have Hgeom := Hwin hb hkap hs hg u v cj ck bs i C alive (P4BOriginalMediumFibreSWWindow.first_spec hi)
  obtain ⟨hx0,_,hxv,hvx,hU,hlo,htop,hZ,hfreq⟩ := Hgeom
  refine ⟨fun n => P4BOriginalMediumHBHead.alpha_one _ _ _ _ _ n,
    fun n hn p hp hd => hZ.trans_lt (P4BOriginalMediumHBHead.alpha_rough hn p hp hd),?_⟩
  intro lo hi' hLo hLH hHi k q residue hk' hq hres
  have hτ := hfreq ξ hξ
  unfold L at Hraw
  rw [P4BOriginalMediumFibreSWWindow.original_cutoff]
  exact Hraw hx0 hxv hvx (bs i) hU hlo htop r Y (ξ i) lo hi'
    (by simpa only [Real.rpow_natCast] using hτ) hLo hLH hHi k q residue hk' hq hres

end
end ImbalancedChen.P4BOriginalMediumAuxiliaryBound
