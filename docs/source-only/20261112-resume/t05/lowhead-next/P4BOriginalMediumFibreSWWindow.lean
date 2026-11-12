import ImbalancedChen.P4BOriginalHighRankPostModulusCount
import ImbalancedChen.Part3ActualRoughIntervalAllModuliSW

/-! The original before-HB cutoff, complementary dyadic length and retained
frequency all belong to the same occupied first-medium fibre. -/
namespace ImbalancedChen.P4BOriginalMediumFibreSWWindow
noncomputable section
open Classical Filter
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.ExactOriginalSmoothDyadicPartition (R R_pos scales beforeHBCutoff)
open P5Z.OriginalChartRoughCutoff (argument roughF)
open P5Z.ActualHBMediumBranchPartition (firstMedium)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P5Z.AllRankCauchyCubeTail (outsideCube)
open P4BOriginalHighRankComplementBlocks (fibre same_scale)
open P4BOriginalHighRankPostModulusRow (H bandwidthOrder eventually_local_twists)
open P4BUpperPairOrderedRowGeometry (integerProfile)
open P4BOuterRampRoughness (baseline)

def chartArgument (K cj ck : ℕ) : ℝ := argument K (scales [cj,ck])

theorem original_cutoff (K cj ck : ℕ) :
    beforeHBCutoff K [cj,ck] =
      Part3.ActualRoughContourParameters20261026b.roughZ (chartArgument K cj ck) := rfl

theorem argument_value (K cj ck : ℕ) :
    chartArgument K cj ck = (2:ℝ)^(6*K+2)*(4*(R cj*R ck)) := by
  norm_num [chartArgument,argument,scales]

theorem first_spec {t cj ck : ℕ} {zeta : ℝ} {bs : Fin t→Block} {i : Fin t}
    (h : P4BOriginalHighRankPostModulusFibres.first cj ck zeta bs=some i) :
    firstMedium (originalMediumLow zeta [cj,ck]) (originalMediumHigh zeta [cj,ck])
      (List.ofFn bs)=some i.val := by
  unfold P4BOriginalHighRankPostModulusFibres.first at h
  cases w : firstMedium (originalMediumLow zeta [cj,ck]) (originalMediumHigh zeta [cj,ck])
      (List.ofFn bs) with
  | none => simp [w] at h
  | some j =>
    by_cases hj : j<t
    · have he : (⟨j,hj⟩ : Fin t)=i := by simpa [w,hj] using h
      exact congrArg some (congrArg Fin.val he)
    · simp [w,hj] at h

/-- One common target threshold for all occupied fibres, every admissible
outer width, the original dyadic labels and every retained frequency. -/
theorem eventually_window (K A : ℕ) (B : ℝ) {zeta kappa kap0 : ℝ}
    (hz : 0<zeta) (hz1 : zeta≤1/400) (hk : 0<kappa) (hkz : kappa≤zeta)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop, ∀ {b kap s : ℝ}, 0<b → 0<kap → 0<s → 2*s≤baseline b kap-19/96 →
    ∀ (u v cj ck : ℕ) (bs : Fin (u+v)→Block) (i : Fin (u+v)) (C : Block),
    (∃ y∈fibre bs i C,integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y≠0) →
    firstMedium (originalMediumLow zeta [cj,ck]) (originalMediumHigh zeta [cj,ck])
      (List.ofFn bs)=some i.val →
    let U := (lower (bs i):ℝ)
    let x := U*(lower C:ℝ)
    B≤x ∧ 1<x ∧ x≤chartArgument K cj ck ∧ chartArgument K cj ck≤x^2 ∧
    1<U ∧ x^(2*zeta)≤U ∧ 2*U≤x ∧ roughF x≤beforeHBCutoff K [cj,ck] ∧
    ∀ ξ : Fin (u+v)→ℝ, ξ∈(outsideCube (u+v) (H N A))ᶜ →
      |ξ i|≤(Real.log x)^(bandwidthOrder A+1) := by
  let e : ℝ := 1/3+zeta/2
  have he : 0<1-e := by dsimp [e]; linarith
  obtain ⟨R0,hR⟩ := eventually_atTop.mp
    ((Real.tendsto_rpow_atTop he).eventually_ge_atTop (2:ℝ))
  let D : ℝ := (2:ℝ)^(6*K+2)
  let B0 := max B (max R0 (64*D))
  have hD : 1≤D := one_le_pow₀ (by norm_num)
  filter_upwards [P4BOriginalHighRankLiveFibreModes.eventually_fixed_live_window K hz hz1 hk hkz ht ht1,
    eventually_local_twists A (show kappa≤1 by linarith),
    P4BOriginalRankTwoChartScales.eventually_power (4*B0) (1-kap0) (by linarith),
    eventually_ge_atTop (1:ℕ)] with N hwindow hfreq hpower hN
  intro b kap s hb hkap hs hg u v cj ck bs i C hlive hfirst
  let U := (lower (bs i):ℝ)
  let x := U*(lower C:ℝ)
  let X := R cj*R ck
  obtain ⟨hx,_,hNx,hUlow,hUhigh,hZ,_⟩ := hwindow hb hkap hs hg u v cj ck bs i C hlive hfirst
  obtain ⟨y,hy,hyw⟩ := hlive
  obtain ⟨hlo,_,hX,hxX⟩ := P4BOriginalHighRankMotherScale.live_geometry (by omega : 0<N)
    hb hkap hs hg cj ck bs y i (Finset.mem_filter.mp hy).1 hyw
  rw [same_scale hy] at hlo hX hxX
  have hB0 : B0≤x := by change (1/4:ℝ)*(N:ℝ)^(1-kap0)≤x at hlo; linarith
  have hB : B≤x := (le_max_left _ _).trans hB0
  have hR0 : R0≤x := (le_max_left _ _).trans ((le_max_right _ _).trans hB0)
  have h64 : 64*D≤x := (le_max_right _ _).trans ((le_max_right _ _).trans hB0)
  have hxp : 0<x := zero_lt_one.trans hx
  have hX0 : 0≤X := mul_nonneg (R_pos cj).le (R_pos ck).le
  have hv1 : x≤chartArgument K cj ck := by
    rw [argument_value]
    exact hxX.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hD (show 0≤4*X by positivity))
  have hv2 : chartArgument K cj ck≤x^2 := by
    rw [argument_value,pow_two]
    have h1 := mul_le_mul_of_nonneg_left hX (show 0≤4*D by linarith)
    have h2 := mul_le_mul_of_nonneg_right h64 hxp.le
    change D*(4*X)≤x*x
    change 4*D*X≤4*D*(16*x) at h1
    nlinarith only [h1,h2]
  have h2U : 2*U≤x := by
    have h := mul_le_mul (hR x hR0) hUhigh (by dsimp [U]; positivity)
      (Real.rpow_nonneg hxp.le (1-e))
    change 2*U≤x^(1-e)*x^e at h
    rwa [← Real.rpow_add hxp,show 1-e+e=1 by ring,Real.rpow_one] at h
  exact ⟨hB,hx,hv1,hv2,(Real.one_lt_rpow hx (by linarith : 0<2*zeta)).trans_le hUlow,
    hUlow,h2U,hZ,fun ξ hξ => hfreq x hx hNx _ ξ hξ i⟩

end
end ImbalancedChen.P4BOriginalMediumFibreSWWindow
