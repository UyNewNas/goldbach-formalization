import ImbalancedChen.P1OriginalSingletonOneLongGeometry
import ImbalancedChen.P4BOriginalHighRankComplementBlocks
import ImbalancedChen.RestrictedResidueScale

/-!
SOURCE CANDIDATE / NOT COMPILED.

The original one-group profile supplies the complete local scale of its
first-medium fibre. The reused complement and tuple-scale lemmas are
generic in the number of slots; no two-group profile is instantiated.
This file proves geometry only, not a medium discrepancy estimate.
-/
namespace ImbalancedChen.P1OriginalSingletonMediumWindow
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open P5Z.ActualLowerNormalizedAtlasOccurrence
  (integerProfile scalarProfile scalarProfile_eq_ambient scalarProfile_support)
open P5Z.ActualEtaPsiOccurrenceBudget (eta eta_zero)
open P5Z.ExactOriginalSmoothDyadicPartition (R R_pos scales beforeHBCutoff)
open P5Z.ActualHBMediumBranchPartition (firstMedium firstMedium_some Medium)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P5Z.OriginalChartRoughCutoff (roughF roughF_mono roughF_upper)
open P4BOriginalHighRankMotherScale (completeScale tuple_scale)
open P4BOriginalHighRankComplementBlocks (fibre same_scale)
open P4BOriginalRankTwoChartScales (psi_window eventually_power)
open P1OriginalSingletonOneLongGeometry (original_cutoff_singleton)

/-- Read support from the actual normalized singleton profile. The trim
uses the physical target N; the source cap remains 2*N. -/
theorem live_geometry (kap : ℝ) (hkap : kap<1) {N : ℕ} (hN : 0<N)
    (cj : ℕ) (kap0 : ℝ) {r : ℕ} (bs : Fin r→Block)
    (n : Fin r→ℕ) (i : Fin r) (hn : n∈rectangle bs)
    (hw : integerProfile kap 6 N cj kap0 n≠0) :
    let x := completeScale bs n i
    (1/4:ℝ)*(N:ℝ)^(1-kap0)≤x ∧ x≤2*(N:ℝ) ∧
      R cj≤8*x ∧ x≤2*R cj := by
  have hp : scalarProfile kap 6 N cj kap0 (completeProduct n)≠0 := hw
  have hcap := scalarProfile_support kap hkap 6 N cj kap0 hp
  have htop : (completeProduct n:ℝ)≤2*(N:ℝ) := by exact_mod_cast hcap
  rw [scalarProfile_eq_ambient] at hp
  have hEta : eta ((completeProduct n:ℝ)/(N:ℝ)^(1-kap0))≠0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1).2
  have hpsi := (mul_ne_zero_iff.mp hp).2
  have hden := Real.rpow_pos_of_pos
    (show (0:ℝ)<N by exact_mod_cast hN) (1-kap0)
  have htrim : (N:ℝ)^(1-kap0)<(completeProduct n:ℝ) := by
    by_contra! bad
    exact hEta (eta_zero ((div_le_one hden).mpr bad))
  obtain ⟨hRlo,hRhi⟩ := psi_window (R_pos cj) hpsi
  obtain ⟨hxlo,hxhi⟩ := tuple_scale bs n i hn
  exact ⟨by linarith, hxlo.trans htop, by linarith, by linarith⟩

/-- The selector depends only on the original chart and ordered block
positions, before the tuple and its complementary owner are inspected. -/
theorem selected_window {r : ℕ} (bs : Fin r→Block) (i : Fin r)
    (cj : ℕ) (zeta : ℝ)
    (h : firstMedium (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj])
      (List.ofFn bs)=some i.val) :
    (R cj)^(3*zeta)≤(lower (bs i):ℝ) ∧
      (lower (bs i):ℝ)≤(R cj)^(1/3+zeta/4:ℝ) := by
  obtain ⟨hi,hm,_⟩ := firstMedium_some h
  simpa [Medium,originalMediumLow,originalMediumHigh,scales] using hm

private theorem scale_window (K : ℕ) (xMin : ℝ) {zeta kappa kap0 : ℝ}
    (hz : 0<zeta) (hz1 : zeta≤1/400) (hk : 0<kappa)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop, ∀ (x X U : ℝ),
      (1/4:ℝ)*(N:ℝ)^(1-kap0)≤x → x≤2*(N:ℝ) →
      X≤8*x → x≤2*X → X^(3*zeta)≤U → U≤X^(1/3+zeta/4:ℝ) →
      let v := (2:ℝ)^(6*K+3)*X
      xMin≤x ∧ 1<x ∧ (2:ℝ)⁻¹*x≤N ∧ (N:ℝ)≤x^(1+kappa) ∧
      x^(1-zeta)≤N ∧ 1<U ∧ x^(2*zeta)≤U ∧
      U≤x^(1/3+zeta/2:ℝ) ∧ 2*U≤x ∧ x≤v ∧ v≤x^2 ∧
      roughF x≤roughF v ∧ roughF v≤x^(2/(Real.log (Real.log x))^3) := by
  let D : ℝ := (2:ℝ)^(6*K+3)
  have hD : 2≤D := by
    calc
      (2:ℝ)=(2:ℝ)^(1:ℕ) := by norm_num
      _≤D := pow_le_pow_right₀ (by norm_num) (by omega)
  let e : ℝ := 1/3+zeta/2
  have he : 0<1-e := by dsimp [e]; linarith
  have htX : ∀ᶠ x : ℝ in atTop,
      xMin≤x ∧ Real.exp (Real.exp 3)≤x ∧ 8*D≤x ∧
      2≤x^(1/3:ℝ) ∧ 8≤x^(zeta/4) ∧ 2≤x^zeta ∧ 2≤x^(1-e) := by
    filter_upwards [eventually_ge_atTop xMin,eventually_ge_atTop (Real.exp (Real.exp 3)),
      eventually_ge_atTop (8*D),
      (_root_.tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/3)).eventually_ge_atTop 2,
      (_root_.tendsto_rpow_atTop (by linarith : 0<zeta/4)).eventually_ge_atTop 8,
      (_root_.tendsto_rpow_atTop hz).eventually_ge_atTop 2,
      (_root_.tendsto_rpow_atTop he).eventually_ge_atTop 2]
      with x h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1,h2,h3,h4,h5,h6,h7⟩
  obtain ⟨x0,Hx⟩ := eventually_atTop.mp htX
  obtain ⟨_,N0,_,HN⟩ := exists_manuscript_restrictedResidueScale_threshold
    (by norm_num : (0:ℝ)<1/4) (by norm_num : (0:ℝ)<2) hk ht
  filter_upwards [eventually_ge_atTop N0,
    eventually_power (4*x0) (1-kap0) (by linarith)] with N hN hsize
  intro x X U hlo hhi hX hxX hU hU'
  obtain ⟨hx,rlo,rhi⟩ := HN N hN x hlo hhi
  have hxp := zero_lt_one.trans hx
  have hXp : 0<X := by linarith
  obtain ⟨hB,hlarge,hDx,htwo,height,hres,hend⟩ := Hx x (by linarith)
  have lowerRes : x^(1-zeta)≤N := by
    have h : 2*x^(1-zeta)≤x := by
      calc
        _≤x^zeta*x^(1-zeta) :=
          mul_le_mul_of_nonneg_right hres (Real.rpow_nonneg hxp.le _)
        _=x := by rw [←Real.rpow_add hxp,show zeta+(1-zeta)=1 by ring,Real.rpow_one]
    linarith
  have hXlower : x^(2/3:ℝ)≤X := by
    have hmul := mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hxp.le (2/3:ℝ))
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
  have h8 : (8:ℝ)^g≤8 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ)≤8) (show g≤1 by dsimp [g]; linarith)
  have hUhi : U≤x^(1/3+zeta/2:ℝ) := by
    calc
      U≤X^g := hU'
      _≤(8*x)^g := Real.rpow_le_rpow hXp.le hX hg
      _=8^g*x^g := Real.mul_rpow (by norm_num) hxp.le
      _≤x^(zeta/4)*x^g :=
        mul_le_mul_of_nonneg_right (h8.trans height) (Real.rpow_nonneg hxp.le _)
      _=_ := by rw [←Real.rpow_add hxp]; congr 1; dsimp [g]; ring
  have hUp : 0<U := (Real.rpow_pos_of_pos hxp (2*zeta)).trans_le hUlo
  have h2U : 2*U≤x := by
    have h := mul_le_mul hend hUhi hUp.le (Real.rpow_nonneg hxp.le (1-e))
    change 2*U≤x^(1-e)*x^e at h
    rwa [←Real.rpow_add hxp,show 1-e+e=1 by ring,Real.rpow_one] at h
  have hxv : x≤D*X := hxX.trans (mul_le_mul_of_nonneg_right hD hXp.le)
  have hvx : D*X≤x^2 := by
    have hscaled := mul_le_mul_of_nonneg_left hX (by linarith : 0≤D)
    have hlast := mul_le_mul_of_nonneg_right hDx hxp.le
    nlinarith only [hscaled,hlast]
  have hl3 : Real.exp 3≤Real.log x := (Real.le_log_iff_exp_le hxp).mpr hlarge
  have hloglog : 3≤Real.log (Real.log x) :=
    (Real.le_log_iff_exp_le (Real.log_pos hx)).mpr hl3
  exact ⟨hB,hx,rlo,rhi,lowerRes,
    (Real.one_lt_rpow hx (by linarith : 0<2*zeta)).trans_le hUlo,
    hUlo,hUhi,h2U,hxv,hvx,roughF_mono hx hloglog hxv,roughF_upper hx hloglog hxv hvx⟩

/-- One physical-N threshold precedes every singleton chart, ordered HB
rectangle, first-medium position and complete complementary dyadic owner.
A live point licenses the whole fibre; its other tuples need not have
nonzero profile. No bound on a desired discrepancy is an input. -/
theorem eventually_original_medium_window (K : ℕ) (xMin : ℝ)
    {kap zeta kappa kap0 : ℝ} (hkap : kap<1)
    (hz : 0<zeta) (hz1 : zeta≤1/400) (hk : 0<kappa)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop, ∀ (cj r : ℕ) (bs : Fin r→Block)
      (i : Fin r) (C : Block),
      (∃ n∈fibre bs i C,integerProfile kap 6 N cj kap0 n≠0) →
      firstMedium (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj])
        (List.ofFn bs)=some i.val →
      let U := (lower (bs i):ℝ)
      let x := U*(lower C:ℝ)
      let v := (2:ℝ)^(6*K+3)*R cj
      xMin≤x ∧ 1<x ∧ (2:ℝ)⁻¹*x≤N ∧ (N:ℝ)≤x^(1+kappa) ∧
      x^(1-zeta)≤N ∧ 1<U ∧ x^(2*zeta)≤U ∧
      U≤x^(1/3+zeta/2:ℝ) ∧ 2*U≤x ∧ x≤v ∧ v≤x^2 ∧
      roughF x≤beforeHBCutoff K [cj] ∧
      beforeHBCutoff K [cj]≤x^(2/(Real.log (Real.log x))^3) := by
  filter_upwards [scale_window K xMin hz hz1 hk ht ht1,eventually_ge_atTop (1:ℕ)]
    with N H hN
  intro cj r bs i C hlive hfirst
  obtain ⟨n,hn,hw⟩ := hlive
  obtain ⟨hlo,hhi,hX,hxX⟩ :=
    live_geometry kap hkap (by omega : 0<N) cj kap0 bs n i (Finset.mem_filter.mp hn).1 hw
  rw [same_scale hn] at hlo hhi hX hxX
  obtain ⟨hU,hU'⟩ := selected_window bs i cj zeta hfirst
  have hh := H ((lower (bs i):ℝ)*lower C) (R cj) (lower (bs i):ℝ)
    hlo hhi hX hxX hU hU'
  simpa only [original_cutoff_singleton] using hh

end
end ImbalancedChen.P1OriginalSingletonMediumWindow

