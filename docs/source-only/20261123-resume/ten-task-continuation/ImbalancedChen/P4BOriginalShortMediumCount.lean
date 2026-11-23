import ImbalancedChen.P4BOriginalShortMediumAtlas

/-! Source only. The raw rank-two medium total in the counted RealB
inequality is replaced by the surviving true fibres and word integrals.
The density still uses the original squarefree coefficient. -/
namespace ImbalancedChen.P4BOriginalShortMediumCount
noncomputable section
open Classical Filter
open P4BOriginalCollisionWords (Params)
open P4BOriginalFiniteSmoothCount (mass Q)
open P4BOriginalHighRankScheduledCount (outerWidth)
open P4BOriginalRankTwoMediumRemainder (mediumTotal eventually_RealB_le_original_medium)
open P4BOriginalShortMediumFibreIntegral (WordRange)
open P4BOriginalShortMediumAtlas (remainingAtlas exists_mediumTotal_cost)
open P4BOuterRampRoughness (baseline)

/-- A complete complex error on the physical rank-two medium atlas.
The target accuracy three fixes the order of all retained cubes before N. -/
theorem eventually_mediumTotal_sub_remaining (K : ℕ) (omega T eta : ℝ) (ho : 0<omega) (heta : 0<eta)
    {zeta kappa kap0 b kap : ℝ} (hz : 0<zeta) (hz0 : zeta≤1/20000)
    (hk : 0<kappa) (hkz : kappa≤zeta/200000) (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1)
    (hb : 0<b) (hb1 : b≤1) (hkap : 0<kap) (hgap : 19/96<baseline b kap) :
    ∀ᶠ N : ℕ in atTop,∃ hs : 0<outerWidth N,∃ hg : 2*outerWidth N≤baseline b kap-19/96,
      ∀ P : Params,P.N=N → WordRange P omega T zeta →
      ‖mediumTotal hb hs hg P.N K kap0 zeta P.S P.rho-
        remainingAtlas P b kap (outerWidth N) kap0 zeta K 3‖≤eta*singularNormalization N := by
  obtain ⟨C,_,H⟩ := exists_mediumTotal_cost K 3 omega T ho hz hz0 hk hkz ht ht1 hb hb1 hkap hgap
  filter_upwards [H,p5z_eventually_logCube_le_singularNormalization C eta heta] with N h hfee
  obtain ⟨hs,hg,hp⟩ := h
  exact ⟨hs,hg,fun P hPN R => (hp P hPN R).trans hfee⟩

/-- The original count, on its scheduled width, same density, same
coefficient and true singular normalization. No physical support, Fourier,
SW, or signed-mode estimate needs to be supplied by the caller. -/
theorem eventually_RealB_le_remaining (K : ℕ) (hK : 2≤K) (nu beta T eta : ℝ)
    (hnu : 0<nu) (hbeta : 0<beta) (hbeta1 : beta≤1) (how : nu*beta^2≤19/96) (heta : 0<eta)
    {zeta kappa kap0 b : ℝ} (hz : 0<zeta) (hz0 : zeta≤1/20000)
    (hk : 0<kappa) (hkz : kappa≤zeta/200000) (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1)
    (hkap0 : 0<kap0) (hb : (1:ℝ)/2<b) (hb1 : b<1) (hgate : 19/96<baseline b kap0) :
    ∀ᶠ N : ℕ in atTop,Even N →
      0≤mass b kap0 (outerWidth N) N ∧
      |mass b kap0 (outerWidth N) N/((N:ℝ)/Real.log (N:ℝ))-Real.log (1/b)|<eta ∧
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (k : ℕ),
        let P : Params := ⟨m,r,n,e,q,a,nu*beta^2,k,N,nu*beta⟩
        WordRange P (nu*beta^2) T zeta →
        (RealB b N:ℝ)≤mass b kap0 (outerWidth N) N*physicalDensitySum (Q (nu*beta^2) N) P.rho+
          (remainingAtlas P b kap0 (outerWidth N) kap0 zeta K 3).re+eta*singularNormalization N := by
  have ho : 0<nu*beta^2 := mul_pos hnu (sq_pos_of_pos hbeta)
  have hb0 : 0<b := by linarith
  filter_upwards [eventually_RealB_le_original_medium K hK hz (by linarith) hk (by linarith)
    ht ht1 hkap0 hb hb1 hgate (eta/2) (half_pos heta),
    eventually_mediumTotal_sub_remaining K (nu*beta^2) T (eta/2) ho (half_pos heta) hz hz0 hk hkz ht ht1
      hb0 hb1.le hkap0 hgate,eventually_ge_atTop (2:ℕ)] with N hcount hnorm hN
  intro hev
  obtain ⟨hs,hg,hc⟩ := hcount
  obtain ⟨hm,ha,HC⟩ := hc hev
  obtain ⟨hs',hg',HP⟩ := hnorm
  refine ⟨hm,ha.trans (by linarith),?_⟩
  intro m r n e q a k
  let P : Params := ⟨m,r,n,e,q,a,nu*beta^2,k,N,nu*beta⟩
  change WordRange P (nu*beta^2) T zeta → _
  intro R
  have hell : nu*beta<1/1000 := by
    have h : 2*(nu*beta)≤zeta/16 := R.small_le
    linarith only [h,hz0]
  let old := mediumTotal hb0 hs hg N K kap0 zeta P.S P.rho
  let rest := remainingAtlas P b kap0 (outerWidth N) kap0 zeta K 3
  have H := HC m r n e q a k nu beta hnu hbeta hbeta1 how hell
    (fun d hd => R.supported ho hz0 (by change 1<N; omega) hd)
  have diff : ‖old-rest‖≤eta/2*singularNormalization N := HP P rfl R
  have hreal : old.re-rest.re≤eta/2*singularNormalization N :=
    (Complex.re_le_norm (old-rest)).trans diff
  change (RealB b N:ℝ)≤mass b kap0 (outerWidth N) N*physicalDensitySum (Q (nu*beta^2) N) P.rho+
    old.re+eta/2*singularNormalization N at H
  change (RealB b N:ℝ)≤mass b kap0 (outerWidth N) N*physicalDensitySum (Q (nu*beta^2) N) P.rho+
    rest.re+eta*singularNormalization N
  linarith only [H,hreal]

/-- For fixed physical policy inputs the tag mesh is the actual tau.
The caller supplies only the numerical policy and reserve inequalities. -/
theorem eventually_fixed_policy_RealB (K : ℕ) (hK : 2≤K) (nu beta eta : ℝ)
    (hnu : 0<nu) (hb' : 0<beta) (hb'1 : beta≤1) (how : nu*beta^2≤19/96) (heta : 0<eta)
    {zeta kappa kap0 b : ℝ} (hz : 0<zeta) (hz0 : zeta≤1/20000)
    (hk : 0<kappa) (hkz : kappa≤zeta/200000) (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1)
    (hkap0 : 0<kap0) (hb : (1:ℝ)/2<b) (hb1 : b<1) (hgate : 19/96<baseline b kap0)
    (m r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (k : ℕ) (he : 0≤e) (hem : (e:ℝ)≤1/2048)
    (hq : 0<q) (hmesh : P4BOriginalRankTwoChartPayment.tau m e q a k*
      ((P4AHeldTaggedCompilerSupport.J0 (nu*beta^2):ℝ)+1)≤zeta) (hell : 2*(nu*beta)≤zeta/16) :
    ∀ᶠ N : ℕ in atTop,Even N →
      let P : Params := ⟨m,r,n,e,q,a,nu*beta^2,k,N,nu*beta⟩
      (RealB b N:ℝ)≤mass b kap0 (outerWidth N) N*physicalDensitySum (Q (nu*beta^2) N) P.rho+
        (remainingAtlas P b kap0 (outerWidth N) kap0 zeta K 3).re+eta*singularNormalization N := by
  filter_upwards [eventually_RealB_le_remaining K hK nu beta
    (P4BOriginalRankTwoChartPayment.tau m e q a k) eta hnu hb' hb'1 how heta
    hz hz0 hk hkz ht ht1 hkap0 hb hb1 hgate] with N H
  intro hev
  exact (H hev).2.2 m r n e q a k
    ⟨rfl,rfl,he,hem,hq,hmesh,(mul_pos hnu hb').le,hell⟩

end
end ImbalancedChen.P4BOriginalShortMediumCount
