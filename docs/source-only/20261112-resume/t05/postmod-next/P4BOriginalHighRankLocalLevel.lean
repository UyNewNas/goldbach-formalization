import ImbalancedChen.P4BOriginalHighRankLiveFibreModes

/-! The original global .599 rate, on a live complete-product block.
All moving-residue and trim choices precede N and the actual HB integers. -/
namespace ImbalancedChen.P4BOriginalHighRankLocalLevel
noncomputable section
open Classical Filter
open P4BOuterRampRoughness (baseline)
open P4BUpperPairOrderedRowGeometry (integerProfile)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle)
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower)
open P4BOriginalHighRankMotherScale (completeScale live_geometry)
open P4BOriginalHighRankComplementBlocks (fibre same_scale)
open P4BOriginalFiniteSmoothCount (Q coefficient)
open P4BOriginalFiniteProperArithmetic (modulusExponent)

def theta : ℝ := 1199/2000

theorem typeI_margins {zeta : ℝ} (hz : zeta≤1/400) :
    theta<3/5 ∧ 20*zeta+theta<1 ∧ 40*zeta+3*theta/2<1 := by
  dsimp [theta]; constructor <;> try constructor <;> linarith

/-- A positive trim, as small as desired and chosen after the moving residue
margin.  It can also be the outer half-product parameter in the direct count. -/
theorem exists_direct_trim {b kappa : ℝ} (hb : (1:ℝ)/2<b) (hk : 0<kappa)
    (cap : ℝ) (hcap : 0<cap) :
    ∃ kap0 : ℝ,0<kap0 ∧ kap0<cap ∧ kap0<1 ∧ kap0<kappa/(4*(1+kappa)) ∧
      19/96<baseline b kap0 := by
  let kap0 := min (min (cap/2) (1/8)) (kappa/(8*(1+kappa)))
  have hden : 0<1+kappa := by linarith
  have hp : 0<kap0 := lt_min (lt_min (half_pos hcap) (by norm_num)) (div_pos hk (by linarith))
  have h8 : kap0≤1/8 := (min_le_left _ _).trans (min_le_right _ _)
  have hmov : kap0<kappa/(4*(1+kappa)) :=
    (min_le_right _ _).trans_lt (div_lt_div_of_pos_left hk (by linarith) (by linarith))
  refine ⟨kap0,hp,((min_le_left _ _).trans (min_le_left _ _)).trans_lt (by linarith),by linarith,hmov,?_⟩
  apply (lt_div_iff₀ (show 0<1+b by linarith)).mpr
  have h := mul_le_mul_of_nonneg_right (show (7:ℝ)/8≤1-kap0 by linarith) (show 0≤b by linarith)
  linarith

/-- No medium selector is required here. Every occupied fibre at every chosen
coordinate inherits its original complete-scale bounds, so the local support
and both one/two-long power margins also apply to the no-medium case. -/
theorem eventually_live_level {kappa kap0 zeta : ℝ} (hz : 0<zeta) (hz1 : zeta≤1/400)
    (hk : 0<kappa) (hd : kappa≤zeta/10000) (ht : kap0<kappa/(4*(1+kappa))) :
    ∀ᶠ N : ℕ in atTop,∀ {b kap s : ℝ},0<b → 0<kap → 0<s → 2*s≤baseline b kap-19/96 →
      ∀ (u v cj ck : ℕ) (bs : Fin (u+v)→Block) (i : Fin (u+v)) (C : Block),
      (∃ y∈fibre bs i C,integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck y≠0) →
      let x := (lower (bs i):ℝ)*lower C
      1<x ∧ (Real.exp 1)⁻¹*x≤N ∧ (N:ℝ)≤x^(1+kappa) ∧
      theta<3/5 ∧ 20*zeta+theta<1 ∧ 40*zeta+3*theta/2<1 ∧
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (k : ℕ) (ell : ℝ),
      let c := coefficient m r n e q a omega k N ((N:ℝ)^ell)
      (∀ d,c d≠0 → (d:ℝ)<(N:ℝ)^modulusExponent) →
      ∀ d∈Q omega N,c d≠0 → (d:ℝ)<x^theta := by
  obtain ⟨_,N0,_,H⟩ := exists_manuscript_restrictedResidueScale_threshold
    (by norm_num : (0:ℝ)<1/4) (Real.exp_pos 1) hk ht
  filter_upwards [eventually_ge_atTop N0,eventually_ge_atTop (2:ℕ)] with N hN hN2
  intro b kap s hb hp hs hg u v cj ck bs i C hLive
  obtain ⟨y,hy,hnz⟩ := hLive
  let x := (lower (bs i):ℝ)*lower C
  obtain ⟨hlo,hhi,_,_⟩ := live_geometry (by omega) hb hp hs hg cj ck bs y i (Finset.mem_filter.mp hy).1 hnz
  rw [same_scale hy] at hlo hhi
  obtain ⟨hx,hxN,hNx⟩ := H N hN x hlo hhi
  obtain ⟨h0,h1,h2⟩ := typeI_margins hz1
  refine ⟨hx,hxN,hNx,h0,h1,h2,?_⟩
  intro m r n e q a omega k ell
  dsimp only
  intro hsup d hQ hc
  calc
    (d:ℝ)<(N:ℝ)^modulusExponent := hsup d hc
    _≤(x^(1+kappa))^modulusExponent :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hNx (by norm_num [modulusExponent])
    _=x^((1+kappa)*modulusExponent) := (Real.rpow_mul (zero_lt_one.trans hx).le _ _).symm
    _≤x^theta := Real.rpow_le_rpow_of_exponent_le hx.le (by dsimp [theta,modulusExponent]; linarith)

end
end ImbalancedChen.P4BOriginalHighRankLocalLevel
