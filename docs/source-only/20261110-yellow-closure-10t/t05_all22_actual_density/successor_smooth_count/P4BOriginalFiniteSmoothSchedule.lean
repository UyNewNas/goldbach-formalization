import ImbalancedChen.P4BOriginalFiniteSmoothCount
import ImbalancedChen.P4BPhysicalBoundaryQuantifiers
import ImbalancedChen.P4BJointEndpointBudget

/-! The outer width and its arithmetic target threshold are uniform in
the complete sieve policy, beta and aligned rectangle width. The
source variable is the full physical labelled pair. Its lower product
wall is smoothed around twice the manuscript cutoff power. -/
namespace ImbalancedChen.P4BOriginalFiniteSmoothSchedule
noncomputable section
open scoped Classical BigOperators
open Part3 (primeProductSignedError)
open P4BOuterRampRoughness (baseline)
open P4BOriginalFiniteSmoothCount (Q coefficient weight mass)
open P4AOriginalFull87RawChronology (cutoff)

/-- The manuscript complete-product exponent can be used for every
fixed real imbalance exponent. Its strict upper bound gives enough
room below both primes for the actual sieve exponent. -/
theorem original_product_gap {b kappa kappa0 : ℝ} (hb : (1:ℝ)/2<b)
    (hk : 0<kappa) (hk0 : kappa0<kappa/(4*(1+kappa))) :
    (19/96:ℝ)<baseline b kappa0 := by
  have hden : 0<4*(1+kappa) := by positivity
  have hquarter : kappa/(4*(1+kappa))<1/4 := by
    apply (div_lt_iff₀ hden).mpr
    linarith
  have hcut : kappa0<1/4 := hk0.trans hquarter
  have hbpos : 0<b := by linarith
  have hprod := mul_lt_mul_of_pos_right (show (3:ℝ)/4<1-kappa0 by linarith) hbpos
  unfold baseline
  apply (lt_div_iff₀ (by linarith : 0<1+b)).mpr
  linarith only [hprod,hb]

/-- Fix the imbalance exponent and the complete-product cutoff. One
pre-target width cap and one target threshold pay the four genuine
source walls and the two integer endpoints for every finer smoothing.
The finite policy and aligned index k may be any later fixed choice. -/
theorem exists_same_coefficient_count {b kappa0 : ℝ}
    (hb : (1:ℝ)/2<b) (hb1 : b<1) (hk : 0<kappa0) (hk1 : kappa0<1)
    (hgate : (19/96:ℝ)<baseline b kappa0)
    (eta sMax : ℝ) (heta : 0<eta) (hsMax : 0<sMax) :
    ∃ s0 : ℝ,0<s0 ∧ s0≤sMax ∧
    ∃ N0 : ℕ,2≤N0 ∧ ∀ s : ℝ,0<s → s≤s0 → ∀ N≥N0,Even N →
      0≤mass b kappa0 s N ∧
      |mass b kappa0 s N/((N:ℝ)/Real.log (N:ℝ))-Real.log (1/b)|<eta ∧
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (k : ℕ) (nu beta : ℝ),
        0<nu → 0<beta → beta≤1 → nu*beta^2≤19/96 →
        let omega := nu*beta^2
        let rho := coefficient m r n e q a omega k N ((N:ℝ)^(nu*beta))
        (RealB b N:ℝ)≤mass b kappa0 s N*physicalDensitySum (Q omega N) rho+
          primeProductSignedError 2 N N (Q omega N) rho (weight b kappa0 s N)+
          eta*singularNormalization N := by
  let dec := (baseline b kappa0-19/96)/2
  have hdec : 0<dec := half_pos (sub_pos.mpr hgate)
  obtain ⟨s0,hs0,hsmax,Nm,hNm,hMass⟩ :=
    P4B.exists_uniform_smooth_physical_mass_precision hb hb1 hk hk1 eta (min sMax dec) heta
      (lt_min hsMax hdec)
  obtain ⟨Ne,_,hEnd⟩ :=
    exists_joint_upper_endpoint_threshold hk (show (19/96:ℝ)<1 by norm_num) eta heta
  refine ⟨s0,hs0,hsmax.trans (min_le_left _ _),max Nm Ne,hNm.trans (le_max_left _ _),?_⟩
  intro s hs hss N hN hev
  have hM := (le_max_left Nm Ne).trans hN
  have hE := (le_max_right Nm Ne).trans hN
  have hcost : (Nat.ceil (cutoff N):ℝ)+(manuscriptHalfProductCutoff kappa0 N+1)≤
      eta*singularNormalization N := hEnd N hE
  have hsg := hss.trans (hsmax.trans (min_le_right _ _))
  have hgap : 2*s≤baseline b kappa0-19/96 := by
    dsimp only [dec] at hsg
    linarith only [hsg]
  refine ⟨P4BOriginalFiniteSmoothCount.mass_nonneg _ _ _ _,hMass s hs hss N hM hev,?_⟩
  intro m r n e q a k nu beta hnu hbeta hbmax hw
  have h := P4BOriginalFiniteSmoothCount.realB_le_smooth_signed (by linarith : 0<b) hb1
    (hNm.trans hM) hs hgap m r n e q a k nu beta hnu hbeta hbmax hw
  dsimp only at h ⊢
  linarith only [h,hcost]

end
end ImbalancedChen.P4BOriginalFiniteSmoothSchedule
