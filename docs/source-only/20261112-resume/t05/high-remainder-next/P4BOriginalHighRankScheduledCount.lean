import ImbalancedChen.P4BOriginalHighRankMotherMass
import ImbalancedChen.P4BOriginalFiniteTrimmedCount

/-! A single legal outer resolution for the actual high-rank Fourier calculation
and the true positive RealB upper bound. The remaining signed mode integral is explicit. -/
namespace ImbalancedChen.P4BOriginalHighRankScheduledCount
noncomputable section
open Classical Filter
open scoped BigOperators Topology
open P4BOriginalAllRankClassicalRange (wholeHigh)
open P4BOriginalHighRankMotherModes (eventually_wholeHigh_modes_remainder modes)
open P4BOriginalHighRankMotherMass (totalMass)
open P4BOriginalFiniteSmoothCount (Q coefficient mass)
open P4BOriginalFiniteProperArithmetic (modulusExponent)
open P4BOriginalFiniteSignedTrim (trimmedWeight)
open P4BOuterRampRoughness (baseline)
open P4BArbitraryWidthUpperBlockGeometry (countingScale scaleFactor scaleFactor_one_le)
open P5Z.CompleteProductTailDivisorBudgets (logScale)
open Part3 (primeProductSignedError)

def resolution (N : ℕ) := Nat.floor (Real.log (N:ℝ))
def outerWidth (N : ℕ) := 1/(resolution N+1:ℝ)

theorem eventually_width (s0 : ℝ) (hs0 : 0<s0) :
    ∀ᶠ N : ℕ in atTop,2≤N ∧ 0<outerWidth N ∧ outerWidth N≤s0 ∧
      (resolution N+1:ℝ)≤logScale (countingScale N) ∧
      logScale (countingScale N)≤2*Real.log (N:ℝ) := by
  have ht := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop (2:ℕ),eventually_one_le_nat_log,
    ht.eventually_ge_atTop (1/s0),ht.eventually_ge_atTop (1+Real.log (7*scaleFactor))]
    with N hN hlog hcut hlarge
  have hn : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hp : 0<(resolution N+1:ℝ) := by positivity
  have hf : Real.log (N:ℝ)<(resolution N+1:ℝ) := Nat.lt_floor_add_one _
  have hc : 1≤(7:ℝ)*scaleFactor := by linarith [scaleFactor_one_le]
  have hsc : logScale (countingScale N)=1+Real.log (7*scaleFactor)+Real.log (N:ℝ) := by
    unfold logScale countingScale
    rw [←mul_assoc,Real.log_mul (by linarith : 7*scaleFactor≠0) hn.ne']
    ring
  have H : 1≤s0*(resolution N+1:ℝ) := by
    have h := (div_le_iff₀ hs0).mp (hcut.trans hf.le)
    simpa only [mul_comm] using h
  exact ⟨hN,one_div_pos.mpr hp,(div_le_iff₀ hp).mpr H,by
    rw [hsc]
    have hfloor : (resolution N:ℝ)≤Real.log (N:ℝ) := Nat.floor_le (by linarith)
    linarith [Real.log_nonneg hc],by rw [hsc]; linarith⟩

/-- All normalized Fourier amplitudes on this same outer schedule cost
one fixed power, including the signed HB scalars in absolute value. -/
theorem exists_scheduled_mass : ∃ C : ℝ,0≤C ∧ ∀ {b kap : ℝ},0<b → b≤1 → 0<kap →
    19/96<baseline b kap → ∀ᶠ N : ℕ in atTop,∀ kap0 : ℝ,
      totalMass b kap (outerWidth N) N kap0≤C*(Real.log (N:ℝ))^38 := by
  obtain ⟨C,hC,H⟩ := P4BOriginalHighRankMotherMass.exists_resolution_mass 1
  refine ⟨C*2^38,mul_nonneg hC (by positivity),?_⟩
  intro b kap hb hb1 hk hg
  have ht : 0<(baseline b kap-19/96)/2 := half_pos (sub_pos.mpr hg)
  filter_upwards [eventually_width _ ht,eventually_one_le_nat_log] with N hz hlog
  obtain ⟨hN,hw,hsmall,hr,hL⟩ := hz
  intro kap0
  have hg' : 2*outerWidth N≤baseline b kap-19/96 := by linarith
  have hm := H b kap hb hb1 hk N (resolution N) (by omega) (by simpa only [pow_one] using hr) hg' kap0
  have hL0 : 0≤logScale (countingScale N) := le_trans (by positivity : 0≤(resolution N+1:ℝ)) hr
  change totalMass b kap (outerWidth N) N kap0≤C*logScale (countingScale N)^38 at hm
  exact hm.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hL 38) hC).trans_eq (by ring))

/-- Direct inequality at the selected width for every sufficiently large even N.
The same beta, aligned k, Q and rho are used in the main term and signed modes.
No mode estimate or uniform PP predicate is an input. -/
theorem eventually_RealB_le_high_modes {b kap0 : ℝ} (hb : (1:ℝ)/2<b) (hb1 : b<1)
    (hk : 0<kap0) (hk1 : kap0<1) (hgate : 19/96<baseline b kap0)
    (K : ℕ) (hK : 2≤K) (eta : ℝ) (heta : 0<eta) :
    ∀ᶠ N : ℕ in atTop,Even N →
      0≤mass b kap0 (outerWidth N) N ∧
      |mass b kap0 (outerWidth N) N/((N:ℝ)/Real.log (N:ℝ))-Real.log (1/b)|<eta ∧
      ∀ (m r n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (k : ℕ) (nu beta : ℝ),
      0<nu → 0<beta → beta≤1 → nu*beta^2≤19/96 → nu*beta<1/1000 →
      let omega := nu*beta^2
      let c := coefficient m r n e q a omega k N ((N:ℝ)^(nu*beta))
      (∀ v,c v≠0 → (v:ℝ)<(N:ℝ)^modulusExponent) →
      (RealB b N:ℝ)≤mass b kap0 (outerWidth N) N*physicalDensitySum (Q omega N) c+
        (modes b kap0 (outerWidth N) N K kap0 (wholeHigh m r n e q a omega k N (nu*beta)) c).re+
        eta*singularNormalization N := by
  have hgap : 0<(baseline b kap0-19/96)/2 := half_pos (sub_pos.mpr hgate)
  obtain ⟨s0,hs0,hsMax,N0,hN0,H⟩ := P4BOriginalFiniteTrimmedCount.exists_same_coefficient_trimmed_count
    hb hb1 hk hk1 hgate (eta/2) _ (half_pos heta) hgap
  have hb0 : 0<b := by linarith
  filter_upwards [eventually_width s0 hs0,eventually_ge_atTop N0,
    eventually_wholeHigh_modes_remainder K hK hb0 hk 3 1 (by norm_num),
    p5z_eventually_logCube_le_singularNormalization 1 (eta/2) (half_pos heta)]
    with N hw hN HM hcost
  intro hev
  obtain ⟨_,hs,hs',_,_⟩ := hw
  have hg : 2*outerWidth N≤baseline b kap0-19/96 := by linarith [hs'.trans hsMax]
  obtain ⟨hpos,hmass,hcount⟩ := H (outerWidth N) hs hs' N hN hev
  refine ⟨hpos,hmass.trans (by linarith),?_⟩
  intro m r n e q a k nu beta hnu hp hone hw hell
  dsimp only
  intro hrange
  let w := nu*beta^2
  let c := coefficient m r n e q a w k N ((N:ℝ)^(nu*beta))
  let D := primeProductSignedError 2 N N (Q w N) c (trimmedWeight b kap0 (outerWidth N) kap0 N)
  let Y := modes b kap0 (outerWidth N) N K kap0 (wholeHigh m r n e q a w k N (nu*beta)) c
  have hY : ‖(D:ℂ)-Y‖≤(1:ℝ)*N/(Real.log (N:ℝ))^3 :=
    HM (outerWidth N) hs hg kap0 m r n e q a w k (nu*beta) hell hrange
  have hclose : D-Y.re≤eta/2*singularNormalization N := by
    simpa only [Complex.sub_re,Complex.ofReal_re] using (Complex.re_le_norm ((D:ℂ)-Y)).trans (hY.trans hcost)
  have HC := hcount m r n e q a k nu beta hnu hp hone hw hrange
  change (RealB b N:ℝ)≤mass b kap0 (outerWidth N) N*physicalDensitySum (Q w N) c+D+
    eta/2*singularNormalization N at HC
  change (RealB b N:ℝ)≤mass b kap0 (outerWidth N) N*physicalDensitySum (Q w N) c+Y.re+
    eta*singularNormalization N
  linarith only [HC,hclose]

end
end ImbalancedChen.P4BOriginalHighRankScheduledCount
