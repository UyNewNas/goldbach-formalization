import ImbalancedChen.P1OriginalSingletonMiddleTensor
import ImbalancedChen.P1OriginalFinite87PhysicalReserve
import ImbalancedChen.P4BOriginalCollisionPayment

/-! Preserve the original finite upper bank, eighth saving, compiler and
enlarged fifth policy in the singleton statement. The two positive reserves
are taken on the one beta and aligned k of the published physical schedule. -/
namespace ImbalancedChen.P1OriginalSingletonRectangleSchedule
noncomputable section
open Classical Filter
open scoped BigOperators
open P1OriginalFinite87PhysicalReserve (numericUpper)
open P1OriginalSingletonMiddleTensor (singletonTensor singletonAtlas actual_middle_to_tensor tensor_to_singleton_atlas)
open P4BOriginalCollisionWords (Params)
open P4BOriginalFiniteSmoothCount (Q)
open P4AOriginalFull87EighthPrimeMeanLedger (primeMass)
open P1OriginalSharpFiniteReceiver (literal)
open P4AOriginalOrderedThirdActualCoefficient (alignedWidth)
open P4AOriginalFiniteFallbackCount (jointIndex)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalNewFifthUnion (data)
open P4AHeldTaggedCompilerSupport (J0)
open P4BOuterRampRoughness (baseline)

theorem original_single_prime {b kappa : ℝ} (hb : 1/2<b) (hb1 : b<1)
    (hk : 0<kappa) (cap : ℝ) (hcap : 0<cap) :
    ∃ kap : ℝ,0<kap ∧ kap<cap ∧ kap<1 ∧ kap<kappa/(4*(1+kappa)) ∧ 19/96<baseline b kap ∧
    ∀ K : ℕ,2≤K → ∀ eta etaSharp : ℝ,0<eta → 0<etaSharp →
    ∃ r0 : ℕ,∀ r≥r0,∃ n0 : ℕ,∀ n≥n0,∃ E : ℝ,0<E ∧
    ∀ e : ℚ,0<e → (e:ℝ)<E → ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,∀ a : ℝ,0<a → a≤1/100 →
    ∀ (m : ℕ) (budget nu v uc betaMax : ℝ),0<budget → 0<nu → 0<v → nu*v=19/96 →
    0<uc → 0<betaMax → ∀ fineTolerance : ℝ→ℝ,(∀ b' : ℝ,0<b' → 0<fineTolerance b') →
    ∃ beta : ℝ,0<beta ∧ beta<1/8 ∧ beta<betaMax ∧ beta^2<v ∧ nu*beta^2<a ∧
      nu*beta<1/1000 ∧ nu*beta<(min budget (1/2000))/32 ∧ ∃ k : ℕ,
    alignedWidth (jointIndex (bank m) (data e q a).m) k≤fineTolerance beta ∧
    alignedWidth (jointIndex (bank m) (data e q a).m) k*((J0 (nu*beta^2):ℝ)+1)≤min budget (1/2000) ∧
    ∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N →
      let P : Params := ⟨m,r,n,e,q,a,nu*beta^2,k,N,nu*beta⟩
      let D := physicalDensitySum (Q P.omega N) P.rho
      D<numericUpper m r n e q a P.omega eta uc N ∧
      ∀ x U zeta : ℝ,
        |literal N (Q P.omega N) P.rho-primeMass N*D-singletonTensor P kap x U zeta|
          ≤etaSharp*singularNormalization N ∧
        (singletonTensor P kap x U zeta:ℂ)=singletonAtlas P kap K kap zeta := by
  obtain ⟨kap,hkp,hkc,hk1,hkg,hbase,H⟩ :=
    P1OriginalFinite87PhysicalReserve.original_archive_and_physical_reserves hb hb1 hk cap hcap
  refine ⟨kap,hkp,hkc,hk1,hkg,hbase,?_⟩
  intro K hK eta etaSharp he hs
  obtain ⟨r0,Hr⟩ := H K hK eta (etaSharp/2) eta he (half_pos hs) he
  refine ⟨r0,?_⟩
  intro r hr
  obtain ⟨n0,Hn⟩ := Hr r hr
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨E,hE,HE⟩ := Hn n hn
  refine ⟨E,hE,?_⟩
  intro e he0 heE
  obtain ⟨q0,hq0,Hq⟩ := HE e he0 heE
  refine ⟨q0,hq0,?_⟩
  intro q hq a ha haMax m budget nu v uc betaMax hbudget hnu hv hvv huc hbetaMax fineTolerance hf
  let B := min budget (1/2000:ℝ)
  obtain ⟨beta,hbeta,hb8,hbm,hbsq,hwa,hell,hbSmall,k,hfine,hJ,NC,hNC,hphysical⟩ :=
    Hq q hq a ha haMax m B nu v uc betaMax (lt_min hbudget (by norm_num)) hnu hv hvv huc hbetaMax fineTolerance hf
  let omega := nu*beta^2
  have ho : 0<omega := by dsimp only [omega]; positivity
  obtain ⟨NT,hNT⟩ := eventually_atTop.mp (actual_middle_to_tensor omega kap (etaSharp/2) ho hkp hk1 (half_pos hs))
  refine ⟨beta,hbeta,hb8,hbm,hbsq,hwa,hell,hbSmall,k,hfine,hJ,max NC NT,hNC.trans (le_max_left _ _),?_⟩
  intro N hN hev
  let P : Params := ⟨m,r,n,e,q,a,omega,k,N,nu*beta⟩
  obtain ⟨_,_,_,hD,_,hsharp,_⟩ := hphysical N (by omega) hev
  have hsgn : 0≤P.e := he0.le
  have hcost := P4BOriginalCollisionPayment.fine_budget P
    (hbSmall.trans_le (div_le_div_of_nonneg_right (min_le_right budget (1/2000:ℝ)) (by norm_num)))
    (hJ.trans (min_le_right budget (1/2000:ℝ)))
  obtain ⟨sm0,sm1⟩ := abs_le.mp hsharp
  refine ⟨hD,?_⟩
  intro x U zeta
  have HT := hNT N (by omega) hev P rfl rfl hsgn hell hcost x U zeta
  obtain ⟨ht0,ht1⟩ := abs_le.mp HT
  refine ⟨?_,tensor_to_singleton_atlas P (by change 1<N; omega) kap x U zeta K kap zeta⟩
  change |literal N (Q omega N) P.rho-primeMass N*physicalDensitySum (Q omega N) P.rho-
    singletonTensor P kap x U zeta|≤etaSharp*singularNormalization N
  change -(etaSharp/2*singularNormalization N) ≤ literal N (Q omega N) P.rho-
    primeMass N*physicalDensitySum (Q omega N) P.rho-P1OriginalSharpFiniteReceiver.middle N (Q omega N) P.rho at sm0
  change literal N (Q omega N) P.rho-primeMass N*physicalDensitySum (Q omega N) P.rho-
    P1OriginalSharpFiniteReceiver.middle N (Q omega N) P.rho ≤ etaSharp/2*singularNormalization N at sm1
  exact abs_le.mpr ⟨by linarith only [sm0,ht0],by linarith only [sm1,ht1]⟩

end
end ImbalancedChen.P1OriginalSingletonRectangleSchedule
