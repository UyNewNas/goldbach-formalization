import ImbalancedChen.P4AOriginalFiniteAll22FineCofinalCoefficient
import ImbalancedChen.P4AHistoricalPhysicalSavingsReserve
import ImbalancedChen.RealUpperCountingAssembly

/-!
SOURCE ONLY / UNCOMPILED / NOT KERNEL ACCEPTED.
Fix eta=densityReserve/2 once. The actual correction is nonnegative by
the existing all-retention theorem, so the SAME Fine-selected rho has a
direct K-density bound. Its delta-indexed families below are constant in
delta: no beta/k or coefficient is chosen again for another precision.
The genuine signed PP/distribution obligations remain separate.
-/
namespace ImbalancedChen.P4AOriginalFiniteAll22FineDensity
noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalOrderedThirdActualCoefficient (alignedWidth)
open P4AOriginalFiniteFallbackCount (jointIndex)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalFiniteFallbackPolicy (F)
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)
open P4AAll22OriginalKLedger20261024zSourceOnly
  (densityReserve compilerReserve exactSlack densityReserve_pos exactSlack_pos)
open P4AOriginalFiniteAll22CofinalCoefficient (upper)

def modulusFamily (nu beta : ℝ) (_delta : ℝ) (N : ℕ) : Finset ℕ :=
  moduli N ((N:ℝ)^(nu*beta^2))

def coefficientFamily (m r n : ℕ) (e : ℚ) (q : ℕ) (a nu beta : ℝ) (k : ℕ)
    (_delta : ℝ) (N : ℕ) : ℕ→ℝ :=
  P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a (nu*beta^2) N
    (alignedWidth (jointIndex (bank m) (data e q a).m) k) ((N:ℝ)^(nu*beta))

/-- The existing actual correction has its proved favorable sign. -/
theorem upper_lt_currentK (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ)
    {N : ℕ} (hN : 2≤N) (homega : omega≤19/96) :
    upper m r n e q a omega (densityReserve/2) N<
      currentK*(singularSeries N/Real.log (N:ℝ)) := by
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hwz : (N:ℝ)^omega≤cutoff N := by
    change (N:ℝ)^omega≤(N:ℝ)^(19/96:ℝ)
    exact Real.rpow_le_rpow_of_exponent_le hN1 homega
  have hc := p4aActualPresieveCorrection_nonneg
    (F (bank m) (width r) n (data e q a) omega N) N N ((N:ℝ)^omega) (cutoff N) hwz
  have hcoef : currentK-densityReserve-exactSlack+densityReserve/2<currentK := by
    linarith only [densityReserve_pos,exactSlack_pos]
  have hs := mul_lt_mul_of_pos_right hcoef (densityScale_pos hN)
  unfold upper
  linarith only [hc,hs]

/-- Exact hdensity premise of RealUpperCountingAssembly, on one fixed
actual family, together with the original Fine witnesses and count.
The same N0 works for every delta; the coefficient is delta-constant. -/
theorem exists_fine_same_rho_hdensity (eMax : ℝ) (heMax : 0<eMax) :
    ∃ m0 : ℕ,∀ m≥m0,∃ r0 : ℕ,∀ r≥r0,∃ n0 : ℕ,∀ n≥n0,
    ∃ E : ℝ,0<E ∧ E≤eMax ∧ ∀ e : ℚ,0<(e:ℝ) → (e:ℝ)<E →
    ∀ a : ℝ,0<a → a≤1/800 → ∀ qMin mMin : ℕ,
    ∃ q : ℕ,qMin≤q ∧ 0<q ∧ 256∣q ∧ mMin≤refinedMesh q ∧
    ∀ etaPP : ℝ,0<etaPP → etaPP≤P4AOriginalFiniteFallbackCommonGroups.gap m (data e q a) →
    ∀ nu v betaMax extraPPMargin : ℝ,
    0<nu → 0<v → nu*v=19/96 → 0<betaMax → 0<extraPPMargin →
    ∀ fineTolerance : ℝ→ℝ,(∀ beta : ℝ,0<beta → 0<fineTolerance beta) →
    ∃ beta : ℝ,0<beta ∧ beta<1/8 ∧ beta<betaMax ∧ beta^2<v ∧
      nu*beta^2<a ∧ nu*beta<1/1000 ∧ nu*beta<etaPP/32 ∧ nu*beta<extraPPMargin/32 ∧
    ∃ k : ℕ,
      alignedWidth (jointIndex (bank m) (data e q a).m) k≤fineTolerance beta ∧
      alignedWidth (jointIndex (bank m) (data e q a).m) k*
        ((P4AHeldTaggedCompilerSupport.J0 (nu*beta^2):ℝ)+1)≤etaPP ∧
      alignedWidth (jointIndex (bank m) (data e q a).m) k*
        ((P4AHeldTaggedCompilerSupport.J0 (nu*beta^2):ℝ)+1)≤extraPPMargin ∧
      let Q := modulusFamily nu beta
      let rho := coefficientFamily m r n e q a nu beta k
      (∀ delta : ℝ,0<delta → ∀ᶠ N : ℕ in atTop,Even N →
        physicalDensitySum (Q delta N) (rho delta N)≤
          (currentK+delta)*(singularSeries N/Real.log (N:ℝ))) ∧
      ∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N →
        let omega := nu*beta^2
        let tau := alignedWidth (jointIndex (bank m) (data e q a).m) k
        let w := (N:ℝ)^omega
        let z := cutoff N
        let L := (N:ℝ)^(nu*beta)
        let f := F (bank m) (width r) n (data e q a) omega N
        P4AOriginalFiniteFallbackAllHighAtoms.HighAtoms
          m n N (width r) omega tau (nu*beta) etaPP (data e q a) ∧
        ((N:ℝ)/Real.log (N:ℝ))*P4AFiniteCapTaggedConstructor.compilerExpense
            f (fun _ => []) N N w z tau L < compilerReserve*singularNormalization N ∧
        physicalDensitySum (Q 0 N) (rho 0 N)<upper m r n e q a omega (densityReserve/2) N ∧
        physicalDensitySum (Q 0 N) (rho 0 N)≤currentK*(singularSeries N/Real.log (N:ℝ)) ∧
        (∀ d : ℕ,rho 0 N d≠0 → (d:ℝ)<(N:ℝ)^(599/1000:ℝ)) ∧
        ∀ b T : ℝ,0<b → b<1 → 0<T → (Nat.ceil z:ℝ)≤T^(b/(1+b)) →
          (RealB b N:ℝ)≤((realHalfProductSource b N T).card:ℝ)*
              upper m r n e q a omega (densityReserve/2) N+
            realPhysicalDistributionError b N T (Q 0 N) (rho 0 N)+(Nat.ceil z:ℝ)+(T+1) := by
  obtain ⟨m0,hM⟩ :=
    P4AOriginalFiniteAll22FineCofinalCoefficient.exists_fine_cofinal_same_coefficient_density_and_count
      (densityReserve/2) eMax (half_pos densityReserve_pos) heMax
  refine ⟨m0,?_⟩
  intro m hm
  obtain ⟨r0,hR⟩ := hM m hm
  refine ⟨r0,?_⟩
  intro r hr
  obtain ⟨n0,hC⟩ := hR r hr
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨E,hE,hEmax,hCE⟩ := hC n hn
  refine ⟨E,hE,hEmax,?_⟩
  intro e he heE a ha haSmall qMin mMin
  obtain ⟨q,hq,hqpos,hqdiv,hmesh,hQ⟩ := hCE e he heE a ha haSmall qMin mMin
  refine ⟨q,hq,hqpos,hqdiv,hmesh,?_⟩
  intro etaPP hPP hgap nu v betaMax extra hnu hv hcut hmax hextra fineTolerance hFine
  obtain ⟨beta,hbeta,hb8,hbMax,hbSq,hwa,hlog,hbetaPP,hbetaExtra,k,hfine,hbudgetPP,hbudgetExtra,
      N0,hN0,hBound⟩ := hQ etaPP hPP hgap nu v betaMax extra hnu hv hcut hmax hextra fineTolerance hFine
  have homega : nu*beta^2≤19/96 := by
    have H := (mul_lt_mul_of_pos_left hbSq hnu).le
    rw [hcut] at H
    exact H
  have hK (N : ℕ) (hNN : N0≤N) (hEven : Even N) :
      physicalDensitySum (modulusFamily nu beta 0 N)
        (coefficientFamily m r n e q a nu beta k 0 N)<
        currentK*(singularSeries N/Real.log (N:ℝ)) := by
    obtain ⟨hAtoms,hSpend,hDensity,hRange,hCount⟩ := hBound N hNN hEven
    exact hDensity.trans (upper_lt_currentK m r n e q a (nu*beta^2) (hN0.trans hNN) homega)
  refine ⟨beta,hbeta,hb8,hbMax,hbSq,hwa,hlog,hbetaPP,hbetaExtra,k,hfine,hbudgetPP,hbudgetExtra,?_⟩
  dsimp only
  refine ⟨?_,N0,hN0,?_⟩
  · intro delta hdelta
    filter_upwards [eventually_ge_atTop N0] with N hNN
    intro hEven
    change physicalDensitySum (modulusFamily nu beta 0 N)
      (coefficientFamily m r n e q a nu beta k 0 N)≤_
    exact (hK N hNN hEven).le.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hdelta.le)
        (densityScale_pos (hN0.trans hNN)).le)
  · intro N hNN hEven
    obtain ⟨hAtoms,hSpend,hDensity,hRange,hCount⟩ := hBound N hNN hEven
    exact ⟨hAtoms,hSpend,hDensity,(hK N hNN hEven).le,hRange,hCount⟩

end
end ImbalancedChen.P4AOriginalFiniteAll22FineDensity
