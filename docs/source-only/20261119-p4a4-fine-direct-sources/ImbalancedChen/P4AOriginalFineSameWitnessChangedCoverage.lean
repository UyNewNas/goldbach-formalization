import ImbalancedChen.P4AOriginalFiniteAll22FineCofinalCoefficient
import ImbalancedChen.P4AOriginalFineWitnessChangedSupport

/-!
SOURCE_ONLY / UNCOMPILED / NOT KERNEL ACCEPTED.

Expose actual tagged changed coverage together with the unchanged Fine
conclusions at the very same q, beta, k and N. This is a witness-data
connection: no density, signed distribution or reserve is paid here.
-/
namespace ImbalancedChen.P4AOriginalFineSameWitnessChangedCoverage
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
open P4AAll22OriginalKLedger20261024zSourceOnly (compilerReserve)
open P4AOriginalFiniteAll22CofinalCoefficient (upper)
open P4AOriginalFiniteFallbackWallRate (Charts centresFor)
open P4AUpperTaggedParityCompiler P4AHeldTaggedCompilerSupport
open P4AFull87MarkedPrimePayment P4AFull87ActualAffineDeletion P4AFull87OrdinaryAdmissionDeletion
open P2CanonicalWallFullResidualPayment

/-- All original Fine conclusions and actual changed coverage on its one witness. -/
theorem exists_fine_cofinal_same_witness_with_changed_coverage
    (eta eMax : ℝ) (heta : 0<eta) (heMax : 0<eMax) :
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
    ∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N →
      let omega := nu*beta^2
      let tau := alignedWidth (jointIndex (bank m) (data e q a).m) k
      let w := (N:ℝ)^omega
      let z := cutoff N
      let L := (N:ℝ)^(nu*beta)
      let Q := moduli N w
      let rho := P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N tau L
      let f := F (bank m) (width r) n (data e q a) omega N
      (P4AOriginalFiniteFallbackAllHighAtoms.HighAtoms
        m n N (width r) omega tau (nu*beta) etaPP (data e q a) ∧
      ((N:ℝ)/Real.log (N:ℝ))*P4AFiniteCapTaggedConstructor.compilerExpense
          f (fun _ => []) N N w z tau L < compilerReserve*singularNormalization N ∧
      physicalDensitySum Q rho<upper m r n e q a omega eta N ∧
      (∀ d : ℕ,rho d≠0 → (d:ℝ)<(N:ℝ)^(599/1000:ℝ)) ∧
      ∀ b T : ℝ,0<b → b<1 → 0<T → (Nat.ceil z:ℝ)≤T^(b/(1+b)) →
        (RealB b N:ℝ)≤((realHalfProductSource b N T).card:ℝ)*upper m r n e q a omega eta N+
          realPhysicalDistributionError b N T Q rho+(Nat.ceil z:ℝ)+(T+1)
      ) ∧
      ∀ (tags : ℕ → List Bool) (x : ℕ),
        x ∈ P4AUpperTaggedParityCompiler.universe N N w z →
        P4AUpperTaggedParityCompiler.changed f tags N N w z tau x →
        ∃ i : Charts (bank m) (width r) n (data e q a),
          x ∈ covered N N
            (P4AHeldTaggedCompilerSupport.J0 omega) omega (19/96 : ℝ)
            ((P4AHeldTaggedCompilerSupport.J0 omega : ℝ)*tau)
            (centresFor (bank m) (width r) n (data e q a) N
              (P4AHeldTaggedCompilerSupport.J0 omega) i) := by
  obtain ⟨m0,hM⟩ :=
    P4AOriginalFiniteAll22FineCofinalCoefficient.exists_fine_cofinal_same_coefficient_density_and_count
      eta eMax heta heMax
  refine ⟨m0,?_⟩
  intro m hm
  obtain ⟨r0,hR⟩ := hM m hm
  refine ⟨r0,?_⟩
  intro r hr
  obtain ⟨n0,hN⟩ := hR r hr
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨E,hE,hEmax,hEall⟩ := hN n hn
  refine ⟨E,hE,hEmax,?_⟩
  intro e he heE a ha haSmall qMin mMin
  have heRat : 0 < e := by exact_mod_cast he
  obtain ⟨q,hqMin,hqpos,hqdiv,hmesh,hq⟩ :=
    hEall e he heE a ha haSmall qMin mMin
  refine ⟨q,hqMin,hqpos,hqdiv,hmesh,?_⟩
  intro etaPP hPP hPPgap nu v betaMax extraPPMargin hnu hv hcut hmax hextra fineTolerance hFine
  obtain ⟨beta,hbeta,hb8,hbMax,hbSq,hwa,hlog,hbetaPP,hbetaExtra,k,
    hfine,hbudgetPP,hbudgetExtra,N0,hN0,hAll⟩ :=
    hq etaPP hPP hPPgap nu v betaMax extraPPMargin hnu hv hcut hmax hextra fineTolerance hFine
  refine ⟨beta,hbeta,hb8,hbMax,hbSq,hwa,hlog,hbetaPP,hbetaExtra,k,
    hfine,hbudgetPP,hbudgetExtra,N0,hN0,?_⟩
  intro N hNN hEven
  have hN2 : 2 ≤ N := hN0.trans hNN
  have hOriginal := hAll N hNN hEven
  have hCoverage := P4AOriginalFineWitnessChangedSupport.fine_witness_all_changed_seen
    m r n q k N e heRat.le a nu v beta hnu hbeta hcut hbSq hN2
  dsimp only at hOriginal hCoverage ⊢
  exact ⟨hOriginal,hCoverage⟩

end
end ImbalancedChen.P4AOriginalFineSameWitnessChangedCoverage
