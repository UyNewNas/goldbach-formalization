import ImbalancedChen.P4AOriginalFiniteAll22CofinalCoefficient
import ImbalancedChen.P4AOriginalFiniteFallbackFinePPSchedule
import ImbalancedChen.P4AOriginalFiniteFallbackAllHighAtoms

/-!
SOURCE ONLY / UNCOMPILED / NOT KERNEL ACCEPTED / NO STATUS PROMOTION.

Reuse the nineteen-slot RAW schedule and the original early payment,
then call FinePPSchedule.joined ONCE for beta/k. The ordinary cofinal
existence theorem is not invoked; only its physical upper definition is
shared. Every fine budget, HighAtoms statement, density and actual count
below reads this one final F/rho. Signed distribution remains unpaid.
-/
namespace ImbalancedChen.P4AOriginalFiniteAll22FineCofinalCoefficient
noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalOrderedThirdActualCoefficient (alignedWidth)
open P4AOriginalFiniteFallbackCount (jointIndex)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalFiniteFallbackPolicy (F)
open P4AOriginalFiniteAll22RawLedger (finalPolicy lowerEarlyDefect)
open P1OriginalFifthGrid400RefinedFullBoxCover (refinedMesh)
open P5OriginalCommonPositivePresieve (normalize)
open P4AAll22OriginalKLedger20261024zSourceOnly
  (quotedAll22Raw densityReserve compilerReserve exactSlack)
open P4AOriginalFiniteAll22CofinalCoefficient (upper)

/-- One cofinal mesh, one beta, one aligned k. The compiler reserve is
the original reserve exactly once. The additional positive margins and
fineTolerance constrain this same selection; they are not PP estimates. -/
theorem exists_fine_cofinal_same_coefficient_density_and_count
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
      P4AOriginalFiniteFallbackAllHighAtoms.HighAtoms
        m n N (width r) omega tau (nu*beta) etaPP (data e q a) ∧
      ((N:ℝ)/Real.log (N:ℝ))*P4AFiniteCapTaggedConstructor.compilerExpense
          f (fun _ => []) N N w z tau L < compilerReserve*singularNormalization N ∧
      physicalDensitySum Q rho<upper m r n e q a omega eta N ∧
      (∀ d : ℕ,rho d≠0 → (d:ℝ)<(N:ℝ)^(599/1000:ℝ)) ∧
      ∀ b T : ℝ,0<b → b<1 → 0<T → (Nat.ceil z:ℝ)≤T^(b/(1+b)) →
        (RealB b N:ℝ)≤((realHalfProductSource b N T).card:ℝ)*upper m r n e q a omega eta N+
          realPhysicalDistributionError b N T Q rho+(Nat.ceil z:ℝ)+(T+1) := by
  have hhalf : 0<eta/2 := half_pos heta
  obtain ⟨h,hh,m0,hM⟩ :=
    P4AOriginalFiniteAll22Nineteen.exists_final_raw_upper_with_early_defect
      (eta/2) eMax hhalf heMax
  obtain ⟨nE,hEarly⟩ :=
    P4AOriginalEarlyFinitePayment.cofinal_actual_early_defect (eta/2) hhalf
  refine ⟨m0,?_⟩
  intro m hm
  obtain ⟨r0,hR⟩ := hM m hm
  refine ⟨r0,?_⟩
  intro r hr
  obtain ⟨nC,hC⟩ := hR r hr
  refine ⟨max nC nE,?_⟩
  intro n hn
  obtain ⟨EC,hEC,hECmax,hCE⟩ := hC n ((le_max_left _ _).trans hn)
  obtain ⟨EE,hEE,hEEall⟩ := hEarly n ((le_max_right _ _).trans hn)
  refine ⟨min EC EE,lt_min hEC hEE,(min_le_left _ _).trans hECmax,?_⟩
  intro e he heE a ha haSmall qMin mMin
  have heRat : 0<e := by exact_mod_cast he
  obtain ⟨q0,hq0,hqMin,hQ⟩ :=
    hCE e he (heE.trans_le (min_le_left _ _)) qMin
  obtain ⟨q,hq,hqpos,hqdiv,hmesh,NE,hNE,hEN⟩ :=
    hEEall e heRat (heE.trans_le (min_le_right _ _)) a ha haSmall q0 mMin
  refine ⟨q,hqMin.trans hq,hqpos,hqdiv,hmesh,?_⟩
  intro etaPP hPP hPPgap nu v betaMax extraPPMargin hnu hv hcut hmax hextra fineTolerance hFine
  obtain ⟨beta,hbeta,hb8,hbCeil,hbSq,hwa,hlog,hbetaBudget,k,hfine,hbudget,NC,hNC,hCN⟩ :=
    P4AOriginalFiniteFallbackFinePPSchedule.joined
      (bank m) (P4AOriginalFiniteFallbackCanonical.bounded m) r n e heRat.le q a ha
      (min etaPP extraPPMargin) (lt_min hPP hextra) nu v compilerReserve
      (min betaMax (h/nu)) hnu hv hcut
      P4AAll22OriginalKLedger20261024zSourceOnly.compilerReserve_pos
      (lt_min hmax (div_pos hh hnu)) fineTolerance hFine
  have hbMax : beta<betaMax := hbCeil.trans_le (min_le_left _ _)
  have hbetaPP : nu*beta<etaPP/32 := by
    linarith only [hbetaBudget,min_le_left etaPP extraPPMargin]
  have hbetaExtra : nu*beta<extraPPMargin/32 := by
    linarith only [hbetaBudget,min_le_right etaPP extraPPMargin]
  have hbudgetPP := hbudget.trans (min_le_left etaPP extraPPMargin)
  have hbudgetExtra := hbudget.trans (min_le_right etaPP extraPPMargin)
  let omega := nu*beta^2
  let tau := alignedWidth (jointIndex (bank m) (data e q a).m) k
  have homega : 0<omega := mul_pos hnu (sq_pos_of_pos hbeta)
  have homegaR : omega<thirdPrefixRho := by
    have H := mul_lt_mul_of_pos_left hbSq hnu
    rw [hcut] at H
    exact H
  have homegaH : omega≤h := by
    have H := (lt_div_iff₀ hnu).mp (hbCeil.trans_le (min_le_right _ _))
    have h1 : beta<1 := by linarith only [hb8]
    have h2 : beta^2≤beta := by nlinarith only [hbeta.le,h1.le]
    exact (mul_le_mul_of_nonneg_left h2 hnu.le).trans (by linarith only [H])
  have htau : 0<tau :=
    div_pos (logPrimeMeshStep_pos (by norm_num) _) (by positivity)
  obtain ⟨NR,hRN⟩ := eventually_atTop.mp
    (hQ q hq a omega homega homegaR hwa.le homegaH haSmall)
  refine ⟨beta,hbeta,hb8,hbMax,hbSq,hwa,hlog,hbetaPP,hbetaExtra,k,
    hfine,hbudgetPP,hbudgetExtra,max NC (max NR NE),hNC.trans (le_max_left _ _),?_⟩
  intro N hN hEven
  have hNC' : NC≤N := (le_max_left _ _).trans hN
  have hNR' : NR≤N := (le_max_left NR NE).trans ((le_max_right _ _).trans hN)
  have hNE' : NE≤N := (le_max_right NR NE).trans ((le_max_right _ _).trans hN)
  have hN2 : 2≤N := hNC.trans hNC'
  have hN1 : 1<N := by omega
  obtain ⟨hNRaw,hRaw⟩ := hRN N hNR' hEven
  have hDefect := hEN omega hwa.le N hNE' hEven
  have hRawClean : normalize N (rawRoot (finalPolicy m r n e q a omega N) N)<
      quotedAll22Raw+eta := by
    linarith only [hRaw,hDefect]
  obtain ⟨hExpense,hDensity,hSupport,hCount⟩ := hCN N hNC' hEven
  dsimp only at hExpense hDensity hSupport hCount ⊢
  have hRawScale : rawRoot (finalPolicy m r n e q a omega N) N≤
      (quotedAll22Raw+eta)*(singularSeries N/Real.log (N:ℝ)) :=
    (density_le_manuscriptScale_iff_normalized hN2 _ _).mpr hRawClean.le
  have hCoefficient : quotedAll22Raw+eta+compilerReserve=
      currentK-densityReserve-exactSlack+eta := by
    linarith only [P4AAll22OriginalKLedger20261024zSourceOnly.exact_original_budget_identity]
  rw [P4AOriginalFiniteAll22PhysicalLedger.reserve_raw_is_actual_final] at hDensity
  have hUpper : physicalDensitySum (moduli N ((N:ℝ)^omega))
      (P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N tau ((N:ℝ)^(nu*beta)))<
      upper m r n e q a omega eta N := by
    have hScale : rawRoot (finalPolicy m r n e q a omega N) N+
        compilerReserve*(singularSeries N/Real.log (N:ℝ))≤
        (currentK-densityReserve-exactSlack+eta)*(singularSeries N/Real.log (N:ℝ)) := by
      calc
        _ ≤ (quotedAll22Raw+eta)*(singularSeries N/Real.log (N:ℝ))+
            compilerReserve*(singularSeries N/Real.log (N:ℝ)) := add_le_add_right hRawScale _
        _ = _ := by rw [←add_mul,hCoefficient]
    unfold upper
    linarith only [hDensity,hScale]
  have hAtoms := P4AOriginalFiniteFallbackAllHighAtoms.high_atoms
    m n N (width r) omega tau (nu*beta) etaPP (data e q a)
    (width_pos r) (by change 0≤e; exact heRat.le) hN1 homega htau hPP hPPgap
    hbudgetPP (mul_nonneg hnu.le hbeta.le) (by linarith only [hbetaPP])
  refine ⟨hAtoms,hExpense,hUpper,hSupport,?_⟩
  intro b T hb hb1 hT hgate
  have hFinite := hCount b T hb hb1 hT hgate
  have hMass := mul_le_mul_of_nonneg_left hUpper.le
    (Nat.cast_nonneg (realHalfProductSource b N T).card)
  exact hFinite.trans
    (add_le_add_right (add_le_add_right (add_le_add_right hMass _) _) _)

end
end ImbalancedChen.P4AOriginalFiniteAll22FineCofinalCoefficient
