import ImbalancedChen.P4AOriginalFiniteAll22EarlyDefectCounting
import ImbalancedChen.P4AOriginalEarlyFinitePayment

/-!
SOURCE ONLY / UNCOMPILED / NOT KERNEL ACCEPTED / NO STATUS PROMOTION.

Connect the published nineteen-slot final coefficient to the existing
original early0/1/2 payment. Choose the single cofinal mesh after a and
before the single beta/compiler choice. Both suppliers control this
same mesh and target, and the early threshold is uniform in omega<=a.
The genuine signed distribution error, actual presieve correction and
finite count losses remain. This is not a complete hUpper or PP result.
-/
namespace ImbalancedChen.P4AOriginalFiniteAll22CofinalCoefficient
noncomputable section
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
  (densityReserve compilerReserve exactSlack)

/-- All original slots are now paid at the same finite coefficient;
the actual correction and independent density reserve remain literal. -/
def upper (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega eta : ℝ) (N : ℕ) : ℝ :=
  (currentK-densityReserve-exactSlack+eta)*(singularSeries N/Real.log (N:ℝ))-
    p4aActualPresieveCorrection (F (bank m) (width r) n (data e q a) omega N)
      N N ((N:ℝ)^omega) (cutoff N)

/-- The resolution, buffer, early cutoff and a single cofinal q precede
beta/k/N. No supplier is selected after its target threshold, and no
second coefficient is substituted in the physical or counting term. -/
theorem exists_cofinal_same_coefficient_density_and_count
    (eta eMax : ℝ) (heta : 0<eta) (heMax : 0<eMax) :
    ∃ m0 : ℕ,∀ m≥m0,∃ r0 : ℕ,∀ r≥r0,∃ n0 : ℕ,∀ n≥n0,
    ∃ E : ℝ,0<E ∧ E≤eMax ∧ ∀ e : ℚ,0<(e:ℝ) → (e:ℝ)<E →
    ∀ a : ℝ,0<a → a≤1/800 → ∀ qMin mMin : ℕ,
    ∃ q : ℕ,qMin≤q ∧ 0<q ∧ 256∣q ∧ mMin≤refinedMesh q ∧
    ∀ nu v betaMax : ℝ,0<nu → 0<v → nu*v=19/96 → 0<betaMax →
    ∃ beta : ℝ,0<beta ∧ beta<1/8 ∧ beta<betaMax ∧ beta^2<v ∧
      nu*beta^2<a ∧ nu*beta<1/1000 ∧
    ∃ k N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N →
      let omega := nu*beta^2
      let tau := alignedWidth (jointIndex (bank m) (data e q a).m) k
      let w := (N:ℝ)^omega
      let z := cutoff N
      let L := (N:ℝ)^(nu*beta)
      let Q := moduli N w
      let rho := P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N tau L
      let f := F (bank m) (width r) n (data e q a) omega N
      ((N:ℝ)/Real.log (N:ℝ))*P4AFiniteCapTaggedConstructor.compilerExpense
          f (fun _ => []) N N w z tau L < compilerReserve*singularNormalization N ∧
      physicalDensitySum Q rho<upper m r n e q a omega eta N ∧
      (∀ d : ℕ,rho d≠0 → (d:ℝ)<(N:ℝ)^(599/1000:ℝ)) ∧
      ∀ b T : ℝ,0<b → b<1 → 0<T → (Nat.ceil z:ℝ)≤T^(b/(1+b)) →
        (RealB b N:ℝ)≤((realHalfProductSource b N T).card:ℝ)*upper m r n e q a omega eta N+
          realPhysicalDistributionError b N T Q rho+(Nat.ceil z:ℝ)+(T+1) := by
  have hhalf : 0<eta/2 := half_pos heta
  obtain ⟨m0,hM⟩ :=
    P4AOriginalFiniteAll22EarlyDefectCounting.exists_same_coefficient_density_and_count_with_early_defect
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
  intro nu v betaMax hnu hv hcut hmax
  obtain ⟨beta,hbeta,hb8,hbMax,hbSq,hwa,hlog,k,NC,hNC,hCN⟩ :=
    hQ q hq a ha haSmall nu v betaMax hnu hv hcut hmax
  refine ⟨beta,hbeta,hb8,hbMax,hbSq,hwa,hlog,k,max NC NE,
    hNC.trans (le_max_left _ _),?_⟩
  intro N hN hEven
  have hNC' : NC≤N := (le_max_left _ _).trans hN
  have hNE' : NE≤N := (le_max_right _ _).trans hN
  have hN2 : 2≤N := hNC.trans hNC'
  obtain ⟨hExpense,hDensity,hSupport,hCount⟩ := hCN N hNC' hEven
  have hDefect := hEN (nu*beta^2) hwa.le N hNE' hEven
  dsimp only at hExpense hDensity hSupport hCount ⊢
  have hScalar : currentK-densityReserve-exactSlack+
      P4AOriginalFiniteAll22RawLedger.lowerEarlyDefect n e q a (nu*beta^2) N+eta/2 <
      currentK-densityReserve-exactSlack+eta := by
    linarith only [hDefect]
  have hUpper :
      P4AOriginalFiniteAll22EarlyDefectCounting.physicalUpperWithEarlyDefect
        m r n e q a (nu*beta^2) (eta/2) N < upper m r n e q a (nu*beta^2) eta N := by
    unfold P4AOriginalFiniteAll22EarlyDefectCounting.physicalUpperWithEarlyDefect upper
    exact sub_lt_sub_right (mul_lt_mul_of_pos_right hScalar (densityScale_pos hN2)) _
  refine ⟨hExpense,hDensity.trans hUpper,hSupport,?_⟩
  intro b T hb hb1 hT hgate
  have hFinite := hCount b T hb hb1 hT hgate
  have hMass := mul_le_mul_of_nonneg_left hUpper.le
    (Nat.cast_nonneg (realHalfProductSource b N T).card)
  exact hFinite.trans
    (add_le_add_right (add_le_add_right (add_le_add_right hMass _) _) _)

end
end ImbalancedChen.P4AOriginalFiniteAll22CofinalCoefficient
