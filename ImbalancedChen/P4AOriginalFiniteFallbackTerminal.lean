import ImbalancedChen.P4AOriginalFiniteFallbackJointGain

namespace ImbalancedChen.P4AOriginalFiniteFallbackTerminal
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P4AOriginalFiniteFallbackPolicy (policy F)
open P4AOriginalFiniteFallbackJointGain (before gains)
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalOrderedThirdActualCoefficient (alignedWidth)
open P4AOriginalFiniteFallbackCount (jointIndex)
open P4AOriginalFull87HistoryCore (width)
open P4AOrderedThirdArithmeticOccurrence (fresh)
open P5OriginalCommonPositivePresieve (normalize)
open P4AFallbackCanonicalBanks (bank)

/-- Same fully evaluated physical coefficient, target, source and width
for the genuine two signed fallback slots, the positive root, the
compiler, support and count. Both asymptotic tolerances are arbitrary. -/
theorem joint (eta gainError : ℝ) (htol : 0<eta) (hg : 0<gainError) :
    ∃ m0 : ℕ,∀ m≥m0,∃ E : ℝ,0<E ∧ ∀ e : ℚ,0<(e:ℝ) → (e:ℝ)<E → ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,
    ∀ a : ℝ,0<a → a≤1/800 → ∀ r n : ℕ,∀ nu v u_c epsilonMax : ℝ,0<nu → 0<v → nu*v=19/96 → 0<u_c → 0<epsilonMax →
    ∃ eps : ℝ,0<eps ∧ eps<1/8 ∧ eps<epsilonMax ∧ eps^2<v ∧ nu*eps^2<a ∧ nu*eps<1/1000 ∧
    ∃ k N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N →
      let omega := nu*eps^2
      let tau := alignedWidth (jointIndex (bank m) (data e q a).m) k
      let w := (N:ℝ)^omega
      let z := cutoff N
      let L := (N:ℝ)^(nu*eps)
      let Q := moduli N w
      let rho := P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N tau L
      let f := F (bank m) (P4AOriginalFull87HistoryCore.width r) n (data e q a) omega N
      currentUpperEighteenGains 4+currentUpperEighteenGains 5-gainError<
        normalize N (rawRoot (before m (width r) n e q a omega N) N-
          rawRoot (policy (bank m) (width r) n (data e q a) omega N) N) ∧
      normalize N (rawRoot (fresh (data e q a) omega N) N) < (∑ i,currentUpperEighteenPositive i)+eta ∧
      ((N:ℝ)/Real.log (N:ℝ))*P4AFiniteCapTaggedConstructor.compilerExpense f (fun _ => []) N N w z tau L
          <u_c*singularNormalization N ∧
      physicalDensitySum Q rho<p4aReserveRawDensity f N N 0 z-p4aActualPresieveCorrection f N N w z+
        u_c*(singularSeries N/Real.log (N:ℝ)) ∧
      (∀ m : ℕ,rho m≠0 → (m:ℝ)<(N:ℝ)^(599/1000:ℝ)) ∧
      ∀ b T : ℝ,0<b → b<1 → 0<T → (Nat.ceil z:ℝ)≤T^(b/(1+b)) →
        (RealB b N:ℝ)≤((realHalfProductSource b N T).card:ℝ)*physicalDensitySum Q rho+
          realPhysicalDistributionError b N T Q rho+(Nat.ceil z:ℝ)+(T+1) := by
  obtain ⟨h,hh,m0,H⟩ := gains gainError hg
  refine ⟨m0,?_⟩
  intro m hm
  obtain ⟨E,hE,Hs⟩ := H m hm
  obtain ⟨E',hE',Hc⟩ := P4AOriginalFiniteFallbackCanonical.common_schedule m eta htol
  refine ⟨min E E',lt_min hE hE',?_⟩
  intro e he hei
  obtain ⟨qs,hqs,hs⟩ := Hs e he (hei.trans_le (min_le_left _ _))
  obtain ⟨qc,hqc,hc⟩ := Hc e he (hei.trans_le (min_le_right _ _))
  refine ⟨max qs qc,by omega,?_⟩
  intro q hq a ha ha' r n nu v u_c epsilonMax hnu hv hcut hu hm'
  obtain ⟨eps,hp,h8,heps,hsq,hwa,hell,k,Nc,hNc,hpay⟩ :=
    hc q (by omega) a ha r n nu v u_c (min epsilonMax (h/nu)) hnu hv hcut hu (lt_min hm' (div_pos hh hnu))
  have hwh : nu*eps^2≤h := by
    have hx := (lt_div_iff₀ hnu).mp (heps.trans_le (min_le_right _ _))
    have he1 : eps<1 := by linarith
    have he2 : eps^2≤eps := by nlinarith
    exact (mul_le_mul_of_nonneg_left he2 hnu.le).trans (by linarith)
  obtain ⟨Ns,hNs⟩ := eventually_atTop.mp (hs q (by omega) a (nu*eps^2) ha' hwa.le hwh (width r) n)
  refine ⟨eps,hp,h8,heps.trans_le (min_le_left _ _),hsq,hwa,hell,k,max Ns Nc,by omega,?_⟩
  intro N hN hEven
  exact ⟨hNs N (by omega) hEven,hpay N (by omega) hEven⟩

end
end ImbalancedChen.P4AOriginalFiniteFallbackTerminal
