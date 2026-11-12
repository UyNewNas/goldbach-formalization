import ImbalancedChen.P4AOriginalFiniteFallbackJointGain
import ImbalancedChen.P4AOriginalFiniteFallbackAllHighAtoms

namespace ImbalancedChen.P4AOriginalFiniteFallbackJointHigh
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
    ∀ a : ℝ,0<a → a≤1/800 → ∀ r n : ℕ,∀ etaPP : ℝ,0<etaPP → etaPP≤P4AOriginalFiniteFallbackCommonGroups.gap m (data e q a) →
    ∀ nu v u_c epsilonMax : ℝ,0<nu → 0<v → nu*v=19/96 → 0<u_c → 0<epsilonMax →
    ∃ eps : ℝ,0<eps ∧ eps<1/8 ∧ eps<epsilonMax ∧ eps^2<v ∧ nu*eps^2<a ∧ nu*eps<1/1000 ∧ nu*eps<etaPP/32 ∧
    ∃ k N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N →
      let omega := nu*eps^2
      let tau := alignedWidth (jointIndex (bank m) (data e q a).m) k
      let w := (N:ℝ)^omega
      let z := cutoff N
      let L := (N:ℝ)^(nu*eps)
      let Q := moduli N w
      let rho := P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N tau L
      let f := F (bank m) (P4AOriginalFull87HistoryCore.width r) n (data e q a) omega N
      P4AOriginalFiniteFallbackAllHighAtoms.HighAtoms m n N (width r) omega tau (nu*eps) etaPP (data e q a) ∧
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
  obtain ⟨E',hE',Hc⟩ := P4AOrderedThirdPositiveRoot.original_four_positive eta htol
  refine ⟨m0,?_⟩
  intro m hm
  obtain ⟨E,hE,Hs⟩ := H m hm
  refine ⟨min E E',lt_min hE hE',?_⟩
  intro e he hei
  obtain ⟨qs,hqs,hs⟩ := Hs e he (hei.trans_le (min_le_left _ _))
  obtain ⟨qc,hqc,hc⟩ := Hc e he (hei.trans_le (min_le_right _ _))
  refine ⟨max qs qc,by omega,?_⟩
  intro q hq a ha ha' r n etaPP hpp hsmall nu v u_c epsilonMax hnu hv hcut hu hm'
  let d := data e q a
  obtain ⟨eps,hp,h8,heps,hsq,hwa,hell,hell',k,hbudget,Nc,hNc,hpay⟩ :=
    P4AOriginalFiniteFallbackPPSchedule.joined (bank m) (P4AOriginalFiniteFallbackCanonical.bounded m) r n
      e (by exact_mod_cast he.le) q a ha etaPP hpp nu v u_c (min epsilonMax (h/nu)) hnu hv hcut hu
      (lt_min hm' (div_pos hh hnu))
  let omega := nu*eps^2
  let idx := jointIndex (bank m) d.m
  let tau := alignedWidth idx k
  have ht : 0<tau := div_pos (logPrimeMeshStep_pos (by norm_num) _) (by positivity)
  have hw : 0<omega := mul_pos hnu (sq_pos_of_pos hp)
  have htop : omega<thirdPrefixRho := by
    have H := mul_lt_mul_of_pos_left hsq hnu
    rw [hcut] at H; exact H
  have hwh : omega≤h := by
    have H := (lt_div_iff₀ hnu).mp (heps.trans_le (min_le_right _ _))
    have h1 : eps<1 := by linarith
    have h2 : eps^2≤eps := by nlinarith
    exact (mul_le_mul_of_nonneg_left h2 hnu.le).trans (by linarith)
  obtain ⟨Ns,hNs⟩ := eventually_atTop.mp (hs q (by omega) a omega ha' hwa.le hwh (width r) n)
  obtain ⟨Np,hNp⟩ := eventually_atTop.mp (hc q (by omega) a omega hw htop)
  refine ⟨eps,hp,h8,heps.trans_le (min_le_left _ _),hsq,hwa,hell,hell',k,max Nc (max Ns Np),by omega,?_⟩
  intro N hN hEven
  have HH := P4AOriginalFiniteFallbackAllHighAtoms.high_atoms m n N (width r) omega tau (nu*eps) etaPP d
    (P4AOriginalFull87HistoryCore.width_pos r) (by change 0≤e; exact_mod_cast he.le) (by omega) hw ht hpp hsmall
    hbudget (mul_nonneg hnu.le hp.le) (by linarith)
  exact ⟨HH,hNs N (by omega) hEven,hNp N (by omega) hEven,hpay N (by omega) hEven⟩

end
end ImbalancedChen.P4AOriginalFiniteFallbackJointHigh
