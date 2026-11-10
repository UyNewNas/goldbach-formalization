import ImbalancedChen.P4AOrderedThirdSameCoefficient

namespace ImbalancedChen.P4AOrderedThirdCommonSchedule
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P4AOriginalOrderedThirdActualCoefficient (coefficient keep alignedWidth)
open P4AOriginalFull87RawChronology (cutoff rawRoot)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalNewFifthUnion (data)
open P4AOrderedThirdArithmeticOccurrence (fresh)
open P5OriginalCommonPositivePresieve (normalize)

/-- Coarse root choices, finite action resolution, physical beta cutoff
and mesh, and the final target threshold, in their simultaneous order. -/
theorem common_schedule (eta : ℝ) (htol : 0<eta) :
    ∃ E : ℝ,0<E ∧ ∀ e : ℚ,0<(e:ℝ) → (e:ℝ)<E → ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,
    ∀ a : ℝ,0<a → ∀ r n : ℕ,∀ nu v u_c epsilonMax : ℝ,0<nu → 0<v → nu*v=19/96 → 0<u_c → 0<epsilonMax →
    ∃ eps : ℝ,0<eps ∧ eps<1/8 ∧ eps<epsilonMax ∧ eps^2<v ∧ nu*eps^2<a ∧ nu*eps<1/1000 ∧
    ∃ k N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N →
      let omega := nu*eps^2
      let tau := alignedWidth (data e q a).m k
      let w := (N:ℝ)^omega
      let z := cutoff N
      let L := (N:ℝ)^(nu*eps)
      let Q := moduli N w
      let rho := coefficient r n e q a omega N tau L
      let f := keep r n e q a omega N
      normalize N (rawRoot (fresh (data e q a) omega N) N) < (∑ i,currentUpperEighteenPositive i)+eta ∧
      ((N:ℝ)/Real.log (N:ℝ))*P4AFiniteCapTaggedConstructor.compilerExpense f (fun _ => []) N N w z tau L
          <u_c*singularNormalization N ∧
      physicalDensitySum Q rho<p4aReserveRawDensity f N N 0 z-p4aActualPresieveCorrection f N N w z+
        u_c*(singularSeries N/Real.log (N:ℝ)) ∧
      (∀ m : ℕ,rho m≠0 → (m:ℝ)<(N:ℝ)^(599/1000:ℝ)) ∧
      ∀ b T : ℝ,0<b → b<1 → 0<T → (Nat.ceil z:ℝ)≤T^(b/(1+b)) →
        (RealB b N:ℝ)≤((realHalfProductSource b N T).card:ℝ)*physicalDensitySum Q rho+
          realPhysicalDistributionError b N T Q rho+(Nat.ceil z:ℝ)+(T+1) := by
  obtain ⟨E,hE,h⟩ := P4AOrderedThirdPositiveRoot.original_four_positive eta htol
  refine ⟨E,hE,?_⟩
  intro e he heE
  obtain ⟨q0,hq0,harith⟩ := h e he heE
  refine ⟨q0,hq0,?_⟩
  intro q hq a ha r n nu v u_c epsilonMax hnu hv hcut hu hm
  obtain ⟨eps,hp,h8,hmax,hsq,hwa,hell,k,Nc,hNc,hjoint⟩ :=
    P4AOrderedThirdSameCoefficient.joined r n e (by exact_mod_cast he.le) q a ha nu v u_c epsilonMax hnu hv hcut hu hm
  let omega := nu*eps^2
  have hw : 0<omega := mul_pos hnu (sq_pos_of_pos hp)
  have hr : omega<thirdPrefixRho := by
    have hh := mul_lt_mul_of_pos_left hsq hnu
    rw [hcut] at hh
    exact hh
  obtain ⟨Na,hNa⟩ := eventually_atTop.mp (harith q hq a omega hw hr)
  refine ⟨eps,hp,h8,hmax,hsq,hwa,hell,k,max Nc Na,hNc.trans (le_max_left _ _),?_⟩
  intro N hN hEven
  exact ⟨hNa N ((le_max_right _ _).trans hN) hEven,hjoint N ((le_max_left _ _).trans hN) hEven⟩

end
end ImbalancedChen.P4AOrderedThirdCommonSchedule
