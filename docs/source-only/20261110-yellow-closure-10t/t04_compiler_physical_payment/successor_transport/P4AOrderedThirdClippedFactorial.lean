import ImbalancedChen.P4AOrderedThirdPhysicalAtoms
import ImbalancedChen.ActualPrimeSlotSquarefreeSymmetry

namespace ImbalancedChen.P4AOrderedThirdClippedFactorial
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler (universe)
open P4AOrderedThirdPhysicalAtoms (boxScalar)
open P4AOriginalOrderedThirdActualCoefficient (keep)
open P4AOriginalFull87RawChronology (cutoff)

theorem crop {ι : Type*} (B : ι→Finset ℕ) (S : Finset ℕ) (J : List ι) (xs : List ℕ) :
    xs∈actualPrimeSlotBox (fun j => B j∩S) J ↔ xs∈actualPrimeSlotBox B J ∧ ∀ p∈xs,p∈S := by
  induction J generalizing xs with
  | nil => simp [actualPrimeSlotBox]
  | cons j js ih =>
    cases xs with
    | nil => simp [actualPrimeSlotBox]
    | cons p ps =>
      simp only [actualPrimeSlotBox,Finset.mem_image,Prod.exists,Finset.mem_product,
        List.cons.injEq,Finset.mem_inter,ih]
      constructor
      · rintro ⟨x,ys,⟨⟨hb,hs⟩,hy,ht⟩,rfl,rfl⟩
        exact ⟨⟨x,ys,⟨hb,hy⟩,rfl,rfl⟩,by simpa using And.intro hs ht⟩
      · rintro ⟨⟨x,ys,⟨hb,hy⟩,rfl,rfl⟩,h⟩
        exact ⟨x,ys,⟨⟨hb,h _ List.mem_cons_self⟩,hy,fun q hq => h _ (List.mem_cons_of_mem _ hq)⟩,rfl,rfl⟩

theorem physical_iff (N c : ℕ) (w z : ℝ) (xs : List ℕ) (hp : ∀ p∈xs,Nat.Prime p)
    (hsq : Squarefree xs.prod) :
    xs.prod∈universe N c w z ↔ ∀ p∈xs,p∈roughPrimeFinset N c w z := by
  let C := roughPrimeUniverse N c w z
  have hc : C.toFinset=roughPrimeFinset N c w z := roughPrimeUniverse_toFinset _ _ _ _
  constructor
  · intro h p hpx
    obtain ⟨hsub,_⟩ := P2LowerCanonicalRetainedTrace.canonical_subword_of_universe N c w z h
    have he := (Nat.primeFactorsList_unique (rfl : xs.prod=xs.prod) hp).trans (List.reverse_perm xs.prod.primeFactorsList).symm
    rw [←hc,List.mem_toFinset]
    exact hsub.subset (he.mem_iff.mp hpx)
  · intro h
    have hm : xs.toFinset⊆C.toFinset := by
      intro p hp
      rw [hc]
      exact h p (List.mem_toFinset.mp hp)
    have hd := Finset.prod_dvd_prod_of_subset xs.toFinset C.toFinset id hm
    have heq : (∏p∈xs.toFinset,p)=xs.prod := by
      simpa using List.prod_toFinset (fun p : ℕ => p) (actualPrimeVector_nodup_of_squarefree xs hp hsq)
    have hC : (∏p∈C.toFinset,p)=C.prod := by
      simpa using List.prod_toFinset (fun p : ℕ => p) (roughPrimeUniverse_nodup N c w z)
    refine Nat.mem_divisors.mpr ⟨?_,(P2LowerFiniteCellRounding.roughProduct_squarefree N c w z).ne_zero⟩
    change xs.prod∣C.prod
    simpa only [id_eq,heq,hC] using hd

/-- The exact untagged rough coefficient factors on each original word,
including the w and z boundary bins, the common target mask, squarefree
collisions and all repeated labels. The remaining slot functions are
independent one-prime indicators of cropped intervals. -/
theorem rectangular_factorial (r n : ℕ) (e : ℚ) (q : ℕ) (a omega : ℝ) (N : ℕ)
    (hN : 1<N) (tau : ℝ) (ht : 0<tau) (J : List ℕ) (hJ : J.Pairwise (· ≥ ·)) (H : ℕ→ℝ) :
    let f := keep r n e q a omega N
    let w := (N:ℝ)^omega
    let z := cutoff N
    let B := actualPrimeFineLabelFinset N tau
    let I := roughPrimeFinset N N w z
    (boxScalar f N N w z tau J/(actualPrimeFineWordMultiplicity J:ℝ))*
      (∑ ps∈actualPrimeSlotBox (fun j => B j∩I) J,(ArithmeticFunction.moebius ps.prod:ℝ)*H ps.prod)=
      ∑ d∈((actualPrimeSlotBox B J).filter List.SortedGT).image List.prod,
        P4AUpperTaggedParityCompiler.coefficient f (fun _ => []) N N w z tau d*H d := by
  let f := keep r n e q a omega N
  let w := (N:ℝ)^omega
  let z := cutoff N
  let B := actualPrimeFineLabelFinset N tau
  let S := roughPrimeFinset N N w z
  let U := universe N N w z
  have hset : actualPrimeSlotBox (fun j => B j∩S) J=(actualPrimeSlotBox B J).filter
      (fun xs => ∀ p∈xs,p∈S) := by ext xs; rw [crop,Finset.mem_filter]
  rw [← P4AOrderedThirdPhysicalAtoms.original_factorial r n e q a omega N hN tau ht J hJ H]
  congr 1
  rw [hset,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ps hps
  have hprime := actualPrimeSlotBox_prime B J (fun _ _ p hp => (mem_actualPrimeFineLabelFinset.mp hp).1) ps hps
  by_cases hs : Squarefree ps.prod
  · have hi := physical_iff N N w z ps hprime hs
    by_cases h : ps.prod∈U
    · simp [h,hi.mp h]
    · have hh : ¬∀ p∈ps,p∈S := fun H => h (hi.mpr H)
      simp [h,hh]
  · have hz := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs
    simp only [hz,Int.cast_zero,zero_mul,ite_self]

end
end ImbalancedChen.P4AOrderedThirdClippedFactorial
