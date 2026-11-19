import ImbalancedChen.P4AOriginalFiniteFallbackCanonical
import ImbalancedChen.P4AOrderedThirdClippedFactorial
import ImbalancedChen.P4AOrderedThirdActualRoughGeometry

namespace ImbalancedChen.P4AOriginalFiniteFallbackAtoms
noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler P4AUpperTaggedFrozenAdmissionCatalogue P2CanonicalWallFullResidualPayment
open P4AOriginalFiniteFallbackPolicy (F)
open P4AOriginalFiniteFallbackBank (Bank)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalFull87RawChronology (cutoff)
open P4AUpperTaggedMixedWallPayment (raw_support_iff_canonical_validSelection)
open P4AUpperTaggedFirstPrefixDisagreement (decisionAt decisionAt_eq_prefix polarityAfter)
open P4AFull87OrdinaryAdmissionDeletion (reversed_prefix)
open P4AOrderedThirdActualRoughGeometry (every_decision)
open P4AOrderedThirdPhysicalAtoms (outside_scalar boxScalar)
open P4AOrderedThirdClippedFactorial (crop physical_iff)

theorem original_factorial (f : List ℕ → Bool) (omega : ℝ) (N : ℕ)
    (hN : 1<N) (tau : ℝ) (ht : 0<tau) (J : List ℕ) (hJ : J.Pairwise (· ≥ ·)) (H : ℕ → ℝ) :
    let w := (N:ℝ)^omega
    let z := P4AOriginalFull87RawChronology.cutoff N
    let U := universe N N w z
    let B := actualPrimeSlotBox (actualPrimeFineLabelFinset N tau) J
    (boxScalar f N N w z tau J/(actualPrimeFineWordMultiplicity J:ℝ))*
      (∑ ps∈B,(ArithmeticFunction.moebius ps.prod:ℝ)*(if ps.prod∈U then 1 else 0)*H ps.prod)=
      ∑ d∈(B.filter List.SortedGT).image List.prod,coefficient f (fun _ => []) N N w z tau d*H d := by
  dsimp only
  let w := (N:ℝ)^omega
  let z := P4AOriginalFull87RawChronology.cutoff N
  let U := universe N N w z
  have h := actualPrimeFineWord_original_scalar (by omega : 1≤N) ht.le J hJ 1
    (boxScalar f N N w z tau J) (fun d => (if d∈U then 1 else 0)*H d)
  simp only [one_mul,← mul_assoc] at h
  rw [h,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [outside_scalar f N N hN w z tau ht J hd]
  ring

theorem rectangular_factorial (f : List ℕ → Bool) (omega : ℝ) (N : ℕ)
    (hN : 1<N) (tau : ℝ) (ht : 0<tau) (J : List ℕ) (hJ : J.Pairwise (· ≥ ·)) (H : ℕ→ℝ) :
    let w := (N:ℝ)^omega
    let z := cutoff N
    let B := actualPrimeFineLabelFinset N tau
    let I := roughPrimeFinset N N w z
    (boxScalar f N N w z tau J/(actualPrimeFineWordMultiplicity J:ℝ))*
      (∑ ps∈actualPrimeSlotBox (fun j => B j∩I) J,(ArithmeticFunction.moebius ps.prod:ℝ)*H ps.prod)=
      ∑ d∈((actualPrimeSlotBox B J).filter List.SortedGT).image List.prod,
        P4AUpperTaggedParityCompiler.coefficient f (fun _ => []) N N w z tau d*H d := by
  let w := (N:ℝ)^omega
  let z := cutoff N
  let B := actualPrimeFineLabelFinset N tau
  let S := roughPrimeFinset N N w z
  let U := universe N N w z
  have hset : actualPrimeSlotBox (fun j => B j∩S) J=(actualPrimeSlotBox B J).filter
      (fun xs => ∀ p∈xs,p∈S) := by ext xs; rw [crop,Finset.mem_filter]
  rw [← original_factorial f omega N hN tau ht J hJ H]
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

theorem retained_strict_cubes (B : Bank) (delta : ℝ) (hd : 0<delta) (n : ℕ) (d : OriginalData)
    {N cap x : ℕ} (hN : 1<N) {omega v : ℝ} (hw : 0≤omega)
    (hx : x∈rawSupport (P4AOriginalFiniteFallbackPolicy.policy B delta n d omega N false) N cap ((N:ℝ)^omega) ((N:ℝ)^v))
    (k : ℕ) (hk : k<x.primeFactorsList.length) (ho : polarityAfter true (k+1)=false) :
    let r := k+1
    let t := actualPrimeTupleLog N (canonicalPrefix r x)
    let s := P4AOrderedThirdRectangleRate.position r
    let A := (P4AOriginalFiniteFallbackPrograms.code B delta n d s).eval
      (P4AFull87ActualAffineDeletion.coords N _ x.primeFactorsList.reverse)
    (∑ i,t i)<A ∧ ∀ i : Fin r, Even i.val → P5Z.PresievedRoughSlotAffineGates.cube t i<A := by
  let f := F B delta n d 0 N
  have h0 := P4AOriginalFiniteFallbackProjection.support_cut B delta n d (by omega : 1≤N) cap hw ((N:ℝ)^v)
  change x∈rawSupport (F B delta n d omega N) N cap _ _ at hx
  rw [h0] at hx
  obtain ⟨hU,hV⟩ := (raw_support_iff_canonical_validSelection _ _ _ _ _ _).mp hx
  have hlen : k<x.primeFactorsList.reverse.length := by simpa
  have H := every_decision (oddFirstExitPolicy f) _ [] true hV k hlen
  rw [decisionAt_eq_prefix _ _ _ _ _ hlen,ho,List.append_nil,← canonicalPrefix_ofFn (show k+1≤_ from hk),
    reversed_prefix x (k+1) hk] at H
  have hr := (P4AOriginalFiniteFallbackRankReads.read B delta hd n d N cap hN _ _ x hU (k+1) hk ho).2
  have hraw : f (rosserAncestor (k+1) x.primeFactorsList)=true := by simpa [oddFirstExitPolicy] using H
  rw [hr] at hraw
  apply (P5Z.PresievedRoughSlotAffineGates.original_upper_prefix_iff_log hN _ _
    (canonicalPrefix_pos hU hk) (canonicalPrefix_strictAnti hU hk)).mp
  rw [reversed_prefix x (k+1) hk]
  exact of_decide_eq_true hraw


end
end ImbalancedChen.P4AOriginalFiniteFallbackAtoms
