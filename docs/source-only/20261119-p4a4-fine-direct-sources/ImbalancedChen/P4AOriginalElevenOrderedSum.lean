import ImbalancedChen.P4AOriginalElevenOrderedTestLower

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Exact localization of the complete updated signed source: an admitted
word outside the fixed positive G7 box has IDENTICALLY zero cap change.
The remaining true finite sum is on the actual target-deleted prime box;
its error is paid by that fixed box's mass, never the mass near zero.
-/
namespace ImbalancedChen.P4AOriginalElevenOrderedSum
noncomputable section
open VariableEnvelope
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData)
open P2OriginalSixthMomentRow (cutoff)
open P4AOriginalSavedSixthSigned (pre)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87RawChronology (rawRoot)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOriginalElevenActualCommonHistory (bank)

def primes (N : ℕ) := actualPrimeBoxTuples N (fun _ : Fin 6 => cutoff) (fun _ => mu)
def admitted (n : ℕ) (d : OriginalData) (omega : ℝ) (N : ℕ) :=
  P4AOriginalOrderedSixthSigned.admitted n d omega N N (P4AOriginalFull87RawChronology.cutoff N)
def residual (n : ℕ) (d : OriginalData) (omega : ℝ) (N : ℕ) (p : Fin 6→ℕ) :=
  P4AOriginalOrderedSixthSigned.tupleResidual 1 n d omega N N p
def gain (n : ℕ) (d : OriginalData) (omega : ℝ) (N : ℕ) : ℝ :=
  normalize N (rawRoot (P4AOriginalOrderedSixthStages.policy 1 n d omega (N:ℝ)) N-
    rawRoot (P4AOriginalOrderedSixthStages.policy 2 n d omega (N:ℝ)) N)

theorem residual_zero_outside_box (n : ℕ) (d : OriginalData) (omega : ℝ) {N : ℕ}
    (hN : 1<N) (p : Fin 6→ℕ) (hp : p∈admitted n d omega N) (hbox : p∉primes N) :
    residual n d omega N p=0 := by
  let R := P4AOriginalOrderedThirdFullPolicy.current d omega (N:ℝ) (pre p)
  let P := P4AOriginalOrderedSixthStages.orderedLevel 1 n d omega (N:ℝ) (pre p)
  let M := P4AOriginalOrderedSixthStages.orderedLevel 2 n d omega (N:ℝ) (pre p)
  have hPM : P≤M := P4AOriginalOrderedSixthStages.level_mono n R d (N:ℝ) (pre p) (by decide : 1≤2)
  change actualPrimeTupleInitialSaving N N P M p=0
  by_cases heq : P=M
  · rw [heq]
    simp only [actualPrimeTupleInitialSaving,sub_self,zero_mul,zero_div]
  · obtain ⟨c,hc,hupper⟩ := P4AOriginalElevenOrderedChangedSupport.changed_owner n R d (N:ℝ) (pre p)
      (lt_of_le_of_ne hPM heq)
    rw [P4AOriginalElevenPrimeOccurrence.pre_log] at hc
    obtain ⟨i,rfl⟩ := P4AOriginalElevenOwnCaps.sourceCell_surjective c
    have ht := P2OriginalSixthInnerPrimeTests.source_subset_box hc
    have hlist := ((mem_firstExitAdmittedTuples_iff 6
      (P4AOriginalOrderedSixthStages.orderedFifth n d omega (N:ℝ))
      (roughPrimeUniverse N N 0 (P4AOriginalFull87RawChronology.cutoff N)) p).mp hp).1
    have hpri (j : Fin 6) := mem_roughPrimeUniverse.mp (hlist.subset (List.mem_ofFn.mpr ⟨j,rfl⟩))
    exact False.elim (hbox ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
      ⟨fun j => ⟨(hpri j).2.1,(hpri j).2.2.1⟩,ht⟩))

theorem gain_eq_box (n : ℕ) (d : OriginalData) (omega : ℝ) {N : ℕ} (hN : 1<N) :
    gain n d omega N=∑ p∈primes N,(∏ j,1/((p j:ℝ)-1))*
      (if p∈admitted n d omega N then residual n d omega N p else 0) := by
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN.le
  rw [gain,rawRoot,rawRoot,P4AOriginalOrderedSixthSigned.signed_at_stage 1 n d omega N N _ hNr]
  let A := admitted n d omega N
  let B := primes N
  let f := fun p : Fin 6→ℕ => (∏ j,1/((p j:ℝ)-1))*residual n d omega N p
  change (∑ p∈A,f p)=_
  have hrestrict : (∑ p∈A∩B,f p)=∑ p∈A,f p := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro p hp hnot
    have hb : p∉B := fun hh => hnot (Finset.mem_inter.mpr ⟨hp,hh⟩)
    simp only [f,residual_zero_outside_box n d omega hN p hp hb,mul_zero]
  rw [← hrestrict,Finset.inter_comm]
  have he : B∩A=B.filter (fun p => p∈A) := by ext p; simp
  rw [he,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs <;> simp only [f,mul_zero]

theorem sum_test_sums (N r : ℕ) :
    (∑ i : Fin 11,P2OriginalSixthInnerPrimeTests.testSum N r i)=
      ∑ p∈primes N,(∏ j,1/((p j:ℝ)-1))*(∑ i : Fin 11,
        P2OriginalSixthInnerPrimeTests.test r i (actualPrimeTupleLog N p)) := by
  simp only [P2OriginalSixthInnerPrimeTests.testSum,actualPrimeBoxTestSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  exact (Finset.mul_sum _ _ _).symm

theorem exists_ordered_G7_sum_lower (r : ℕ) (eta : ℝ) (heta : 0<eta) :
    ∃ N0 : ℕ,2≤N0 ∧ ∃ n0 : ℕ,∀ n≥n0,∃ e0 : ℝ,0<e0 ∧
    ∀ e : ℚ,0<e → (e:ℝ)<e0 → ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,
    ∀ a omega : ℝ,a≤1/100 → omega≤a → ∀ N≥N0,Even N →
      (∑ i : Fin 11,P2OriginalSixthInnerPrimeTests.testSum N r i)≤gain n (bank e q a) omega N+
        (8*width n/cutoff^2+eta)*actualPrimeBoxMass N (fun _ : Fin 6 => cutoff) (fun _ => mu) := by
  obtain ⟨N0,h0,n0,h⟩ := P4AOriginalElevenOrderedTestLower.exists_ordered_G7_test_lower r eta heta
  refine ⟨N0,h0,n0,?_⟩
  intro n hn
  obtain ⟨e0,he0,hE⟩ := h n hn
  refine ⟨e0,he0,?_⟩
  intro e he hee
  obtain ⟨q0,hq0,hQ⟩ := hE e he hee
  refine ⟨q0,hq0,?_⟩
  intro q hq a omega ha hwa N hN hev
  have hN1 : 1<N := by omega
  have hpoint := hQ q hq a omega ha hwa N hN hev
  have hs := Finset.sum_le_sum (fun p (hp : p∈primes N) =>
    mul_le_mul_of_nonneg_left (hpoint p hp) (actualPrimeBoxWeight_nonneg hp))
  rw [sum_test_sums,gain_eq_box n (bank e q a) omega hN1]
  calc
    _ ≤ ∑ p∈primes N,(∏ j,1/((p j:ℝ)-1))*
        ((if p∈admitted n (bank e q a) omega N then residual n (bank e q a) omega N p else 0)+
          (8*width n/cutoff^2+eta)) := hs
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,actualPrimeBoxMass,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      ring

end
end ImbalancedChen.P4AOriginalElevenOrderedSum
