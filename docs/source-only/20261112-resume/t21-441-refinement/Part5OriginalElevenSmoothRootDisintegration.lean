import ImbalancedChen.Part5OriginalH430SmoothPrefixRequests
import ImbalancedChen.CurrentP5MarkedElevenWitnessSource
import ImbalancedChen.RenewalFiniteErrorPropagationP5

/-! The parallel eleven roots on the *original* tagged positive witnesses.
Rows six and eleven use the same E; signed coefficients are applied only
outside each positive split. No new root prime is manufactured for a start,
and this module assigns no 430-generation table to the other nine rows. -/
namespace ImbalancedChen.Part5OriginalElevenSmoothRootDisintegration
noncomputable section
open Set
open scoped Classical BigOperators
open Part5OriginalCausalSmoothAtlas Part5OriginalH430SmoothPrefixRequests
open P2EnhancedLowerPrimeChildCarriers P5RenewalFiniteError
open Part5OriginalH430RequestedHistory Part5OriginalH430PhysicalRoots

/-- Read the physical word largest first, retaining the original tuple in
the index. The zero padding in p5MarkedElevenSource is not a prime slot. -/
def nativeWord (q : P5WitnessFour) : List ℕ :=
  [q.2.2,q.2.1,q.1.2,q.1.1].filter (fun x => x ≠ 0)

theorem no_start_slot : nativeWord p5WitnessZero = [] := by simp [nativeWord,p5WitnessZero]
theorem one_root_slot {p : ℕ} (hp : 0 < p) : nativeWord (p5PadOne p) = [p] := by
  simp [nativeWord,p5PadOne,hp.ne']
theorem two_root_slots {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    nativeWord (p5PadPair (p,q)) = [q,p] := by simp [nativeWord,p5PadPair,hp.ne',hq.ne']
theorem four_root_slots {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    nativeWord ((a,b),(c,d)) = [d,c,b,a] := by simp [nativeWord,ha.ne',hb.ne',hc.ne',hd.ne']

private def ValidPad (n : ℕ) (q : P5WitnessFour) : Prop :=
  (q.1.1=0 ∨ q.1.1 ∈ n.primeFactors) ∧ (q.1.2=0 ∨ q.1.2 ∈ n.primeFactors) ∧
  (q.2.1=0 ∨ q.2.1 ∈ n.primeFactors) ∧ (q.2.2=0 ∨ q.2.2 ∈ n.primeFactors)

private theorem actual_valid (N n : ℕ) (E : ℕ × ℕ → Prop) (i : Fin 11)
    (q : P5WitnessFour) (hw : q ∈ p5PaddedActualWitnesses N E n i) : ValidPad n q := by
  classical
  have ind (C : Prop) (hq : q ∈ p5IndicatorWitness C) : ValidPad n q := by
    by_cases h : C
    · have hq0 : q = p5WitnessZero := by simpa [p5IndicatorWitness,h] using hq
      simp [hq0,ValidPad,p5WitnessZero]
    · simp [p5IndicatorWitness,h] at hq
  have one (S : Finset ℕ) (hs : S ⊆ n.primeFactors) (hq : q ∈ S.image p5PadOne) : ValidPad n q := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact ⟨Or.inr (hs hp),Or.inl rfl,Or.inl rfl,Or.inl rfl⟩
  have two (S : Finset (ℕ × ℕ)) (hs : S ⊆ n.primeFactors ×ˢ n.primeFactors)
      (hq : q ∈ S.image p5PadPair) : ValidPad n q := by
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hq
    have h := Finset.mem_product.mp (hs ht)
    exact ⟨Or.inr h.1,Or.inr h.2,Or.inl rfl,Or.inl rfl⟩
  have four (hq : q ∈ chenFourPrimeCarrier n) : ValidPad n q := by
    obtain ⟨h1,h2⟩ := Finset.mem_product.mp hq
    exact ⟨Or.inr (Finset.mem_product.mp h1).1,Or.inr (Finset.mem_product.mp h1).2,
      Or.inr (Finset.mem_product.mp h2).1,Or.inr (Finset.mem_product.mp h2).2⟩
  fin_cases i
  · exact ind _ hw
  · exact ind _ hw
  · exact one _ (fun _ h => (Finset.mem_filter.mp h).1) hw
  · exact one _ (fun _ h => (Finset.mem_filter.mp h).1) hw
  · exact two _ (fun _ h => (Finset.mem_filter.mp h).1) hw
  · exact two _ (fun _ h => (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1) hw
  · exact two _ (fun _ h => (Finset.mem_filter.mp h).1) hw
  · exact two _ (fun _ h => (Finset.mem_filter.mp h).1) hw
  · exact two _ (fun _ h => (Finset.mem_filter.mp h).1) hw
  · exact four (Finset.mem_filter.mp hw).1
  · exact four (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1

theorem actual_native_prime {N : ℕ} {E : ℕ × ℕ → Prop} {i : Fin 11} {P : ℕ}
    {q : P5WitnessFour} (hw : (i,P,q) ∈ p5MarkedElevenSource N E)
    {p : ℕ} (hp : p ∈ nativeWord q) : p ∈ (N-P).primeFactors := by
  have h := actual_valid N (N-P) E i q ((mem_p5MarkedElevenSource N E i P q).1 hw).2
  have hmem := (List.mem_filter.mp hp).1
  have hn : p ≠ 0 := of_decide_eq_true (List.mem_filter.mp hp).2
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
  rcases hmem with h4|h3|h2|h1
  · subst p; exact h.2.2.2.resolve_left hn
  · subst p; exact h.2.2.1.resolve_left hn
  · subst p; exact h.2.1.resolve_left hn
  · subst p; exact h.1.resolve_left hn

theorem marked_cube {N : ℕ} {E : ℕ × ℕ → Prop} {w : P5MarkedWitness}
    (hN : 1 < N) (hw : w ∈ p5MarkedElevenSource N E) (i : Fin (nativeWord w.2.2).length) :
    logs N (nativeWord w.2.2) i ∈ Icc (0:ℝ) 1 := by
  rcases w with ⟨row, P, q⟩
  have hP := ((mem_p5MarkedElevenSource N E row P q).1 hw).1
  have hPN := (mem_chenAdditivePrimeCarrier.mp hP).1
  have hf := actual_native_prime hw (List.get_mem _ i)
  have hh := Nat.mem_primeFactors.mp hf
  exact physicalPrime_unit hN hh.1.one_lt.le
    ((Nat.le_of_dvd (by omega : 0 < N-P) hh.2.1).trans (Nat.sub_le _ _))

theorem quarter_weight (i : Fin 11) : p5CausalReceiverLedgerWeight i / 4 = rootCoefficient i := by
  fin_cases i <;> norm_num [p5CausalReceiverLedgerWeight,rootCoefficient]

/-- Each input witness has the original additive prime, its original tuple
and its row tag; a common pre-N chart acts only on the physical factors.
Taking arbitrary F preserves all labels/filters; it is an exact identity,
not an analytic licence to filter a sharp inequality. -/
theorem eleven_split (A : Plan) {N : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop)
    (F : P5MarkedWitness → ℝ) :
    (∑ w ∈ p5MarkedElevenSource N E, ∑ j : Box A (nativeWord w.2.2).length,
      atom A j (logs N (nativeWord w.2.2)) * F w) =
      ∑ w ∈ p5MarkedElevenSource N E, F w := by
  apply Finset.sum_congr rfl
  intro w hw
  exact integrate_constant A (marked_cube hN hw) _

theorem actual_quarter_root (A : Plan) {N : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop) :
    (∑ w ∈ p5MarkedElevenSource N E, ∑ j : Box A (nativeWord w.2.2).length,
      atom A j (logs N (nativeWord w.2.2)) * rootCoefficient w.1) =
      currentChenPairedPrimeSum N E / 4 := by
  rw [eleven_split A hN E (fun w => rootCoefficient w.1)]
  simp_rw [← quarter_weight]
  rw [← Finset.sum_div, p5MarkedElevenSource_signed_sum]

/-- At a real U3/U4 one-prime witness, the 430 root begins with exactly
that one slot. This identifies a coordinate, not a descendant count. -/
theorem U34_start_word (N n : ℕ) (root : Root) (tau : ℝ) {p : ℕ} (hp : p.Prime) :
    nativeWord (p5PadOne p) = (rootRequest N n root tau p).old := one_root_slot hp.pos

end
end ImbalancedChen.Part5OriginalElevenSmoothRootDisintegration
