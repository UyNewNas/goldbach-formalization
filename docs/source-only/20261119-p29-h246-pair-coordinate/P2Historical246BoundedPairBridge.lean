import ImbalancedChen.P2Historical246PairCarrierPartition
import ImbalancedChen.P2OriginalBankThetaMassLimits

/-!
SOURCE ONLY / UNEVALUATED. Same-Q logarithmic coordinate identity and
bounded prime-pair membership bridge. The five exceptional pieces,
unbounded-natural-tuple reindexing and analytic payments remain separate.
-/
namespace ImbalancedChen.P2Historical246BoundedPairBridge

noncomputable section
open Set Finset
open scoped Classical BigOperators
open P2EnhancedLowerPrimeChildCarriers P2Historical246PairCarrierPartition
open P2OriginalBankThetaMassLimits P2OriginalHalfOpenProfileCarrier
open P2OriginalBankChildPrimeMass P5OriginalFeedbackDomains P5OriginalActionMassBound
open P2HistoricalScheduledPointReads P2HistoricalNativePointCounts
open P2Historical248Authentication P2HistoricalW2ArchivedPairWindows
open Part5OriginalH430W2UpperPolygons (parameterQ)
open Part5OriginalH430W2UpperArchiveData (weights)

def pairValues {N : ℕ} (p : Fin (N+1) × Fin (N+1)) : Pair := ![p.1.val,p.2.val]

/-- Both coordinates are evaluated at the same actual total Q and old
product. No change of the prime ceiling, residual exponent or ordering. -/
theorem pairPoint_eq_normalizedLog {N : ℕ} {Q L : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (p : Fin (N+1) × Fin (N+1)) :
    pairPoint Q old p.1.val p.2.val = normalizedLog N L (pairValues p) := by
  have hc (i : Fin 2) : relativePrime Q old (pairValues p i) =
      normalizedLog N L (pairValues p) i := by
    have hr := physical_log_ratio hN hd hL (pairValues p) i
    simpa only [relativePrime,residualLevel,hQ,normalizedLog] using hr
  funext i
  fin_cases i
  · simpa [pairPoint,pairValues] using hc 0
  · simpa [pairPoint,pairValues] using hc 1

/-- The exact passing bucket from the preceding six-way partition. -/
def activeCarrier (N : ℕ) (Q L chi : ℝ) (old : List ℕ)
    (j : Fin 36) (k : Fin 4) : Finset Pair :=
  (halfCarrier N L j k).filter (fun p =>
    interior N L j k p ∧ parentWindow N Q old chi ∧ bothCoprime N old p ∧
      orderedCeiling N chi p ∧ productGate Q old p)

/-- For an already bounded pair, membership is equivalent in both
literal carriers. The half-open arithmetic atoms not in this bucket
remain in the other five pieces of the parent packet. -/
theorem bounded_pair_mem_iff_active {N : ℕ} {Q L chi : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (j : Fin 36) (k : Fin 4) (p : Fin (N+1) × Fin (N+1)) :
    p ∈ pairChildren j k N Q old chi ↔ pairValues p ∈ activeCarrier N Q L chi old j k := by
  have hpoint := pairPoint_eq_normalizedLog hN hd hL hQ p
  constructor
  · intro hp
    obtain ⟨⟨h0,h1⟩,hparent,horder,hdom,hc0,hc1,hprod⟩ := mem_pairChildren.mp hp
    have hinner : interior N L j k (pairValues p) := by
      unfold interior
      rw [← hpoint]
      exact hdom
    have hhalf : normalizedLog N L (pairValues p) ∈ pairHalf (originalW2At j) k :=
      (pairHalf_partition (originalW2At j) k _).mpr (Or.inl hinner)
    have hprime (i : Fin 2) : (pairValues p i).Prime := by
      fin_cases i
      · simpa [pairValues] using h0.1
      · simpa [pairValues] using h1.1
    have hnotN (i : Fin 2) : ¬ pairValues p i ∣ N := by
      fin_cases i
      · have hc := (Nat.coprime_mul_iff_right.mp h0.2).1
        simpa [pairValues] using h0.1.coprime_iff_not_dvd.mp hc
      · have hc := (Nat.coprime_mul_iff_right.mp h1.2).1
        simpa [pairValues] using h1.1.coprime_iff_not_dvd.mp hc
    have hbox : pairValues p ∈ actualPrimeBoxTuples N
        (fun _ : Fin 2 => L/10) (fun _ => 3*L/5) := by
      apply mem_actualPrimeBoxTuples_iff.mpr
      intro i
      have hc := mem_logPrimeBox.mp
        ((pairHalf_in_cube (originalRepairedW2Bank_geometry _ (originalW2At_mem j)) k) hhalf) i
      have hb := (normalizedLog_window hN hL (pairValues p)
        (fun x => (hprime x).pos) i (1/10) (3/5)).mp hc
      refine ⟨hprime i,hnotN i,?_,?_⟩
      · convert hb.1 using 1 <;> congr 1 <;> ring
      · convert hb.2 using 1 <;> congr 1 <;> ring
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hbox,hhalf⟩,hinner,hparent,?_,?_,?_⟩
    · simpa [bothCoprime,pairValues] using And.intro h0.2 h1.2
    · simpa [orderedCeiling,pairValues] using And.intro horder (And.intro hc0 hc1)
    · simpa [productGate,pairValues] using hprod
  · intro hp
    obtain ⟨hhalf,hinner,hparent,hcop,hceiling,hproduct⟩ := Finset.mem_filter.mp hp
    have hbox := (Finset.mem_filter.mp hhalf).1
    have hprime0 : p.1.val.Prime := by
      simpa [pairValues] using (mem_actualPrimeBoxTuples_iff.mp hbox 0).1
    have hprime1 : p.2.val.Prime := by
      simpa [pairValues] using (mem_actualPrimeBoxTuples_iff.mp hbox 1).1
    have hc : p.1.val.Coprime (N*parentProduct old) ∧
        p.2.val.Coprime (N*parentProduct old) := by simpa [bothCoprime,pairValues] using hcop
    have he : p.1.val < p.2.val ∧ physicalPrime N p.1.val < chi ∧
        physicalPrime N p.2.val < chi := by simpa [orderedCeiling,pairValues] using hceiling
    have hq : ((parentProduct old*p.2.val*p.1.val : ℕ) : ℝ) < Q := by
      simpa [productGate,pairValues] using hproduct
    have hdom : pairPoint Q old p.1.val p.2.val ∈ W2PairDomain (originalW2At j) k := by
      rw [hpoint]
      exact hinner
    exact mem_pairChildren.mpr
      ⟨⟨⟨hprime0,hc.1⟩,⟨hprime1,hc.2⟩⟩,hparent,he.1,hdom,he.2.1,he.2.2,hq⟩

/-- The natural-number profile bucket has no extra primes beyond the
bounded child type: its original product gate and parent window imply
both coordinates are strictly below N. -/
theorem pairChildren_image_eq_active {N : ℕ} {Q L chi : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (j : Fin 36) (k : Fin 4) :
    (pairChildren j k N Q old chi).image pairValues = activeCarrier N Q L chi old j k := by
  ext q
  constructor
  · intro h
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
    exact (bounded_pair_mem_iff_active hN hd hL hQ j k p).mp hp
  · intro hq
    obtain ⟨hhalf,_,hparent,_,_,hproduct⟩ := Finset.mem_filter.mp hq
    have hbox := (Finset.mem_filter.mp hhalf).1
    have hp0 : 0 < q 0 := ((mem_actualPrimeBoxTuples_iff.mp hbox) 0).1.pos
    have hp1 : 0 < q 1 := ((mem_actualPrimeBoxTuples_iff.mp hbox) 1).1.pos
    have hmulR : ((parentProduct old*q 1*q 0 : ℕ) : ℝ) < N :=
      lt_of_lt_of_le hproduct hparent.2.2.2.1
    have hmul : parentProduct old*q 1*q 0 < N := by exact_mod_cast hmulR
    have hfactor0 : 1 ≤ parentProduct old*q 1 := Nat.mul_pos hd hp1
    have hfactor1 : 1 ≤ parentProduct old*q 0 := Nat.mul_pos hd hp0
    have hsmall : q 0 ≤ parentProduct old*q 1*q 0 := by
      simpa using Nat.mul_le_mul_right (q 0) hfactor0
    have hlarge : q 1 ≤ parentProduct old*q 1*q 0 := by
      simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul_right (q 1) hfactor1
    have h0 : q 0 < N+1 := by omega
    have h1 : q 1 < N+1 := by omega
    let p : Fin (N+1) × Fin (N+1) := (⟨q 0,h0⟩,⟨q 1,h1⟩)
    have hp : pairValues p = q := by
      funext i
      fin_cases i <;> rfl
    refine Finset.mem_image.mpr ⟨p,?_,hp⟩
    apply (bounded_pair_mem_iff_active hN hd hL hQ j k p).mpr
    simpa only [hp] using hq

/-- Pair value projection does not identify two bounded labelled pairs. -/
theorem pairValues_injective (N : ℕ) : Function.Injective (@pairValues N) := by
  intro p q h
  apply Prod.ext
  · apply Fin.ext
    simpa [pairValues] using congrFun h 0
  · apply Fin.ext
    simpa [pairValues] using congrFun h 1

/-- The passing finite bucket is the actual child-pair sum, including
its original test and multiplicity. It does not pay the other buckets. -/
theorem active_sum_eq_pairChildren {N : ℕ} {Q L chi : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (j : Fin 36) (k : Fin 4) (F : Pair → ℝ) :
    (∑ q ∈ activeCarrier N Q L chi old j k, F q) =
      ∑ p ∈ pairChildren j k N Q old chi, F (pairValues p) := by
  rw [← pairChildren_image_eq_active hN hd hL hQ j k]
  exact Finset.sum_image (fun p _ q _ h => pairValues_injective N h)

/-- Apply the exact bounded bridge at the actual 246th scheduled row;
all four ordered historical lanes retain their original tags. -/
theorem generation246_tagged_bounded_bridge {N : ℕ} {Q L chi : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    {b : Tagged} (hb : b ∈ taggedW2 246) :
    ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧ b.2.pairRows.length = 4 ∧
      (∀ k : Fin 4, encode (lane b.2 k) = weights j k) ∧
      ∀ (k : Fin 4) (p : Fin (N+1) × Fin (N+1)),
        p ∈ pairChildren j k N Q old chi ↔ pairValues p ∈ activeCarrier N Q L chi old j k := by
  obtain ⟨j,hp,hn,hlanes⟩ := actual_pair_lists 246 hb
  exact ⟨j,hp,hn,hlanes,fun k p => bounded_pair_mem_iff_active hN hd hL hQ j k p⟩


/-- The actual generation-246 profile's passing pair contribution can be
summed over the literal child carrier. The profile keeps d=parentProduct
and the original H-side 246 table; this is before the single W2 /5. -/
theorem generation246_tagged_active_profile {N : ℕ} {Q L chi : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    {b : Tagged} (hb : b ∈ taggedW2 246) :
    ∃ j : Fin 36, parameters b.1 = List.ofFn (parameterQ j) ∧ b.2.pairRows.length = 4 ∧
      (∀ k : Fin 4, encode (lane b.2 k) = weights j k) ∧
      ∀ k : Fin 4,
        (∑ q ∈ activeCarrier N Q L chi old j k,
          oldPairAtom N Q L (parentProduct old) j k q) =
        ∑ p ∈ pairChildren j k N Q old chi,
          oldPairAtom N Q L (parentProduct old) j k (pairValues p) := by
  obtain ⟨j,hp,hn,hlanes⟩ := actual_pair_lists 246 hb
  exact ⟨j,hp,hn,hlanes,fun k => active_sum_eq_pairChildren hN hd hL hQ j k _⟩

end
end ImbalancedChen.P2Historical246BoundedPairBridge
