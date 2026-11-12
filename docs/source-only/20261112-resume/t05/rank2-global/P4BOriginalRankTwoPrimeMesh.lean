import ImbalancedChen.P4BOriginalRankTwoPositiveRestoration

/-! Literal dyadic windows and a common integer subdivision of the head.
The choices of intervals precede both rows and all progression tests. -/
namespace ImbalancedChen.P4BOriginalRankTwoPrimeMesh
noncomputable section
open Classical
open scoped BigOperators
open P4BOriginalRankTwoPositiveRestoration (discrepancy)
open P4BOriginalPairFibreDictionary (naturalWeight kernel)
open P4BOriginalFiniteSignedTrim (trimmedWeight)
open P4BLabelledPairDictionary
open Part3 (labelledPrimeTuples labelledProduct primeProductSignedError)

def primes (l u : ℕ) := (Finset.Ioc l u).filter Nat.Prime
def base (i : ℕ) : ℕ := 2^i
def cap (N P : ℕ) := min N (2*P)
def bank (N : ℕ) := Finset.range (Nat.log2 N+1)
def box (N i : ℕ) := primes (base i) (cap N (base i))

theorem mem_primes {l u p : ℕ} : p∈primes l u ↔ l<p ∧ p≤u ∧ p.Prime := by
  simp only [primes,Finset.mem_filter,Finset.mem_Ioc]
  tauto

theorem count_primes (l u : ℕ) : (primes l u).card≤u-l := by
  simpa only [Nat.card_Ioc] using Finset.card_le_card
    (Finset.filter_subset Nat.Prime (Finset.Ioc l u))

theorem base_le {N i : ℕ} (hN : 0<N) (hi : i∈bank N) : base i≤N :=
  (Nat.le_log2 hN.ne').mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

theorem box_le (N i : ℕ) : (box N i).card≤base i := by
  apply (count_primes _ _).trans
  have h := min_le_right N (2*base i)
  change min N (2*base i)-base i≤base i
  omega

theorem box_spec {N i p : ℕ} (h : p∈box N i) :
    p∈chenPrimePrefix N ∧ base i<p ∧ p≤2*base i := by
  obtain ⟨hl,hh,hp⟩ := mem_primes.mp h
  exact ⟨mem_chenPrimePrefix.mpr ⟨hh.trans (min_le_left _ _),hp⟩,hl,hh.trans (min_le_right _ _)⟩

theorem dyadic_sum (N : ℕ) (F : ℕ → ℝ) :
    (∑ p∈chenPrimePrefix N,F p)=∑ i∈bank N,∑ p∈box N i,F p := by
  let idx := fun p : ℕ => Nat.log2 (p-1)
  have owns (p : ℕ) (hp : p∈chenPrimePrefix N) : idx p∈bank N := by
    obtain ⟨hpN,hpr⟩ := mem_chenPrimePrefix.mp hp
    have hz : p-1≠0 := by have := hpr.two_le; omega
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_log2
      (show N≠0 by have := hpr.two_le; omega)).mpr ((Nat.log2_self_le hz).trans (by omega))))
  have hf (i : ℕ) : (chenPrimePrefix N).filter (fun p => idx p=i)=box N i := by
    ext p
    constructor
    · intro h
      obtain ⟨hp,he⟩ := Finset.mem_filter.mp h
      obtain ⟨hpN,hpr⟩ := mem_chenPrimePrefix.mp hp
      have hz : p-1≠0 := by have := hpr.two_le; omega
      have h := (Nat.log2_eq_iff hz).mp he
      rw [pow_succ] at h
      exact mem_primes.mpr ⟨by dsimp [base]; omega,
        le_min hpN (by dsimp [base]; omega),hpr⟩
    · intro h
      obtain ⟨hp,hl,hu⟩ := box_spec h
      have hz : p-1≠0 := by have := (mem_chenPrimePrefix.mp hp).2.two_le; omega
      refine Finset.mem_filter.mpr ⟨hp,(Nat.log2_eq_iff hz).mpr ⟨?_,?_⟩⟩
      · change 2^i<p at hl
        omega
      · rw [pow_succ]
        change p≤2*(2^i) at hu
        omega
  simpa only [hf] using (Finset.sum_fiberwise_of_maps_to
    (s:=chenPrimePrefix N) (t:=bank N) (g:=idx) owns F).symm

private theorem unlabel (N : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ t∈labelledPrimeTuples 2 N,F (tuplePair t).1 (tuplePair t).2)=
      ∑ p∈chenPrimePrefix N,∑ t∈chenPrimePrefix N,F p t := by
  rw [← Finset.sum_product' (chenPrimePrefix N) (chenPrimePrefix N) F]
  apply Finset.sum_bij (fun t _ => tuplePair t)
  · intro t ht
    have hp := (Finset.mem_filter.mp ht).2
    exact Finset.mem_product.mpr ⟨mem_chenPrimePrefix.mpr ⟨Nat.lt_succ_iff.mp (t 0).isLt,hp 0⟩,
      mem_chenPrimePrefix.mpr ⟨Nat.lt_succ_iff.mp (t 1).isLt,hp 1⟩⟩
  · exact fun _ _ _ _ he => tuplePair_injective N he
  · intro z hz
    obtain ⟨hp,hq⟩ := Finset.mem_product.mp hz
    exact ⟨pairTuple N z (mem_chenPrimePrefix.mp hp).1 (mem_chenPrimePrefix.mp hq).1,
      P4BOriginalPairFibreDictionary.pair_mem hp hq,tuplePair_pairTuple _ _ _ _⟩
  · exact fun _ _ => rfl

theorem source_blocks (N : ℕ) (b kap s kap0 : ℝ) (S : Finset ℕ) (c : ℕ → ℝ) :
    primeProductSignedError 2 N N S c (trimmedWeight b kap s kap0 N)=
      ∑ i∈bank N,∑ j∈bank N,discrepancy N S c (box N i) (box N j)
        (naturalWeight b kap s kap0 N) := by
  let W := naturalWeight b kap s kap0 N
  have inner (d : ℕ) : (∑ u∈labelledPrimeTuples 2 N,
      trimmedWeight b kap s kap0 N u*kernel N d (labelledProduct u))=
      ∑ i∈bank N,∑ j∈bank N,∑ p∈box N i,∑ t∈box N j,W p t*kernel N d (p*t) := by
    calc
      _ = ∑ u∈labelledPrimeTuples 2 N,W (tuplePair u).1 (tuplePair u).2*
          kernel N d ((tuplePair u).1*(tuplePair u).2) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [P4BOriginalPairFibreDictionary.trimmed_on _ _ _ _ hu,labelledProduct_eq_pairProduct]
      _ = ∑ p∈chenPrimePrefix N,∑ t∈chenPrimePrefix N,W p t*kernel N d (p*t) := unlabel N _
      _ = _ := by
        rw [dyadic_sum N]
        apply Finset.sum_congr rfl
        intro i _
        calc
          _ = ∑ p∈box N i,∑ j∈bank N,∑ t∈box N j,W p t*kernel N d (p*t) :=
            Finset.sum_congr rfl (fun p _ => dyadic_sum N (fun t => W p t*kernel N d (p*t)))
          _ = _ := Finset.sum_comm
  change (∑ d∈S,c d*(∑ u∈labelledPrimeTuples 2 N,trimmedWeight b kap s kap0 N u*
    kernel N d (labelledProduct u)))=_
  simp only [inner,discrepancy,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact Finset.sum_comm

def stride (P J : ℕ) := P/J+1
def edge (P H J i : ℕ) := min H (P+i*stride P J)
def cell (P H J i : ℕ) := primes (edge P H J i) (edge P H J (i+1))

theorem edge_mono (P H J : ℕ) : Monotone (edge P H J) :=
  fun _ _ h => min_le_min_left _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _)

theorem edge_zero {P H J : ℕ} (hPH : P≤H) : edge P H J 0=P := by simp [edge,min_eq_right hPH]

theorem edge_last {P H J : ℕ} (hJ : 0<J) (hH : H≤2*P) : edge P H J J=H := by
  have h := Nat.mod_add_div P J
  have hr := Nat.mod_lt P hJ
  unfold edge stride
  rw [Nat.mul_add,Nat.mul_one]
  exact min_eq_left (by omega)

theorem edge_bounds {P H J : ℕ} (hPH : P≤H) (i : ℕ) : P≤edge P H J i ∧ edge P H J i≤H :=
  ⟨le_min hPH (Nat.le_add_right _ _),min_le_left _ _⟩

theorem cell_card (P H J i : ℕ) : (cell P H J i).card≤stride P J := by
  apply (count_primes _ _).trans
  unfold edge
  rw [Nat.succ_mul]
  omega

theorem stride_bound {P J : ℕ} (hJ : 0<J) (hJP : J≤P) :
    (stride P J:ℝ)≤2*(P:ℝ)/J := by
  have hJr : 0<(J:ℝ) := by exact_mod_cast hJ
  have hratio : 1≤(P:ℝ)/J := (one_le_div hJr).mpr (by exact_mod_cast hJP)
  have h := (Nat.cast_div_le (m:=P) (n:=J) : ((P/J:ℕ):ℝ)≤(P:ℝ)/J)
  simp only [stride,Nat.cast_add,Nat.cast_one]
  linarith

theorem cells_sum {P H J : ℕ} (hPH : P≤H) (hH : H≤2*P) (hJ : 0<J) (F : ℕ → ℝ) :
    (∑ p∈primes P H,F p)=∑ i∈Finset.range J,∑ p∈cell P H J i,F p := by
  let E := edge P H J
  have he := edge_mono P H J
  have hzero : E 0=P := edge_zero hPH
  have hadd (i : ℕ) : (∑ p∈primes P (E i),F p)+(∑ p∈cell P H J i,F p)=
      ∑ p∈primes P (E (i+1)),F p := by
    have hPH' : P≤E i := (edge_bounds hPH i).1
    have hh := he (Nat.le_succ i)
    change (∑ p∈primes P (E i),F p)+(∑ p∈primes (E i) (E (i+1)),F p)=_
    rw [← Finset.sum_union (Finset.disjoint_left.mpr (fun p hp hq =>
      (not_lt_of_ge (mem_primes.mp hp).2.1) (mem_primes.mp hq).1))]
    congr 1
    ext p
    simp only [Finset.mem_union,mem_primes]
    omega
  have hc (i : ℕ) : (∑ p∈cell P H J i,F p)=(∑ p∈primes P (E (i+1)),F p)-
      ∑ p∈primes P (E i),F p := by linarith only [hadd i]
  simp_rw [hc]
  rw [Finset.sum_range_sub,show E J=H from edge_last hJ hH,hzero]
  simp [primes]

end
end ImbalancedChen.P4BOriginalRankTwoPrimeMesh
