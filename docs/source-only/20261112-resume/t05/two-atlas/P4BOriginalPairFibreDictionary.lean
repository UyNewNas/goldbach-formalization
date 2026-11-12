import ImbalancedChen.P4BOriginalPairFibreVariation
import ImbalancedChen.P5RoughSquareWeightedBudget

/-! Reindex both literal ordered prime slots. The first coordinate owns
ties. Values in the primitive residue class and the coprime centre use the
same original modulus, including at noninvertible smaller primes. -/
namespace ImbalancedChen.P4BOriginalPairFibreDictionary
noncomputable section
open scoped Classical BigOperators
open P4B P4BLabelledPairDictionary
open P4BOriginalPairFibreVariation
open P4BOriginalFiniteSignedTrim (trimmedWeight)
open P5Z.ActualEtaPsiOccurrenceBudget (eta)
open Part3 (labelledPrimeTuples labelledProduct primeProductSignedError)

def kernel (N d x : ℕ) : ℝ :=
  (if Nat.ModEq d x N then 1 else 0)-(if x.Coprime d then 1 else 0)/(d.totient:ℝ)

def outer (N : ℕ) := (chenPrimePrefix N).filter (fun p => (p:ℝ)^2≤Real.exp 1*(N:ℝ))

def cap (N p : ℕ) := min N (Nat.ceil (Real.exp 1*(N:ℝ)/(p:ℝ)))

def naturalWeight (b kappa s kappa0 : ℝ) (N p j : ℕ) : ℝ :=
  eta (((p:ℝ)*(j:ℝ))/(N:ℝ)^(1-kappa0)) *
    smoothPhysicalProfile b N (manuscriptHalfProductCutoff kappa N) s ![coord N p,coord N j]

theorem trimmed_on {N : ℕ} (b kappa s kappa0 : ℝ) {u : Fin 2 → Fin (N+1)}
    (hu : u∈labelledPrimeTuples 2 N) :
    trimmedWeight b kappa s kappa0 N u =
      naturalWeight b kappa s kappa0 N (tuplePair u).1 (tuplePair u).2 := by
  have hp := (Finset.mem_filter.mp hu).2
  have h0 : (1:ℝ)≤((u 0).val:ℝ) := by exact_mod_cast (hp 0).one_le
  have h1 : (1:ℝ)≤((u 1).val:ℝ) := by exact_mod_cast (hp 1).one_le
  have hlog : P4BLabelledLogGeometry.logPoint N u = ![coord N (u 0).val,coord N (u 1).val] := by
    funext i
    fin_cases i <;> simp [P4BLabelledLogGeometry.logPoint,coord,max_eq_right h0,max_eq_right h1]
  simp only [trimmedWeight,naturalWeight,labelledProduct_eq_pairProduct,Nat.cast_mul,
    smoothPhysicalPairOuterRamp_eq_profile,tuplePair,hlog,P4BOriginalFiniteSmoothCount.weight]

theorem pair_mem {N p j : ℕ} (hp : p∈chenPrimePrefix N) (hj : j∈chenPrimePrefix N) :
    pairTuple N (p,j) (mem_chenPrimePrefix.mp hp).1 (mem_chenPrimePrefix.mp hj).1∈
      labelledPrimeTuples 2 N := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro i
  fin_cases i
  · exact (mem_chenPrimePrefix.mp hp).2
  · exact (mem_chenPrimePrefix.mp hj).2

private theorem natural_product {b kappa s kappa0 : ℝ} {N p j : ℕ}
    (hN : (1:ℝ)<N) (hs : 0<s) (hs1 : s≤1)
    (hp : p∈chenPrimePrefix N) (hj : j∈chenPrimePrefix N)
    (h : naturalWeight b kappa s kappa0 N p j≠0) :
    (p:ℝ)*(j:ℝ)≤Real.exp 1*(N:ℝ) := by
  let u := pairTuple N (p,j) (mem_chenPrimePrefix.mp hp).1 (mem_chenPrimePrefix.mp hj).1
  have hu : u∈labelledPrimeTuples 2 N := pair_mem hp hj
  have he : tuplePair u=(p,j) := tuplePair_pairTuple _ _ _ _
  have ht := trimmed_on b kappa s kappa0 hu
  rw [he] at ht
  have htrim : trimmedWeight b kappa s kappa0 N u≠0 := by rw [ht]; exact h
  have hn : P4BOriginalFiniteSmoothCount.weight b kappa s N u≠0 :=
    (mul_ne_zero_iff.mp htrim).2
  have H := smoothPhysicalPairOuterRamp_nonzero_product_lt_exp_mul_N hN hs hu hn
  rw [he,Nat.cast_mul] at H
  exact H.le.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hs1) (Nat.cast_nonneg _))

theorem fibre_eq (swap : Bool) (b kappa s kappa0 : ℝ) (N p j : ℕ) :
    fibre swap b kappa s kappa0 N p j =
      owner swap p j * (if swap then naturalWeight b kappa s kappa0 N j p
                       else naturalWeight b kappa s kappa0 N p j) := by
  cases swap
  · have h : offset false N p+coord N j • direction false = ![coord N p,coord N j] := by
      funext i
      fin_cases i <;> simp [offset,direction]
    simp [fibre,smoothPhysicalProfileLine,h,naturalWeight]
  · have h : offset true N p+coord N j • direction true = ![coord N j,coord N p] := by
      funext i
      fin_cases i <;> simp [offset,direction]
    simp [fibre,smoothPhysicalProfileLine,h,naturalWeight,mul_comm (p:ℝ) (j:ℝ)]

theorem fibre_support {N p j : ℕ} {b kappa s kappa0 : ℝ}
    (hN : (1:ℝ)<N) (hs : 0<s) (hs1 : s≤1) (swap : Bool)
    (hp : p∈chenPrimePrefix N) (hj : j∈chenPrimePrefix N)
    (hf : fibre swap b kappa s kappa0 N p j≠0) : p∈outer N ∧ j≤cap N p := by
  rw [fibre_eq] at hf
  obtain ⟨ho,hw⟩ := mul_ne_zero_iff.mp hf
  have hpj : p≤j := by
    cases swap
    · by_contra h
      exact ho (by simp [owner,h])
    · have : p<j := by
        by_contra h
        exact ho (by simp [owner,h])
      exact this.le
  have hprod : (p:ℝ)*(j:ℝ)≤Real.exp 1*(N:ℝ) := by
    cases swap
    · exact natural_product hN hs hs1 hp hj (by simpa using hw)
    · simpa only [mul_comm (j:ℝ) (p:ℝ)] using
        natural_product hN hs hs1 hj hp (by simpa using hw)
  have hpR : (0:ℝ)<p := by exact_mod_cast (mem_chenPrimePrefix.mp hp).2.pos
  refine ⟨Finset.mem_filter.mpr ⟨hp,?_⟩,le_min (mem_chenPrimePrefix.mp hj).1 ?_⟩
  · rw [pow_two]
    exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hpj) hpR.le).trans hprod
  · apply Nat.cast_le.mp
    apply le_trans _ (Nat.le_ceil _)
    exact (le_div_iff₀ hpR).mpr (by simpa only [mul_comm (j:ℝ) (p:ℝ)] using hprod)

private theorem unlabel {N : ℕ} (F : ℕ → ℕ → ℝ) :
    (∑ u∈labelledPrimeTuples 2 N,F (tuplePair u).1 (tuplePair u).2) =
      ∑ p∈chenPrimePrefix N,∑ j∈chenPrimePrefix N,F p j := by
  rw [← Finset.sum_product' (chenPrimePrefix N) (chenPrimePrefix N) F]
  apply Finset.sum_bij (fun t _ => tuplePair t)
  · intro t ht
    have H := (Finset.mem_filter.mp ht).2
    exact Finset.mem_product.mpr ⟨mem_chenPrimePrefix.mpr ⟨Nat.lt_succ_iff.mp (t 0).isLt,H 0⟩,
      mem_chenPrimePrefix.mpr ⟨Nat.lt_succ_iff.mp (t 1).isLt,H 1⟩⟩
  · exact fun _ _ _ _ h => tuplePair_injective N h
  · intro x hx
    obtain ⟨hp,hj⟩ := Finset.mem_product.mp hx
    exact ⟨pairTuple N x (mem_chenPrimePrefix.mp hp).1 (mem_chenPrimePrefix.mp hj).1,
      pair_mem hp hj,tuplePair_pairTuple _ _ _ _⟩
  · exact fun _ _ => rfl

private theorem own_sum {N : ℕ} (b kappa s kappa0 : ℝ) (d : ℕ) :
    (∑ u∈labelledPrimeTuples 2 N,trimmedWeight b kappa s kappa0 N u *
      kernel N d (labelledProduct u)) =
      (∑ p∈chenPrimePrefix N,∑ j∈chenPrimePrefix N,fibre false b kappa s kappa0 N p j *
        kernel N d (p*j)) +
      (∑ p∈chenPrimePrefix N,∑ j∈chenPrimePrefix N,fibre true b kappa s kappa0 N p j *
        kernel N d (p*j)) := by
  let W := naturalWeight b kappa s kappa0 N
  calc
    _ = ∑ u∈labelledPrimeTuples 2 N,W (tuplePair u).1 (tuplePair u).2 *
          kernel N d ((tuplePair u).1*(tuplePair u).2) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [trimmed_on b kappa s kappa0 hu,labelledProduct_eq_pairProduct]
    _ = ∑ p∈chenPrimePrefix N,∑ j∈chenPrimePrefix N,W p j*kernel N d (p*j) :=
      unlabel _
    _ = _ := by
      conv_rhs => rhs; rw [Finset.sum_comm]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [fibre_eq,fibre_eq]
      by_cases h : p≤j
      · simp [owner,h,not_lt.mpr h,W]
      · simp [owner,h,lt_of_not_ge h,W,Nat.mul_comm j p]

theorem sum_to_outer {N : ℕ} {b kappa s kappa0 : ℝ}
    (hN : (1:ℝ)<N) (hs : 0<s) (hs1 : s≤1) (swap : Bool) (d : ℕ) :
    (∑ p∈chenPrimePrefix N,∑ j∈chenPrimePrefix N,fibre swap b kappa s kappa0 N p j *
      kernel N d (p*j)) =
    ∑ p∈outer N,∑ j∈chenPrimePrefix (cap N p),fibre swap b kappa s kappa0 N p j *
      kernel N d (p*j) := by
  have shrink (p : ℕ) (hp : p∈chenPrimePrefix N) :
      (∑ j∈chenPrimePrefix N,fibre swap b kappa s kappa0 N p j * kernel N d (p*j)) =
        ∑ j∈chenPrimePrefix (cap N p),fibre swap b kappa s kappa0 N p j*kernel N d (p*j) := by
    symm
    apply Finset.sum_subset
    · intro j hj
      obtain ⟨hle,hprime⟩ := mem_chenPrimePrefix.mp hj
      exact mem_chenPrimePrefix.mpr ⟨hle.trans (min_le_left _ _),hprime⟩
    · intro j hj hj'
      by_cases hz : fibre swap b kappa s kappa0 N p j=0
      · rw [hz,zero_mul]
      · exact (hj' (mem_chenPrimePrefix.mpr ⟨(fibre_support hN hs hs1 swap hp hj hz).2,
          (mem_chenPrimePrefix.mp hj).2⟩)).elim
  calc
    _ = ∑ p∈outer N,∑ j∈chenPrimePrefix N,fibre swap b kappa s kappa0 N p j*
          kernel N d (p*j) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro p hp hn
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hz : fibre swap b kappa s kappa0 N p j=0
      · rw [hz,zero_mul]
      · exact (hn (fibre_support hN hs hs1 swap hp hj hz).1).elim
    _ = _ := Finset.sum_congr rfl (fun p hp => shrink p (Finset.mem_filter.mp hp).1)

def row (N : ℕ) (S : Finset ℕ) (c : ℕ → ℝ) (swap : Bool) (b kappa s kappa0 : ℝ)
    (p : ℕ) : ℝ :=
  ∑ d∈S,c d*(∑ j∈chenPrimePrefix (cap N p),fibre swap b kappa s kappa0 N p j *
    kernel N d (p*j))

theorem signed_rows {N : ℕ} {b kappa s kappa0 : ℝ}
    (hN : (1:ℝ)<N) (hs : 0<s) (hs1 : s≤1) (S : Finset ℕ) (c : ℕ → ℝ) :
    primeProductSignedError 2 N N S c (trimmedWeight b kappa s kappa0 N) =
      (∑ p∈outer N,row N S c false b kappa s kappa0 p)+
      (∑ p∈outer N,row N S c true b kappa s kappa0 p) := by
  unfold primeProductSignedError row
  change (∑ d∈S,c d*(∑ u∈labelledPrimeTuples 2 N,trimmedWeight b kappa s kappa0 N u*
    kernel N d (labelledProduct u)))=_
  simp_rw [own_sum, sum_to_outer hN hs hs1,mul_add,Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  exact congrArg₂ (·+·) (Finset.sum_comm) (Finset.sum_comm)

end
end ImbalancedChen.P4BOriginalPairFibreDictionary
