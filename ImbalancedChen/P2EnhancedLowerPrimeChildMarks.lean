import ImbalancedChen.P2EnhancedLowerPrimeChildGeometry
import ImbalancedChen.P5zMarkedPrimeFamilyMultiplicity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
TRUE labelled-prime child sigma for one original graph-node mark. The
carrier is the concrete BH/W1/W2 prime-child family, not an arbitrary S or
sigma supplied as an input. Original old slots are retained positionwise;
the node/path mark remains an external summation index when unrolling.
An incoming scalar c is multiplied by the original edge scalar ONCE.
There is no total-rank factorial or new marked factorial normalization.
The /2 and /5 are finite action weights, not count-asymptotic licences.
-/

namespace ImbalancedChen.P2EnhancedLowerPrimeChildMarks
noncomputable section
open Classical Finset
open scoped BigOperators
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry

def oldWord {r N : ℕ} (old : Fin r → Fin (N+1)) : List ℕ :=
  List.ofFn (fun i => (old i).val)

def singleTuple {r N : ℕ} (old : Fin r → Fin (N+1)) (p : Fin (N+1)) :
    Fin (r+1) → Fin (N+1) := Fin.snoc old p

def pairTuple {r N : ℕ} (old : Fin r → Fin (N+1))
    (p : Fin (N+1) × Fin (N+1)) : Fin (r+2) → Fin (N+1) :=
  Fin.snoc (Fin.snoc old p.2) p.1

def singleFamily {r : ℕ} (rule : SingleRule) (N : ℕ) (Q : ℝ)
    (old : Fin r → Fin (N+1)) (chi : ℝ) : Finset (Fin (r+1) → Fin (N+1)) :=
  (singleChildren rule N Q (oldWord old) chi).image (singleTuple old)

def pairFamily {r : ℕ} (bank : Fin 36) (piece : Fin 4) (N : ℕ) (Q : ℝ)
    (old : Fin r → Fin (N+1)) (chi : ℝ) : Finset (Fin (r+2) → Fin (N+1)) :=
  (pairChildren bank piece N Q (oldWord old) chi).image (pairTuple old)

theorem singleTuple_old_label {r N : ℕ} (old : Fin r → Fin (N+1)) (p : Fin (N+1)) (i : Fin r) :
    singleTuple old p i.castSucc=old i := by simp [singleTuple]

theorem pairTuple_old_label {r N : ℕ} (old : Fin r → Fin (N+1))
    (p : Fin (N+1) × Fin (N+1)) (i : Fin r) :
    pairTuple old p i.castSucc.castSucc=old i := by simp [pairTuple]

theorem singleTuple_injective {r N : ℕ} (old : Fin r → Fin (N+1)) :
    Function.Injective (singleTuple old) := by
  intro p q hpq
  simpa only [singleTuple,Fin.snoc_last] using congrFun hpq (Fin.last r)

theorem pairTuple_injective {r N : ℕ} (old : Fin r → Fin (N+1)) :
    Function.Injective (pairTuple old) := by
  intro p q hpq
  apply Prod.ext
  · simpa only [pairTuple,Fin.snoc_last] using congrFun hpq (Fin.last (r+1))
  · simpa only [pairTuple,Fin.snoc_castSucc,Fin.snoc_last] using
      congrFun hpq (Fin.castSucc (Fin.last r))

theorem singleTuple_product {r N : ℕ} (old : Fin r → Fin (N+1)) (p : Fin (N+1)) :
    Part3.labelledProduct (singleTuple old p)=(singleWord (oldWord old) p.val).prod := by
  simp [Part3.labelledProduct,singleTuple,singleWord,oldWord,List.prod_ofFn,
    Fin.prod_univ_castSucc]

theorem pairTuple_product {r N : ℕ} (old : Fin r → Fin (N+1))
    (p : Fin (N+1) × Fin (N+1)) :
    Part3.labelledProduct (pairTuple old p)=(pairWord (oldWord old) p.1.val p.2.val).prod := by
  simp [Part3.labelledProduct,pairTuple,pairWord,oldWord,List.prod_ofFn,
    Fin.prod_univ_castSucc,mul_assoc]

theorem singleFamily_primes {r N : ℕ} (old : Fin r → Fin (N+1))
    (hold : ∀ i,(old i).val.Prime) (rule : SingleRule) (Q chi : ℝ) :
    singleFamily rule N Q old chi ⊆ Part3.labelledPrimeTuples (r+1) N := by
  intro t ht
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [singleTuple,Fin.snoc_last] using (mem_singleChildren.mp hp).1.1
  · simpa only [singleTuple,Fin.snoc_castSucc] using hold j

theorem pairFamily_primes {r N : ℕ} (old : Fin r → Fin (N+1))
    (hold : ∀ i,(old i).val.Prime) (bank : Fin 36) (piece : Fin 4) (Q chi : ℝ) :
    pairFamily bank piece N Q old chi ⊆ Part3.labelledPrimeTuples (r+2) N := by
  intro t ht
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [pairTuple,Fin.snoc_last] using (mem_pairChildren.mp hp).1.1.1
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simpa only [pairTuple,Fin.snoc_castSucc,Fin.snoc_last] using (mem_pairChildren.mp hp).1.2.1
    · simpa only [pairTuple,Fin.snoc_castSucc] using hold k

theorem singleFamily_product_cap {r N : ℕ} (rule : SingleRule) (Q chi : ℝ)
    (old : Fin r → Fin (N+1)) :
    ∀ t ∈ singleFamily rule N Q old chi,Part3.labelledProduct t≤N := by
  intro t ht
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
  rw [singleTuple_product]
  exact (single_actual_residual hp).2.1

theorem pairFamily_product_cap {r N : ℕ} (bank : Fin 36) (piece : Fin 4) (Q chi : ℝ)
    (old : Fin r → Fin (N+1)) :
    ∀ t ∈ pairFamily bank piece N Q old chi,Part3.labelledProduct t≤N := by
  intro t ht
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
  rw [pairTuple_product]
  exact (pair_actual_residual hp).2.1

/-- Original incoming mark scalar, with its original singleton edge once. -/
def singleSigma {r : ℕ} (c : ℝ) (rule : SingleRule) (N : ℕ) (Q : ℝ)
    (old : Fin r → Fin (N+1)) (chi : ℝ) : ℕ → ℝ :=
  p5z_markedProductWeight (singleFamily rule N Q old chi) (fun _ => c*singleEdgeScalar rule)

/-- Original incoming mark scalar, with the W2 PAIR edge1/5 once. Gamma1
unchanged-prefix4/5 and1/5 terms belong to the graph action, not this family. -/
def pairSigma {r : ℕ} (c : ℝ) (bank : Fin 36) (piece : Fin 4) (N : ℕ) (Q : ℝ)
    (old : Fin r → Fin (N+1)) (chi : ℝ) : ℕ → ℝ :=
  p5z_markedProductWeight (pairFamily bank piece N Q old chi) (fun _ => c/5)

theorem singleSigma_nonneg {r N : ℕ} (c : ℝ) (hc : 0≤c) (rule : SingleRule)
    (Q chi : ℝ) (old : Fin r → Fin (N+1)) (m : ℕ) : 0≤singleSigma c rule N Q old chi m :=
  p5z_markedProductWeight_nonneg _ _ (fun _ _ => mul_nonneg hc (singleEdgeScalar_nonneg rule)) m

theorem pairSigma_nonneg {r N : ℕ} (c : ℝ) (hc : 0≤c) (bank : Fin 36) (piece : Fin 4)
    (Q chi : ℝ) (old : Fin r → Fin (N+1)) (m : ℕ) : 0≤pairSigma c bank piece N Q old chi m :=
  p5z_markedProductWeight_nonneg _ _ (fun _ _ => div_nonneg hc (by norm_num)) m

/-- Actual child sigma is the marked pushforward. Product collisions are
summed with their multiplicities before any signed test is evaluated. -/
theorem singleSigma_test {r N : ℕ} (c : ℝ) (rule : SingleRule) (Q chi : ℝ)
    (old : Fin r → Fin (N+1)) (G : ℕ → ℝ) :
    (∑ m ∈ Finset.range (N+1),singleSigma c rule N Q old chi m*G m)=
      ∑ t ∈ singleFamily rule N Q old chi,(c*singleEdgeScalar rule)*G (Part3.labelledProduct t) :=
  p5z_markedProductWeight_sum _ _ (singleFamily_product_cap rule Q chi old) G

theorem pairSigma_test {r N : ℕ} (c : ℝ) (bank : Fin 36) (piece : Fin 4) (Q chi : ℝ)
    (old : Fin r → Fin (N+1)) (G : ℕ → ℝ) :
    (∑ m ∈ Finset.range (N+1),pairSigma c bank piece N Q old chi m*G m)=
      ∑ t ∈ pairFamily bank piece N Q old chi,(c/5)*G (Part3.labelledProduct t) :=
  p5z_markedProductWeight_sum _ _ (pairFamily_product_cap bank piece Q chi old) G

/-- Uniform multiplicity is DERIVED from the actual labelled prime family;
the parent rank is fixed and one/two slots are appended. It is not norm1. -/
theorem singleSigma_bound {r N : ℕ} (c : ℝ) (hc : 0≤c) (rule : SingleRule) (Q chi : ℝ)
    (old : Fin r → Fin (N+1)) (hold : ∀ i,(old i).val.Prime) (m : ℕ) :
    singleSigma c rule N Q old chi m≤c*singleEdgeScalar rule*((r+1)^(r+1) : ℕ) := by
  exact p5z_markedProductWeight_le _ (singleFamily_primes old hold rule Q chi) _
    (c*singleEdgeScalar rule) (mul_nonneg hc (singleEdgeScalar_nonneg rule)) (fun _ _ => le_rfl) m

theorem pairSigma_bound {r N : ℕ} (c : ℝ) (hc : 0≤c) (bank : Fin 36) (piece : Fin 4)
    (Q chi : ℝ) (old : Fin r → Fin (N+1)) (hold : ∀ i,(old i).val.Prime) (m : ℕ) :
    pairSigma c bank piece N Q old chi m≤(c/5)*((r+2)^(r+2) : ℕ) := by
  exact p5z_markedProductWeight_le _ (pairFamily_primes old hold bank piece Q chi) _
    (c/5) (div_nonneg hc (by norm_num)) (fun _ _ => le_rfl) m

end
end ImbalancedChen.P2EnhancedLowerPrimeChildMarks
