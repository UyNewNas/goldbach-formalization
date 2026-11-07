import ImbalancedChen.P5WeightedLabelMultinomialComparison
import ImbalancedChen.ActualFrozenSlotCoefficientRegrouping

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Literal weighted prime-word fibres are identified with their positive
Dirichlet product. Finite prime carriers may overlap between labels: the
weights carry the labels, not a disjointness premise. Prime powers remain
in every fibre. A pointwise subpartition over labels bounds the total
rank-r coefficient by r!, using the PRIMARY actual ordered-prime-fibre
bound, not an assumed unit coefficient.
-/
namespace ImbalancedChen.P5Z.LiteralWeightedPrimeWord
noncomputable section
open scoped Classical BigOperators
open WeightedLabelMultinomialComparison

def pointMass (p : ℕ) : ArithmeticFunction ℝ≥0 :=
  ⟨fun n => if n=p ∧ p≠0 then 1 else 0, by simp⟩

theorem pointMass_one : pointMass 1 = 1 := by
  ext n
  simp [pointMass,ArithmeticFunction.one_apply]

theorem pointMass_mul (p q : ℕ) (hp : p≠0) (hq : q≠0) :
    pointMass p*pointMass q = pointMass (p*q) := by
  ext n
  rw [ArithmeticFunction.mul_apply]
  by_cases hn : n=p*q
  · subst n
    rw [Finset.sum_eq_single (p,q)]
    · simp [pointMass,hp,hq,Nat.mul_ne_zero hp hq]
    · intro d hd hne
      by_cases hd1 : d.1=p
      · have hd2 : d.2≠q := fun h => hne (Prod.ext hd1 h)
        simp [pointMass,hd1,hd2,hp,hq]
      · simp [pointMass,hd1]
    · intro hnot
      exact False.elim (hnot (Nat.mem_divisorsAntidiagonal.mpr ⟨rfl,Nat.mul_ne_zero hp hq⟩))
  · have hsum : ∑ d ∈ n.divisorsAntidiagonal, pointMass p d.1*pointMass q d.2 = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      by_cases hd1 : d.1=p
      · have hd2 : d.2≠q := by
          intro h
          have heq := (Nat.mem_divisorsAntidiagonal.mp hd).1
          rw [hd1,h] at heq
          exact hn heq.symm
        simp [pointMass,hd1,hd2,hp,hq]
      · simp [pointMass,hd1]
    rw [hsum]
    simp [pointMass,hn]

def primeFunction (P : Finset ℕ) (a : ℕ → ℝ≥0) : ArithmeticFunction ℝ≥0 :=
  ∑ p ∈ P, a p • pointMass p

theorem primeFunction_apply (P : Finset ℕ) (a : ℕ → ℝ≥0)
    (hprime : ∀ p ∈ P, Nat.Prime p) (n : ℕ) :
    primeFunction P a n = if n∈P then a n else 0 := by
  change coefficient n (∑ p ∈ P, a p • pointMass p) = _
  rw [map_sum]
  simp only [coefficient,AddMonoidHom.coe_mk,ZeroHom.coe_mk,ArithmeticFunction.smul_map,smul_eq_mul]
  by_cases hn : n∈P
  · rw [if_pos hn,Finset.sum_eq_single n]
    · simp [pointMass,(hprime n hn).ne_zero]
    · intro p hp hpn
      simp [pointMass,Ne.symm hpn]
    · exact fun h => False.elim (h hn)
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro p hp
    have hnp : n≠p := fun h => hn (h.symm ▸ hp)
    simp [pointMass,hnp]

def tupleWeight {ι : Type*} (a : ι → ℕ → ℝ≥0) : List ι → List ℕ → ℝ≥0
  | [],[] => 1
  | i::word,p::ps => a i p*tupleWeight a word ps
  | _,_ => 0

def wordFunction {ι : Type*} (P : Finset ℕ) (a : ι → ℕ → ℝ≥0) (word : List ι) :
    ArithmeticFunction ℝ≥0 := (word.map (fun i => primeFunction P (a i))).prod

def literalCoefficient {ι : Type*} (P : Finset ℕ) (a : ι → ℕ → ℝ≥0)
    (word : List ι) (n : ℕ) : ℝ≥0 :=
  ∑ ps ∈ actualPrimeSlotBox (fun _ : ι => P) word,
    if ps.prod=n then tupleWeight a word ps else 0

private theorem box_prod_ne_zero {ι : Type*} (P : Finset ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p) (word : List ι) (ps : List ℕ)
    (hps : ps∈actualPrimeSlotBox (fun _ : ι => P) word) : ps.prod≠0 := by
  have hp : ∀ p∈ps, 0<p := actualPrimeSlotBox_forall (fun _ : ι => P) word
    (fun p => 0<p) (fun i hi p hp => (hprime p hp).pos) ps hps
  exact Nat.ne_of_gt (List.prod_pos hp)

private theorem box_sum_cons (P : Finset ℕ) {ι : Type*} (i : ι) (word : List ι)
    (F : List ℕ → ArithmeticFunction ℝ≥0) :
    (∑ ps∈actualPrimeSlotBox (fun _ : ι => P) (i::word), F ps) =
      ∑ p∈P, ∑ ps∈actualPrimeSlotBox (fun _ : ι => P) word, F (p::ps) := by
  rw [actualPrimeSlotBox,Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro x hx y hy h
    exact Prod.ext (List.cons.inj h).1 (List.cons.inj h).2

/-- Exact weighted finite Cartesian expansion, before coefficient
projection and BEFORE any normalization or squarefree restriction. -/
theorem wordFunction_expansion {ι : Type*} (P : Finset ℕ) (a : ι → ℕ → ℝ≥0)
    (hprime : ∀ p∈P, Nat.Prime p) (word : List ι) :
    wordFunction P a word =
      ∑ ps∈actualPrimeSlotBox (fun _ : ι => P) word,
        tupleWeight a word ps • pointMass ps.prod := by
  induction word with
  | nil => simp [wordFunction,actualPrimeSlotBox,tupleWeight,pointMass_one]
  | cons i word ih =>
    change primeFunction P (a i)*wordFunction P a word = _
    rw [primeFunction,ih,Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [box_sum_cons]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro ps hps
    rw [smul_mul_assoc,mul_smul_comm,smul_smul,
      pointMass_mul p ps.prod (hprime p hp).ne_zero (box_prod_ne_zero P hprime word ps hps)]
    rfl

/-- Literal weighted prime-word fibre, including ALL prime powers. -/
theorem wordFunction_coefficient {ι : Type*} (P : Finset ℕ) (a : ι → ℕ → ℝ≥0)
    (hprime : ∀ p∈P, Nat.Prime p) (word : List ι) (n : ℕ) :
    wordFunction P a word n = literalCoefficient P a word n := by
  rw [wordFunction_expansion P a hprime]
  change coefficient n (∑ ps∈actualPrimeSlotBox (fun _ : ι => P) word,
    tupleWeight a word ps • pointMass ps.prod) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro ps hps
  have hp := box_prod_ne_zero P hprime word ps hps
  change tupleWeight a word ps*pointMass ps.prod n = _
  simp [pointMass,hp,eq_comm]

theorem tupleWeight_one {ι : Type*} (word : List ι) (ps : List ℕ)
    (hlen : ps.length=word.length) : tupleWeight (fun _ : ι => fun _ => 1) word ps = 1 := by
  induction word generalizing ps with
  | nil => cases ps <;> simp_all [tupleWeight]
  | cons i word ih => cases ps <;> simp_all [tupleWeight]

/-- The total rank-r prime function is bounded by r!, using the primary
unweighted ACTUAL prime fibre theorem. Repeated-prime fibres are retained. -/
theorem prime_indicator_power_le_factorial (P : Finset ℕ)
    (hprime : ∀ p∈P, Nat.Prime p) (r n : ℕ) :
    (primeFunction P (fun _ => 1)^r) n ≤ (r.factorial : ℕ) := by
  let T := actualPrimeSlotBox (fun _ : Unit => P) (List.replicate r ())
  have hcoef : (primeFunction P (fun _ => 1)^r) n = (actualPrimeTupleCoefficient T n : ℝ≥0) := by
    have h := wordFunction_coefficient P (fun _ : Unit => fun _ => 1) hprime (List.replicate r ()) n
    simp only [wordFunction,List.map_replicate,List.prod_replicate] at h
    rw [h]
    unfold literalCoefficient
    calc
      _ = ∑ ps∈T, if ps.prod=n then (1 : ℝ≥0) else 0 := by
        apply Finset.sum_congr rfl
        intro ps hps
        rw [tupleWeight_one _ ps (actualPrimeSlotBox_length _ _ ps hps)]
      _ = _ := by simp [actualPrimeTupleCoefficient,← Finset.sum_filter]
  rw [hcoef]
  exact_mod_cast actualPrimeTupleCoefficient_le_factorial T r n
    (fun ps hps => by simpa using actualPrimeSlotBox_length (fun _ : Unit => P) (List.replicate r ()) ps hps)
    (actualPrimeSlotBox_prime (fun _ : Unit => P) _ (fun i hi p hp => hprime p hp))

theorem sum_primeFunction_le_indicator {ι : Type*} (P : Finset ℕ)
    (hprime : ∀ p∈P, Nat.Prime p) (S : Finset ι) (a : ι → ℕ → ℝ≥0)
    (hassign : ∀ p∈P, ∑ i∈S, a i p ≤ 1) (n : ℕ) :
    (∑ i∈S, primeFunction P (a i)) n ≤ primeFunction P (fun _ => 1) n := by
  change coefficient n (∑ i∈S, primeFunction P (a i)) ≤ _
  rw [map_sum,primeFunction_apply P _ hprime]
  by_cases hn : n∈P
  · rw [if_pos hn]
    simpa only [coefficient,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
      primeFunction_apply P _ hprime,if_pos hn] using hassign n hn
  · simp only [coefficient,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
      primeFunction_apply P _ hprime,if_neg hn,Finset.sum_const_zero,le_refl]

/-- A genuine pointwise label subpartition, rather than disjoint prime
supports, pays the TOTAL prime coefficient. -/
theorem subpartition_total_power_le_factorial {ι : Type*} (P : Finset ℕ)
    (hprime : ∀ p∈P, Nat.Prime p) (S : Finset ι) (a : ι → ℕ → ℝ≥0)
    (hassign : ∀ p∈P, ∑ i∈S, a i p ≤ 1) (r n : ℕ) :
    ((∑ i∈S, primeFunction P (a i))^r) n ≤ (r.factorial : ℕ) :=
  (pow_coefficient_mono (sum_primeFunction_le_indicator P hprime S a hassign) r n).trans
    (prime_indicator_power_le_factorial P hprime r n)

end
end ImbalancedChen.P5Z.LiteralWeightedPrimeWord
