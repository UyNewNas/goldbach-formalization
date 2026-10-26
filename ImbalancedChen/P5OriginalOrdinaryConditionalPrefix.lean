import ImbalancedChen.P5OriginalOrdinaryBetaRegroup
import Mathlib.Data.List.Sort

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Literal Rosser prefix tests after the exact small/rough split. Rough primes
come first in decreasing order. The rough prefix gates are unchanged;
every subsequent small-prefix gate has the actual rough product d and the
actual rough cardinality as its state. No fixed independent beta polynomial
is substituted, and the existing physical sigma is unchanged.
-/

namespace ImbalancedChen.P5Z.OriginalOrdinaryConditionalPrefix

noncomputable section
open scoped BigOperators
open Classical
open OriginalOrdinaryBetaRegroup
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

/-- At a rough prime, the small part contributes nothing to the prefix. -/
theorem rough_prefix_filter {A B : Finset ℕ} {w : ℝ}
    (hA : ∀ q∈A,w≤(q:ℝ)) (hB : ∀ q∈B,(q:ℝ)<w)
    {p : ℕ} (hp : p∈A) :
    (A∪B).filter (fun q=>p≤q)=A.filter (fun q=>p≤q) := by
  ext q
  simp only [Finset.mem_filter,Finset.mem_union]
  constructor
  · rintro ⟨hq,hpq⟩
    rcases hq with hq|hq
    · exact ⟨hq,hpq⟩
    · have hpqR : (p:ℝ)≤q := by exact_mod_cast hpq
      exact ((not_lt_of_ge ((hA p hp).trans hpqR)) (hB q hq)).elim
  · rintro ⟨hq,hpq⟩
    exact ⟨Or.inl hq,hpq⟩

/-- At a small prime, the whole rough part is already in the prefix. -/
theorem small_prefix_filter {A B : Finset ℕ} {w : ℝ}
    (hA : ∀ q∈A,w≤(q:ℝ)) (hB : ∀ q∈B,(q:ℝ)<w)
    {p : ℕ} (hp : p∈B) :
    (A∪B).filter (fun q=>p≤q)=A∪B.filter (fun q=>p≤q) := by
  ext q
  simp only [Finset.mem_filter,Finset.mem_union]
  constructor
  · rintro ⟨hq,hpq⟩
    exact hq.elim Or.inl (fun hq=>Or.inr ⟨hq,hpq⟩)
  · rintro (hq|⟨hq,hpq⟩)
    · refine ⟨Or.inl hq,?_⟩
      have h : (p:ℝ)<q := (hB p hp).trans_le (hA q hq)
      exact_mod_cast h.le
    · exact ⟨Or.inr hq,hpq⟩

theorem separated_disjoint {A B : Finset ℕ} {w : ℝ}
    (hA : ∀ q∈A,w≤(q:ℝ)) (hB : ∀ q∈B,(q:ℝ)<w) : Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro p hpA hpB
  exact (not_lt_of_ge (hA p hpA)) (hB p hpB)

/-- Exact finite state of the original odd-prefix gates. The second
conjunct displays the real state: card A and prod A, with no target gate
assumed as a hypothesis. -/
theorem upperAdmissible_union_iff {A B : Finset ℕ} {w L : ℝ}
    (hA : ∀ q∈A,w≤(q:ℝ)) (hB : ∀ q∈B,(q:ℝ)<w) :
    UpperAdmissibleSet L (A∪B) ↔
      UpperAdmissibleSet L A ∧
      ∀ p∈B, ¬Even (A.card+(B.filter (fun q=>p≤q)).card) →
        ((A.prod id:ℕ):ℝ)*(((B.filter (fun q=>p≤q)).prod id:ℕ):ℝ)*(p:ℝ)^2<L := by
  have hdis := separated_disjoint hA hB
  have hdisP (p : ℕ) : Disjoint A (B.filter (fun q=>p≤q)) :=
    hdis.mono_right (Finset.filter_subset _ _)
  constructor
  · intro h
    constructor
    · intro p hp hodd
      have hh := h p (Finset.mem_union_left _ hp)
      rw [rough_prefix_filter hA hB hp] at hh
      exact hh hodd
    · intro p hp hodd
      have hh := h p (Finset.mem_union_right _ hp)
      rw [small_prefix_filter hA hB hp,Finset.card_union_of_disjoint (hdisP p),
        Finset.prod_union (hdisP p),Nat.cast_mul] at hh
      exact hh hodd
  · rintro ⟨hrough,hsmall⟩ p hp hodd
    rcases Finset.mem_union.mp hp with hp|hp
    · rw [rough_prefix_filter hA hB hp] at hodd ⊢
      exact hrough p hp hodd
    · rw [small_prefix_filter hA hB hp,Finset.card_union_of_disjoint (hdisP p)] at hodd
      rw [small_prefix_filter hA hB hp,Finset.prod_union (hdisP p),Nat.cast_mul]
      exact hsmall p hp hodd

/-- An even rough cardinality leaves the upper parity on the small part;
the real level is divided by the actual rough product. -/
theorem even_state_small_gates {A B : Finset ℕ} {L : ℝ}
    (hprod : 0<((A.prod id:ℕ):ℝ)) (hEven : Even A.card) :
    (∀ p∈B, ¬Even (A.card+(B.filter (fun q=>p≤q)).card) →
      ((A.prod id:ℕ):ℝ)*(((B.filter (fun q=>p≤q)).prod id:ℕ):ℝ)*(p:ℝ)^2<L) ↔
      UpperAdmissibleSet (L/((A.prod id:ℕ):ℝ)) B := by
  have hpar (k : ℕ) : ¬Even (A.card+k) ↔ ¬Even k := by
    simp only [Nat.even_iff] at hEven ⊢
    omega
  unfold UpperAdmissibleSet
  constructor
  · intro h p hp hodd
    have hh := h p hp ((hpar _).mpr hodd)
    apply (lt_div_iff₀ hprod).mpr
    nlinarith only [hh]
  · intro h p hp hodd
    have hh := (lt_div_iff₀ hprod).mp (h p hp ((hpar _).mp hodd))
    nlinarith only [hh]

/-- An odd rough cardinality flips to the literal LOWER small-prefix
parity. No nonnegativity of the lower small polynomial is asserted. -/
theorem odd_state_small_gates {A B : Finset ℕ} {L : ℝ}
    (hprod : 0<((A.prod id:ℕ):ℝ)) (hOdd : ¬Even A.card) :
    (∀ p∈B, ¬Even (A.card+(B.filter (fun q=>p≤q)).card) →
      ((A.prod id:ℕ):ℝ)*(((B.filter (fun q=>p≤q)).prod id:ℕ):ℝ)*(p:ℝ)^2<L) ↔
      LowerAdmissibleSet (L/((A.prod id:ℕ):ℝ)) B := by
  have hpar (k : ℕ) : ¬Even (A.card+k) ↔ Even k := by
    simp only [Nat.even_iff] at hOdd ⊢
    omega
  unfold LowerAdmissibleSet
  constructor
  · intro h p hp heven
    have hh := h p hp ((hpar _).mpr heven)
    apply (lt_div_iff₀ hprod).mpr
    nlinarith only [hh]
  · intro h p hp hodd
    have hh := (lt_div_iff₀ hprod).mp (h p hp ((hpar _).mp hodd))
    nlinarith only [hh]

/-- Concrete original e*d gates, with the actual natural rough product d
as state. Both empty factor lists and the prime exactly at w are covered. -/
theorem actual_upper_gates {N cap e d : ℕ} {w Z L : ℝ}
    (he : e∈actualSmallRosserSupport N cap w)
    (hd : d∈roughSupport N cap w Z) :
    UpperAdmissibleSet L (e*d).primeFactors ↔
      UpperAdmissibleSet L d.primeFactors ∧
      ∀ p∈e.primeFactors, ¬Even (d.primeFactors.card+(e.primeFactors.filter (fun q=>p≤q)).card) →
        (d:ℝ)*(((e.primeFactors.filter (fun q=>p≤q)).prod id:ℕ):ℝ)*(p:ℝ)^2<L := by
  have heS := actualSmallRosserSupport_smallPrimeSupportedAt N cap w he
  have hdR := roughSupport_rough hd
  have hdSF := Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd).1
    (roughProduct_squarefree N cap w Z)
  rw [Nat.primeFactors_mul heS.1 hdR.1,Finset.union_comm]
  have hh := upperAdmissible_union_iff hdR.2 heS.2 (L:=L)
  rwa [Nat.prod_primeFactors_of_squarefree hdSF] at hh

theorem actual_upper_gates_even {N cap e d : ℕ} {w Z L : ℝ}
    (he : e∈actualSmallRosserSupport N cap w)
    (hd : d∈roughSupport N cap w Z) (hEven : Even d.primeFactors.card) :
    UpperAdmissibleSet L (e*d).primeFactors ↔
      UpperAdmissibleSet L d.primeFactors ∧ UpperAdmissibleSet (L/(d:ℝ)) e.primeFactors := by
  have hdSF := Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd).1
    (roughProduct_squarefree N cap w Z)
  have hpos : 0<((d.primeFactors.prod id:ℕ):ℝ) := by
    rw [Nat.prod_primeFactors_of_squarefree hdSF]
    exact_mod_cast Nat.pos_of_ne_zero hdSF.ne_zero
  have hc := even_state_small_gates (B:=e.primeFactors) (L:=L) hpos hEven
  rw [Nat.prod_primeFactors_of_squarefree hdSF] at hc
  rw [actual_upper_gates he hd,hc]

theorem actual_upper_gates_odd {N cap e d : ℕ} {w Z L : ℝ}
    (he : e∈actualSmallRosserSupport N cap w)
    (hd : d∈roughSupport N cap w Z) (hOdd : ¬Even d.primeFactors.card) :
    UpperAdmissibleSet L (e*d).primeFactors ↔
      UpperAdmissibleSet L d.primeFactors ∧ LowerAdmissibleSet (L/(d:ℝ)) e.primeFactors := by
  have hdSF := Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd).1
    (roughProduct_squarefree N cap w Z)
  have hpos : 0<((d.primeFactors.prod id:ℕ):ℝ) := by
    rw [Nat.prod_primeFactors_of_squarefree hdSF]
    exact_mod_cast Nat.pos_of_ne_zero hdSF.ne_zero
  have hc := odd_state_small_gates (B:=e.primeFactors) (L:=L) hpos hOdd
  rw [Nat.prod_primeFactors_of_squarefree hdSF] at hc
  rw [actual_upper_gates he hd,hc]

/-- The actual native arithmetic function, not just its support predicate,
has precisely these finite states. The last state is (d, card(primes d));
all e-dependence remains in its genuine small-prime prefixes and cutoff. -/
theorem actual_native_conditional_value {N cap e d : ℕ} {w Z L : ℝ}
    (hwZ : w≤Z) (he : e∈actualSmallRosserSupport N cap w)
    (hd : d∈roughSupport N cap w Z) :
    actualSmallRosserPlus N cap Z L (e*d) =
      if ((e*d:ℕ):ℝ)<L ∧ UpperAdmissibleSet L d.primeFactors ∧
        (∀ p∈e.primeFactors,
          ¬Even (d.primeFactors.card+(e.primeFactors.filter (fun q=>p≤q)).card) →
          (d:ℝ)*(((e.primeFactors.filter (fun q=>p≤q)).prod id:ℕ):ℝ)*(p:ℝ)^2<L)
      then (-1:ℝ)^(d.primeFactors.card+e.primeFactors.card) else 0 := by
  have heS := actualSmallRosserSupport_smallPrimeSupportedAt N cap w he
  have hdR := roughSupport_rough hd
  have hdis : Disjoint d.primeFactors e.primeFactors := separated_disjoint hdR.2 heS.2
  have hcard : (e*d).primeFactors.card=d.primeFactors.card+e.primeFactors.card := by
    rw [Nat.primeFactors_mul heS.1 hdR.1,Finset.card_union_of_disjoint hdis.symm]
    omega
  have hmem : e*d∈actualSmallRosserSupport N cap Z := by
    rw [nativeSupport_eq_products N cap hwZ]
    exact Finset.mem_image.mpr ⟨(e,d),Finset.mem_product.mpr ⟨he,hd⟩,rfl⟩
  have hmem' : e*d∈(actualSmallPrimeProduct N cap Z).divisors := hmem
  change upperWeight (actualSmallPrimeProduct N cap Z) L (e*d)=_
  rw [upperWeight_apply]
  simp only [hmem',true_and,actual_upper_gates he hd,hcard,and_assoc]

/-- Sorted original prime factors are connected as ROUGH then SMALL.
The statement concerns the actual factor lists, not a replacement scan. -/
theorem descending_actual_factor_connection {e d : ℕ} {w : ℝ}
    (he : SmallPrimeSupportedAt w e) (hd : RoughPrimeSupportedAt w d) :
    (e*d).primeFactorsList.reverse=d.primeFactorsList.reverse++e.primeFactorsList.reverse := by
  have hcross : ∀ p∈d.primeFactorsList.reverse,∀ q∈e.primeFactorsList.reverse,q≤p := by
    intro p hp q hq
    have hpd : p∈d.primeFactors := Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp hp),
        Nat.dvd_of_mem_primeFactorsList (List.mem_reverse.mp hp),hd.1⟩
    have hqe : q∈e.primeFactors := Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp hq),
        Nat.dvd_of_mem_primeFactorsList (List.mem_reverse.mp hq),he.1⟩
    have h : (q:ℝ)<p := (he.2 q hqe).trans_le (hd.2 p hpd)
    exact_mod_cast h.le
  have hsort : (d.primeFactorsList.reverse++e.primeFactorsList.reverse).Pairwise (·≥·) := by
    apply List.pairwise_append.mpr
    exact ⟨(Nat.primeFactorsList_sorted d).reverse.pairwise,
      (Nat.primeFactorsList_sorted e).reverse.pairwise,hcross⟩
  have hprime : ∀ p∈d.primeFactorsList.reverse++e.primeFactorsList.reverse,Nat.Prime p := by
    intro p hp
    rcases List.mem_append.mp hp with hp|hp
    all_goals exact Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp hp)
  have hprimeF : ∀ p∈(e*d).primeFactorsList.reverse,Nat.Prime p :=
    fun p hp=>Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp hp)
  have hprod : (d.primeFactorsList.reverse++e.primeFactorsList.reverse).prod=
      ((e*d).primeFactorsList.reverse).prod := by
    rw [List.prod_append,List.prod_reverse,List.prod_reverse,List.prod_reverse,
      Nat.prod_primeFactorsList hd.1,Nat.prod_primeFactorsList he.1,
      Nat.prod_primeFactorsList (mul_ne_zero he.1 hd.1)]
    exact Nat.mul_comm d e
  have hperm := (Nat.primeFactorsList_unique hprod hprime).trans
    (Nat.primeFactorsList_unique
      (rfl : ((e*d).primeFactorsList.reverse).prod=((e*d).primeFactorsList.reverse).prod) hprimeF).symm
  exact (hperm.eq_of_pairwise' hsort ((Nat.primeFactorsList_sorted (e*d)).reverse.pairwise)).symm

end
end ImbalancedChen.P5Z.OriginalOrdinaryConditionalPrefix
