import ImbalancedChen.P2EnhancedTwentyOneSameQWeighted
import ImbalancedChen.P2SeedOmegaQuotientUnitCarrierExact

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual labelled unsifted sources at arbitrary physical Q. The remaining
integer is positive and rough for the OLD d*N mask. No output-prime test
is present. Original colour words are lists, so repeated occurrences are
never collapsed. Unit and nonunit sources are partitioned before any
asymptotic argument. This file proves no Buchstab mass limit or PP licence.
-/

namespace ImbalancedChen.P2EnhancedSwitchedUnsiftedSource
noncomputable section
open Finset Wu2008DoubleSieve
open P2EnhancedPrefixMaskDefect P2EnhancedTwentyOneQuotientFinite
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open scoped Classical BigOperators

/-- The integer quotient before testing the receiver N-d*prod(l)*m for
primality. Target deletion on specified primes is in `labels` below. -/
def roughCarrier (N d : ℕ) (l : List ℕ) (z : ℝ) : Finset ℕ :=
  (range (N+1)).filter fun m =>
    0<m ∧ d*l.prod*m≤N ∧ Sifted (d*N) m z

def unitCarrier (N d : ℕ) (l : List ℕ) (z : ℝ) : Finset ℕ :=
  (roughCarrier N d l z).filter (fun m => m=1)

def nonunitCarrier (N d : ℕ) (l : List ℕ) (z : ℝ) : Finset ℕ :=
  (roughCarrier N d l z).filter (fun m => m≠1)

theorem rough_partition (N d : ℕ) (l : List ℕ) (z : ℝ) :
    (unitCarrier N d l z).card+(nonunitCarrier N d l z).card=
      (roughCarrier N d l z).card := card_filter_add_card_filter_not _

theorem one_sifted (M : ℕ) (z : ℝ) : Sifted M 1 z := by
  intro p hp _ _ hpd
  exact hp.not_dvd_one hpd

/-- Quotient one contributes a full atom whenever its labelled prime
product fits. It is not a null subset of the nonunit rough count. -/
theorem unitCarrier_exact {N d : ℕ} {l : List ℕ} (hp : 0<d*l.prod) (z : ℝ) :
    unitCarrier N d l z=if d*l.prod≤N then {1} else ∅ := by
  ext m
  by_cases hcap : d*l.prod≤N
  · rw [if_pos hcap]
    simp only [unitCarrier,roughCarrier,mem_filter,mem_range,mem_singleton]
    constructor
    · exact fun h => h.2
    · intro hm
      subst m
      exact ⟨⟨by omega,by norm_num,by simpa using hcap,one_sifted _ _⟩,rfl⟩
  · rw [if_neg hcap]
    simp only [unitCarrier,roughCarrier,mem_filter,mem_range,not_mem_empty,iff_false]
    rintro ⟨⟨_,_,h,_⟩,rfl⟩
    exact hcap (by simpa using h)

theorem unit_card {N d : ℕ} {l : List ℕ} (hp : 0<d*l.prod) (z : ℝ) :
    (unitCarrier N d l z).card=if d*l.prod≤N then 1 else 0 := by
  rw [unitCarrier_exact hp]
  split_ifs <;> simp

/-- The zero complement is retained separately. Removing it requires
the usual even-N prime argument; no silent positive-quotient assumption. -/
def positiveQuotient (N d : ℕ) (l : List ℕ) : Finset ℕ :=
  (quotientCarrier N d l).filter (fun ell => ell<N)

theorem positiveQuotient_card_le_rough (N d : ℕ) (l : List ℕ) :
    (positiveQuotient N d l).card≤
      (roughCarrier N d l (l.getD (l.length-2) 0)).card := by
  apply card_le_card_of_injOn (fun ell => (N-ell)/(d*l.prod))
  · intro ell hell
    obtain ⟨hell,hlt⟩ := mem_filter.mp hell
    change ell ∈ (range (N+1)).filter (fun ell => ell.Prime ∧
      d*l.prod ∣ N-ell ∧ Sifted (d*N) ((N-ell)/(d*l.prod))
        (l.getD (l.length-2) 0)) at hell
    obtain ⟨_,_,hdiv,hs⟩ := mem_filter.mp hell
    have he := Nat.mul_div_cancel' hdiv
    have hpos : 0<(N-ell)/(d*l.prod) := by
      by_contra hn
      have hz : (N-ell)/(d*l.prod)=0 := by omega
      rw [hz,mul_zero] at he
      omega
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_,hpos,?_,hs⟩
    · have h := (Nat.div_le_self (N-ell) (d*l.prod)).trans (Nat.sub_le N ell)
      omega
    · rw [he]
      exact Nat.sub_le N ell
  · intro ell hell ell' hell' heq
    obtain ⟨hell,hlt⟩ := mem_filter.mp hell
    obtain ⟨hell',hlt'⟩ := mem_filter.mp hell'
    have hd := (mem_filter.mp hell).2.2.1
    have hd' := (mem_filter.mp hell').2.2.1
    have h := congrArg (fun m => d*l.prod*m) heq
    rw [Nat.mul_div_cancel' hd,Nat.mul_div_cancel' hd'] at h
    omega

theorem quotient_zero_partition (N d : ℕ) (l : List ℕ) :
    (positiveQuotient N d l).card+
      ((quotientCarrier N d l).filter (fun ell => ¬ell<N)).card=
      (quotientCarrier N d l).card := card_filter_add_card_filter_not _

theorem positiveQuotient_eq {N : ℕ} (hN : 4≤N) (heven : Even N)
    (d : ℕ) (l : List ℕ) : positiveQuotient N d l=quotientCarrier N d l := by
  apply filter_eq_self.mpr
  intro ell hell
  have hm := mem_filter.mp hell
  have hle : ell≤N := Nat.le_of_lt_succ (mem_range.mp hm.1)
  have hprime : ell.Prime := hm.2.1
  by_contra hn
  have he : ell=N := by omega
  rw [he] at hprime
  have htwo := hprime.even_iff.mp heven
  omega

theorem quotient_card_le_rough {N : ℕ} (hN : 4≤N) (heven : Even N)
    (d : ℕ) (l : List ℕ) :
    (quotientCarrier N d l).card≤
      (roughCarrier N d l (l.getD (l.length-2) 0)).card := by
  rw [← positiveQuotient_eq hN heven]
  exact positiveQuotient_card_le_rough N d l

/-- Exact original half-open prime windows, old target deletion N,
strict ordering, and original colour word at the actual common Q. -/
def labels (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) : Finset (List ℕ) :=
  (secondFunctionalMotherTuples
    (primeWindow N (cutoff Q d (227/50)) (cutoff Q d (11/5))) cs.length).filter
      (fun l => l.map (secondFunctionalMotherColour (cutoff Q d (353/100))
        (cutoff Q d (29/10)) (cutoff Q d (61/25)))=cs)

def wordMass (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) : ℝ :=
  ∑ l∈labels N Q d cs, (roughCarrier N d l (l.getD (l.length-2) 0)).card

def unitWordMass (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) : ℝ :=
  ∑ l∈labels N Q d cs, (unitCarrier N d l (l.getD (l.length-2) 0)).card

def nonunitWordMass (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) : ℝ :=
  ∑ l∈labels N Q d cs, (nonunitCarrier N d l (l.getD (l.length-2) 0)).card

private theorem prod_pos_of_prime (l : List ℕ) (hp : ∀p∈l,p.Prime) : 0<l.prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    exact mul_pos (hp p (by simp)).pos (ih (fun q hq => hp q (by simp [hq])))

/-- The unit arithmetic source is exactly the prime-product simplex
count. Its distinct dimensions five and six have not been conflated. -/
theorem unitWordMass_eq_product_count {N d : ℕ} (hd : 0<d) (Q : ℝ) (cs : List ℕ) :
    unitWordMass N Q d cs=
      (((labels N Q d cs).filter (fun l => d*l.prod≤N)).card : ℝ) := by
  unfold unitWordMass
  calc
    _ = ∑ l∈labels N Q d cs, if d*l.prod≤N then (1:ℝ) else 0 := by
      apply sum_congr rfl
      intro l hl
      have htuple := (secondFunctionalMother_tuple_mem _ _ _).mp (mem_filter.mp hl).1
      have hp : 0<d*l.prod := mul_pos hd (prod_pos_of_prime l
        (fun p hp => (mem_primeWindow.mp (htuple.2.2 p hp)).1))
      rw [unit_card hp]
      split_ifs <;> norm_num
    _ = _ := by simp

/-- Actual enhanced quotient counts embed into these unsifted sources.
This comparison uses no classical source box or asymptotic input. -/
theorem quotientPrefixTerm_le_wordMass {N : ℕ} (hN : 4≤N) (heven : Even N)
    (Q : ℝ) (d : ℕ) (cs : List ℕ) :
    quotientPrefixTerm N d N (cutoff Q d (227/50)) (cutoff Q d (353/100))
      (cutoff Q d (29/10)) (cutoff Q d (61/25)) (cutoff Q d (11/5)) cs≤
      wordMass N Q d cs := by
  unfold quotientPrefixTerm wordMass labels
  rw [sum_filter]
  apply sum_le_sum
  intro l _
  split_ifs
  · exact_mod_cast quotient_card_le_rough hN heven d l
  · exact le_rfl

theorem originalPrefixTerm_le_wordMass_add_collision {N : ℕ}
    (hN : 4≤N) (heven : Even N) (Q : ℝ) (d : ℕ) (cs : List ℕ) :
    secondFunctionalMotherPrefixTerm N d N
      (cutoff Q d (227/50)) (cutoff Q d (353/100)) (cutoff Q d (29/10))
      (cutoff Q d (61/25)) (cutoff Q d (11/5)) cs≤wordMass N Q d cs+
      collisionPrefixTerm N d N (cutoff Q d (227/50)) (cutoff Q d (353/100))
        (cutoff Q d (29/10)) (cutoff Q d (61/25)) (cutoff Q d (11/5)) cs :=
  (prefixTerm_le_quotient_add_collision N d N _ _ _ _ _ cs).trans
    (add_le_add_right (quotientPrefixTerm_le_wordMass hN heven Q d cs) _)

theorem wordMass_partition (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) :
    wordMass N Q d cs=unitWordMass N Q d cs+nonunitWordMass N Q d cs := by
  unfold wordMass unitWordMass nonunitWordMass
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro l _
  exact_mod_cast (rough_partition N d l _).symm

def gammaMass (N : ℕ) (Q : ℝ) (d i : ℕ) : ℝ :=
  ((secondFunctionalMotherGammaWords i).map (wordMass N Q d)).sum

def markedGammaMass (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (i : ℕ) : ℝ := ∑ d∈D,sigma d*gammaMass N Q d i

/-- This literal expansion exhibits all 20 occurrences. The repeated
112 and 122 words are each counted twice across the original Gamma terms. -/
theorem all_switched_multiplicities (F : List ℕ → ℝ) :
    (∑ j : Fin 13,((secondFunctionalMotherGammaWords (9+j.val)).map F).sum)=
      F [1,1,1]+2*F [1,1,2]+2*F [1,2,2]+F [2,2,2]+F [1,1,3]+
      F [0,0,3]+F [0,1,2]+F [0,1,3]+F [0,2,2]+F [0,2,3]+F [0,3,3]+
      F [1,2,3]+F [2,2,2,2]+F [2,2,2,3]+F [2,2,3,3]+F [1,3,3,3]+
      F [2,3,3,3,3]+F [3,3,3,3,3,3] := by
  norm_num [Fin.sum_univ_succ,secondFunctionalMotherGammaWords]
  ring

theorem gamma20_partition (N : ℕ) (Q : ℝ) (d : ℕ) :
    gammaMass N Q d 20=unitWordMass N Q d [2,3,3,3,3]+
      nonunitWordMass N Q d [2,3,3,3,3] := by
  simpa [gammaMass,secondFunctionalMotherGammaWords] using
    wordMass_partition N Q d [2,3,3,3,3]

theorem gamma21_partition (N : ℕ) (Q : ℝ) (d : ℕ) :
    gammaMass N Q d 21=unitWordMass N Q d [3,3,3,3,3,3]+
      nonunitWordMass N Q d [3,3,3,3,3,3] := by
  simpa [gammaMass,secondFunctionalMotherGammaWords] using
    wordMass_partition N Q d [3,3,3,3,3,3]

theorem marked_last_partition (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) :
    markedGammaMass N Q D sigma 20+markedGammaMass N Q D sigma 21=
      (∑ d∈D,sigma d*unitWordMass N Q d [2,3,3,3,3])+
      (∑ d∈D,sigma d*nonunitWordMass N Q d [2,3,3,3,3])+
      (∑ d∈D,sigma d*unitWordMass N Q d [3,3,3,3,3,3])+
      (∑ d∈D,sigma d*nonunitWordMass N Q d [3,3,3,3,3,3]) := by
  simp only [markedGammaMass,gamma20_partition,gamma21_partition,mul_add,sum_add_distrib]
  ring

/-- Gamma5 retains its two ordered low-band labels. The excluded square
gate is imposed physically and includes equality. -/
def pairLabels (N : ℕ) (Q : ℝ) (d : ℕ) : Finset (List ℕ) :=
  secondFunctionalMotherTuples
    (primeWindow N (cutoff Q d (227/50)) (cutoff Q d (29/10))) 2

def badPair (Q : ℝ) (d : ℕ) (l : List ℕ) : Prop :=
  Q≤(d:ℝ)*(l.getD 0 0:ℝ)^2*(l.getD 1 0:ℝ)

/-- The unsifted receiver map for any original (unscaled) source mask.
For bad Gamma5 the cutoff is the inherited a0, not the first prime. -/
theorem originalCarrier_card_le_rough {N : ℕ} (hN : 4≤N) (heven : Even N)
    (d : ℕ) (l : List ℕ) (z : ℝ) :
    (sourceSieveCarrier N (d*l.prod) (d*N) z).card≤(roughCarrier N d l z).card := by
  apply card_le_card_of_injOn (fun ell => (N-ell)/(d*l.prod))
  · intro ell hell
    obtain ⟨hrange,hprime,hdiv,hs⟩ := mem_filter.mp hell
    have hle : ell≤N := Nat.le_of_lt_succ (mem_range.mp hrange)
    have hlt : ell<N := by
      by_contra hn
      have he : ell=N := by omega
      rw [he] at hprime
      have htwo := hprime.even_iff.mp heven
      omega
    have he := Nat.mul_div_cancel' hdiv
    have hpos : 0<(N-ell)/(d*l.prod) := by
      by_contra hn
      have hz : (N-ell)/(d*l.prod)=0 := by omega
      rw [hz,mul_zero] at he
      omega
    apply mem_filter.mpr
    refine ⟨mem_range.mpr ?_,hpos,?_,?_⟩
    · have h := (Nat.div_le_self (N-ell) (d*l.prod)).trans (Nat.sub_le N ell)
      omega
    · rw [he]
      exact Nat.sub_le N ell
    · intro p hp hcop hcut hpd
      apply hs p hp hcop hcut
      have hh := dvd_mul_of_dvd_right hpd (d*l.prod)
      simpa only [he] using hh
  · intro ell hell ell' hell' heq
    obtain ⟨hrange,_,hdiv,_⟩ := mem_filter.mp hell
    obtain ⟨hrange',_,hdiv',_⟩ := mem_filter.mp hell'
    have hle : ell≤N := Nat.le_of_lt_succ (mem_range.mp hrange)
    have hle' : ell'≤N := Nat.le_of_lt_succ (mem_range.mp hrange')
    have h := congrArg (fun m => d*l.prod*m) heq
    rw [Nat.mul_div_cancel' hdiv,Nat.mul_div_cancel' hdiv'] at h
    omega

def pairMass (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  ∑ l∈pairLabels N Q d, (roughCarrier N d l (cutoff Q d (227/50))).card

def badPairMass (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  ∑ l∈(pairLabels N Q d).filter (badPair Q d),
    (roughCarrier N d l (cutoff Q d (227/50))).card

def goodPairMass (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  ∑ l∈(pairLabels N Q d).filter (fun l => ¬badPair Q d l),
    (roughCarrier N d l (cutoff Q d (227/50))).card

def originalBadPairCount (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  ∑ l∈(pairLabels N Q d).filter (badPair Q d),
    (sourceSieveCarrier N (d*l.prod) (d*N) (cutoff Q d (227/50))).card

theorem originalBadPairCount_le_unsifted {N : ℕ} (hN : 4≤N) (heven : Even N)
    (Q : ℝ) (d : ℕ) : originalBadPairCount N Q d≤badPairMass N Q d := by
  apply sum_le_sum
  intro l _
  exact_mod_cast originalCarrier_card_le_rough hN heven d l (cutoff Q d (227/50))

theorem pairMass_exact_split (N : ℕ) (Q : ℝ) (d : ℕ) :
    pairMass N Q d=badPairMass N Q d+goodPairMass N Q d := by
  unfold pairMass badPairMass goodPairMass
  rw [sum_filter,sum_filter,← sum_add_distrib]
  apply sum_congr rfl
  intro l _
  by_cases h : badPair Q d l <;> simp [h]

theorem badPairMass_nonneg (N : ℕ) (Q : ℝ) (d : ℕ) : 0≤badPairMass N Q d :=
  sum_nonneg (fun _ _ => Nat.cast_nonneg _)

end
end ImbalancedChen.P2EnhancedSwitchedUnsiftedSource
