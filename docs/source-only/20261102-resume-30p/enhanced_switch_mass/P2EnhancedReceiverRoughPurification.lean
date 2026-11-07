import ImbalancedChen.P2EnhancedSwitchedTrueNormalization
import MathlibNt.Wu2008DoubleSieve.Omega3FiniteError
import MathlibNt.Wu2008DoubleSieve.InclusiveRoughUniform

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Purification is performed while the receiver is still prime. O's larger
masked raw carrier cannot be treated as an ordinary rough-number source:
Sifted(d*N) permits prime factors of d*N. The two exact discarded events
below are old-prefix repetition and quotient noncoprimality with N.
The latter is bounded by receiver primes dividing N; the broader event
ell|N is NOT identified with the exact event. Both exact events exclude
quotient one. The estimates here are finite/per-tuple; their aggregate
enhanced marked-family payment is deliberately not asserted.
-/

namespace ImbalancedChen.P2EnhancedReceiverRoughPurification
noncomputable section
open Finset Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedPrefixMaskDefect
open P2EnhancedSwitchedUnsiftedSource
open P2EnhancedTwentyOneQuotientFinite
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedSwitchedTrueNormalization (trueAlpha)
open scoped Classical BigOperators

def roughReceiver (N d D : ℕ) (z : ℝ) : Finset ℕ :=
  (sieveCarrier N D (d*N) z).filter (fun ell => Rough z ((N-ell)/D))

def repeatReceiver (N d D : ℕ) (z : ℝ) : Finset ℕ :=
  (sieveCarrier N D (d*N) z).filter (fun ell => ¬d.Coprime ((N-ell)/D))

def centerReceiver (N d D : ℕ) (z : ℝ) : Finset ℕ :=
  (sieveCarrier N D (d*N) z).filter (fun ell => ¬((N-ell)/D).Coprime N)

/-- The precise two coprimality conditions remove the old mask. This
does not assert either condition for every member of O's raw carrier. -/
theorem masked_rough_of_coprime {N d m : ℕ} {z : ℝ}
    (hs : Sifted (d*N) m z) (hd : d.Coprime m) (hN : m.Coprime N) : Rough z m := by
  intro p hp hpm
  by_contra hsmall
  have hpd : p.Coprime d := hd.symm.of_dvd_left hpm
  have hpN : p.Coprime N := hN.of_dvd_left hpm
  exact hs p hp (Nat.coprime_mul_iff_right.mpr ⟨hpd,hpN⟩)
    (lt_of_not_ge hsmall) hpm

theorem receiver_card_le_three (N d D : ℕ) (z : ℝ) :
    (sieveCarrier N D (d*N) z).card≤
      (roughReceiver N d D z).card+(repeatReceiver N d D z).card+
        (centerReceiver N d D z).card := by
  have hcover : sieveCarrier N D (d*N) z⊆
      (roughReceiver N d D z∪repeatReceiver N d D z)∪centerReceiver N d D z := by
    intro ell hell
    by_cases hr : Rough z ((N-ell)/D)
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hell,hr⟩))
    · by_cases hd : d.Coprime ((N-ell)/D)
      · have hN : ¬((N-ell)/D).Coprime N := by
          intro hn
          exact hr (masked_rough_of_coprime (mem_filter.mp hell).2.2.2 hd hn)
        exact mem_union_right _ (mem_filter.mpr ⟨hell,hN⟩)
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hell,hd⟩))
  exact (card_le_card hcover).trans
    (card_union_le.trans (Nat.add_le_add_right card_union_le _))

/-- Prime receiver complement is positive for the original even N. -/
theorem receiver_lt {N d D ell : ℕ} {z : ℝ}
    (hN : 4≤N) (he : Even N) (hell : ell∈sieveCarrier N D (d*N) z) : ell<N := by
  obtain ⟨hrange,hprime,_,_⟩ := mem_filter.mp hell
  exact omega3_prime_output_lt hN he hprime (Nat.lt_succ_iff.mp (mem_range.mp hrange))

/-- The purified physical receiver maps to the ACTUAL inclusive ordinary
roughNumbers carrier, preserving the unit and the strict cutoff convention. -/
theorem roughReceiver_card_le {N d D : ℕ} {z : ℝ}
    (hN : 4≤N) (he : Even N) (hD : 0<D) :
    (roughReceiver N d D z).card≤(roughNumbers ((N:ℝ)/D) z).card := by
  apply card_le_card_of_injOn (fun ell => (N-ell)/D)
  · intro ell hell
    obtain ⟨hell,hr⟩ := mem_filter.mp hell
    have hlt := receiver_lt hN he hell
    have hdiv := (mem_filter.mp hell).2.2.1
    have hm := Nat.mul_div_cancel' hdiv
    have hp : 0<(N-ell)/D := by
      by_contra hn
      have hz : (N-ell)/D=0 := by omega
      rw [hz,mul_zero] at hm
      omega
    apply mem_roughNumbers.mpr
    refine ⟨hp,?_,hr⟩
    apply (le_div_iff₀ (Nat.cast_pos.mpr hD)).mpr
    have hcap : D*((N-ell)/D)≤N := hm.trans_le (Nat.sub_le N ell)
    exact_mod_cast (by simpa only [mul_comm] using hcap)
  · intro ell hell ell' hell' heq
    have h := congrArg (fun m => D*m) heq
    rw [Nat.mul_div_cancel' (mem_filter.mp (mem_filter.mp hell).1).2.2.1,
      Nat.mul_div_cancel' (mem_filter.mp (mem_filter.mp hell').1).2.2.1] at h
    have hlt := receiver_lt hN he (mem_filter.mp hell).1
    have hlt' := receiver_lt hN he (mem_filter.mp hell').1
    omega

/-- Every exact bad-N quotient forces its prime receiver to divide N.
The converse is neither used nor claimed. -/
theorem center_subset_primeFactors {N d D : ℕ} {z : ℝ} (hN : 0<N) :
    centerReceiver N d D z⊆N.primeFactors := by
  intro ell hell
  obtain ⟨hell,hbad⟩ := mem_filter.mp hell
  obtain ⟨hrange,hprime,hdiv,_⟩ := mem_filter.mp hell
  have hle : ell≤N := Nat.lt_succ_iff.mp (mem_range.mp hrange)
  obtain ⟨p,hp,hpm,hpN⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
  have hpcomp : p∣N-ell := by
    have hm := dvd_mul_of_dvd_right hpm D
    simpa only [Nat.mul_div_cancel' hdiv] using hm
  have hpel : p∣ell := by
    simpa only [Nat.sub_sub_self hle] using Nat.dvd_sub hpN hpcomp
  have heq : p=ell := (Nat.prime_dvd_prime_iff_eq hp hprime).mp hpel
  exact Nat.mem_primeFactors.mpr ⟨hprime,heq ▸ hpN,hN.ne'⟩

theorem center_card_le {N d D : ℕ} {z : ℝ} (hN : 0<N) :
    (centerReceiver N d D z).card≤N.primeFactors.card :=
  card_le_card (center_subset_primeFactors hN)

/-- Old-prefix repetition is charged at the COMPLETE labelled divisor.
The finite floor bound is the existing actual repeated-complement bound. -/
theorem repeat_card_le_floor {N d D : ℕ} {z : ℝ}
    (hN : 4≤N) (he : Even N) (hD : 0<D) (hdD : d∣D) :
    (repeatReceiver N d D z).card≤∑p∈D.primeFactors,N/(D*p) := by
  have hcard : (repeatReceiver N d D z).card≤(omega3BadComplements N D).card := by
    apply card_le_card_of_injOn (fun ell => N-ell)
    · intro ell hell
      obtain ⟨hell,hbad⟩ := mem_filter.mp hell
      have hlt := receiver_lt hN he hell
      have hdiv := (mem_filter.mp hell).2.2.1
      obtain ⟨p,hp,hpd,hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
      apply mem_filter.mpr
      refine ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le N ell)),
        (Nat.sub_pos_of_lt hlt).ne',p,
        Nat.mem_primeFactors.mpr ⟨hp,hpd.trans hdD,hD.ne'⟩,?_⟩
      have hm := Nat.mul_dvd_mul_left D hpm
      simpa only [Nat.mul_div_cancel' hdiv] using hm
    · intro ell hell ell' hell' heq
      have hlt := receiver_lt hN he (mem_filter.mp hell).1
      have hlt' := receiver_lt hN he (mem_filter.mp hell').1
      omega
  exact hcard.trans (omega3_bad_complements_card_le N D)

/-- Neither exact correction removes quotient one, at any Q or cutoff. -/
theorem unit_exceptions_empty (N d D : ℕ) (z : ℝ) :
    ((repeatReceiver N d D z).filter (fun ell => (N-ell)/D=1))=∅ ∧
    ((centerReceiver N d D z).filter (fun ell => (N-ell)/D=1))=∅ := by
  constructor
  · apply eq_empty_iff_forall_notMem.mpr
    intro ell hell
    obtain ⟨hell,hu⟩ := mem_filter.mp hell
    have hbad := (mem_filter.mp hell).2
    simpa only [hu,Nat.coprime_one_right,not_true_eq_false] using hbad
  · apply eq_empty_iff_forall_notMem.mpr
    intro ell hell
    obtain ⟨hell,hu⟩ := mem_filter.mp hell
    have hbad := (mem_filter.mp hell).2
    simpa only [hu,Nat.coprime_one_left,not_true_eq_false] using hbad

/-- A new ordinary-rough comparison, retaining BOTH exact exception
carriers. O's larger masked unsifted mass is never identified with it. -/
theorem receiver_le_rough_add_exact_errors {N d D : ℕ} {z : ℝ}
    (hN : 4≤N) (he : Even N) (hD : 0<D) :
    (sieveCarrier N D (d*N) z).card≤(roughNumbers ((N:ℝ)/D) z).card+
      (repeatReceiver N d D z).card+(centerReceiver N d D z).card :=
  (receiver_card_le_three N d D z).trans
    (Nat.add_le_add_right (Nat.add_le_add_right (roughReceiver_card_le hN he hD) _) _)

/-- The actual inclusive Buchstab supplier is uniform BEFORE the marked
divisor and real cutoff. Unit mass is a separate, unmultiplied atom. -/
theorem receiver_buchstab_upper {eta tau : ℝ} (heta : 0<eta) (htau : 0<tau) :
    ∃T : ℕ,4≤T ∧ ∀N : ℕ,T≤N → Even N → ∀d D : ℕ,0<D → ∀z : ℝ,
      (N:ℝ)^eta≤z →
      ((sieveCarrier N D (d*N) z).card:ℝ)≤
        (if D≤N then 1 else 0)+
        (if z≤(N:ℝ)/D then
          (buchstab (Real.log ((N:ℝ)/D)/Real.log z)+tau)*((N:ℝ)/D)/Real.log z else 0)+
        ((repeatReceiver N d D z).card:ℝ)+((centerReceiver N d D z).card:ℝ) := by
  obtain ⟨T,hT,hbound⟩ := InclusiveRoughUniform.uniform_upper heta htau
  refine ⟨T,hT,?_⟩
  intro N hNT he d D hD z hz
  have hN4 := hT.trans hNT
  have hp := hbound N hNT ((N:ℝ)/D) z
    (div_le_self (Nat.cast_nonneg N) (by exact_mod_cast hD)) hz
  have hgate : 1≤(N:ℝ)/D ↔ D≤N := by
    rw [one_le_div (Nat.cast_pos.mpr hD)]
    exact_mod_cast Iff.rfl
  rw [hgate] at hp
  have hfinite : ((sieveCarrier N D (d*N) z).card:ℝ)≤
      ((roughNumbers ((N:ℝ)/D) z).card:ℝ)+
      ((repeatReceiver N d D z).card:ℝ)+((centerReceiver N d D z).card:ℝ) := by
    exact_mod_cast receiver_le_rough_add_exact_errors hN4 he hD
  linarith

/-- The Buchstab argument at the full labelled product has genuine
alpha, including arbitrary real Gamma5 cutoff z. No alpha=2 reset. -/
theorem physical_buchstab_argument {N d : ℕ} {Q z : ℝ} {l : List ℕ}
    (hN : 0<N) (hd : 0<d) (hl : 0<l.prod) (hR : 1<Q/d) (hz : 1<z) :
    Real.log ((N:ℝ)/(d*l.prod:ℕ))/Real.log z=
      (trueAlpha N Q d-Real.log (l.prod:ℝ)/Real.log (Q/d))/
        (Real.log z/Real.log (Q/d)) := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hdr : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hlr : (0:ℝ)<l.prod := Nat.cast_pos.mpr hl
  have hscale : (N:ℝ)/(d*l.prod:ℕ)=((N:ℝ)/d)/(l.prod:ℝ) := by
    push_cast
    ring
  rw [hscale,Real.log_div (div_pos hNr hdr).ne' hlr.ne']
  unfold trueAlpha
  field_simp [(Real.log_pos hR).ne',(Real.log_pos hz).ne']
  ring

def ordinaryWordMass (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) : ℝ :=
  ∑l∈labels N Q d cs,
    ((roughNumbers ((N:ℝ)/(d*l.prod:ℕ)) (l.getD (l.length-2) 0)).card:ℝ)

def repeatWordMass (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) : ℝ :=
  ∑l∈labels N Q d cs,
    ((repeatReceiver N d (d*l.prod) (l.getD (l.length-2) 0)).card:ℝ)

def centerWordMass (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) : ℝ :=
  ∑l∈labels N Q d cs,
    ((centerReceiver N d (d*l.prod) (l.getD (l.length-2) 0)).card:ℝ)

/-- Actual original word sum. This applies to every retained occurrence
of Gamma9--21, so duplicated words are not collapsed by products. -/
theorem quotient_word_upper {N d : ℕ} (hN : 4≤N) (he : Even N) (hd : 0<d)
    (Q : ℝ) (cs : List ℕ) :
    quotientPrefixTerm N d N (cutoff Q d (227/50)) (cutoff Q d (353/100))
      (cutoff Q d (29/10)) (cutoff Q d (61/25)) (cutoff Q d (11/5)) cs≤
      ordinaryWordMass N Q d cs+repeatWordMass N Q d cs+centerWordMass N Q d cs := by
  have hsum : quotientPrefixTerm N d N
      (cutoff Q d (227/50)) (cutoff Q d (353/100)) (cutoff Q d (29/10))
      (cutoff Q d (61/25)) (cutoff Q d (11/5)) cs=
      ∑l∈labels N Q d cs,((quotientCarrier N d l).card:ℝ) := by
    simp only [quotientPrefixTerm,labels,sum_filter]
  rw [hsum]
  unfold ordinaryWordMass repeatWordMass centerWordMass
  rw [← sum_add_distrib,← sum_add_distrib]
  apply sum_le_sum
  intro l hl
  have ht := (secondFunctionalMother_tuple_mem _ _ _).mp (mem_filter.mp hl).1
  have hprod : 0<d*l.prod := mul_pos hd
    (List.prod_pos (fun p hp => (mem_primeWindow.mp (ht.2.2 p hp)).1.pos))
  exact_mod_cast receiver_le_rough_add_exact_errors hN he hprod

/-- The old selected-prime collision is an additional, already exposed
source-convention cost; purification does not erase or rename it. -/
theorem original_word_upper {N d : ℕ} (hN : 4≤N) (he : Even N) (hd : 0<d)
    (Q : ℝ) (cs : List ℕ) :
    secondFunctionalMotherPrefixTerm N d N
      (cutoff Q d (227/50)) (cutoff Q d (353/100)) (cutoff Q d (29/10))
      (cutoff Q d (61/25)) (cutoff Q d (11/5)) cs≤
      ordinaryWordMass N Q d cs+repeatWordMass N Q d cs+centerWordMass N Q d cs+
      collisionPrefixTerm N d N (cutoff Q d (227/50)) (cutoff Q d (353/100))
        (cutoff Q d (29/10)) (cutoff Q d (61/25)) (cutoff Q d (11/5)) cs :=
  (prefixTerm_le_quotient_add_collision N d N _ _ _ _ _ cs).trans
    (add_le_add_right (quotient_word_upper hN he hd Q cs) _)

/-- For bad Gamma5 the source mask is on the full complement. Descending
to its quotient is valid before purification and uses the SAME real z. -/
theorem sourceReceiver_subset (N d D : ℕ) (z : ℝ) :
    sourceSieveCarrier N D (d*N) z⊆sieveCarrier N D (d*N) z := by
  intro ell hell
  obtain ⟨hrange,hprime,hdiv,hs⟩ := mem_filter.mp hell
  apply mem_filter.mpr
  refine ⟨hrange,hprime,hdiv,?_⟩
  intro p hp hcop hcut hpd
  apply hs p hp hcop hcut
  have hh := dvd_mul_of_dvd_right hpd D
  simpa only [Nat.mul_div_cancel' hdiv] using hh

def badPairPurifiedUpper (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  ∑l∈(pairLabels N Q d).filter (badPair Q d),
    ((roughNumbers ((N:ℝ)/(d*l.prod:ℕ)) (cutoff Q d (227/50))).card:ℝ)+
    ((repeatReceiver N d (d*l.prod) (cutoff Q d (227/50))).card:ℝ)+
    ((centerReceiver N d (d*l.prod) (cutoff Q d (227/50))).card:ℝ)

/-- The excluded D5 portion retains its original strict ordered labels,
bad-square gate (including equality) and inherited a0 cutoff. -/
theorem original_badPair_upper {N d : ℕ}
    (hN : 4≤N) (he : Even N) (hd : 0<d) (Q : ℝ) :
    originalBadPairCount N Q d≤badPairPurifiedUpper N Q d := by
  apply sum_le_sum
  intro l hl
  have ht := (secondFunctionalMother_tuple_mem _ _ _).mp (mem_filter.mp hl).1
  have hprod : 0<d*l.prod := mul_pos hd
    (List.prod_pos (fun p hp => (mem_primeWindow.mp (ht.2.2 p hp)).1.pos))
  have hsub := card_le_card (sourceReceiver_subset N d (d*l.prod) (cutoff Q d (227/50)))
  have hr := receiver_le_rough_add_exact_errors (d:=d) (z:=cutoff Q d (227/50)) hN he hprod
  exact_mod_cast hsub.trans hr

end
end ImbalancedChen.P2EnhancedReceiverRoughPurification
