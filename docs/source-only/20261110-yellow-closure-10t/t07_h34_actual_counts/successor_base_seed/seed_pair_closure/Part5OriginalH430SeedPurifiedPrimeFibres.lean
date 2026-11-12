import ImbalancedChen.Part5OriginalH430SeedThirteenPrimeWords
import ImbalancedChen.P2EnhancedExactExceptionTheta
import ImbalancedChen.P2EnhancedBadGamma5ArithmeticGeometry

/-! Positive-prime restriction and unsifted mass on literally the same
inclusive ordinary rough integers. The quotient map is a bijection
on the absolute-rough receivers. The two old exact exceptions stay on
the masked receiver until their marked same-Q payment. -/
namespace ImbalancedChen.Part5OriginalH430SeedPurifiedPrimeFibres
noncomputable section
open Finset Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedTwentyOneQuotientFinite (quotientPrefixTerm)
open P2TwentyOneUnsiftedArithmeticSource (quotientPrefixTerm_eq_primeMass)
open P2EnhancedSwitchedUnsiftedSource (labels pairLabels badPair originalBadPairCount)
open P2EnhancedBadGamma5ArithmeticGeometry (badLabels ordinaryBad pair_prod_pos)
open P2EnhancedReceiverRoughPurification
open P2EnhancedExactExceptionFinite (badPairRepeat badPairCenter)
open P2EnhancedExactExceptionTheta (localErrors)
open Part5OriginalH430SeedThirteenPrimeWords (primeWord longPrime restrictedPrime)
open scoped Classical BigOperators

/-- The Boolean selects the additive-prime test on the independent mass.
Its integer range, strict prime cutoff and possible last unit are common. -/
def fibre (tested : Bool) (N D : ℕ) (z : ℝ) : ℝ :=
  let M := roughNumbers ((N:ℝ)/D) z
  if tested then p5z_labelledPrimeMass M (fun m => D*m) (fun _ => 1) N
  else p5z_labelledMass M (fun _ => 1)

theorem raw_fibre (N D : ℕ) (z : ℝ) :
    fibre false N D z=((roughNumbers ((N:ℝ)/D) z).card:ℝ) := by
  simp [fibre,p5z_labelledMass]

theorem rough_receiver_eq_prime_fibre {N d D : ℕ} {z : ℝ} (hN : 4≤N) (he : Even N) (hD : 0<D) :
    ((roughReceiver N d D z).card:ℝ)=fibre true N D z := by
  let M := roughNumbers ((N:ℝ)/D) z
  let S := M.filter (fun m => D*m<N ∧ (N-D*m).Prime)
  have heq : (roughReceiver N d D z).card=S.card := by
    refine card_bij (fun ell _ => (N-ell)/D) ?_ ?_ ?_
    · intro ell hell
      obtain ⟨hcar,hr⟩ := mem_filter.mp hell
      have hlt := receiver_lt hN he hcar
      have hh := (mem_filter.mp hcar).2
      have hm := Nat.mul_div_cancel' hh.2.1
      have hp : 0<(N-ell)/D := by
        by_contra h
        have hz : (N-ell)/D=0 := by omega
        rw [hz,mul_zero] at hm
        omega
      have hmM : (N-ell)/D∈M := by
        apply mem_roughNumbers.mpr
        refine ⟨hp,(le_div_iff₀ (Nat.cast_pos.mpr hD)).mpr ?_,hr⟩
        exact_mod_cast (show (N-ell)/D*D≤N by rw [Nat.mul_comm,hm]; exact Nat.sub_le N ell)
      exact mem_filter.mpr ⟨hmM,by rw [hm]; exact Nat.sub_lt (by omega) hh.1.pos,
        by simpa only [hm,Nat.sub_sub_self hlt.le] using hh.1⟩
    · intro ell h ell' h' hh
      have h1 := (mem_filter.mp h).1
      have h2 := (mem_filter.mp h').1
      have hlt := receiver_lt hN he h1
      have hlt' := receiver_lt hN he h2
      have heq' := congrArg (fun m => D*m) hh
      rw [Nat.mul_div_cancel' (mem_filter.mp h1).2.2.1,Nat.mul_div_cancel' (mem_filter.mp h2).2.2.1] at heq'
      omega
    · intro m hm
      obtain ⟨hM,hcap,hpr⟩ := mem_filter.mp hm
      have hr := (mem_roughNumbers.mp hM).2.2
      have hsub : N-(N-D*m)=D*m := Nat.sub_sub_self hcap.le
      have hquot : (N-(N-D*m))/D=m := by rw [hsub]; exact Nat.mul_div_cancel_left _ hD
      refine ⟨N-D*m,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega),hpr,?_,?_⟩,?_⟩,hquot⟩
      · rw [hsub]
        exact dvd_mul_right _ _
      · rw [hquot]
        exact fun q hq _ hz hdvd => (hr q hq hdvd).not_gt hz
      · simpa only [hquot] using hr
  have hmass : (S.card:ℝ)=∑ m∈M,if D*m<N ∧ (N-D*m).Prime then (1:ℝ) else 0 := by
    calc
      _ = ∑ _m∈S,(1:ℝ) := by simp
      _ = _ := by dsimp only [S]; rw [sum_filter]
  rw [heq]
  exact hmass

theorem masked_to_tested {N d D : ℕ} {z : ℝ} (hN : 4≤N) (he : Even N) (hD : 0<D) :
    ((sieveCarrier N D (d*N) z).card:ℝ)≤fibre true N D z+
      ((repeatReceiver N d D z).card:ℝ)+((centerReceiver N d D z).card:ℝ) := by
  rw [←rough_receiver_eq_prime_fibre (d:=d) hN he hD]
  exact_mod_cast receiver_card_le_three N d D z

def wordFibre (tested : Bool) (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) : ℝ :=
  ∑ l∈labels N Q d cs,fibre tested N (d*l.prod) (l.getD (l.length-2) 0)

def badFibre (tested : Bool) (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  ∑ l∈badLabels N Q d,fibre tested N (d*l.prod) (cutoff Q d (227/50))

def switchedFibre (tested : Bool) (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  badFibre tested N Q d+
    ∑ j : Fin 13,((secondFunctionalMotherGammaWords (9+j.val)).map (wordFibre tested N Q d)).sum

theorem raw_word (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) :
    wordFibre false N Q d cs=ordinaryWordMass N Q d cs := by simp only [wordFibre,raw_fibre,ordinaryWordMass]

theorem raw_bad (N : ℕ) (Q : ℝ) (d : ℕ) :
    badFibre false N Q d=ordinaryBad N Q d := by simp only [badFibre,raw_fibre,ordinaryBad]

theorem prime_word_purified {N d : ℕ} (Q : ℝ) (hN : 4≤N) (he : Even N) (hd : 0<d) (cs : List ℕ) :
    primeWord N Q d cs≤wordFibre true N Q d cs+repeatWordMass N Q d cs+centerWordMass N Q d cs := by
  let A := cutoff Q d (227/50); let B := cutoff Q d (353/100); let C := cutoff Q d (29/10)
  let E := cutoff Q d (61/25); let Z := cutoff Q d (11/5)
  have h : quotientPrefixTerm N d N A B C E Z cs=primeWord N Q d cs := by
    simpa only [one_mul,primeWord] using (quotientPrefixTerm_eq_primeMass (N:=N) (d:=d) (M:=N)
      (a:=A) (b:=B) (c:=C) (e:=E) (f:=Z) (cs:=cs) hN he hd 1)
  have hsum : quotientPrefixTerm N d N A B C E Z cs=
      ∑ l∈labels N Q d cs,((P2EnhancedPrefixMaskDefect.quotientCarrier N d l).card:ℝ) := by
    simp only [quotientPrefixTerm,labels,sum_filter,A,B,C,E,Z]
  rw [←h,hsum,wordFibre,repeatWordMass,centerWordMass,←sum_add_distrib,←sum_add_distrib]
  apply sum_le_sum
  intro l hl
  have ht := (secondFunctionalMother_tuple_mem _ _ _).mp (mem_filter.mp hl).1
  have hD := Nat.mul_pos hd (List.prod_pos (fun q hq => (mem_primeWindow.mp (ht.2.2 q hq)).1.pos))
  exact masked_to_tested hN he hD

theorem prime_bad_purified {N d : ℕ} (Q : ℝ) (hN : 4≤N) (he : Even N) (hd : 0<d) :
    originalBadPairCount N Q d≤badFibre true N Q d+badPairRepeat N Q d+badPairCenter N Q d := by
  unfold originalBadPairCount badFibre badLabels badPairRepeat badPairCenter
  rw [←sum_add_distrib,←sum_add_distrib]
  apply sum_le_sum
  intro l hl
  have hs := card_le_card (sourceReceiver_subset N d (d*l.prod) (cutoff Q d (227/50)))
  have hD := Nat.mul_pos hd (pair_prod_pos (mem_filter.mp hl).1)
  exact (Nat.cast_le.mpr hs).trans (masked_to_tested hN he hD)

theorem restricted_prime_purified {N d : ℕ} (Q : ℝ) (hN : 4≤N) (he : Even N) (hd : 0<d) :
    restrictedPrime N Q d≤switchedFibre true N Q d+localErrors N Q d := by
  have hw (cs : List ℕ) := prime_word_purified Q hN he hd cs
  have hf := sum_le_sum (s:=univ) (fun j _ => secondFunctionalMother_list_sum_mono
    (secondFunctionalMotherGammaWords (9+(j : Fin 13).val)) (primeWord N Q d)
    (fun cs => wordFibre true N Q d cs+(repeatWordMass N Q d cs+centerWordMass N Q d cs))
    (fun cs _ => by linarith only [hw cs]))
  simp only [List.sum_map_add,sum_add_distrib] at hf
  unfold restrictedPrime longPrime switchedFibre localErrors
  simp only [List.sum_map_add,sum_add_distrib]
  linarith only [hf,prime_bad_purified Q hN he hd]

end
end ImbalancedChen.Part5OriginalH430SeedPurifiedPrimeFibres
