import ImbalancedChen.Part5OriginalH430ClassicalSeedLargeRemainder

/-! Canonical prime-factor expansion on the retained integer, indexed inside
its original outer word and position. The repeated-prime and cutoff-equality
cases are present. The restored product and additive-prime test are exact. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalLargePrimeTuples
noncomputable section
open Finset Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedSwitchedUnsiftedSource (labels)
open P2EnhancedNonunitLabelGeometry (label_prod_pos)
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430SeedHistoryMass Part5OriginalH430HistoryQuotientCounts
open Part5OriginalH430TaggedArithmeticReceivers (original_band_prime original_band_geometry)
open Part5OriginalH430FrozenClassicalRootModuli
open Part5OriginalH430ClassicalCausalSeedScale
open Part5OriginalH430ClassicalSmallSwitchedIntegers
open scoped Classical BigOperators

def canonicalLargeWord (tested : Bool) (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) (X : ℝ) : ℝ :=
  ∑ qs∈labels N Q d cs,∑ rs∈(largeIntegers N (d*qs.prod) (qs.getD (qs.length-2) 0) X).image Nat.primeFactorsList,
    testWeight tested N (d*qs.prod) rs.prod

theorem prime_tuple_reindex (tested : Bool) (N : ℕ) (Q : ℝ) (d : ℕ) (cs : List ℕ) (X : ℝ) :
    largeWord tested N Q d cs X=canonicalLargeWord tested N Q d cs X := by
  apply sum_congr rfl
  intro qs _
  let S := largeIntegers N (d*qs.prod) (qs.getD (qs.length-2) 0) X
  have hpos (m : ℕ) (hm : m∈S) : 0<m := (mem_roughNumbers.mp (mem_filter.mp hm).1).1
  have hi : Set.InjOn Nat.primeFactorsList (S : Set ℕ) := by
    intro m hm m' hm' h
    simpa only [Nat.prod_primeFactorsList (hpos m hm).ne',Nat.prod_primeFactorsList (hpos m' hm').ne']
      using congrArg List.prod h
  rw [sum_image (fun a ha b hb hh => hi ha hb hh)]
  apply sum_congr rfl
  intro m hm
  rw [Nat.prod_primeFactorsList (hpos m hm).ne']

private theorem at_least_three (j : Fin 13) {cs : List ℕ}
    (hc : cs∈secondFunctionalMotherGammaWords (9+j.val)) : 3≤cs.length := by
  fin_cases j <;> norm_num [secondFunctionalMotherGammaWords] at hc <;> aesop

/-- The full original word may have equal tail primes. Every occurrence
has at least five prime groups and a fixed rank ceiling, uniformly in
the generation and the outer p. No distribution hypothesis is used. -/
theorem actual_large_prime_tuple {N n p dep m : ℕ} {τ κ : ℝ} (hN : 2≤N)
    (ht : 0≤τ) (ht' : τ≤1/12) (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈classicalBand N)
    (l : LevelIndex N n .U3 τ p dep) (j : Fin 13) {cs qs : List ℕ}
    (hc : cs∈secondFunctionalMotherGammaWords (9+j.val))
    (hqs : qs∈labels N (rootQ N n .U3 τ p) (wordProduct l) cs)
    (hk : κ≤1/112)
    (hm : m∈largeIntegers N (wordProduct l*qs.prod) (qs.getD (qs.length-2) 0) (smallProduct N κ)) :
    let old := (levelOccurrence l).current.old
    let rs := m.primeFactorsList; let A := (old++qs)++rs
    rs.Pairwise (·≤·) ∧ (∀ q∈rs,qs.getD (qs.length-2) 0≤q) ∧
    A.prod=wordProduct l*qs.prod*m ∧ (A.prod:ℝ)∈Set.Ioc (smallProduct N κ) (N:ℝ) ∧
    (∀ q∈A,q.Prime ∧ (N:ℝ)^frozenLeafCutoffFloor≤(q:ℝ)) ∧
    5≤A.length ∧ A.length≤⌊1/frozenLeafCutoffFloor⌋₊ := by
  let d := wordProduct l
  let old := (levelOccurrence l).current.old
  let rs := m.primeFactorsList
  let A := (old++qs)++rs
  let Q := rootQ N n .U3 τ p
  have hb := (mem_filter.mp hp).1
  have ho := (levelOccurrence_source l).1
  have hco := rootHistory_coherent (by omega : 1<N) ht ht' hn
    (original_band_prime hb) (original_band_geometry hN hb) ho
  have hrough := history_integer_roughness hN ht ht' hn hb ho
  have hd := (actual_cubic_residual hN ht ht' hn hp l).1
  have hD : (0:ℝ)<(d*qs.prod:ℕ) := Nat.cast_pos.mpr (Nat.mul_pos hd (label_prod_pos hqs))
  have hq := (secondFunctionalMother_tuple_mem _ _ _).mp (mem_filter.mp hqs).1
  have hq3 : 3≤qs.length := hq.1.symm ▸ at_least_three j hc
  obtain ⟨hmrough,hlarge⟩ := mem_filter.mp hm
  obtain ⟨hmpos,hmcap,hmcut⟩ := mem_roughNumbers.mp hmrough
  have h1 : m≠1 := by
    rintro rfl
    rw [Nat.mul_one] at hlarge
    exact (not_lt_of_ge (every_original_unit_low hN ht ht' hn hp l j hc hqs hk)) hlarge
  have hprod : A.prod=d*qs.prod*m := by
    simp only [A,old,rs,List.prod_append,Nat.prod_primeFactorsList hmpos.ne',wordProduct,
      P2EnhancedLowerPrimeChildCarriers.parentProduct,d,mul_assoc]
  have hphysical : (A.prod:ℝ)≤N := by
    rw [hprod,Nat.cast_mul]
    simpa only [mul_comm] using (le_div_iff₀ hD).mp hmcap
  have hold (q : ℕ) (hmq : q∈old) : q.Prime ∧ (N:ℝ)^frozenLeafCutoffFloor≤(q:ℝ) := by
    have hpr := (hco.letters q hmq).1
    exact ⟨hpr,hrough.2.2.1 q (Nat.mem_primeFactors.mpr ⟨hpr,List.dvd_prod hmq,hd.ne'⟩)⟩
  have hnew (q : ℕ) (hmq : q∈qs) : q.Prime ∧ (N:ℝ)^frozenLeafCutoffFloor≤(q:ℝ) := by
    have hw := mem_primeWindow.mp (hq.2.2 q hmq)
    exact ⟨hw.1,hrough.2.2.2.trans hw.2.2.1⟩
  have hpen : qs.getD (qs.length-2) 0∈qs := by
    rw [List.getD_eq_getElem _ _ (show qs.length-2<qs.length by omega)]
    exact List.getElem_mem _
  have htail (q : ℕ) (hmq : q∈rs) : q.Prime ∧ qs.getD (qs.length-2) 0≤q := by
    have hpr := Nat.prime_of_mem_primeFactorsList hmq
    refine ⟨hpr,?_⟩
    exact_mod_cast hmcut q hpr (Nat.dvd_of_mem_primeFactorsList hmq)
  have hA (q : ℕ) (hmq : q∈A) : q.Prime ∧ (N:ℝ)^frozenLeafCutoffFloor≤(q:ℝ) := by
    rcases List.mem_append.mp hmq with h | h
    · rcases List.mem_append.mp h with h | h
      · exact hold q h
      · exact hnew q h
    · exact ⟨(htail q h).1,(hnew _ hpen).2.trans (by exact_mod_cast (htail q h).2)⟩
  have hrold : 0<old.length := List.length_pos_iff.mpr (by
    intro he
    have h : p∈old := root_modulus_mem l
    rw [he] at h
    simpa using h)
  have hrs : 0<rs.length := List.length_pos_iff.mpr (by
    intro he
    have h : rs.prod=m := Nat.prod_primeFactorsList hmpos.ne'
    rw [he,List.prod_nil] at h
    exact h1 h.symm)
  have hlower : 5≤A.length := by simp only [A,List.length_append]; omega
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hN0 := zero_lt_one.trans hNr
  have hη := frozenLeafCutoffFloor_pos
  have hlenPow : (N:ℝ)^(frozenLeafCutoffFloor*(A.length:ℝ))≤(N:ℝ)^(1:ℝ) := by
    rw [rpow_mul hN0.le,rpow_natCast,rpow_one]
    apply le_trans ?_ hphysical
    have hh := List.prod_map_le_prod_map₀ (s:=A) (fun _ : ℕ => (N:ℝ)^frozenLeafCutoffFloor)
      (fun q : ℕ => (q:ℝ)) (fun _ _ => rpow_nonneg hN0.le _) (fun q h => (hA q h).2)
    simpa only [List.map_const',List.prod_replicate,Nat.cast_list_prod] using hh
  have hlen := (rpow_le_rpow_left_iff hNr).mp hlenPow
  refine ⟨(Nat.primeFactorsList_sorted m).pairwise,fun q h => (htail q h).2,hprod,
    ⟨by rw [hprod]; exact hlarge,hphysical⟩,hA,hlower,Nat.le_floor ?_⟩
  exact (le_div_iff₀ hη).mpr (by linarith only [hlen])

end
end ImbalancedChen.Part5OriginalH430ClassicalLargePrimeTuples
