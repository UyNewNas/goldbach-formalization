import ImbalancedChen.Part5OriginalH430GoodPairSourcesAtAP
import ImbalancedChen.P2EnhancedSwitchedUnsiftedSource

/-! Exact arithmetic bad-pair receiver at the original seed. The second
prime is below the square wall in all four windows. The other physical
wall can reject only Γ5. Its equality stays in the original finite count. -/
namespace ImbalancedChen.Part5OriginalH430SeedRejectedPairCounts
noncomputable section
open Finset Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P5OriginalActionMassBound (originalW2At)
open P2W2PhysicalChildFeedback (PairGate source_pair_eq_frozen)
open P2OriginalW2CountTupleReindex (sourceRejectedOccurrence)
open P2OriginalW2MotherOccurrenceReindex (rejectedPairCount)
open P2FrozenReceiverCountActions (frozenCount)
open P2EnhancedSwitchedUnsiftedSource (originalBadPairCount badPair pairLabels)
open P2SeedOmegaLiteralFibre (a1 a2 a3)
open scoped Classical BigOperators

private theorem caps (Q : ℝ) (d : ℕ) :
    cutoff Q d (353/100)=(Q/d)^a1 ∧ cutoff Q d (29/10)=(Q/d)^a2 ∧
      cutoff Q d (61/25)=(Q/d)^a3 := by
  norm_num [cutoff,a1,a2,a3]

private theorem q_square {Q : ℝ} {d q : ℕ} (hd : 0<d) (hR : 1<Q/(d:ℝ))
    (hq : 0<q) (hc : (q:ℝ)<(Q/d)^a3) : (d:ℝ)*(q:ℝ)^2<Q := by
  let R := Q/(d:ℝ)
  have hR0 : 0<R := zero_lt_one.trans hR
  have hq0 : (0:ℝ)<q := Nat.cast_pos.mpr hq
  have hv : (q:ℝ)^2<R := calc
    _ = (q:ℝ)*q := sq _
    _ < (R^a3)*(R^a3) := mul_lt_mul hc hc.le hq0 (Real.rpow_pos_of_pos hR0 _).le
    _ = R^(a3+a3) := (Real.rpow_add hR0 _ _).symm
    _ ≤ R^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hR.le (by norm_num [a3])
    _ = R := Real.rpow_one _
  simpa only [mul_comm (d:ℝ)] using (lt_div_iff₀ (Nat.cast_pos.mpr hd : (0:ℝ)<d)).mp hv

private theorem other_gate {Q : ℝ} {d p q : ℕ} (hd : 0<d) (hR : 1<Q/(d:ℝ))
    (hp : 0<p) (hq : 0<q) (hc : (p:ℝ)<(Q/d)^a1) (hv : (q:ℝ)<(Q/d)^a3) :
    PairGate Q d p q := by
  refine ⟨q_square hd hR hq hv,?_⟩
  let R := Q/(d:ℝ)
  have hR0 : 0<R := zero_lt_one.trans hR
  have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr hp
  have hq0 : (0:ℝ)<q := Nat.cast_pos.mpr hq
  have hpp : (p:ℝ)*(p:ℝ)<R^a1*R^a1 :=
    mul_lt_mul hc hc.le hp0 (Real.rpow_pos_of_pos hR0 _).le
  have hh : (p:ℝ)^2*(q:ℝ)<R := calc
    _ = ((p:ℝ)*p)*q := by rw [sq]
    _ < (R^a1*R^a1)*R^a3 := mul_lt_mul hpp hv.le hq0 (by positivity)
    _ = R^((a1+a1)+a3) := by rw [Real.rpow_add hR0,Real.rpow_add hR0]
    _ ≤ R^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hR.le (by norm_num [a1,a3])
    _ = R := Real.rpow_one _
  have hh' := (lt_div_iff₀ (Nat.cast_pos.mpr hd : (0:ℝ)<d)).mp hh
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hh'

private theorem rejected_zero {N d : ℕ} {Q : ℝ} (hR : 1<Q/(d:ℝ)) (hd : 0<d)
    (l l' u : ℝ) (z : ℕ → ℕ → ℝ) (hu : u≤(Q/d)^a3) :
    rejectedPairCount N Q d (primeWindow N l (cutoff Q d (353/100))) (primeWindow N l' u) z=0 := by
  apply sum_eq_zero
  intro p hpm
  apply sum_eq_zero
  intro q hqm
  have hp := mem_primeWindow.mp hpm
  have hq := mem_primeWindow.mp hqm
  have hh := other_gate hd hR hp.1.pos hq.1.pos ((caps Q d).1 ▸ hp.2.2.2)
    (hq.2.2.2.trans_le hu)
  exact if_neg (fun h => h.2 hh)

theorem only_fifth_rejected {N d : ℕ} {Q : ℝ} (hd : 0<d) (hR : 1<Q/(d:ℝ)) :
    sourceRejectedOccurrence N Q d (originalW2At 0) 1=0 ∧
      sourceRejectedOccurrence N Q d (originalW2At 0) 2=0 ∧
      sourceRejectedOccurrence N Q d (originalW2At 0) 3=0 := by
  have hh1 : cutoff Q d (353/100)≤(Q/d)^a3 := (caps Q d).1.le.trans
    (Real.rpow_le_rpow_of_exponent_le hR.le (by norm_num [a1,a3]))
  have hh2 : cutoff Q d (29/10)≤(Q/d)^a3 := (caps Q d).2.1.le.trans
    (Real.rpow_le_rpow_of_exponent_le hR.le (by norm_num [a2,a3]))
  exact ⟨rejected_zero hR hd _ _ _ _ (caps Q d).2.2.le,
    rejected_zero hR hd _ _ _ _ hh1,rejected_zero hR hd _ _ _ _ hh2⟩

theorem rejected_fifth_eq_original {N d : ℕ} {Q : ℝ} (hd : 0<d) (hR : 1<Q/(d:ℝ)) :
    sourceRejectedOccurrence N Q d (originalW2At 0) 0=originalBadPairCount N Q d := by
  let A := cutoff Q d (227/50)
  let C := cutoff Q d (29/10)
  let P := primeWindow N A C
  change rejectedPairCount N Q d P P (fun _ _ => A)=_
  unfold originalBadPairCount pairLabels
  rw [sum_filter,MotherPair.tuple_pairs,sum_image (by
    intro x _ y _ h
    have hh : x.1=y.1 ∧ x.2=y.2 := by simpa using h
    exact Prod.ext hh.1 hh.2)]
  simp only [sum_filter,sum_product]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q hq
  have hp' := mem_primeWindow.mp hp
  have hq' := mem_primeWindow.mp hq
  have hc : C≤(Q/d)^a3 := (caps Q d).2.1.le.trans
    (Real.rpow_le_rpow_of_exponent_le hR.le (by norm_num [a2,a3]))
  have hs := q_square hd hR hq'.1.pos (hq'.2.2.2.trans_le hc)
  have hg : (¬ PairGate Q d p q) ↔ Q≤(d:ℝ)*(p:ℝ)^2*(q:ℝ) := by
    simp only [PairGate,hs,true_and,not_lt]
  have hcount := source_pair_eq_frozen N d hp'.1 hq'.1 hp'.2.2.1 hq'.2.2.1
  simp only [sourceSieveCount,Int.cast_natCast] at hcount
  by_cases hlt : p<q
  · by_cases hbad : Q≤(d:ℝ)*(p:ℝ)^2*(q:ℝ)
    · simp [hlt,hg.mpr hbad,badPair,hbad,A,List.prod_cons,Nat.mul_assoc] at ⊢
      simpa only [Nat.mul_assoc] using hcount.symm
    · have hok := not_not.mp (fun h => hbad (hg.mp h))
      simp [hlt,hok,badPair,hbad]
  · simp [hlt]

theorem four_rejected_eq_original {N d : ℕ} {Q : ℝ} (hd : 0<d) (hR : 1<Q/(d:ℝ)) :
    (∑ k : Fin 4,sourceRejectedOccurrence N Q d (originalW2At 0) k)=originalBadPairCount N Q d := by
  obtain ⟨h6,h7,h8⟩ := only_fifth_rejected (N:=N) hd hR
  rw [Fin.sum_univ_four,h6,h7,h8,rejected_fifth_eq_original hd hR]
  ring

end
end ImbalancedChen.Part5OriginalH430SeedRejectedPairCounts
