import ImbalancedChen.Part5OriginalH430ReceiptFourBand
import ImbalancedChen.Part5OriginalH430FreshReceiptCounts

/-! Per-additive-prime disintegration of the four ordinary positive W2
occurrences. The first two have fixed cutoff a, the prefix pair has
cutoff p. In each case the filter survives the change of summation. -/
namespace ImbalancedChen.Part5OriginalH430ReceiptPairIncidences
noncomputable section
open Finset Wu2008DoubleSieve
open P2FrozenReceiverCountActions (frozenCarrier frozenCount)
open P2OriginalW2MotherOccurrenceReindex (colour_pair_reindex)
open P2W2PhysicalChildFeedback (source_mask_prime)
open Part5OriginalH430ReceiptFourBand (count)
open scoped Classical BigOperators

def rect (P R : Finset ℕ) (F : ℕ → ℕ → ℝ) : ℝ :=
  ∑ p∈P, ∑ q∈R, if p<q then F p q else 0

def outputs (N d : ℕ) (a : ℝ) (E : ℕ → Prop) : Finset ℕ :=
  (sieveCarrier N d (d*N) a).filter E

def labels (N d : ℕ) (a f : ℝ) (ell : ℕ) : Finset ℕ :=
  divisorsIn (primeWindow (d*N) a f) ((N-ell)/d)

private theorem filter_switch (S : Finset ℕ) (E F : ℕ → Prop) :
    (S.filter E).filter F = (S.filter F).filter E := by
  ext x
  simp only [mem_filter]
  tauto

private theorem change_mask (N d p q : ℕ) (z : ℝ)
    (hp : p.Prime) (hq : q.Prime) (hzp : z≤p) (hzq : z≤q) :
    sourceSieveCarrier N (d*p*q) (d*N) z =
      sourceSieveCarrier N (d*p*q) ((d*p*q)*N) z := by
  rw [show (d*p*q)*N=q*(p*(d*N)) by ring,
    source_mask_prime N (d*p*q) (p*(d*N)) hq hzq,
    source_mask_prime N (d*p*q) (d*N) hp hzp]

theorem fixed_pair_mass (N d : ℕ) (E : ℕ → Prop) (a u v w : ℝ) (hav : a≤v) :
    let P := primeWindow (d*N) a u
    let R := primeWindow (d*N) v w
    (∑ ell∈outputs N d a E,
      ((((divisorsIn P ((N-ell)/d)) ×ˢ (divisorsIn R ((N-ell)/d))).filter
          (fun x => x.1<x.2)).card:ℝ)) =
      rect P R (fun p q => count N (d*p*q) E a) := by
  let P := primeWindow (d*N) a u
  let R := primeWindow (d*N) v w
  let A := outputs N d a E
  have point (ell : ℕ) :
      ((((divisorsIn P ((N-ell)/d)) ×ˢ (divisorsIn R ((N-ell)/d))).filter
        (fun x => x.1<x.2)).card:ℝ) =
      ∑ p∈P, ∑ q∈R, if p<q ∧ p∣(N-ell)/d ∧ q∣(N-ell)/d then (1:ℝ) else 0 := by
    simp only [←sum_boole,sum_product,divisorsIn,sum_filter]
    apply sum_congr rfl
    intro p _
    by_cases h : p∣(N-ell)/d
    · simp only [h,if_true,true_and]
      apply sum_congr rfl
      intro q _
      split_ifs <;> simp_all
    · simp [h]
  change (∑ ell∈A, _) = rect P R _
  simp_rw [point]
  rw [sum_comm (s:=A)]
  unfold rect
  apply sum_congr rfl
  intro p hp
  rw [sum_comm (s:=A)]
  apply sum_congr rfl
  intro q hq
  by_cases h : p<q
  · simp only [h,if_true,true_and,sum_boole]
    have hpr := (mem_primeWindow.mp hp).1
    have hqr := (mem_primeWindow.mp hq).1
    have hd (n : ℕ) : p∣n ∧ q∣n ↔ p*q∣n :=
      ⟨fun hh => ((Nat.coprime_primes hpr hqr).mpr h.ne).mul_dvd_of_dvd_of_dvd hh.1 hh.2,
       fun hh => ⟨(dvd_mul_right p q).trans hh,(dvd_mul_left q p).trans hh⟩⟩
    simp_rw [hd]
    change (((((sieveCarrier N d (d*N) a).filter E).filter
      (fun ell => p*q∣(N-ell)/d)).card):ℝ) = _
    rw [filter_switch,fourthRowMother_fixed_carrier N d (p*q) (d*N) a (dvd_mul_right d N),
      ←Nat.mul_assoc,change_mask N d p q a hpr hqr (mem_primeWindow.mp hp).2.2.1
        (hav.trans (mem_primeWindow.mp hq).2.2.1)]
    simp only [count,frozenCount,frozenCarrier,Int.cast_natCast]
  · simp [h]

theorem gamma56 (N d : ℕ) (E : ℕ → Prop) {a b c e f : ℝ}
    (hab : a≤b) (hbc : b≤c) (hce : c≤e) (hef : e≤f) :
    let χ := secondFunctionalMotherColour b c e
    let s := labels N d a f
    let win := primeWindow (d*N)
    let F := fun p q => count N (d*p*q) E a
    (∑ ell∈outputs N d a E,((fourthRowMotherLowPairs (s ell) χ).card:ℝ)) =
      rect (win a c) (win a c) F ∧
    (∑ ell∈outputs N d a E,((fourthRowMotherCrossPairs (s ell) χ).card:ℝ)) =
      rect (win a b) (win c e) F := by
  dsimp only
  constructor
  · simpa only [labels,fourthRowMotherLowPairs,secondFunctionalMother_band_low _ _ hbc
      (hce.trans hef)] using fixed_pair_mass N d E a c a c le_rfl
  · rw [←fixed_pair_mass N d E a b c e (hab.trans hbc)]
    apply sum_congr rfl
    intro ell _
    simp only [labels,fourthRowMotherCrossPairs,secondFunctionalMother_band_zero _ _
      (hbc.trans (hce.trans hef)),secondFunctionalMother_band_two _ _ hab hbc hef]
    have hs : ∀ x∈ (divisorsIn (primeWindow (d*N) a b) ((N-ell)/d)) ×ˢ
        (divisorsIn (primeWindow (d*N) c e) ((N-ell)/d)), x.1<x.2 := by
      rintro ⟨p,q⟩ hx
      obtain ⟨hp,hq⟩ := mem_product.mp hx
      exact_mod_cast ((mem_primeWindow.mp (mem_filter.mp hp).1).2.2.2.trans_le
        (hbc.trans (mem_primeWindow.mp (mem_filter.mp hq).1).2.2.1))
    rw [filter_eq_self.mpr hs]

theorem prefix_pair_mass (N d : ℕ) (E : ℕ → Prop) (a b c e f : ℝ) (v w : ℕ) :
    let P := primeWindow (d*N) a f
    let χ := secondFunctionalMotherColour b c e
    (∑ ell∈outputs N d a E,
      ((fourthRowMotherColoured (labels N d a f ell) χ [v,w]).card:ℝ)) =
      rect (P.filter (fun p => χ p=v)) (P.filter (fun q => χ q=w))
        (fun p q => count N (d*p*q) E p) := by
  let P := primeWindow (d*N) a f
  let χ := secondFunctionalMotherColour b c e
  let A := outputs N d a E
  let L := fun ell => fourthRowMotherPrefixes (labels N d a f ell) 2
  have fibre (ell : ℕ) : fourthRowMotherColoured (labels N d a f ell) χ [v,w] =
      (secondFunctionalMotherTuples P 2).filter (fun l => l.map χ=[v,w] ∧ l∈L ell) := by
    ext l
    simp only [fourthRowMotherColoured,mem_filter]
    constructor
    · rintro ⟨hl,hc⟩
      exact ⟨secondFunctionalMother_prefix_in_tuples hl,hc,hl⟩
    · exact fun h => ⟨h.2.2,h.2.1⟩
  change (∑ ell∈A, ((fourthRowMotherColoured (labels N d a f ell) χ [v,w]).card:ℝ)) = _
  simp only [fibre,←sum_boole]
  rw [sum_comm]
  let F := fun l : List ℕ => ((A.filter (fun ell => l∈L ell)).card:ℝ)
  have he (l : List ℕ) : (∑ ell∈A, if l.map χ=[v,w] ∧ l∈L ell then (1:ℝ) else 0) =
      if l.map χ=[v,w] then F l else 0 := by
    by_cases hc : l.map χ=[v,w] <;> simp [hc,F]
  simp_rw [he]
  rw [colour_pair_reindex P b c e v w F]
  unfold rect
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q hq
  by_cases h : p<q
  · simp only [if_pos h]
    have hp' := (mem_filter.mp hp).1
    have hq' := (mem_filter.mp hq).1
    dsimp only [F,A,outputs,L,labels]
    rw [filter_switch,fourthRowMother_pair_carrier N d hp' hq' h,←Nat.mul_assoc,
      change_mask N d p q p (mem_primeWindow.mp hp').1 (mem_primeWindow.mp hq').1
        le_rfl (by exact_mod_cast h.le)]
    simp only [count,frozenCount,frozenCarrier,Int.cast_natCast]
  · simp [h]

end
end ImbalancedChen.Part5OriginalH430ReceiptPairIncidences
