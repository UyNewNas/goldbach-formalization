import ImbalancedChen.P2OriginalSingleChildWindowDictionary

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

All four ORIGINAL W2 mother pair occurrences are split into the actual
strict arithmetic child, a fresh lower-wall fibre, and an old-prefix
repeat fibre. The last two are retained finite sums. In particular a
repeat means p | old.prod or q | old.prod; the original p < q remains in
all three lanes. This is not the selected-square collision cost and is
not an additional payment of the earlier endpoint/mass errors.
-/

namespace ImbalancedChen.P2OriginalPairChildWindowDictionary
noncomputable section
open Finset Set Wu2008DoubleSieve
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2OriginalHalfOpenProfileCarrier P2OriginalW2CountTupleReindex
open P2OriginalBankThetaMassLimits

def fullPair (N : ℕ) (L : ℝ) (bank : Fin 36) (piece : Fin 4) : Finset (Fin 2 → ℕ) :=
  (actualPrimeBoxTuples N (fun _ : Fin 2 => L/10) (fun _ => 3*L/5)).filter
    (fun p => normalizedLog N L p ∈ pairHalf (originalW2At bank) piece)

def fresh (d : ℕ) (p : Fin 2 → ℕ) : Prop := ¬ p 0 ∣ d ∧ ¬ p 1 ∣ d

def pairTuple {N : ℕ} (p : Fin (N+1) × Fin (N+1)) : Fin 2 → ℕ :=
  ![p.1.val,p.2.val]

theorem pairTuple_injective {N : ℕ} : Function.Injective (@pairTuple N) := by
  intro p q h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  apply Prod.ext
  · exact Fin.ext (by simpa only [pairTuple, Matrix.cons_val_zero] using h0)
  · exact Fin.ext (by simpa only [pairTuple, Matrix.cons_val_one] using h1)

theorem relativePrime_normalized {N : ℕ} {Q L : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (p : Fin 2 → ℕ) (i : Fin 2) :
    relativePrime Q old (p i) = normalizedLog N L p i := by
  unfold relativePrime residualLevel
  rw [hQ]
  exact physical_log_ratio hN hd hL p i

theorem pairPoint_normalized {N : ℕ} {Q L : ℝ} {old : List ℕ}
    (hN : 1 < N) (hd : 0 < parentProduct old) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L) (p : Fin 2 → ℕ) :
    pairPoint Q old (p 0) (p 1) = normalizedLog N L p := by
  funext i
  fin_cases i
  · exact relativePrime_normalized hN hd hL hQ p 0
  · exact relativePrime_normalized hN hd hL hQ p 1

/-- The strict domains remove exactly their listed lower walls. The
strict p<q and both original square gates stay on both sides. -/
theorem strict_pair_iff_half_not_wall (bank : Fin 36) (piece : Fin 4) (x : Point) :
    x ∈ W2PairDomain (originalW2At bank) piece ↔
      x ∈ pairHalf (originalW2At bank) piece ∧
        x ∉ pairLowerWall (originalW2At bank) piece := by
  have hn : x ∈ W2PairDomain (originalW2At bank) piece →
      x ∉ pairLowerWall (originalW2At bank) piece := by
    fin_cases piece
    · rintro ⟨ha,hrest⟩ he
      change x 0 = a0 (originalW2At bank) at he
      linarith
    · rintro ⟨ha,hb,hc,hd⟩ (he | he) <;> linarith
    · rintro ⟨ha,hrest⟩ he
      change x 0 = a0 (originalW2At bank) at he
      linarith
    · rintro ⟨ha,hb,hc,hd⟩ (he | he) <;> linarith
  constructor
  · intro h
    exact ⟨(pairHalf_partition _ piece x).mpr (Or.inl h),hn h⟩
  · rintro ⟨hh,hw⟩
    rcases (pairHalf_partition _ piece x).mp hh with h | h
    · exact h
    · exact False.elim (hw h.2)

/-- The original bank's phi3 >= target row supplies the physical ceiling;
the W2Geometry bound by 1/2 alone would be insufficient for that purpose. -/
theorem pairHalf_below_target (bank : Fin 36) (piece : Fin 4) {x : Point}
    (hx : x ∈ pairHalf (originalW2At bank) piece) :
    x 0 < 1/(originalW2At bank).s ∧ x 1 < 1/(originalW2At bank).s := by
  obtain ⟨hs,h3,h2,h1,h0,h5⟩ :=
    P2AllW2SameQRawCountAction.original_W2_order _ (originalW2At_mem bank)
  have hs0 : 0 < (originalW2At bank).s := by linarith
  have hrec : a3 (originalW2At bank) ≤ 1/(originalW2At bank).s :=
    one_div_le_one_div_of_le hs0 h3
  obtain ⟨_,_,h12,h23,_,_,_,_,_⟩ :=
    originalRepairedW2Bank_geometry _ (originalW2At_mem bank)
  fin_cases piece <;>
    simp only [pairHalf,mem_setOf_eq] at hx <;> constructor <;> linarith

/-- Full N-window tuples already have both prime enumeration caps and
positive product support. No coprimality to the old prefix is used. -/
theorem fullPair_support {N : ℕ} {Q L chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (bank : Fin 36) (piece : Fin 4) {p : Fin 2 → ℕ}
    (hp : p ∈ fullPair N L bank piece)
    (hc : physicalLevel N Q old/(originalW2At bank).s ≤ chi) :
    p 0 < p 1 ∧ p 0 < N ∧ p 1 < N ∧
      ((parentProduct old*p 1*p 0 : ℕ) : ℝ) < Q ∧
      physicalPrime N (p 0) < chi ∧ physicalPrime N (p 1) < chi := by
  have hbox := (mem_filter.mp hp).1
  have hx := (mem_filter.mp hp).2
  have hpr := mem_actualPrimeBoxTuples_iff.mp hbox
  have hcarr := (pair_count_carrier_membership hw.1 hw.2.1 hL hQ
    (originalRepairedW2Bank_geometry _ (originalW2At_mem bank)) piece p).mp hp
  have hd0 : (0 : ℝ) < parentProduct old := Nat.cast_pos.mpr hw.2.1
  have hd1 : (1 : ℝ) ≤ parentProduct old := by
    exact_mod_cast (show 1 ≤ parentProduct old by omega)
  have hp0 : (0 : ℝ) < p 0 := Nat.cast_pos.mpr (hpr 0).1.pos
  have hq0 : (0 : ℝ) < p 1 := Nat.cast_pos.mpr (hpr 1).1.pos
  have hp1 : (1 : ℝ) ≤ p 0 := by exact_mod_cast (hpr 0).1.one_lt.le
  have hpq : (p 0 : ℝ) < p 1 := by exact_mod_cast hcarr.2.1
  have hmul := mul_lt_mul_of_pos_left hpq (mul_pos hd0 hq0)
  have hprod : ((parentProduct old*p 1*p 0 : ℕ) : ℝ) < Q := by
    have hg := hcarr.2.2.1
    push_cast
    nlinarith only [hmul,hg]
  have hprodR : (parentProduct old : ℝ)*(p 1 : ℝ)*(p 0 : ℝ) < Q := by
    simpa only [Nat.cast_mul] using hprod
  have hdp : (1 : ℝ) ≤ (parentProduct old : ℝ)*(p 0 : ℝ) := by
    nlinarith only [hd1,hp1]
  have hqprod : (p 1 : ℝ) ≤ (parentProduct old : ℝ)*(p 1 : ℝ)*(p 0 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hdp hq0.le
    nlinarith only [hm]
  have hqN : p 1 < N := by
    have hr : (p 1 : ℝ) < (N : ℝ) := hqprod.trans_lt (hprodR.trans_le hw.2.2.2.1)
    exact_mod_cast hr
  have ht := pairHalf_below_target bank piece hx
  have hceiling (i : Fin 2) (hu : normalizedLog N L p i < 1/(originalW2At bank).s) :
      physicalPrime N (p i) < chi := by
    rw [← relativePrime_normalized hw.1 hw.2.1 hL hQ] at hu
    have hm := mul_lt_mul_of_pos_left hu (parentWindow_logs hw).2.2
    rw [relativePrime_physical hw] at hm
    exact hm.trans_le (by simpa only [mul_one_div] using hc)
  exact ⟨hcarr.2.1,hcarr.2.1.trans hqN,hqN,hprod,
    hceiling 0 ht.1,hceiling 1 ht.2⟩

/-- Both directions tie the complete original carrier to the ACTUAL
production child constructor. The only omitted points are identified,
not assumed to be negligible. -/
theorem pairChild_iff {N : ℕ} {Q L chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (bank : Fin 36) (piece : Fin 4)
    (hc : physicalLevel N Q old/(originalW2At bank).s ≤ chi)
    (p : Fin (N+1) × Fin (N+1)) :
    p ∈ pairChildren bank piece N Q old chi ↔
      pairTuple p ∈ fullPair N L bank piece ∧ fresh (parentProduct old) (pairTuple p) ∧
        normalizedLog N L (pairTuple p) ∉ pairLowerWall (originalW2At bank) piece := by
  have he := pairPoint_normalized hw.1 hw.2.1 hL hQ (pairTuple p)
  constructor
  · intro hp
    have h := mem_pairChildren.mp hp
    have hx : normalizedLog N L (pairTuple p) ∈ W2PairDomain (originalW2At bank) piece := by
      rw [← he]
      exact h.2.2.2.1
    have hhalf := (strict_pair_iff_half_not_wall bank piece _).mp hx
    have hpr : ∀ i, ((pairTuple p) i).Prime ∧ ¬ (pairTuple p) i ∣ N := by
      intro i
      fin_cases i
      · exact ⟨h.1.1.1,h.1.1.1.coprime_iff_not_dvd.mp
          (Nat.coprime_mul_iff_right.mp h.1.1.2).1⟩
      · exact ⟨h.1.2.1,h.1.2.1.coprime_iff_not_dvd.mp
          (Nat.coprime_mul_iff_right.mp h.1.2.2).1⟩
    have hfull : pairTuple p ∈ fullPair N L bank piece := by
      refine mem_filter.mpr ⟨mem_actualPrimeBoxTuples_iff.mpr (fun i => ?_),hhalf.1⟩
      have hb := (normalizedLog_window hw.1 hL (pairTuple p)
        (fun i => (hpr i).1.pos) i (1/10) (3/5)).mp
          (mem_logPrimeBox.mp (pairHalf_in_cube
            (originalRepairedW2Bank_geometry _ (originalW2At_mem bank)) piece hhalf.1) i)
      refine ⟨(hpr i).1,(hpr i).2,?_,?_⟩
      · convert hb.1 using 1 <;> congr 1 <;> ring
      · convert hb.2 using 1 <;> congr 1 <;> ring
    refine ⟨hfull,?_,hhalf.2⟩
    exact ⟨h.1.1.1.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_right.mp h.1.1.2).2,
      h.1.2.1.coprime_iff_not_dvd.mp (Nat.coprime_mul_iff_right.mp h.1.2.2).2⟩
  · rintro ⟨hp,hfresh,hwall⟩
    have hpr := mem_actualPrimeBoxTuples_iff.mp (mem_filter.mp hp).1
    have hs := fullPair_support hw hL hQ bank piece hp hc
    have hx := (strict_pair_iff_half_not_wall bank piece _).mpr
      ⟨(mem_filter.mp hp).2,hwall⟩
    have hdomain : pairPoint Q old p.1.val p.2.val ∈
        W2PairDomain (originalW2At bank) piece := by
      rw [he]
      exact hx
    apply mem_pairChildren.mpr
    refine ⟨⟨⟨(hpr 0).1,?_⟩,⟨(hpr 1).1,?_⟩⟩,hw,hs.1,hdomain,
      hs.2.2.2.2.1,hs.2.2.2.2.2,hs.2.2.2.1⟩
    · exact Nat.coprime_mul_iff_right.mpr
        ⟨(hpr 0).1.coprime_iff_not_dvd.mpr (hpr 0).2.1,
          (hpr 0).1.coprime_iff_not_dvd.mpr hfresh.1⟩
    · exact Nat.coprime_mul_iff_right.mpr
        ⟨(hpr 1).1.coprime_iff_not_dvd.mpr (hpr 1).2.1,
          (hpr 1).1.coprime_iff_not_dvd.mpr hfresh.2⟩

theorem pairChild_image {N : ℕ} {Q L chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (bank : Fin 36) (piece : Fin 4)
    (hc : physicalLevel N Q old/(originalW2At bank).s ≤ chi) :
    (pairChildren bank piece N Q old chi).image pairTuple =
      (fullPair N L bank piece).filter (fun p => fresh (parentProduct old) p ∧
        normalizedLog N L p ∉ pairLowerWall (originalW2At bank) piece) := by
  ext p
  constructor
  · intro hp
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
    exact mem_filter.mpr ((pairChild_iff hw hL hQ bank piece hc q).mp hq)
  · intro hp
    obtain ⟨hp,hfresh,hwall⟩ := mem_filter.mp hp
    have hs := fullPair_support hw hL hQ bank piece hp hc
    let q : Fin (N+1) × Fin (N+1) := (⟨p 0,by omega⟩,⟨p 1,by omega⟩)
    have he : pairTuple q = p := by funext i; fin_cases i <;> rfl
    refine mem_image.mpr ⟨q,?_,he⟩
    apply (pairChild_iff hw hL hQ bank piece hc q).mpr
    simpa only [he] using And.intro hp (And.intro hfresh hwall)

/-- All four source occurrences with arbitrary signed history-valued
tests. The repeat lane includes endpoint repeats; the fresh endpoint lane
is disjoint from it, so no occurrence is lost or counted twice. -/
theorem W2_pair_window_sum {N : ℕ} {Q L chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (hL : 0 < L)
    (hQ : Q = (parentProduct old : ℝ)*(N : ℝ)^L)
    (bank : Fin 36) (piece : Fin 4)
    (hc : physicalLevel N Q old/(originalW2At bank).s ≤ chi) (F : ℕ → ℕ → ℝ) :
    windowOccurrence N Q L (parentProduct old) (originalW2At bank) piece F =
      (∑ p ∈ pairChildren bank piece N Q old chi, F p.1.val p.2.val) +
      (∑ p ∈ (fullPair N L bank piece).filter (fun p => fresh (parentProduct old) p ∧
        normalizedLog N L p ∈ pairLowerWall (originalW2At bank) piece), F (p 0) (p 1)) +
      ∑ p ∈ (fullPair N L bank piece).filter (fun p => ¬ fresh (parentProduct old) p),
        F (p 0) (p 1) := by
  have hsource := all_four_window_occurrences_reindex hw.1 hw.2.1 hL hQ
    (originalRepairedW2Bank_geometry _ (originalW2At_mem bank)) piece F
  have himage := pairChild_image hw hL hQ bank piece hc
  have hstrict : (∑ p ∈ pairChildren bank piece N Q old chi, F p.1.val p.2.val) =
      ∑ p ∈ (fullPair N L bank piece).filter (fun p => fresh (parentProduct old) p ∧
        normalizedLog N L p ∉ pairLowerWall (originalW2At bank) piece), F (p 0) (p 1) := by
    calc
      _ = ∑ p ∈ pairChildren bank piece N Q old chi,
          F (pairTuple p 0) (pairTuple p 1) := rfl
      _ = ∑ p ∈ (pairChildren bank piece N Q old chi).image pairTuple,
          F (p 0) (p 1) :=
        (sum_image (fun _ _ _ _ h => pairTuple_injective h)).symm
      _ = _ := by rw [himage]
  rw [hstrict]
  have hfull : windowOccurrence N Q L (parentProduct old) (originalW2At bank) piece F =
      ∑ p ∈ fullPair N L bank piece, F (p 0) (p 1) := by
    simpa only [fullPair,sum_filter] using hsource
  rw [hfull]
  simp only [sum_filter]
  rw [← sum_add_distrib,← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  by_cases hf : fresh (parentProduct old) p <;>
    by_cases hb : normalizedLog N L p ∈ pairLowerWall (originalW2At bank) piece <;>
    simp [hf,hb]

theorem repeat_iff_divides (d : ℕ) (p : Fin 2 → ℕ) :
    ¬ fresh d p ↔ p 0 ∣ d ∨ p 1 ∣ d := by
  simp only [fresh,not_and_or,not_not]

end
end ImbalancedChen.P2OriginalPairChildWindowDictionary
