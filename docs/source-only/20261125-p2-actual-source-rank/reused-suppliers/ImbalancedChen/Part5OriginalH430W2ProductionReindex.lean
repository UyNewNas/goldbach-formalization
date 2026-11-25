import ImbalancedChen.Part5OriginalH430W2ProductionGeometry

/-!
SOURCE ONLY / UNCOMPILED.

Two-sided finite carrier dictionary. The forward direction derives all
production ceiling/product/order tests; the reverse direction proves
membership in the original enclosing tuple box. Natural primes are put
in Fin(N+1) only after the cap is proved. Arbitrary signed tests are
preserved, so equal products and repeated external history labels cannot
be collapsed by this reindexing. Endpoint/repeat payment is reused, not
charged again here.
-/
namespace ImbalancedChen.Part5OriginalH430W2ProductionReindex

noncomputable section
open Set Classical
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackDomains
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open P2OriginalHalfOpenProfileCarrier P2OriginalBankThetaMassLimits
open P2OriginalBankChildPrimeMass
open Part5OriginalH430W2DiscardedCarriers Part5OriginalH430W2ProductionGeometry

def singleTuple (p : ℕ) : Fin 1 → ℕ := fun _ => p
def pairTuple (small large : ℕ) : Fin 2 → ℕ := ![small, large]

@[simp] theorem singleTuple_eta (q : Fin 1 → ℕ) : singleTuple (q 0) = q := by
  funext i
  fin_cases i
  rfl

@[simp] theorem pairTuple_eta (q : Fin 2 → ℕ) : pairTuple (q 0) (q 1) = q := by
  funext i
  fin_cases i <;> rfl

theorem normalized_pair_eq {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (small large : ℕ) :
    normalizedLog N (physicalLevel N Q old) (pairTuple small large) =
      pairPoint Q old small large := by
  funext i
  rw [normalized_eq_relative hw]
  fin_cases i <;> rfl

/-- No residual ceiling/product filter is left unexplained on either side. -/
theorem freshSingle_iff_production {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (j : Fin 36) (k : Fin 3)
    (hceil : physicalLevel N Q old/(originalW2At j).s ≤ chi) (p : Fin (N+1)) :
    singleTuple p.val ∈ freshSingle N (parentProduct old) (physicalLevel N Q old)
      (originalW2At j) k ↔ p ∈ singleChildren (.w2 j k) N Q old chi := by
  have hgeo := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  constructor
  · intro hp
    obtain ⟨hbox,hi,hfresh⟩ := mem_freshSingle_iff.mp hp
    have hprime : p.val.Prime := (mem_actualPrimeBoxTuples_iff.mp hbox 0).1
    have hcop : p.val.Coprime (N*parentProduct old) := (fresh_iff_coprime hbox).mp hfresh 0
    have hdom : relativePrime Q old p.val ∈ W2SingletonDomain (originalW2At j) k := by
      simpa only [singleInterior, normalized_eq_relative hw, singleTuple] using hi
    have hcoords := W2SingletonDomain_subset hgeo k hdom
    have hprod := product_lt_of_relative_lt_one hw hprime.pos
      (hcoords.2.trans_lt (by norm_num : (1/2:ℝ) < 1))
    exact mem_singleChildren.mpr ⟨⟨hprime,hcop⟩,hw,hdom,
      physical_lt_ceiling hw j hceil (singleton_lt_target_recip j k hdom),hprod⟩
  · intro hp
    have hh := mem_singleChildren.mp hp
    have hdom : relativePrime Q old p.val ∈ W2SingletonDomain (originalW2At j) k := hh.2.2.1
    have hcoords := W2SingletonDomain_subset hgeo k hdom
    have hbox := mem_box_of_relative_bounds hw (singleTuple p.val)
      (fun _ => hh.1) (fun _ => hcoords)
    apply mem_freshSingle_iff.mpr
    refine ⟨hbox, ?_, (fresh_iff_coprime hbox).mpr (fun _ => hh.1.2)⟩
    simpa only [singleInterior, normalized_eq_relative hw, singleTuple] using hdom

/-- Both coordinates are kept. The arithmetic pair is ordered small<large,
while its physical word appends [large,small]. These are not interchanged. -/
theorem freshPair_iff_production {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (j : Fin 36) (k : Fin 4)
    (hceil : physicalLevel N Q old/(originalW2At j).s ≤ chi)
    (p : Fin (N+1) × Fin (N+1)) :
    pairTuple p.1.val p.2.val ∈ freshPair N (parentProduct old) (physicalLevel N Q old)
      (originalW2At j) k ↔ p ∈ pairChildren j k N Q old chi := by
  have hgeo := originalRepairedW2Bank_geometry _ (originalW2At_mem j)
  have hnorm := normalized_pair_eq hw p.1.val p.2.val
  constructor
  · intro hp
    obtain ⟨hbox,hi,hfresh⟩ := mem_freshPair_iff.mp hp
    have hs : p.1.val.Prime := (mem_actualPrimeBoxTuples_iff.mp hbox 0).1
    have hl : p.2.val.Prime := (mem_actualPrimeBoxTuples_iff.mp hbox 1).1
    have hcop := (fresh_iff_coprime hbox).mp hfresh
    have hdom : pairPoint Q old p.1.val p.2.val ∈ W2PairDomain (originalW2At j) k := by
      simpa only [pairInterior, hnorm] using hi
    have hg := W2PairDomain_gates hgeo k hdom
    have hord : p.1.val < p.2.val := (relative_lt_iff hw hs.pos hl.pos).mp hg.2.1
    have hmargin := (W2PairDomain_geometry hgeo k hdom).2
    have hsum : relativePrime Q old p.1.val + relativePrime Q old p.2.val < 1 := by
      change (1/5:ℝ) ≤ 1-relativePrime Q old p.1.val-relativePrime Q old p.2.val at hmargin
      linarith only [hmargin]
    have hc := pair_lt_target_recip j k hdom
    exact mem_pairChildren.mpr ⟨⟨⟨hs,hcop 0⟩,⟨hl,hcop 1⟩⟩,hw,hord,hdom,
      physical_lt_ceiling hw j hceil (hc 0), physical_lt_ceiling hw j hceil (hc 1),
      pair_product_lt_of_sum hw hs.pos hl.pos hsum⟩
  · intro hp
    have hh := mem_pairChildren.mp hp
    have hdom := hh.2.2.2.1
    have hcoords := (W2PairDomain_geometry hgeo k hdom).1
    have hprimes : ∀ i, ((pairTuple p.1.val p.2.val) i).Prime ∧
        ((pairTuple p.1.val p.2.val) i).Coprime (N*parentProduct old) := by
      intro i
      fin_cases i
      · exact hh.1.1
      · exact hh.1.2
    have hbounds : ∀ i, (1/5:ℝ) ≤ relativePrime Q old ((pairTuple p.1.val p.2.val) i) ∧
        relativePrime Q old ((pairTuple p.1.val p.2.val) i) ≤ 1/2 := by
      intro i
      fin_cases i
      · exact ⟨hcoords.1 0,hcoords.2 0⟩
      · exact ⟨hcoords.1 1,hcoords.2 1⟩
    have hbox := mem_box_of_relative_bounds hw _ hprimes hbounds
    apply mem_freshPair_iff.mpr
    refine ⟨hbox, ?_, (fresh_iff_coprime hbox).mpr (fun i => (hprimes i).2)⟩
    simpa only [pairInterior, hnorm] using hdom

/-- The complete natural singleton sum, not a selected/truncated image. -/
theorem freshSingle_sum_eq_production {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (j : Fin 36) (k : Fin 3)
    (hceil : physicalLevel N Q old/(originalW2At j).s ≤ chi)
    (F : (Fin 1 → ℕ) → ℝ) :
    (∑ q ∈ freshSingle N (parentProduct old) (physicalLevel N Q old) (originalW2At j) k, F q) =
      ∑ p ∈ singleChildren (.w2 j k) N Q old chi, F (singleTuple p.val) := by
  symm
  apply Finset.sum_bij (fun p _ => singleTuple p.val)
  · intro p hp
    exact (freshSingle_iff_production hw j k hceil p).mpr hp
  · intro p _ r _ h
    exact Fin.ext (congrFun h 0)
  · intro q hq
    obtain ⟨hb,hi,_⟩ := mem_freshSingle_iff.mp hq
    have hp := (mem_actualPrimeBoxTuples_iff.mp hb 0).1
    have hd : relativePrime Q old (q 0) ∈ W2SingletonDomain (originalW2At j) k := by
      simpa only [singleInterior, normalized_eq_relative hw] using hi
    have hx := W2SingletonDomain_subset
      (originalRepairedW2Bank_geometry _ (originalW2At_mem j)) k hd
    have hcap := prime_cap_of_relative_lt_one hw hp.pos
      (hx.2.trans_lt (by norm_num : (1/2:ℝ) < 1))
    let p : Fin (N+1) := ⟨q 0,Nat.lt_succ_of_le hcap⟩
    have he : singleTuple p.val = q := singleTuple_eta q
    refine ⟨p, (freshSingle_iff_production hw j k hceil p).mp ?_, he⟩
    rwa [he]
  · intro p _
    rfl

theorem freshPair_sum_eq_production {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (hw : parentWindow N Q old chi) (j : Fin 36) (k : Fin 4)
    (hceil : physicalLevel N Q old/(originalW2At j).s ≤ chi)
    (F : (Fin 2 → ℕ) → ℝ) :
    (∑ q ∈ freshPair N (parentProduct old) (physicalLevel N Q old) (originalW2At j) k, F q) =
      ∑ p ∈ pairChildren j k N Q old chi, F (pairTuple p.1.val p.2.val) := by
  symm
  apply Finset.sum_bij (fun p _ => pairTuple p.1.val p.2.val)
  · intro p hp
    exact (freshPair_iff_production hw j k hceil p).mpr hp
  · intro p _ r _ h
    exact Prod.ext (Fin.ext (congrFun h 0)) (Fin.ext (congrFun h 1))
  · intro q hq
    obtain ⟨hb,hi,_⟩ := mem_freshPair_iff.mp hq
    have hx := (W2PairDomain_geometry
      (originalRepairedW2Bank_geometry _ (originalW2At_mem j)) k hi).1
    have hcap (i : Fin 2) : q i ≤ N := by
      have hu : relativePrime Q old (q i) ≤ 1/2 := by
        simpa only [normalized_eq_relative hw] using hx.2 i
      exact prime_cap_of_relative_lt_one hw (mem_actualPrimeBoxTuples_iff.mp hb i).1.pos
        (hu.trans_lt (by norm_num : (1/2:ℝ) < 1))
    let p : Fin (N+1) × Fin (N+1) :=
      (⟨q 0,Nat.lt_succ_of_le (hcap 0)⟩,⟨q 1,Nat.lt_succ_of_le (hcap 1)⟩)
    have he : pairTuple p.1.val p.2.val = q := pairTuple_eta q
    refine ⟨p, (freshPair_iff_production hw j k hceil p).mp ?_, he⟩
    rwa [he]
  · intro p _
    rfl

end
end ImbalancedChen.Part5OriginalH430W2ProductionReindex
