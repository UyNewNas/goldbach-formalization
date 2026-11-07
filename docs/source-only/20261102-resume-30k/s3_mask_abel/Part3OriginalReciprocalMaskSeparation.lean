import ImbalancedChen.Part3OriginalFrozenCauchyCaller

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal mask factorization of the J row. In particular the six clean
coprimality gates are not silently dropped: their inner dependence is
EXACTLY (s1,a*c)=1. The h support and both individual rough-factor
supports are independent of the outer tuple. Only one product interval
is left on s1, with fixed original physical endpoints.
-/

noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumDoubleLambdaColorWindows20261028
open ImbalancedChen.Part3.OriginalActualProductBoundDifferences20261028
open ImbalancedChen.Part3.OriginalActualThreePairPolarization20261102
open ImbalancedChen.Part3.OriginalActualPolarizedProductCaller20261102
open ImbalancedChen.Part3.OriginalActualFrozenSmoothPackets20261102
open ImbalancedChen.Part3.OriginalFrozenReciprocalCauchy20261102
open ImbalancedChen.Part3.OriginalFrozenReciprocalMask20261102
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumOwnedCanonicalReindex20261028
open ImbalancedChen.Part3.MediumCanonicalFixedBlock20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028

namespace ImbalancedChen.Part3.OriginalReciprocalMaskSeparation20261102

attribute [local instance] Classical.propDecidable

theorem mem_original_carrier (B : FixedBlock) (t : Index) :
    t ∈ B.carrier ↔
      t.q ∈ B.qCarrier ∧ t.w1 ∈ B.wCarrier ∧ t.w2 ∈ B.wCarrier ∧
      t.n1 ∈ B.nCarrier ∧ t.n2 ∈ B.nCarrier ∧
      t.h ∈ B.hCarrier ∧ B.clean t := by
  constructor
  · intro ht
    obtain ⟨ht, hc⟩ := mem_filter.mp ht
    obtain ⟨q, hq, ht⟩ := mem_biUnion.mp ht
    obtain ⟨w1, hw1, ht⟩ := mem_biUnion.mp ht
    obtain ⟨w2, hw2, ht⟩ := mem_biUnion.mp ht
    obtain ⟨n1, hn1, ht⟩ := mem_biUnion.mp ht
    obtain ⟨n2, hn2, ht⟩ := mem_biUnion.mp ht
    obtain ⟨h, hh, he⟩ := mem_image.mp ht
    cases he
    exact ⟨hq, hw1, hw2, hn1, hn2, hh, hc⟩
  · rintro ⟨hq, hw1, hw2, hn1, hn2, hh, hc⟩
    apply mem_filter.mpr
    refine ⟨?_, hc⟩
    apply mem_biUnion.mpr
    refine ⟨t.q, hq, ?_⟩
    apply mem_biUnion.mpr
    refine ⟨t.w1, hw1, ?_⟩
    apply mem_biUnion.mpr
    refine ⟨t.w2, hw2, ?_⟩
    apply mem_biUnion.mpr
    refine ⟨t.n1, hn1, ?_⟩
    apply mem_biUnion.mpr
    refine ⟨t.n2, hn2, ?_⟩
    exact mem_image.mpr ⟨t.h, hh, by cases t; rfl⟩

def originalFactors (atom : MediumAtom) (z : ℝ) (k : Key) (small : ℕ) :
    FactorData := (fixedBlock k small).factorData atom (strictReceiverCutoff z)

theorem mem_actualFactorAmbient (atom : MediumAtom) (z : ℝ) (k : Key)
    (small : ℕ) (p : Factor) :
    p ∈ actualFactorAmbient atom z k small ↔
      p.s ∈ (originalFactors atom z k small).smoothS ∧
      p.t ∈ (originalFactors atom z k small).smoothT ∧
      p.u ∈ (originalFactors atom z k small).roughU ∧
      p.v ∈ (originalFactors atom z k small).roughV := by
  constructor
  · intro hp
    obtain ⟨s, hs, hp⟩ := mem_biUnion.mp hp
    obtain ⟨t, ht, hp⟩ := mem_biUnion.mp hp
    obtain ⟨u, hu, hp⟩ := mem_biUnion.mp hp
    obtain ⟨v, hv, he⟩ := mem_image.mp hp
    cases he
    exact ⟨hs, ht, hu, hv⟩
  · rintro ⟨hs, ht, hu, hv⟩
    apply mem_biUnion.mpr
    refine ⟨p.s, hs, ?_⟩
    apply mem_biUnion.mpr
    refine ⟨p.t, ht, ?_⟩
    apply mem_biUnion.mpr
    refine ⟨p.u, hu, ?_⟩
    exact mem_image.mpr ⟨p.v, hv, by cases p; rfl⟩

/-- No opposite-label, outer-variable, rectangle or product dependence. -/
def commonS (atom : MediumAtom) (z : ℝ) (k : Key) (small : ℕ)
    (st : ℕ × ℕ) : Finset ℕ :=
  (originalFactors atom z k small).roughU.filter
    (fun s => s * st.1 ∈ factorCarrier atom.Q2)

def commonR (atom : MediumAtom) (z : ℝ) (k : Key) (small : ℕ)
    (st : ℕ × ℕ) : Finset ℕ :=
  (originalFactors atom z k small).roughV.filter
    (fun r => r * st.2 ∈ factorCarrier atom.Q3)

def tagGate (atom : MediumAtom) (z y : ℝ) (k : Key) (small : ℕ)
    (st : ℕ × ℕ) : Prop :=
  st.1 ∈ (originalFactors atom z k small).smoothS ∧
  st.2 ∈ (originalFactors atom z k small).smoothT ∧
  st.1 * st.2 = small ∧ (st.1 : ℝ) ≤ y ∧ (st.2 : ℝ) ≤ y

theorem original_choice_split (atom : MediumAtom) (z y : ℝ) (k : Key)
    (small : ℕ) (st : ℕ × ℕ) (s r : ℕ) :
    (⟨st.1, st.2, s, r⟩ : Factor) ∈
        choicesWithoutProductWindow atom z y k small ↔
      tagGate atom z y k small st ∧
      s ∈ commonS atom z k small st ∧ r ∈ commonR atom z k small st := by
  simp only [choicesWithoutProductWindow, mem_filter, mem_actualFactorAmbient,
    tagGate, commonS, commonR]
  tauto

theorem commonS_window (atom : MediumAtom) (z : ℝ) (k : Key) (small : ℕ)
    (st : ℕ × ℕ) {s : ℕ} (hs : s ∈ commonS atom z k small st) :
    2 ^ k.u ≤ s ∧ s < 2 * 2 ^ k.u := by
  have hw := (mem_filter.mp (mem_filter.mp hs).1).1
  change s ∈ Icc (2 ^ k.u) (2 ^ (k.u + 1) - 1) at hw
  have h := mem_Icc.mp hw
  rw [pow_succ] at h
  omega

/-- The ORIGINAL clean predicate has just one inner unit gate. No
(a,c)=1 hypothesis, coloring hypothesis or desired row equality is used. -/
theorem original_clean_split (B : FixedBlock) (o : Outer)
    (st st' : ℕ × ℕ) (s : ℕ) (h : ℤ) :
    B.clean (rebuild o st st' (s,h)).1 ↔
      B.clean (rebuild o st st' (1,0)).1 ∧
        s.Coprime (B.atom.residue.natAbs * packetC o) := by
  simp only [FixedBlock.clean, rebuild, packetC, one_mul,
    Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right]
  simp only [Nat.coprime_comm]
  tauto

theorem outer_rebuild_iff (B : FixedBlock) (o : Outer) (st st' : ℕ × ℕ)
    (s : ℕ) (h : ℤ) :
    outer B (rebuild o st st' (s,h)) = o ↔
      signedF B (rebuild o st st' (1,0)).1 = o.f := by
  cases o
  simp [outer, rebuild, signedF]

/-- This entire h set is fixed before ANY outer tuple is summed. -/
def commonH (B : FixedBlock) (R : Rectangle) : Finset ℤ :=
  B.hCarrier ∩ Icc R.hLo R.hHi

def productLo (B : FixedBlock) (R : Rectangle) : ℕ :=
  max (Nat.ceil B.roughLength) R.w1Lo

def productHi (B : FixedBlock) (R : Rectangle) (Br : ℕ) : ℕ :=
  min (Nat.floor (2 * B.roughLength)) (min R.w1Hi Br)

theorem productLo_pos (B : FixedBlock) (R : Rectangle) :
    0 < productLo B R :=
  (Nat.ceil_pos.mpr B.rough_pos).trans_le (le_max_left _ _)

theorem original_product_interval (B : FixedBlock) (R : Rectangle)
    (Br w : ℕ) :
    w ∈ B.wCarrier ∧ w ∈ Icc R.w1Lo R.w1Hi ∧ w ≤ Br ↔
      productLo B R ≤ w ∧ w ≤ productHi B R Br := by
  simp only [FixedBlock.wCarrier, factorCarrier, mem_Icc,
    productLo, productHi, max_le_iff, le_min_iff]
  tauto

def outerGate (B : FixedBlock) (atom : MediumAtom) (z y : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) (Bs : ℕ) (st st' : ℕ × ℕ) (o : Outer) : Prop :=
  tagGate atom z y k small st ∧ tagGate atom z y k small st' ∧
  o.r1 ∈ commonR atom z k small st ∧
  o.s2 ∈ commonS atom z k small st' ∧ o.r2 ∈ commonR atom z k small st' ∧
  o.q ∈ B.qCarrier ∧ o.s2 * o.r2 ∈ B.wCarrier ∧
  o.n1 ∈ B.nCarrier ∧ o.n2 ∈ B.nCarrier ∧
  o.q ∈ Icc R.qLo R.qHi ∧ o.s2 * o.r2 ∈ Icc R.w2Lo R.w2Hi ∧
  o.n1 ∈ Icc R.n1Lo R.n1Hi ∧ o.s2 * o.r2 ≤ Bs ∧
  B.clean (rebuild o st st' (1,0)).1 ∧
  signedF B (rebuild o st st' (1,0)).1 = o.f

/-- Complete iff for J's actual inner image. The original arithmetic
and factor-fibre masks have been factored, not replaced by assumptions. -/
theorem mem_innerImage_separated (B : FixedBlock) (atom : MediumAtom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (o : Outer) (s : ℕ) (h : ℤ) :
    (s,h) ∈ innerImage B atom z y k small R Br Bs st st' o ↔
      outerGate B atom z y k small R Bs st st' o ∧
      s ∈ commonS atom z k small st ∧
      s.Coprime (B.atom.residue.natAbs * packetC o) ∧
      productLo B R ≤ s * o.r1 ∧ s * o.r1 ≤ productHi B R Br ∧
      h ∈ commonH B R := by
  rw [mem_innerImage_iff, outer_rebuild_iff]
  have hclean := original_clean_split B o st st' s h
  have hprod := original_product_interval B R Br (s * o.r1)
  simp only [sourceCarrier, mem_filter, mem_product, mem_original_carrier,
    Rectangle.contains, rebuild, smoothTag, Prod.mk.injEq, and_self,
    eq_self_iff_true, true_and, and_true] at ⊢
  rw [original_choice_split, original_choice_split]
  unfold outerGate commonH
  simp only [mem_inter]
  dsimp only [rebuild] at hclean
  tauto

/-- This row has no outer-dependent h mask, no opaque factor fibre and
no clean arithmetic indicator beyond the required s-unit condition. -/
def separatedRow (B : FixedBlock) (atom : MediumAtom) (z : ℝ) (k : Key)
    (small : ℕ) (R : Rectangle) (Br : ℕ) (st st' : ℕ × ℕ)
    (e : Fin 4) (o : Outer) : ℂ :=
  ∑ s ∈ commonS atom z k small st,
    if s.Coprime (B.atom.residue.natAbs * packetC o) ∧
        productLo B R ≤ s * o.r1 ∧ s * o.r1 ≤ productHi B R Br then
      ∑ h ∈ commonH B R, innerAtom B atom st st' e o (s,h)
    else 0

theorem original_row_eq_separated (B : FixedBlock) (atom : MediumAtom)
    (z y : ℝ) (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) (e : Fin 4) (o : Outer) :
    row B atom z y k small R Br Bs st st' e o =
      if outerGate B atom z y k small R Bs st st' o then
        separatedRow B atom z k small R Br st st' e o else 0 := by
  rw [row_eq_inner_image]
  by_cases ho : outerGate B atom z y k small R Bs st st' o
  · rw [if_pos ho]
    have hc : innerImage B atom z y k small R Br Bs st st' o =
        ((commonS atom z k small st).filter (fun s =>
          s.Coprime (B.atom.residue.natAbs * packetC o) ∧
          productLo B R ≤ s * o.r1 ∧ s * o.r1 ≤ productHi B R Br)) ×ˢ
          commonH B R := by
      ext u
      rcases u with ⟨s,h⟩
      rw [mem_innerImage_separated]
      simp only [ho, true_and, mem_product, mem_filter]
      tauto
    rw [hc, sum_product, sum_filter]
    rfl
  · rw [if_neg ho]
    apply sum_eq_zero
    intro u hu
    exact (ho ((mem_innerImage_separated B atom z y k small R Br Bs st st'
      o u.1 u.2).mp hu).1).elim

/-- The manuscript's coloring label is outer data; it cannot create a
hidden s or h coefficient. This remains true for every original color map. -/
theorem original_color_outer {B : FixedBlock} {K : ℕ}
    (C : CrossColoring B K) (o : Outer) (st st' : ℕ × ℕ) (s : ℕ) (h : ℤ) :
    C.color ((rebuild o st st' (s,h)).1.n1 *
      (rebuild o st st' (s,h)).1.w2, (rebuild o st st' (s,h)).1.n2) =
        C.color (packetC o, o.n2) := by
  congr 1
  apply Prod.ext
  · simp only [rebuild, packetC]
    ring
  · rfl

theorem source_packetC (B : FixedBlock) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) {s : Source}
    (hs : s ∈ sourceCarrier B atom z y k small R Br Bs st st') :
    packetC (outer B s) = s.1.n1 * s.1.w2 := by
  have hp := (mem_filter.mp hs).2.2.2.2.1
  simp only [packetC, outer]
  rw [← hp]
  ring

/-- Cross-coprimality of the ORIGINAL color survives the exact outer
map. There is no independently asserted packet coloring or pair source. -/
theorem original_outer_color_cross {B : FixedBlock} {K : ℕ}
    (C : CrossColoring B K) (atom : MediumAtom) (z y : ℝ)
    (k : Key) (small : ℕ) (R : Rectangle) (Br Bs : ℕ)
    (st st' : ℕ × ℕ) {o1 o2 : Outer}
    (ho1 : o1 ∈ (sourceCarrier B atom z y k small R Br Bs st st').image (outer B))
    (ho2 : o2 ∈ (sourceCarrier B atom z y k small R Br Bs st st').image (outer B))
    (hc : C.color (packetC o1,o1.n2) = C.color (packetC o2,o2.n2)) :
    (packetC o1).Coprime o2.n2 ∧ (packetC o2).Coprime o1.n2 := by
  obtain ⟨s1, hs1, rfl⟩ := mem_image.mp ho1
  obtain ⟨s2, hs2, rfl⟩ := mem_image.mp ho2
  have h1 := source_packetC B atom z y k small R Br Bs st st' hs1
  have h2 := source_packetC B atom z y k small R Br Bs st st' hs2
  have ht1 : s1.1 ∈ B.carrier :=
    (mem_filter.mp (mem_product.mp (mem_filter.mp hs1).1).1).1
  have ht2 : s2.1 ∈ B.carrier :=
    (mem_filter.mp (mem_product.mp (mem_filter.mp hs2).1).1).1
  rw [h1, h2] at hc ⊢
  exact C.cross s1.1 ht1 s2.1 ht2 hc

end ImbalancedChen.Part3.OriginalReciprocalMaskSeparation20261102
