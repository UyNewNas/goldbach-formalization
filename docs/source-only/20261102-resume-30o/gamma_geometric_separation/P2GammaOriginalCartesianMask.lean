import ImbalancedChen.P2OriginalGammaDivisorNorm

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual original head/complement dictionary, before any analytic
separation.  The complement contains the old marked pair, every remaining
specified prime and the exact quotient (including 1).  The two remaining
head-dependent conditions are displayed, rather than silently erased.
-/

namespace ImbalancedChen.P2GammaOriginalCartesianMask
noncomputable section
open scoped Classical BigOperators
open Wu2008DoubleSieve P2TwentyOneUnsiftedArithmeticSource
open P2TwentyOneMaskedTailFloor P2OriginalU5WholeGroupCapacity
open P2OriginalGammaDivisorNorm
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2OriginalU5SmallPartnerRootPayment (rootQ smallCap)
open P5OriginalU5CausalFinite (pairSupport)

def rootWindow (N : ℕ) (t : ℕ × ℕ) : Finset ℕ :=
  primeWindow N
    (cutoff (rootQ N t) (t.1*t.2) (227/50))
    (cutoff (rootQ N t) (t.1*t.2) (11/5))

def rootColour (N : ℕ) (t : ℕ × ℕ) : ℕ → ℕ :=
  secondFunctionalMotherColour
    (cutoff (rootQ N t) (t.1*t.2) (353/100))
    (cutoff (rootQ N t) (t.1*t.2) (29/10))
    (cutoff (rootQ N t) (t.1*t.2) (61/25))

def headCarrier (N : ℕ) (t : ℕ × ℕ) (c : ℕ) : Finset ℕ :=
  (rootWindow N t).filter (fun p => rootColour N t p=c)

def rebuild (p : ℕ) (y : Label) : Label := (p::y.1,y.2)

theorem rebuild_product (d p : ℕ) (y : Label) :
    product d (rebuild p y)=product d y*p := by
  simp only [rebuild,product,List.prod_cons]
  ring

@[simp] theorem head_rebuild (p : ℕ) (y : Label) :
    labelHead (rebuild p y)=p := rfl

@[simp] theorem complement_rebuild (p : ℕ) (y : Label) :
    labelComplement (rebuild p y)=y := by cases y; rfl

theorem rebuild_head_complement {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    {x : Label} (hx : x∈rootLabels N t (c::cs)) :
    rebuild (labelHead x) (labelComplement x)=x := by
  have hlen := root_word_length hx
  rcases x with ⟨w,n⟩
  cases w with
  | nil => simp at hlen
  | cons p v => rfl

private theorem mem_words_iff (M : ℕ) (a b c e f : ℝ)
    (cs w : List ℕ) :
    w∈words M a b c e f cs ↔
      w.length=cs.length ∧ w.Pairwise (· < ·) ∧
      (∀ p∈w,p∈primeWindow M a f) ∧
      w.map (secondFunctionalMotherColour b c e)=cs := by
  simp only [words,Finset.mem_filter,secondFunctionalMother_tuple_mem]
  tauto

/-- The exact two coupled tests are strict head ordering and the complete
product ceiling.  The quotient roughness depends only on the complement.
This is a proved dictionary for the literal source, not a separation
assumption. -/
theorem rebuild_mem_absoluteGood_iff (N d M z p c : ℕ)
    (a b cc e f : ℝ) (cs : List ℕ) (y : Label) :
    rebuild p y∈absoluteGoodLabels N d M a b cc e f (c::cs) z ↔
      p∈primeWindow M a f ∧ secondFunctionalMotherColour b cc e p=c ∧
      y.1∈words M a b cc e f cs ∧ (∀ r∈y.1,p<r) ∧
      y.2∈Finset.range (N+1) ∧ 0<y.2 ∧ GoodTail z y ∧
      product d y*p<N := by
  simp only [absoluteGoodLabels,Finset.mem_filter,Finset.mem_product,
    mem_words_iff,rebuild_product,rebuild,List.length_cons,List.pairwise_cons,
    List.map_cons,List.cons.injEq,List.mem_cons,forall_eq_or_imp,
    Nat.add_right_cancel_iff,GoodTail]
  tauto

/-- Projecting the actual carrier preserves all tail data.  In
particular no independent rough-quotient hypothesis is introduced. -/
theorem complement_has_original_head {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    {y : Label} (hy : y∈rootComplementLabels N t (c::cs)) :
    ∃ p : ℕ,rebuild p y∈rootLabels N t (c::cs) := by
  obtain ⟨x,hx,hxy⟩ := Finset.mem_image.mp hy
  refine ⟨labelHead x,?_⟩
  change labelComplement x=y at hxy
  rw [← hxy,rebuild_head_complement hx]
  exact hx

theorem original_head_mem_carrier {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    {x : Label} (hx : x∈rootLabels N t (c::cs)) :
    labelHead x∈headCarrier N t c := by
  have hx' := hx
  rw [← rebuild_head_complement hx] at hx'
  change rebuild (labelHead x) (labelComplement x)∈
    absoluteGoodLabels N (t.1*t.2) N _ _ _ _ _ (c::cs) (smallCap N) at hx'
  obtain ⟨hp,hc,_⟩ := (rebuild_mem_absoluteGood_iff _ _ _ _ _ _ _ _ _ _ _ _ _).mp hx'
  exact Finset.mem_filter.mpr ⟨hp,hc⟩

theorem headCarrier_prime_and_target_deleted {N c p : ℕ} {t : ℕ × ℕ}
    (hp : p∈headCarrier N t c) : p.Prime ∧ p.Coprime N := by
  have h := mem_primeWindow.mp (Finset.mem_filter.mp hp).1
  exact ⟨h.1,h.2.1⟩

/-- An ambient head may be attached to the projected complement exactly
when the remaining two head-dependent geometric tests hold. -/
theorem rebuild_mem_root_iff {N c p : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (hp : p∈headCarrier N t c) {y : Label}
    (hy : y∈rootComplementLabels N t (c::cs)) :
    rebuild p y∈rootLabels N t (c::cs) ↔
      (∀ r∈y.1,p<r) ∧ product (t.1*t.2) y*p<N := by
  obtain ⟨p₀,hp₀⟩ := complement_has_original_head hy
  change rebuild p₀ y∈absoluteGoodLabels N (t.1*t.2) N _ _ _ _ _
    (c::cs) (smallCap N) at hp₀
  obtain ⟨_,_,hw,_,hn,hpos,hgood,_⟩ :=
    (rebuild_mem_absoluteGood_iff _ _ _ _ _ _ _ _ _ _ _ _ _).mp hp₀
  obtain ⟨hwin,hcolour⟩ := Finset.mem_filter.mp hp
  change rebuild p y∈absoluteGoodLabels N (t.1*t.2) N _ _ _ _ _
    (c::cs) (smallCap N) ↔ _
  rw [rebuild_mem_absoluteGood_iff]
  exact ⟨fun h => ⟨h.2.2.2.1,h.2.2.2.2.2.2.2⟩,
    fun h => ⟨hwin,hcolour,hw,h.1,hn,hpos,hgood,h.2⟩⟩

theorem complement_product_pos {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (ht : t∈pairSupport N) {y : Label}
    (hy : y∈rootComplementLabels N t (c::cs)) :
    0<product (t.1*t.2) y := by
  obtain ⟨p,hp⟩ := complement_has_original_head hy
  have hd := rootLabels_data hp
  have hw : 0<y.1.prod := by
    have hh := word_prod_pos hd.1
    change 0<p*y.1.prod at hh
    exact (Nat.mul_pos_iff.mp hh).2
  exact Nat.mul_pos
    (Nat.mul_pos (P2OriginalU5SmallPartnerRootPayment.pair_product_pos ht) hw) hd.2.1

theorem complement_contains_old_pair {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (ht : t∈pairSupport N) {y : Label}
    (hy : y∈rootComplementLabels N t (c::cs)) :
    t.1*t.2≤product (t.1*t.2) y := by
  have hpos := complement_product_pos ht hy
  exact Nat.le_of_dvd hpos ⟨y.1.prod*y.2,by simp only [product]; ring⟩

theorem original_two_factor_floors {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (hN : 2≤N) (ht : t∈pairSupport N) {x : Label}
    (hx : x∈rootLabels N t (c::cs)) :
    (N : ℝ)^(68/1135 : ℝ)≤(labelHead x : ℝ) ∧
      (N : ℝ)^(417/2500 : ℝ)≤
        (product (t.1*t.2) (labelComplement x) : ℝ) := by
  have hmem : labelHead x∈x.1 := by
    have hh := congrArg Prod.fst (rebuild_head_complement hx)
    rw [← hh]
    exact List.mem_cons_self _ _
  refine ⟨specified_prime_floor hN ht hx _ hmem,?_⟩
  apply (old_group_floor hN ht).trans
  exact_mod_cast complement_contains_old_pair ht
    (Finset.mem_image_of_mem (fun z : Label => (z.1.tail,z.2)) hx)

def pairCarrier (N : ℕ) (t : ℕ × ℕ) (c : ℕ) (cs : List ℕ) :
    Finset (ℕ × Label) :=
  (headCarrier N t c).product (rootComplementLabels N t (c::cs))

def legalPairs (N : ℕ) (t : ℕ × ℕ) (c : ℕ) (cs : List ℕ) :
    Finset (ℕ × Label) :=
  (pairCarrier N t c cs).filter (fun z => rebuild z.1 z.2∈rootLabels N t (c::cs))

/-- All original labels, including different labels with the same
complete product, are retained exactly once. -/
theorem original_word_test_eq_legalPairs
    (N : ℕ) (t : ℕ × ℕ) (c : ℕ) (cs : List ℕ)
    (W : ℕ → Label → ℂ) (F : ℕ → ℂ) :
    (∑ x∈rootLabels N t (c::cs),
      W (labelHead x) (labelComplement x)*F (product (t.1*t.2) x)) =
      ∑ z∈legalPairs N t c cs,W z.1 z.2*F (product (t.1*t.2) z.2*z.1) := by
  apply Finset.sum_bij (fun x _ => (labelHead x,labelComplement x))
  · intro x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨original_head_mem_carrier hx,?_⟩,?_⟩
    · exact Finset.mem_image_of_mem (fun z : Label => (z.1.tail,z.2)) hx
    · rw [rebuild_head_complement hx]
      exact hx
  · intro x hx y hy hxy
    have hh := congrArg (fun z : ℕ × Label => rebuild z.1 z.2) hxy
    simpa only [rebuild_head_complement hx,rebuild_head_complement hy] using hh
  · intro z hz
    have hzroot := (Finset.mem_filter.mp hz).2
    exact ⟨rebuild z.1 z.2,hzroot,by simp⟩
  · intro x hx
    rw [original_label_head_product (by simp) hx]

/-- The generic zero-extension step is private in spirit: the smooth
chart file proves its premise from numerical box endpoints, not from an
assumed source identity or discrepancy estimate. -/
theorem original_word_test_eq_cartesian
    (N : ℕ) (t : ℕ × ℕ) (c : ℕ) (cs : List ℕ)
    (W : ℕ → Label → ℂ) (F : ℕ → ℂ)
    (hzero : ∀ p∈headCarrier N t c,∀ y∈rootComplementLabels N t (c::cs),
      rebuild p y∉rootLabels N t (c::cs) → W p y=0) :
    (∑ x∈rootLabels N t (c::cs),
      W (labelHead x) (labelComplement x)*F (product (t.1*t.2) x)) =
      ∑ p∈headCarrier N t c,∑ y∈rootComplementLabels N t (c::cs),
        W p y*F (product (t.1*t.2) y*p) := by
  rw [original_word_test_eq_legalPairs]
  unfold legalPairs
  rw [Finset.sum_filter]
  have hs : (∑ z∈pairCarrier N t c cs,
      if rebuild z.1 z.2∈rootLabels N t (c::cs) then
        W z.1 z.2*F (product (t.1*t.2) z.2*z.1) else 0) =
      ∑ z∈pairCarrier N t c cs,W z.1 z.2*F (product (t.1*t.2) z.2*z.1) := by
    apply Finset.sum_congr rfl
    intro z hz
    obtain ⟨hp,hy⟩ := Finset.mem_product.mp hz
    by_cases h : rebuild z.1 z.2∈rootLabels N t (c::cs)
    · rw [if_pos h]
    · rw [if_neg h,hzero _ hp _ hy h,zero_mul]
  rw [hs]
  exact Finset.sum_product _ _ _

end
end ImbalancedChen.P2GammaOriginalCartesianMask
