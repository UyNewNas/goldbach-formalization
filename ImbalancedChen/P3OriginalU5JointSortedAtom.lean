import ImbalancedChen.P3OriginalU5JointPrimeWallPayment
import ImbalancedChen.ActualFrozenSlotCoefficientRegrouping

/-! A joint original U5 fibre is exactly the decreasing squarefree part
of an independent prime-slot box. Exterior slots retain the actual marked
cutoffs, their coarse physical buckets and their fine labels. The remaining
slots use the actual target-deleted rough interval and their fine labels. -/

namespace ImbalancedChen.P3OriginalU5JointSortedAtom

noncomputable section
open scoped Classical BigOperators List
open P2PhysicalIncomingPrefixCells (CellCode exponentCode)
open P2LowerCapPlanIntegerRetention (coordinate)
open P2OriginalPairSourceReceiver (PairRange ceiling)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2LowerFiniteCellRounding (primeLabel label roughProduct_squarefree)
open P2LowerCanonicalRetainedTrace (canonical_subword_of_universe)
open P3OriginalU5CommonPhysicalRoot (rowAddress)
open P3OriginalU5JointCellCoefficient (Point carrier roughCarrier cell jointLabel coefficient coefficient_eq_of_same_label)
open P3OriginalU5JointPrimeWallPayment (word)
open private word_data from ImbalancedChen.P3OriginalU5JointPrimeWallPayment
open P5OriginalU5CausalFinite (cutoff smallCutoff pairSupport)

abbrev Slot (m : ℕ) := (CellCode m × ℤ) ⊕ ℤ

def outerCode (R : PairRange) (m N p : ℕ) : CellCode m :=
  exponentCode (R.epsilon : ℝ) (ceiling : ℝ) m (coordinate N p)

theorem rowAddress_eq_iff (R : PairRange) (m N : ℕ) (t u : ℕ × ℕ) :
    rowAddress R m N t = rowAddress R m N u ↔
      outerCode R m N t.2 = outerCode R m N u.2 ∧
      outerCode R m N t.1 = outerCode R m N u.1 := by
  constructor
  · intro h
    exact ⟨congrArg (fun c => (c (0 : Fin 5)).1) h, congrArg (fun c => (c (1 : Fin 5)).1) h⟩
  · rintro ⟨h₂,h₁⟩
    funext i
    fin_cases i
    · exact Prod.ext h₂ rfl
    · exact Prod.ext h₁ rfl
    · rfl
    · rfl
    · rfl

abbrev roughPrimes (N : ℕ) (epsilon : ℝ) :=
  roughPrimeUniverse N (Nat.ceil (cutoff N)) (smallCutoff N epsilon) (cutoff N)

def primeSet (R : PairRange) (m N : ℕ) (epsilon tau : ℝ) : Slot m → Finset ℕ
  | .inl (c,j) => (chenAdditivePrimeCarrier N).filter fun p =>
      cutoff N ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ (19/125 : ℝ) ∧
      outerCode R m N p = c ∧ primeLabel N tau p = j
  | .inr j => (roughPrimes N epsilon).toFinset.filter (fun p => primeLabel N tau p = j)

def slots (R : PairRange) (m N : ℕ) (tau : ℝ) (x : Point) : List (Slot m) :=
  .inl (outerCode R m N x.1.2, primeLabel N tau x.1.2) ::
    .inl (outerCode R m N x.1.1, primeLabel N tau x.1.1) ::
      (label N tau x.2).map Sum.inr

def sortedBox (R : PairRange) (m N : ℕ) (epsilon tau : ℝ) (x : Point) : Finset (List ℕ) :=
  (actualPrimeSlotBox (primeSet R m N epsilon tau) (slots R m N tau x)).filter List.SortedGT

theorem primeSet_disjoint (R : PairRange) (m N : ℕ) (epsilon tau : ℝ) {i j : Slot m}
    (hne : i ≠ j) : Disjoint (primeSet R m N epsilon tau i) (primeSet R m N epsilon tau j) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  cases i with
  | inl a =>
    obtain ⟨c,k⟩ := a
    obtain ⟨_,hlo,_,hc,hk⟩ := Finset.mem_filter.mp hp
    cases j with
    | inl a =>
      obtain ⟨c',k'⟩ := a
      obtain ⟨_,_,_,hc',hk'⟩ := Finset.mem_filter.mp hq
      exact hne (congrArg Sum.inl (Prod.ext (hc.symm.trans hc') (hk.symm.trans hk')))
    | inr k' =>
      exact (not_lt_of_ge hlo) (mem_roughPrimeUniverse_upper (List.mem_toFinset.mp (Finset.mem_filter.mp hq).1))
  | inr k =>
    obtain ⟨hrough,hk⟩ := Finset.mem_filter.mp hp
    cases j with
    | inl a =>
      obtain ⟨c',k'⟩ := a
      exact (not_lt_of_ge (Finset.mem_filter.mp hq).2.1)
        (mem_roughPrimeUniverse_upper (List.mem_toFinset.mp hrough))
    | inr k' =>
      exact hne (congrArg Sum.inr (hk.symm.trans (Finset.mem_filter.mp hq).2))

theorem primeSet_prime (R : PairRange) (m N : ℕ) (epsilon tau : ℝ) (i : Slot m)
    {p : ℕ} (hp : p ∈ primeSet R m N epsilon tau i) : Nat.Prime p := by
  cases i with
  | inl a =>
    obtain ⟨c,k⟩ := a
    exact (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1
  | inr k =>
    exact mem_roughPrimeUniverse_prime (List.mem_toFinset.mp (Finset.mem_filter.mp hp).1)

private theorem slot_cons_cases {ι : Type*} (B : ι → Finset ℕ) {i : ι} {is : List ι} {ps : List ℕ}
    (h : ps ∈ actualPrimeSlotBox B (i :: is)) :
    ∃ p ∈ B i, ∃ qs ∈ actualPrimeSlotBox B is, ps = p :: qs := by
  obtain ⟨⟨p,qs⟩, hmem, heq⟩ := Finset.mem_image.mp h
  obtain ⟨hp,hqs⟩ := Finset.mem_product.mp hmem
  exact ⟨p,hp,qs,hqs,heq.symm⟩

private theorem cons_mem_slot {ι : Type*} (B : ι → Finset ℕ) {i : ι} {is : List ι} {p : ℕ} {ps : List ℕ} :
    p :: ps ∈ actualPrimeSlotBox B (i :: is) ↔ p ∈ B i ∧ ps ∈ actualPrimeSlotBox B is := by
  constructor
  · intro h
    obtain ⟨q,hq,qs,hqs,heq⟩ := slot_cons_cases B h
    obtain ⟨rfl,rfl⟩ := List.cons.inj heq
    exact ⟨hq,hqs⟩
  · rintro ⟨hp,hps⟩
    exact Finset.mem_image.mpr ⟨(p,ps),Finset.mem_product.mpr ⟨hp,hps⟩,rfl⟩

private theorem rough_box_iff (R : PairRange) (m N : ℕ) (epsilon tau : ℝ) (js : List ℤ)
    (ps : List ℕ) :
    ps ∈ actualPrimeSlotBox (primeSet R m N epsilon tau) (js.map Sum.inr) ↔
      ps.map (primeLabel N tau) = js ∧ ∀ p ∈ ps, p ∈ roughPrimes N epsilon := by
  induction js generalizing ps with
  | nil =>
    cases ps <;> simp [actualPrimeSlotBox]
  | cons j js ih =>
    cases ps with
    | nil =>
      constructor
      · intro h
        obtain ⟨p,_,qs,_,he⟩ := slot_cons_cases _ h
        cases he
      · rintro ⟨he,_⟩
        cases he
    | cons p ps =>
      rw [List.map_cons, cons_mem_slot, ih]
      constructor
      · rintro ⟨hp,he,hs⟩
        obtain ⟨hb,hj⟩ := Finset.mem_filter.mp hp
        refine ⟨congrArg₂ List.cons hj he, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact List.mem_toFinset.mp hb
        · exact hs q hq
      · rintro ⟨hm,hs⟩
        obtain ⟨hj,he⟩ := List.cons.inj hm
        exact ⟨Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hs p (List.mem_cons_self ..)),hj⟩,
          he,fun q hq => hs q (List.mem_cons_of_mem _ hq)⟩

private theorem rough_product (N : ℕ) (epsilon : ℝ) (ps : List ℕ)
    (hs : ps.Pairwise (· > ·)) (hu : ∀ p ∈ ps, p ∈ roughPrimes N epsilon) :
    ps.prod ∈ roughCarrier N epsilon ∧ ps.prod.primeFactorsList.reverse = ps := by
  have hp := fun p h => mem_roughPrimeUniverse_prime (hu p h)
  have hnodup : ps.Nodup := hs.imp (fun h => ne_of_gt h)
  have h1 : (∏ p ∈ ps.toFinset, p) = ps.prod := by
    simpa using List.prod_toFinset (fun p : ℕ => p) hnodup
  have h2 : (∏ p ∈ (roughPrimes N epsilon).toFinset, p) = (roughPrimes N epsilon).prod := by
    simpa using List.prod_toFinset (fun p : ℕ => p) (roughPrimeUniverse_nodup N _ _ _)
  have hsub : ps.toFinset ⊆ (roughPrimes N epsilon).toFinset :=
    fun _ hm => List.mem_toFinset.mpr (hu _ (List.mem_toFinset.mp hm))
  have hdiv : ps.prod ∣ (roughPrimes N epsilon).prod := by
    rw [← h1, ← h2]
    exact Finset.prod_dvd_prod_of_subset _ _ id hsub
  have hperm := (Nat.primeFactorsList_unique (rfl : ps.prod = ps.prod) hp).trans
    (List.reverse_perm (Nat.primeFactorsList ps.prod)).symm
  exact ⟨Nat.mem_divisors.mpr ⟨hdiv,(roughProduct_squarefree N _ _ _).ne_zero⟩,
    (hperm.eq_of_pairwise' (hs.imp (fun h => h.le)) (Nat.primeFactorsList_sorted _).reverse.pairwise).symm⟩

/-- Both directions retain the original marked pair, all its cutoffs, and
the exact canonical residual divisor. The full Cartesian product is taken
first, and the strictly decreasing selector is displayed explicitly. -/
theorem cell_image_eq_sortedBox (R : PairRange) (m : ℕ) {N : ℕ} (hN : 2 ≤ N)
    {epsilon : ℝ} (he : 0 < epsilon) (he8 : epsilon < 1/8) (tau : ℝ) (x : Point) :
    (cell R m N epsilon tau x).image word = sortedBox R m N epsilon tau x := by
  ext ps
  constructor
  · intro hm
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hyc,heq⟩ := Finset.mem_filter.mp hy
    obtain ⟨hpair,hd⟩ := Finset.mem_product.mp hyc
    obtain ⟨hmk,hlo,h12,hhi⟩ := Finset.mem_filter.mp hpair
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp hmk
    have h12r : (y.1.1 : ℝ) < y.1.2 := by exact_mod_cast h12
    obtain ⟨hc₂,hc₁⟩ := (rowAddress_eq_iff R m N y.1 x.1).mp (congrArg Prod.fst heq)
    obtain ⟨hf₂,hh⟩ := List.cons.inj (congrArg Prod.snd heq)
    obtain ⟨hf₁,hrough⟩ := List.cons.inj hh
    refine Finset.mem_filter.mpr ⟨?_,List.sortedGT_iff_pairwise.mpr (word_data hN he he8 hyc).1⟩
    apply (cons_mem_slot _).mpr
    refine ⟨Finset.mem_filter.mpr ⟨hp₂,hlo.trans h12r.le,hhi,hc₂,hf₂⟩,?_⟩
    apply (cons_mem_slot _).mpr
    refine ⟨Finset.mem_filter.mpr ⟨hp₁,hlo,h12r.trans hhi,hc₁,hf₁⟩,?_⟩
    exact (rough_box_iff R m N epsilon tau _ _).mpr ⟨hrough,
      (canonical_subword_of_universe N _ _ _ hd).1.subset⟩
  · intro hm
    obtain ⟨hbox,hstrict⟩ := Finset.mem_filter.mp hm
    obtain ⟨p₂,hp₂,tail,htail,rfl⟩ := slot_cons_cases _ hbox
    obtain ⟨p₁,hp₁,qs,hqs,rfl⟩ := slot_cons_cases _ htail
    obtain ⟨hc₂,_,hhi,hcode₂,hf₂⟩ := Finset.mem_filter.mp hp₂
    obtain ⟨hc₁,hlo,_,hcode₁,hf₁⟩ := Finset.mem_filter.mp hp₁
    have horder := List.pairwise_cons.mp (List.sortedGT_iff_pairwise.mp hstrict)
    have horder' := List.pairwise_cons.mp horder.2
    have h12 : p₁ < p₂ := horder.1 p₁ (List.mem_cons_self ..)
    obtain ⟨hf,hu⟩ := (rough_box_iff R m N epsilon tau _ _).mp hqs
    obtain ⟨hd,hcan⟩ := rough_product N epsilon qs horder'.2 hu
    have ht : (p₁,p₂) ∈ pairSupport N :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc₁,hc₂⟩,hlo,h12,hhi⟩
    have hlabel : label N tau qs.prod = label N tau x.2 := by
      change qs.prod.primeFactorsList.reverse.map _ = _
      rw [hcan]
      exact hf
    refine Finset.mem_image.mpr ⟨((p₁,p₂),qs.prod),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ht,hd⟩,?_⟩,?_⟩
    · exact Prod.ext ((rowAddress_eq_iff R m N _ _).mpr ⟨hcode₂,hcode₁⟩)
        (congrArg₂ List.cons hf₂ (congrArg₂ List.cons hf₁ hlabel))
    · change p₂ :: p₁ :: qs.prod.primeFactorsList.reverse = p₂ :: p₁ :: qs
      rw [hcan]

private theorem word_injOn {N : ℕ} {epsilon : ℝ} {x y : Point}
    (hx : x ∈ carrier N epsilon) (hy : y ∈ carrier N epsilon) (h : word x = word y) : x = y := by
  obtain ⟨h₂,h'⟩ := List.cons.inj h
  obtain ⟨h₁,hrs⟩ := List.cons.inj h'
  have hp := congrArg List.prod hrs
  rw [(canonical_subword_of_universe N _ _ _ (Finset.mem_product.mp hx).2).2,
    (canonical_subword_of_universe N _ _ _ (Finset.mem_product.mp hy).2).2] at hp
  exact Prod.ext (Prod.ext h₁ h₂) hp

/-- Weighted equality at the same physical product for every test,
including an individual modulus fibre. The scalar is the actual signed
joint rough coefficient of the cell. -/
theorem cell_test_eq_sortedBox (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ)
    (m : ℕ) {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ} (he : 0 < epsilon)
    (he8 : epsilon < 1/8) (tau : ℝ) {x : Point} (hx : x ∈ carrier N epsilon) (F : ℕ → ℝ) :
    (∑ y ∈ cell R m N epsilon tau x,
      coefficient R bank b m N epsilon tau y * F ((y.1.1 * y.1.2) * y.2)) =
      ∑ ps ∈ sortedBox R m N epsilon tau x, coefficient R bank b m N epsilon tau x * F ps.prod := by
  rw [← cell_image_eq_sortedBox R m hN he he8 tau x, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro y hy
    obtain ⟨hyc,heq⟩ := Finset.mem_filter.mp hy
    rw [coefficient_eq_of_same_label R bank b m N epsilon tau hyc hx heq, (word_data hN he he8 hyc).2.2]
  · intro y hy z hz h
    exact word_injOn (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hz).1 h

end
end ImbalancedChen.P3OriginalU5JointSortedAtom
