import ImbalancedChen.P5ActualLowerNormalizedHBSource
import ImbalancedChen.P5ActualHBPostModulusLogCutoff

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Finite reindexing of the literal ordered positive HB factor tuples.
The source is the existing factorTuples, not a supplied occurrence bank.
Equal values in different positions remain different coordinates.
-/
namespace ImbalancedChen.P5Z.OrderedFactorTupleRectangleReindex
noncomputable section
open Classical
open scoped BigOperators
open LiteralHeathBrownOccurrenceWords ActualRoughHeathBrownWords
open HBRightClosedDyadicRoles ActualHBDyadicOccurrenceFamily
open ActualHBDyadicProductWindow ActualHBPostModulusLogCutoff
open ImbalancedChen.Part3.OriginalProperPowerActualChart

def blockIntegers : Block → Finset ℕ
  | .unit => {1}
  | .dyadic j => Finset.Ioc (2^j) (2^(j+1))

def rectangle {m : ℕ} (bs : Fin m → Block) : Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun a => blockIntegers (bs a))

def blockVector (m : ℕ) (bs : List Block) : Fin m → Block :=
  fun a => bs.getD a.val .unit

theorem ofFn_blockVector {m : ℕ} {bs : List Block} (hb : bs.length = m) :
    List.ofFn (blockVector m bs) = bs := by
  apply List.ext_getElem
  · simp [hb]
  · intro i hi hj
    simp only [List.getElem_ofFn, blockVector]
    exact List.getD_eq_getElem _ _ hj

theorem mem_blockIntegers (b : Block) (n : ℕ) :
    n ∈ blockIntegers b ↔ Owns b n := by
  cases b <;> simp [blockIntegers, Owns]

theorem mem_rectangle {m : ℕ} (bs : Fin m → Block) (n : Fin m → ℕ) :
    n ∈ rectangle bs ↔ ∀ a, Owns (bs a) (n a) := by
  simp only [rectangle, Fintype.mem_piFinset, mem_blockIntegers]

theorem owns_pos {b : Block} {p : ℕ} (h : Owns b p) : 0 < p :=
  (lower_pos b).trans_le (owns_bounds h).1

private theorem forall₂_getD {α β : Type*} (R : α → β → Prop)
    (a : α) (b : β) {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) :
    ∀ i, i < xs.length → R (xs.getD i a) (ys.getD i b) := by
  induction h with
  | nil => intro i hi; simp at hi
  | cons hxy htail ih =>
    intro i hi
    cases i with
    | zero => simpa using hxy
    | succ i =>
      have hi' : i < _ := by simpa using hi
      simpa using ih i hi'

private theorem forall₂_of_getD {α β : Type*} (R : α → β → Prop)
    (a : α) (b : β) : ∀ (xs : List α) (ys : List β),
    xs.length = ys.length →
    (∀ i, i < xs.length → R (xs.getD i a) (ys.getD i b)) →
    List.Forall₂ R xs ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys hlen h
    have hy : ys = [] := List.length_eq_zero.mp hlen.symm
    subst ys
    exact List.Forall₂.nil
  | cons x xs ih =>
    intro ys hlen h
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      refine List.Forall₂.cons (by simpa using h 0 (by simp)) ?_
      apply ih ys (by simpa using hlen)
      intro i hi
      simpa using h (i+1) (by simpa using hi)

theorem owns_word_iff {m : ℕ} {bs : List Block} {fs : List ℕ}
    (hb : bs.length = m) (hf : fs.length = m) :
    List.Forall₂ Owns bs fs ↔
      ∀ a : Fin m, Owns (blockVector m bs a) (wordVector m fs a) := by
  constructor
  · intro h a
    exact forall₂_getD Owns .unit 0 h a.val (by omega)
  · intro h
    apply forall₂_of_getD Owns .unit 0 bs fs (hb.trans hf.symm)
    intro i hi
    exact h ⟨i, by omega⟩

@[simp] theorem wordVector_ofFn {m : ℕ} (n : Fin m → ℕ) :
    wordVector m (List.ofFn n) = n := by
  funext a
  simp [wordVector]

/-- Converse for the actual recursively constructed divisor-antidiagonal
carrier. This does not identify tuples by their product. -/
theorem factorTuples_mem {m n : ℕ} {fs : List ℕ}
    (hlen : fs.length = m) (hprod : fs.prod = n)
    (hpos : ∀ p ∈ fs, 0 < p) : fs ∈ factorTuples m n := by
  induction m generalizing n fs with
  | zero =>
    have hf : fs = [] := List.length_eq_zero.mp hlen
    subst fs
    have hn : n = 1 := by simpa using hprod.symm
    simp [factorTuples, hn]
  | succ m ih =>
    cases fs with
    | nil => simp at hlen
    | cons p fs =>
      have hp : 0 < p := hpos p (by simp)
      have ht : ∀ q ∈ fs, 0 < q := fun q hq =>
        hpos q (List.mem_cons_of_mem p hq)
      have hft : fs ∈ factorTuples m fs.prod :=
        ih (by simpa using hlen) rfl ht
      have hn : n ≠ 0 := by
        have h := List.prod_pos hpos
        rw [hprod] at h
        exact h.ne'
      apply Finset.mem_biUnion.mpr
      refine ⟨(p, fs.prod), Nat.mem_divisorsAntidiagonal.mpr ⟨?_, hn⟩, ?_⟩
      · simpa using hprod
      · exact Finset.mem_image.mpr ⟨fs, hft, rfl⟩

private theorem tupleFibres_disjoint (m cap : ℕ) :
    Set.PairwiseDisjoint (Finset.Icc 1 cap : Set ℕ) (factorTuples m) := by
  intro p hp q hq hpq
  apply Finset.disjoint_left.mpr
  intro fs hfp hfq
  exact hpq ((factorTuples_spec m p fs hfp).2.1.symm.trans
    (factorTuples_spec m q fs hfq).2.1)

/-- First reindex, with the original integer source cap still visible.
The only removed summands have zero assigned interval weight. -/
theorem sum_factorTuples_capped {m : ℕ} (cap : ℕ) (z y : ℝ)
    (rs : List Role) (bs : List Block) (hb : bs.length = m)
    (F : List ℕ → ℂ) :
    (∑ p ∈ Finset.Icc 1 cap, ∑ fs ∈ factorTuples m p,
      assignedWeight z y rs bs fs * F fs) =
    ∑ n ∈ (rectangle (blockVector m bs)).filter (fun n => completeProduct n ≤ cap),
      roughTupleWeight z y rs (List.ofFn n) * F (List.ofFn n) := by
  let S := (Finset.Icc 1 cap).biUnion (factorTuples m)
  have hS {fs : List ℕ} (hf : fs ∈ S) :
      fs.length = m ∧ fs.prod ≤ cap ∧ ∀ p ∈ fs, 0 < p := by
    obtain ⟨p, hp, hfp⟩ := Finset.mem_biUnion.mp hf
    obtain ⟨hlen, hprod, hpos⟩ := factorTuples_spec m p fs hfp
    exact ⟨hlen, by simpa only [hprod] using (Finset.mem_Icc.mp hp).2, hpos⟩
  calc
    _ = ∑ fs ∈ S, assignedWeight z y rs bs fs * F fs := by
      dsimp [S]
      rw [Finset.sum_biUnion (tupleFibres_disjoint m cap)]
    _ = ∑ fs ∈ S.filter (fun fs => List.Forall₂ Owns bs fs),
        assignedWeight z y rs bs fs * F fs := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro fs hf
      by_cases ho : List.Forall₂ Owns bs fs
      · simp only [if_pos ho]
      · have hz : assignedWeight z y rs bs fs = 0 := by
          by_contra hn
          exact ho (assigned_nonzero_owns rs bs fs hn)
        simp only [if_neg ho, hz, zero_mul]
    _ = _ := by
      apply Finset.sum_bij (fun fs hf => wordVector m fs)
      · intro fs hf
        obtain ⟨hfs, ho⟩ := Finset.mem_filter.mp hf
        obtain ⟨hlen, hprod, hpos⟩ := hS hfs
        apply Finset.mem_filter.mpr
        refine ⟨(mem_rectangle _ _).mpr ((owns_word_iff hb hlen).mp ho), ?_⟩
        simpa only [completeProduct, ← List.prod_ofFn, ofFn_wordVector hlen] using hprod
      · intro fs hf gs hg heq
        exact wordVector_injOn_length m (hS (Finset.mem_filter.mp hf).1).1
          (hS (Finset.mem_filter.mp hg).1).1 heq
      · intro n hn
        obtain ⟨hnrect, hncap⟩ := Finset.mem_filter.mp hn
        have hown : List.Forall₂ Owns bs (List.ofFn n) :=
          (owns_word_iff hb (List.length_ofFn n)).mpr
            (by simpa only [wordVector_ofFn] using (mem_rectangle _ _).mp hnrect)
        have hpos : ∀ p ∈ List.ofFn n, 0 < p := by
          intro p hp
          obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hp
          exact owns_pos ((mem_rectangle _ _).mp hnrect a)
        have hfp : List.ofFn n ∈ factorTuples m (completeProduct n) :=
          factorTuples_mem (List.length_ofFn n) (by simp [completeProduct]) hpos
        have hp : 1 ≤ completeProduct n := by
          have hh := List.prod_pos hpos
          simpa only [List.prod_ofFn, completeProduct] using hh
        refine ⟨List.ofFn n, Finset.mem_filter.mpr ⟨?_, hown⟩, wordVector_ofFn n⟩
        exact Finset.mem_biUnion.mpr ⟨completeProduct n,
          Finset.mem_Icc.mpr ⟨hp, hncap⟩, hfp⟩
      · intro fs hf
        obtain ⟨hfs, ho⟩ := Finset.mem_filter.mp hf
        rw [ofFn_wordVector (hS hfs).1, assigned_eq_rough_of_owns ho rs]

/-- The cap is removed only when the actual summand vanishes outside it.
The resulting arithmetic carrier is the FULL Cartesian rectangle. -/
theorem sum_factorTuples_rectangle {m : ℕ} (cap : ℕ) (z y : ℝ)
    (rs : List Role) (bs : List Block) (hb : bs.length = m)
    (F : List ℕ → ℂ)
    (hzero : ∀ n ∈ rectangle (blockVector m bs), cap < completeProduct n →
      F (List.ofFn n) = 0) :
    (∑ p ∈ Finset.Icc 1 cap, ∑ fs ∈ factorTuples m p,
      assignedWeight z y rs bs fs * F fs) =
      ∑ n ∈ rectangle (blockVector m bs),
        roughTupleWeight z y rs (List.ofFn n) * F (List.ofFn n) := by
  rw [sum_factorTuples_capped cap z y rs bs hb F, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hc : completeProduct n ≤ cap
  · simp only [if_pos hc]
  · simp only [if_neg hc, hzero n hn (lt_of_not_ge hc), mul_zero]

end
end ImbalancedChen.P5Z.OrderedFactorTupleRectangleReindex
