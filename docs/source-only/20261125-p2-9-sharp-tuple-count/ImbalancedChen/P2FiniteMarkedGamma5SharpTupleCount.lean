import ImbalancedChen.P2FiniteMarkedGamma5SharpSourceInverse
import ImbalancedChen.P2FiniteMarkedGamma5ActualRadialAggregate
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.OfFn

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

The original bounded complete-prime-tuple carrier, restricted to a fixed
literal old word, the original sharp Gamma5 raw program and target-coprime
fresh primes, injects into the original badLabels/roughNumbers source.
The old rank is recovered from the fixed old word; the tail rank and
ordered tail are recovered from the decoded cofactor's canonical prime
factor list. Thus summing over the original bounded Split costs exactly
one, with no product-fibre multiplicity factor.

All old, fresh and tail coordinates remain in order. Empty old and tail
blocks and repeated tail primes are retained. No rank-admission premise
is promoted to an actual-source conclusion. This is the single-direction
sharp count dictionary, not the smooth-inner comparison, a transport of
history marks, a J identification or a prime-product licence.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5SharpTupleCount
noncomputable section
open Finset Real LiLiuPrereqBuchstab
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedBadGamma5ArithmeticGeometry (badLabels ordinaryBad)
open P2FiniteMarkedGamma5LogExtension (program raw)
open P2FiniteMarkedGamma5EulerWordBudget (slotEquiv)
open P2FiniteMarkedGamma5RadialNaturalMass (tupleValues tupleValues_injective)
open P2FiniteMarkedGamma5ActualRadialAggregate (Split admissibleSplit tuplePrefix tuplePrefix_length)
open P2FiniteMarkedGamma5SharpSourceInverse (raw_source_inverse)
open scoped Classical BigOperators

/-- Read the original fresh block through the existing slot equivalence. -/
def tupleFresh {k r : ℕ} (u : Fin (k + (2 + r)) → ℕ) (i : Fin 2) : ℕ :=
  u (slotEquiv k r (.inr (.inl i)))

/-- Read the original tail block without sorting or removing repetitions. -/
def tupleTail {k r : ℕ} (u : Fin (k + (2 + r)) → ℕ) (i : Fin r) : ℕ :=
  u (slotEquiv k r (.inr (.inr i)))

theorem tuple_list_decomposition {k r : ℕ} (u : Fin (k + (2 + r)) → ℕ) :
    List.ofFn u = tuplePrefix u ++ [tupleFresh u 0, tupleFresh u 1] ++
      List.ofFn (tupleTail u) := by
  have hpair : List.ofFn (tupleFresh u) = [tupleFresh u 0, tupleFresh u 1] := by
    simp only [List.ofFn_succ, List.ofFn_zero]
  calc
    List.ofFn u = tuplePrefix u ++
        (List.ofFn (tupleFresh u) ++ List.ofFn (tupleTail u)) := by
      rw [List.ofFn_add (n := k) (m := 2 + r) (f := u),
        List.ofFn_add (n := 2) (m := r)
          (f := fun i : Fin (2 + r) => u (Fin.natAdd k i))]
      rfl
    _ = _ := by rw [hpair, List.append_assoc]

abbrev Tuple (N : ℕ) (s : Split) :=
  Fin (s.1.val + (2 + s.2.val)) → Fin (2 * N + 1)

abbrev SharpAtom (N : ℕ) := Σ s : Split, Tuple N s

/-- This is a filter of the same bounded prime enumerator as the raw
selected-profile sums. Its old word and original raw gates are literal. -/
def sharpTuples (N : ℕ) (Q : ℝ) (w : List ℕ) (s : Split) :
    Finset (Tuple N s) :=
  (Part3.labelledPrimeTuples (s.1.val + (2 + s.2.val)) (2 * N)).filter fun v =>
    admissibleSplit s ∧
      w = tuplePrefix (tupleValues v) ∧
      (∀ i : Fin 2, (tupleFresh (tupleValues v) i).Coprime N) ∧
      ∀ g ∈ program s.2.val,
        raw N Q w.prod (tupleFresh (tupleValues v)) (tupleTail (tupleValues v)) g

theorem mem_sharpTuples {N : ℕ} {Q : ℝ} {w : List ℕ} {s : Split} {v : Tuple N s} :
    v ∈ sharpTuples N Q w s ↔
      (∀ i, (v i).val.Prime) ∧ admissibleSplit s ∧
        w = tuplePrefix (tupleValues v) ∧
        (∀ i : Fin 2, (tupleFresh (tupleValues v) i).Coprime N) ∧
        ∀ g ∈ program s.2.val,
          raw N Q w.prod (tupleFresh (tupleValues v)) (tupleTail (tupleValues v)) g := by
  simp only [sharpTuples, Part3.labelledPrimeTuples, mem_filter, mem_univ, true_and]

def sharpAtoms (N : ℕ) (Q : ℝ) (w : List ℕ) : Finset (SharpAtom N) :=
  (univ : Finset Split).sigma (sharpTuples N Q w)

/-- The target is just the original pair/cofactor source, written as a
dependent finite set so that its cardinal is literally ordinaryBad. -/
abbrev OriginalAtom := Σ _ : List ℕ, ℕ

def originalAtoms (N : ℕ) (Q : ℝ) (d : ℕ) : Finset OriginalAtom :=
  (badLabels N Q d).sigma fun l =>
    roughNumbers ((N : ℝ) / (d * l.prod : ℕ)) (cutoff Q d (227 / 50))

def decode {N : ℕ} (a : SharpAtom N) : OriginalAtom :=
  ⟨[tupleFresh (tupleValues a.2) 0, tupleFresh (tupleValues a.2) 1],
    (List.ofFn (tupleTail (tupleValues a.2))).prod⟩

private theorem decode_source_data {N : ℕ} {Q : ℝ} {w : List ℕ}
    {s : Split} {v : Tuple N s} (hd : 0 < w.prod)
    (hv : v ∈ sharpTuples N Q w s) :
    (decode ⟨s, v⟩).1 ∈ badLabels N Q w.prod ∧
      (decode ⟨s, v⟩).2 ∈ roughNumbers
        ((N : ℝ) / (w.prod * (decode ⟨s, v⟩).1.prod : ℕ))
        (cutoff Q w.prod (227 / 50)) ∧
      (decode ⟨s, v⟩).2.primeFactorsList = List.ofFn (tupleTail (tupleValues v)) := by
  obtain ⟨hprime, _, _, hcoprime, hraw⟩ := mem_sharpTuples.mp hv
  simpa only [decode] using
    (raw_source_inverse (qs := tupleFresh (tupleValues v))
      (rs := tupleTail (tupleValues v)) hd
      (fun i => ⟨hprime _, hcoprime i⟩) (fun i => hprime _) hraw)

theorem decode_mem {N : ℕ} {Q : ℝ} {w : List ℕ}
    (hd : 0 < w.prod) {a : SharpAtom N} (ha : a ∈ sharpAtoms N Q w) :
    decode a ∈ originalAtoms N Q w.prod := by
  rcases a with ⟨s, v⟩
  have hv : v ∈ sharpTuples N Q w s := (mem_sigma.mp ha).2
  have hsource := decode_source_data hd hv
  exact mem_sigma.mpr ⟨hsource.1, hsource.2.1⟩

/-- No injection of the complete-product map is used. The pair is kept
as an ordered list, while the sorted prime tail is recovered from m.
The fixed old word and this canonical tail also recover both ranks. -/
theorem decode_injOn (N : ℕ) (Q : ℝ) (w : List ℕ) (hd : 0 < w.prod) :
    Set.InjOn (decode (N := N)) (sharpAtoms N Q w : Set (SharpAtom N)) := by
  rintro ⟨⟨k, r⟩, u⟩ hu ⟨⟨k', r'⟩, v⟩ hv he
  have hu' : u ∈ sharpTuples N Q w (k, r) := (mem_sigma.mp hu).2
  have hv' : v ∈ sharpTuples N Q w (k', r') := (mem_sigma.mp hv).2
  have hwu := (mem_sharpTuples.mp hu').2.2.1
  have hwv := (mem_sharpTuples.mp hv').2.2.1
  have hku : w.length = k.val := by rw [hwu, tuplePrefix_length]
  have hkv : w.length = k'.val := by rw [hwv, tuplePrefix_length]
  have hk : k = k' := Fin.ext (hku.symm.trans hkv)
  subst k'
  have hsu := (decode_source_data hd hu').2.2
  have hsv := (decode_source_data hd hv').2.2
  have hm : (decode ⟨(k, r), u⟩).2 = (decode ⟨(k, r'), v⟩).2 :=
    congrArg (fun a : OriginalAtom => a.2) he
  have hru : (decode ⟨(k, r), u⟩).2.primeFactorsList.length = r.val := by
    rw [hsu, List.length_ofFn]
  have hrv : (decode ⟨(k, r'), v⟩).2.primeFactorsList.length = r'.val := by
    rw [hsv, List.length_ofFn]
  have hr : r = r' := Fin.ext (by
    calc
      r.val = (decode ⟨(k, r), u⟩).2.primeFactorsList.length := hru.symm
      _ = (decode ⟨(k, r'), v⟩).2.primeFactorsList.length := by rw [hm]
      _ = r'.val := hrv)
  subst r'
  have hp :
      [tupleFresh (tupleValues u) 0, tupleFresh (tupleValues u) 1] =
        [tupleFresh (tupleValues v) 0, tupleFresh (tupleValues v) 1] :=
    congrArg (fun a : OriginalAtom => a.1) he
  have ht : List.ofFn (tupleTail (tupleValues u)) =
      List.ofFn (tupleTail (tupleValues v)) :=
    hsu.symm.trans ((congrArg Nat.primeFactorsList hm).trans hsv)
  have hw : tuplePrefix (tupleValues u) = tuplePrefix (tupleValues v) :=
    hwu.symm.trans hwv
  have hlist : List.ofFn (tupleValues u) = List.ofFn (tupleValues v) := by
    calc
      List.ofFn (tupleValues u) =
          tuplePrefix (tupleValues u) ++
            [tupleFresh (tupleValues u) 0, tupleFresh (tupleValues u) 1] ++
            List.ofFn (tupleTail (tupleValues u)) := tuple_list_decomposition _
      _ = tuplePrefix (tupleValues v) ++
            [tupleFresh (tupleValues v) 0, tupleFresh (tupleValues v) 1] ++
            List.ofFn (tupleTail (tupleValues v)) := by rw [hw, hp, ht]
      _ = List.ofFn (tupleValues v) := (tuple_list_decomposition _).symm
  have huv : u = v := tupleValues_injective N _ (List.ofFn_injective hlist)
  cases huv
  rfl

theorem originalAtoms_card (N : ℕ) (Q : ℝ) (d : ℕ) :
    ((originalAtoms N Q d).card : ℝ) = ordinaryBad N Q d := by
  simp only [originalAtoms, card_sigma, Nat.cast_sum, ordinaryBad]

theorem sharpAtoms_card (N : ℕ) (Q : ℝ) (w : List ℕ) :
    ((sharpAtoms N Q w).card : ℝ) =
      ∑ s : Split, ((sharpTuples N Q w s).card : ℝ) := by
  simp only [sharpAtoms, card_sigma, Nat.cast_sum]

/-- Single-direction transport into the original inclusive sharp source.
The coefficient is one, even after summing over every bounded split.
No target mass inequality, product-fibre bound or rank-admission theorem
is supplied as a hypothesis. -/
theorem sharp_count_le_ordinaryBad (N : ℕ) (Q : ℝ) (w : List ℕ)
    (hd : 0 < w.prod) :
    (∑ s : Split, ((sharpTuples N Q w s).card : ℝ)) ≤ ordinaryBad N Q w.prod := by
  have hcard : (sharpAtoms N Q w).card ≤ (originalAtoms N Q w.prod).card :=
    card_le_card_of_injOn (decode (N := N))
      (fun _ ha => decode_mem hd ha) (decode_injOn N Q w hd)
  have hreal : ((sharpAtoms N Q w).card : ℝ) ≤
      ((originalAtoms N Q w.prod).card : ℝ) := by exact_mod_cast hcard
  rw [sharpAtoms_card, originalAtoms_card] at hreal
  exact hreal

end
end ImbalancedChen.P2FiniteMarkedGamma5SharpTupleCount
