import ImbalancedChen.Part3ActualWResidualCompletion
import ImbalancedChen.ActualPrimeFineWordSlotRegrouping

/-!
# The W run on the original fine-label Cartesian atom

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The labels, atom and integer upper keys are the pre-existing
actualPrimeFineLabelFinset, actualPrimeSlotBox and
actualPrimeFineLabelIntegerUpper. Repeated labels retain distinct original
occurrences: no function from a label to its actual prime is used.

An actual retained representative supplies ALL key squares through exact
qscale conversion and the (k+1)*tau inflation budget. The allocation is
then computed on the frozen key word once. Every tuple of that original
atom has the same three label lists, its exact original full product, and
the key-product bounds. The literal initial key-capacity tests and late
key bound remain explicit geometry inputs, not an endpoint-support or
final-factorization supplier. Small attachment, W-close geometry and
analytic monomials are not asserted here.
-/

namespace ImbalancedChen.Part3.ActualWFineWordAdapter

noncomputable section

open scoped Classical
open ActualWThreeCapacityRun ActualWResidualCompletion ActualCompactAllRankSupport
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

private theorem slot_cons_mem {ι : Type*} (B : ι → Finset ℕ)
    {i : ι} {word : List ι} {q : ℕ} {qs : List ℕ}
    (hq : q ∈ B i) (hqs : qs ∈ actualPrimeSlotBox B word) :
    q :: qs ∈ actualPrimeSlotBox B (i :: word) :=
  Finset.mem_image.mpr ⟨(q, qs), Finset.mem_product.mpr ⟨hq, hqs⟩, rfl⟩

/-- Pair each original occurrence with its own prime, including repeated
interval labels with different prime values. -/
theorem atom_pairing {ι : Type*} (B : ι → Finset ℕ) (word : List ι)
    (ps : List ℕ) (hps : ps ∈ actualPrimeSlotBox B word) :
    ∃ paired : List (ι × ℕ), paired.map Prod.fst = word ∧
      paired.map Prod.snd = ps ∧ ∀ iq ∈ paired, iq.2 ∈ B iq.1 := by
  induction word generalizing ps with
  | nil =>
      have hp : ps = [] := by simpa [actualPrimeSlotBox] using hps
      subst ps
      exact ⟨[], rfl, rfl, by simp⟩
  | cons i word ih =>
      obtain ⟨⟨q, qs⟩, hmem, rfl⟩ := Finset.mem_image.mp hps
      obtain ⟨hq, hqs⟩ := Finset.mem_product.mp hmem
      obtain ⟨paired, hlabels, hvalues, hpair⟩ := ih qs hqs
      refine ⟨(i, q) :: paired, by simp [hlabels], by simp [hvalues], ?_⟩
      intro iq hiq
      rcases List.mem_cons.mp hiq with rfl | hiq
      · exact hq
      · exact hpair iq hiq

/-- The canonical integer key has the original multiplicative width. -/
theorem fine_key_inflation {N j q : ℕ} {sigma : ℝ} (hN : 0 < N)
    (hq : q ∈ actualPrimeFineLabelFinset N sigma j) :
    (actualPrimeFineLabelIntegerUpper N sigma j : ℝ) ≤ (N : ℝ) ^ sigma * q := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlo := (mem_actualPrimeFineLabelFinset.mp hq).2.2.1
  calc
    _ ≤ (N : ℝ) ^ (sigma * ((j : ℝ) + 1)) :=
      actualPrimeFineLabelIntegerUpper_le_power N j sigma
    _ = (N : ℝ) ^ sigma * (N : ℝ) ^ (sigma * j) := by
      rw [← Real.rpow_add hNr]
      congr 1
      ring
    _ ≤ (N : ℝ) ^ sigma * q :=
      mul_le_mul_of_nonneg_left hlo (Real.rpow_nonneg hNr.le _)

/-- Key support is derived from one ACTUAL retained representative in the
original atom.  The local scale and its full rank cost are explicit. -/
theorem actual_frontier_fine_word_support
    (e h : ℝ) (m N cap k : ℕ) (hk : 3 ≤ k) (w z : ℝ) (weight : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k
      (actualExtendedThirdCompactUpperPolicy e h m N) weight [] true 1
      (roughPrimeUniverse N cap w z))
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (howned : primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 state.selectedPrefix) ∈
      actualExtendedThirdOwnedCell m j)
    (sigma x tau theta : ℝ) (hN : 0 < N) (hx : 1 < x) (htau : 0 ≤ tau)
    (hscale : (N : ℝ) ^ sigma ≤ x ^ tau) (word : List ℕ)
    (hatom : state.selectedPrefix.reverse ∈
      actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) word)
    (hbudget : (Real.log (N : ℝ) / Real.log x) * actualExtendedThirdPhysicalLevel e m j +
      tau * (k + 1) ≤ theta) :
    PrefixSquareBound (fun label => (actualPrimeFineLabelIntegerUpper N sigma label : ℝ))
      (x ^ theta) word := by
  obtain ⟨paired, hlabels, hvalues, hpair⟩ :=
    atom_pairing (actualPrimeFineLabelFinset N sigma) word _ hatom
  have hlen : paired.length ≤ k := by
    have hh := congrArg List.length hvalues
    rw [List.length_map, List.length_reverse,
      firstExitDepthFrontier_selected_length k _ weight [] _ true 1 (by simp) state hstate] at hh
    exact hh.le
  have hsize (iq : ℕ × ℕ) (hiq : iq ∈ paired) :
      (actualPrimeFineLabelIntegerUpper N sigma iq.1 : ℝ) ≤ x ^ tau * iq.2 := by
    exact (fine_key_inflation hN (hpair iq hiq)).trans
      (mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg _))
  have hphysical : actualDwellSupport ((N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j)
      (paired.map Prod.snd) := by
    rw [hvalues]
    exact actual_compact_frontier_all_rank_support e h m N cap k hk w z weight
      state hstate hj howned
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hupper := ActualCompactInitialSupport.physical_support_upper_local
    (R := k) hNr hx htau Prod.snd
    (fun iq : ℕ × ℕ => actualPrimeFineLabelIntegerUpper N sigma iq.1)
    paired hlen hsize hphysical hbudget
  have hmap : paired.map (fun iq : ℕ × ℕ => actualPrimeFineLabelIntegerUpper N sigma iq.1) =
      word.map (actualPrimeFineLabelIntegerUpper N sigma) := by
    rw [← hlabels, List.map_map]
    rfl
  rw [hmap] at hupper
  intro i hi
  have hh := hupper i (by simpa using hi)
  simpa only [← List.map_take, List.map_map, List.getElem_map, Function.comp_def] using hh

def flatten {α : Type*} (g : Bins α) : List α := g.left ++ g.middle ++ g.right

private theorem putLeft_perm {α : Type*} (g : Bins α) (p : α) :
    (flatten (putLeft g p)).Perm (flatten g ++ [p]) := by
  simpa only [flatten, putLeft, List.append_assoc] using
    (List.perm_append_comm (l₁ := [p]) (l₂ := g.middle ++ g.right)).append_left g.left

private theorem putMiddle_perm {α : Type*} (g : Bins α) (p : α) :
    (flatten (putMiddle g p)).Perm (flatten g ++ [p]) := by
  simpa only [flatten, putMiddle, List.append_assoc] using
    (List.perm_append_comm (l₁ := [p]) (l₂ := g.right)).append_left (g.left ++ g.middle)

theorem trace_perm {α : Type*} {g out : Bins α} {xs : List α} (h : Trace g xs out) :
    (flatten out).Perm (flatten g ++ xs) := by
  induction h with
  | nil g => simp
  | @left g p xs out h ih =>
      exact ih.trans (by simpa only [List.append_assoc, List.singleton_append] using
        (putLeft_perm g p).append_right xs)
  | @middle g p xs out h ih =>
      exact ih.trans (by simpa only [List.append_assoc, List.singleton_append] using
        (putMiddle_perm g p).append_right xs)
  | @right g p xs out h ih =>
      simpa only [flatten, putRight, List.append_assoc, List.singleton_append] using ih

/-- Transport the actual tuple occurrences along a fixed label permutation.
This preserves distinct occurrences even when labels repeat. -/
theorem atom_perm {ι : Type*} (B : ι → Finset ℕ) {word word' : List ι}
    (hperm : word.Perm word') (ps : List ℕ) (hps : ps ∈ actualPrimeSlotBox B word) :
    ∃ qs ∈ actualPrimeSlotBox B word', qs.Perm ps := by
  induction hperm generalizing ps with
  | nil => exact ⟨ps, hps, List.Perm.refl _⟩
  | cons i hperm ih =>
      obtain ⟨⟨q, qs⟩, hmem, rfl⟩ := Finset.mem_image.mp hps
      obtain ⟨hq, hqs⟩ := Finset.mem_product.mp hmem
      obtain ⟨rs, hrs, hp⟩ := ih qs hqs
      exact ⟨q :: rs, slot_cons_mem B hq hrs, hp.cons q⟩
  | swap i j word =>
      obtain ⟨⟨q, qs⟩, hmem, rfl⟩ := Finset.mem_image.mp hps
      obtain ⟨hq, hqs⟩ := Finset.mem_product.mp hmem
      obtain ⟨⟨r, rs⟩, hmem', rfl⟩ := Finset.mem_image.mp hqs
      obtain ⟨hr, hrs⟩ := Finset.mem_product.mp hmem'
      exact ⟨r :: q :: rs, slot_cons_mem B hr (slot_cons_mem B hq hrs),
        List.Perm.swap _ _ _⟩
  | trans h₁ h₂ ih₁ ih₂ =>
      obtain ⟨qs, hqs, hp⟩ := ih₁ ps hps
      obtain ⟨rs, hrs, hp'⟩ := ih₂ qs hqs
      exact ⟨rs, hrs, hp'.trans hp⟩

theorem atom_append_split {ι : Type*} (B : ι → Finset ℕ)
    (left right : List ι) (ps : List ℕ)
    (hps : ps ∈ actualPrimeSlotBox B (left ++ right)) :
    ∃ ls rs, ls ∈ actualPrimeSlotBox B left ∧ rs ∈ actualPrimeSlotBox B right ∧ ps = ls ++ rs := by
  induction left generalizing ps with
  | nil => exact ⟨[], ps, by simp [actualPrimeSlotBox], hps, rfl⟩
  | cons i left ih =>
      obtain ⟨⟨q, qs⟩, hmem, rfl⟩ := Finset.mem_image.mp hps
      obtain ⟨hq, hqs⟩ := Finset.mem_product.mp hmem
      obtain ⟨ls, rs, hls, hrs, heq⟩ := ih qs hqs
      exact ⟨q :: ls, rs, slot_cons_mem B hq hls, hrs, by simp [heq]⟩

/-- Every tuple in the ORIGINAL atom uses the same three label lists.
Its full product is exact and each group obeys its fixed key product. -/
theorem whole_atom_same_bins (N : ℕ) (sigma : ℝ) {word : List ℕ} {g : Bins ℕ}
    (hperm : (flatten g).Perm word) :
    ∀ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) word,
      ∃ ls ms rs,
        ls ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) g.left ∧
        ms ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) g.middle ∧
        rs ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) g.right ∧
        ls.prod * ms.prod * rs.prod = ps.prod ∧
        (ls.prod : ℝ) ≤ wp (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) g.left ∧
        (ms.prod : ℝ) ≤ wp (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) g.middle ∧
        (rs.prod : ℝ) ≤ wp (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) g.right := by
  intro ps hps
  obtain ⟨qs, hqs, hp⟩ := atom_perm (actualPrimeFineLabelFinset N sigma) hperm.symm ps hps
  obtain ⟨ls, rest, hls, hrest, heq⟩ := atom_append_split
    (actualPrimeFineLabelFinset N sigma) g.left (g.middle ++ g.right) qs
    (by simpa only [flatten, List.append_assoc] using hqs)
  obtain ⟨ms, rs, hms, hrs, hrestEq⟩ := atom_append_split
    (actualPrimeFineLabelFinset N sigma) g.middle g.right rest hrest
  have hbound (labels primes : List ℕ)
      (hprimes : primes ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) labels) :
      (primes.prod : ℝ) ≤ wp (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) labels := by
    have hh := actualPrimeSlotBox_prod_le_upper (actualPrimeFineLabelFinset N sigma)
      (actualPrimeFineLabelIntegerUpper N sigma) labels
      (fun _ _ _ hq => actualPrimeFineLabelFinset_le_integerUpper hq) primes hprimes
    have hr : (primes.prod : ℝ) ≤ ((labels.map (actualPrimeFineLabelIntegerUpper N sigma)).prod : ℝ) :=
      by exact_mod_cast hh
    simpa only [wp, ← actualNatList_cast_prod, List.map_map, Function.comp_def] using hr
  refine ⟨ls, ms, rs, hls, hms, hrs, ?_, hbound _ _ hls, hbound _ _ hms, hbound _ _ hrs⟩
  simpa only [heq, hrestEq, List.prod_append, mul_assoc] using hp.prod_eq

/-- First two ORIGINAL label occurrences, allocated using their canonical keys. -/
def fineInitial (N : ℕ) (sigma A : ℝ) (p : Fin 3 → ℕ) : Bins ℕ :=
  let ac := actualTwoCapacityGreedy
    (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) A [p 1]
  ⟨ac.1, [p 0], ac.2⟩

def fineSlots (N : ℕ) (sigma A B C : ℝ) (p : Fin 3 → ℕ) (tail : List ℕ) : Bins ℕ :=
  complete (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) A B C
    (fineInitial N sigma A p) (p 2 :: tail)

theorem fineInitial_perm (N : ℕ) (sigma A : ℝ) (p : Fin 3 → ℕ) :
    (flatten (fineInitial N sigma A p)).Perm [p 0, p 1] := by
  let ac := actualTwoCapacityGreedy
    (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) A [p 1]
  have hpart := actualTwoCapacityGreedy_partition
    (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) A [p 1]
  have hmove : (ac.1 ++ [p 0] ++ ac.2).Perm ([p 0] ++ (ac.1 ++ ac.2)) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm (l₁ := ac.1) (l₂ := [p 0])).append_right ac.2
  exact hmove.trans (hpart.perm.append_left [p 0])

/-- The numerical endpoint run instantiated on the actual fine word.
The complete key square hypothesis is an internal intermediate; the final
retained-frontier consumer below supplies it from source support. -/
theorem fineSlots_correct (N : ℕ) (sigma : ℝ) {A B C U D : ℝ}
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (hA : 1 ≤ A) (hC : 1 ≤ C)
    (hkeypos : ∀ l ∈ p 0 :: p 1 :: p 2 :: tail,
      0 < (actualPrimeFineLabelIntegerUpper N sigma l : ℝ))
    (hfirst : (actualPrimeFineLabelIntegerUpper N sigma (p 0) : ℝ) ≤ B)
    (hsecond : (actualPrimeFineLabelIntegerUpper N sigma (p 1) : ℝ) ^ 2 ≤ A * C)
    (hlate : ∀ l ∈ p 2 :: tail, (actualPrimeFineLabelIntegerUpper N sigma l : ℝ) ≤ U)
    (hfull : PrefixSquareBound (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) D
      (p 0 :: p 1 :: p 2 :: tail)) :
    let out := fineSlots N sigma A B C p tail
    (flatten out).Perm (p 0 :: p 1 :: p 2 :: tail) ∧
      (Bounded (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) A B C out ∨
        (B < wp (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) out.middle ∧
          wp (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) out.middle ≤ B * U ∧
          wp (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) out.left ≤ A ∧
          wp (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) out.right ≤
            D / (A * wp (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)) out.middle))) := by
  let key := fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)
  have hsingle : PrefixSquareBound key (A * C) [p 1] := by
    intro i hi
    have hi0 : i = 0 := by simp only [List.length_singleton] at hi; omega
    subst i
    simpa using hsecond
  obtain ⟨hpart, hleft, hright⟩ := actualTwoCapacityGreedy_correct key hA hC [p 1] hsingle
  have hinit : Bounded key A B C (fineInitial N sigma A p) :=
    ⟨hleft, by simpa [fineInitial, wp] using hfirst, hright⟩
  have hpositive : Positive key (fineInitial N sigma A p) := by
    have h0 := hkeypos (p 0) (by simp)
    have h1 := hkeypos (p 1) (by simp)
    by_cases hf : (actualPrimeFineLabelIntegerUpper N sigma (p 1) : ℝ) ≤ A
    · simpa [Positive, fineInitial, actualTwoCapacityGreedy, actualTwoCapacityStep,
        wp, key, hf] using And.intro h1 (And.intro h0 (by norm_num : (0 : ℝ) < 1))
    · simpa [Positive, fineInitial, actualTwoCapacityGreedy, actualTwoCapacityStep,
        wp, key, hf] using And.intro (by norm_num : (0 : ℝ) < 1) (And.intro h0 h1)
  have hseed : total key (fineInitial N sigma A p) = wp key [p 0, p 1] := by
    have hh := (fineInitial_perm N sigma A p).map key |>.prod_eq
    simpa [flatten, total, wp, List.map_append, List.prod_append, mul_assoc] using hh
  obtain ⟨ht, hprod, hcases⟩ := complete_correct key (zero_lt_one.trans_le hA)
    hinit hpositive (fun l hl => ⟨hkeypos l (by simp only [List.mem_cons] at hl ⊢; tauto), hlate l hl⟩)
    hseed hfull
  refine ⟨?_, hcases⟩
  exact (trace_perm ht).trans ((fineInitial_perm N sigma A p).append_right (p 2 :: tail))

/-- Original retained atom consumer.  No endpoint-supported premise is
accepted: its entire key support is paid from the actual retained source.
The same fixed bins realize every tuple in the original atom, including
tuples with equal primes or repeated interval labels. -/
theorem actual_frontier_frozen_fine_word
    (e h : ℝ) (m N cap k : ℕ) (hk : 3 ≤ k) (w z : ℝ) (weight : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k
      (actualExtendedThirdCompactUpperPolicy e h m N) weight [] true 1
      (roughPrimeUniverse N cap w z))
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (howned : primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 state.selectedPrefix) ∈
      actualExtendedThirdOwnedCell m j)
    (sigma x tau theta : ℝ) (hN : 0 < N) (hx : 1 < x) (htau : 0 ≤ tau)
    (hscale : (N : ℝ) ^ sigma ≤ x ^ tau) (p : Fin 3 → ℕ) (tail : List ℕ)
    (hatom : state.selectedPrefix.reverse ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N sigma) (p 0 :: p 1 :: p 2 :: tail))
    (hbudget : (Real.log (N : ℝ) / Real.log x) * actualExtendedThirdPhysicalLevel e m j +
      tau * (k + 1) ≤ theta)
    {A B C U : ℝ} (hA : 1 ≤ A) (hC : 1 ≤ C)
    (hfirst : (actualPrimeFineLabelIntegerUpper N sigma (p 0) : ℝ) ≤ B)
    (hsecond : (actualPrimeFineLabelIntegerUpper N sigma (p 1) : ℝ) ^ 2 ≤ A * C)
    (hlate : ∀ l ∈ p 2 :: tail, (actualPrimeFineLabelIntegerUpper N sigma l : ℝ) ≤ U) :
    let key := fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)
    let out := fineSlots N sigma A B C p tail
    (flatten out).Perm (p 0 :: p 1 :: p 2 :: tail) ∧
      (Bounded key A B C out ∨
        (B < wp key out.middle ∧ wp key out.middle ≤ B * U ∧
          wp key out.left ≤ A ∧ wp key out.right ≤ (x ^ theta) / (A * wp key out.middle))) ∧
      ∀ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) (p 0 :: p 1 :: p 2 :: tail),
        ∃ ls ms rs,
          ls ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.left ∧
          ms ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.middle ∧
          rs ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.right ∧
          ls.prod * ms.prod * rs.prod = ps.prod ∧
          (ls.prod : ℝ) ≤ wp key out.left ∧ (ms.prod : ℝ) ≤ wp key out.middle ∧
          (rs.prod : ℝ) ≤ wp key out.right := by
  have hsupport := actual_frontier_fine_word_support e h m N cap k hk w z weight state hstate
    hj howned sigma x tau theta hN hx htau hscale (p 0 :: p 1 :: p 2 :: tail) hatom hbudget
  obtain ⟨paired, hlabels, hvalues, hpair⟩ := atom_pairing
    (actualPrimeFineLabelFinset N sigma) (p 0 :: p 1 :: p 2 :: tail) _ hatom
  have hkeypos : ∀ l ∈ p 0 :: p 1 :: p 2 :: tail,
      0 < (actualPrimeFineLabelIntegerUpper N sigma l : ℝ) := by
    intro l hl
    have hl' : l ∈ paired.map Prod.fst := by rwa [hlabels]
    obtain ⟨iq, hiq, rfl⟩ := List.mem_map.mp hl'
    have hq := hpair iq hiq
    have hh : 0 < actualPrimeFineLabelIntegerUpper N sigma iq.1 :=
      (mem_actualPrimeFineLabelFinset.mp hq).1.pos.trans_le
        (actualPrimeFineLabelFinset_le_integerUpper hq)
    exact_mod_cast hh
  obtain ⟨hperm, hcases⟩ := fineSlots_correct N sigma p tail hA hC hkeypos
    hfirst hsecond hlate hsupport
  exact ⟨hperm, hcases, whole_atom_same_bins N sigma hperm⟩

end

end ImbalancedChen.Part3.ActualWFineWordAdapter
