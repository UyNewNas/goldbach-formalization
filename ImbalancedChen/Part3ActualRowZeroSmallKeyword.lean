import ImbalancedChen.Part3ActualWSmallThirdAttachment

/-!
# Actual row-zero first-prefix atom with the same small Rosser factor

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Row zero is the literal leading-singleton tent, not an arbitrary mask.
The least-winner theorem supplies its pointwise tent; original retained
support pays the whole fine-key word. The selected-capacity and full-word
repair branches use the existing deterministic closeSlots program, whose
definition itself does not depend on a W winner. Both physical monomial
cases use the original A<=N^(1/3). The small factor extracted from the
same nonzero rho is placed only on group 3 with delta=e/128 remaining.

Rows 2/3, rows 6/7, analytic local alpha/theta perturbation and the full
signed tensor license are not claimed by this row-zero theorem.
-/

namespace ImbalancedChen.Part3.ActualRowZeroSmallKeyword

noncomputable section

open ActualWThreeCapacityRun ActualWResidualCompletion ActualWFineWordAdapter
open ActualWCloseFineHead ActualWCloseFullRepair ActualWCloseSameKeyMonomials
open ActualWSameKeyMonomials ActualWSmallThirdAttachment ActualAttachedRoughFrontier
open VariableEnvelope
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

/-- A genuine leading tent with reserve pays the canonical first key. -/
theorem fine_head_bounds_of_tent {N : ℕ} {e sigma theta : ℝ}
    (hN : 1 < N) (he : 0 < e) (hsigma : sigma ≤ e / 64)
    (p : Fin 3 → ℕ) (hp : ∀ i, 0 < p i) (label : ℕ)
    (hlabel : p 0 ∈ actualPrimeFineLabelFinset N sigma label)
    (htent : theta + e / 2 ≤ v (actualSelectedPrimeCoordinates (N : ℝ) p 0)) :
    (N : ℝ) ^ (2 * theta - 1 + e) ≤ (actualPrimeFineLabelIntegerUpper N sigma label : ℝ) ∧
      (actualPrimeFineLabelIntegerUpper N sigma label : ℝ) ≤
        (N : ℝ) ^ (actualSelectedSubproductUpper 1 theta - e / 4) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNr
  simp only [v, A, C, le_min_iff] at htent
  obtain ⟨hline0, hline1, hline2⟩ := htent
  have hlow : (N : ℝ) ^ (2 * theta - 1 + e) ≤ (p 0 : ℝ) := by
    rw [← rpow_actualSelectedPrimeCoordinates (N : ℝ) hNr p hp 0]
    exact Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith)
  have hlogupper : actualSelectedPrimeCoordinates (N : ℝ) p 0 + e / 3 ≤
      actualSelectedSubproductUpper 1 theta := by
    unfold actualSelectedSubproductUpper
    apply le_min <;> linarith
  have hupper : (p 0 : ℝ) ≤ (N : ℝ) ^ (actualSelectedSubproductUpper 1 theta - e / 3) := by
    rw [← rpow_actualSelectedPrimeCoordinates (N : ℝ) hNr p hp 0]
    exact Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith)
  have hkeylow : (p 0 : ℝ) ≤ (actualPrimeFineLabelIntegerUpper N sigma label : ℝ) := by
    exact_mod_cast actualPrimeFineLabelFinset_le_integerUpper hlabel
  refine ⟨hlow.trans hkeylow, ?_⟩
  calc
    _ ≤ (N : ℝ) ^ sigma * p 0 := fine_key_inflation (Nat.zero_lt_of_lt hN) hlabel
    _ ≤ (N : ℝ) ^ sigma * (N : ℝ) ^ (actualSelectedSubproductUpper 1 theta - e / 3) :=
      mul_le_mul_of_nonneg_left hupper (Real.rpow_nonneg hNpos.le _)
    _ = (N : ℝ) ^ (sigma + (actualSelectedSubproductUpper 1 theta - e / 3)) :=
      (Real.rpow_add hNpos _ _).symm
    _ ≤ (N : ℝ) ^ (actualSelectedSubproductUpper 1 theta - e / 4) :=
      Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith)

private theorem atom_product_pos (N : ℕ) (sigma : ℝ) (word primes : List ℕ)
    (hprimes : primes ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) word) :
    (0 : ℝ) < primes.prod := by
  have hp := actualPrimeSlotBox_prime (actualPrimeFineLabelFinset N sigma) word
    (fun _ _ _ hq => (mem_actualPrimeFineLabelFinset.mp hq).1) primes hprimes
  have hh : 0 < primes.prod := List.prod_pos (fun q hq => (hp q hq).pos)
  exact_mod_cast hh

/-- Numerical consumer for the computed first-slot program. The actual
row-zero caller below derives its square and tent inputs from source.
The result holds on every original tuple, with repeated labels intact. -/
theorem head_program_atom_monomials (N : ℕ) (sigma e theta A : ℝ)
    (hN : 1 < N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (htheta0 : 1 / 2 ≤ theta) (htheta1 : theta ≤ 5 / 8)
    (label : ℕ) (rest representative : List ℕ)
    (hatom : representative ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) (label :: rest))
    (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    (hheadLower : (N : ℝ) ^ (2 * theta - 1 + e) ≤
      (actualPrimeFineLabelIntegerUpper N sigma label : ℝ))
    (hheadUpper : (actualPrimeFineLabelIntegerUpper N sigma label : ℝ) ≤
      (N : ℝ) ^ (actualSelectedSubproductUpper 1 theta - e / 4))
    (hsquares : PrefixSquareBound (fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ))
      ((N : ℝ) ^ (theta - e / 32)) (label :: rest)) :
    let out := closeSlots N sigma ((N : ℝ) ^ (theta - e / 32)) A label rest
    ∀ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) (label :: rest),
      ∃ ls ms rs,
        ls ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.left ∧
        ms ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.middle ∧
        rs ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.right ∧
        ls.prod * ms.prod * rs.prod = ps.prod ∧ (ls.prod : ℝ) ≤ A ∧
        Monomials (N : ℝ) (e / 64) A (ls.prod : ℝ) (ms.prod : ℝ) (rs.prod : ℝ) ∧
        ∀ (small : ℕ) (epsilon : ℝ), 0 < small → (small : ℝ) ≤ (N : ℝ) ^ epsilon → epsilon ≤ e / 128 →
          Monomials (N : ℝ) (e / 128) A (ls.prod : ℝ) (ms.prod : ℝ) (small * rs.prod : ℕ) ∧
          ∀ x : ℝ, 1 < x → LocalMonomials (N : ℝ) x (e / 128) A
            (ls.prod : ℝ) (ms.prod : ℝ) (small * rs.prod : ℕ) := by
  let key := fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)
  let out := closeSlots N sigma ((N : ℝ) ^ (theta - e / 32)) A label rest
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hkeypos : 0 < key label := (Real.rpow_pos_of_pos hNpos _).trans_le hheadLower
  have hDA := actual_close_repair_capacity hN he htheta0 hA hAupper
  obtain ⟨hperm, hleft, hcases⟩ := closeSlots_correct N sigma label rest hA hDA.le hkeypos hsquares
  have hwhole := whole_atom_same_bins N sigma hperm
  obtain ⟨ls0, ms0, rs0, hls0, hms0, hrs0, _, hL0, hM0, hR0⟩ := hwhole representative hatom
  have ha : 0 < wp key out.left := (atom_product_pos N sigma _ _ hls0).trans_le hL0
  have hb : 0 < wp key out.middle := (atom_product_pos N sigma _ _ hms0).trans_le hM0
  have hc : 0 < wp key out.right := (atom_product_pos N sigma _ _ hrs0).trans_le hR0
  have hdelta : 2 * (e / 64) = e / 32 := by ring
  have hheadCeiling : key label ≤ (N : ℝ) ^ actualSelectedSubproductUpper 1 theta :=
    hheadUpper.trans (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith))
  have hmono : Monomials (N : ℝ) (e / 64) A
      (wp key out.left) (wp key out.middle) (wp key out.right) := by
    rcases hcases with ⟨hC, hmiddle, hright⟩ | ⟨hsmall, hrightEmpty, hmiddleBound, hDAhead⟩
    · have hmid : wp key out.middle = key label := by rw [hmiddle]; simp [wp]
      have hblower : (N : ℝ) ^ (2 * theta - 1) ≤ wp key out.middle := by
        rw [hmid]
        exact (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith)).trans hheadLower
      have hbupper : wp key out.middle ≤ (N : ℝ) ^ actualSelectedSubproductUpper 1 theta := by
        rw [hmid]
        exact hheadCeiling
      have hproduct : A * wp key out.middle * wp key out.right ≤
          (N : ℝ) ^ (theta - 2 * (e / 64)) := by
        rw [← hmid] at hright
        have hh := (le_div_iff₀ (mul_pos hApos hb)).mp hright
        rw [hdelta]
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
      simpa only [Monomials, mul_one] using selectedPair_monomials (α := 1)
        hNr hApos ha hb hc hproduct hblower hbupper hleft
    · have hcOne : wp key out.right = 1 := by rw [hrightEmpty]; simp [wp]
      have hproduct : A * wp key out.middle ≤ (N : ℝ) ^ (theta - 2 * (e / 64)) := by
        have hh := (le_div_iff₀ hApos).mp hmiddleBound
        rw [hdelta]
        simpa only [mul_comm] using hh
      have hbupper : wp key out.middle ≤ (N : ℝ) ^ actualSelectedSubproductUpper 1 theta :=
        (hmiddleBound.trans hDAhead.le).trans hheadCeiling
      rw [hcOne]
      exact weak_medium_repair_monomials hNr (by linarith) htheta1
        hApos ha hb hAupper hleft hproduct hbupper
  intro ps hps
  obtain ⟨ls, ms, rs, hls, hms, hrs, hprod, hL, hM, hR⟩ := hwhole ps hps
  have hrough := monomials_downward hNpos hApos (atom_product_pos N sigma _ _ hls)
      (atom_product_pos N sigma _ _ hms) (atom_product_pos N sigma _ _ hrs)
      ha hb hc hL hM hR hmono
  refine ⟨ls, ms, rs, hls, hms, hrs, hprod, hL.trans hleft, hrough, ?_⟩
  intro small epsilon hsmall hsize heps
  have hspos : (0 : ℝ) < small := by exact_mod_cast hsmall
  have hm := third_attachment_monomials hNr hApos (atom_product_pos N sigma _ _ hls)
    (atom_product_pos N sigma _ _ hms) (atom_product_pos N sigma _ _ hrs)
    hspos hsize (by linarith : epsilon ≤ e / 64) hrough
  have hm' : Monomials (N : ℝ) (e / 128) A
      (ls.prod : ℝ) (ms.prod : ℝ) (small * rs.prod : ℕ) := by
    simpa only [show (e / 64) / 2 = e / 128 by ring, Nat.cast_mul] using hm
  exact ⟨hm', fun x hx => transport hNpos hx hm'⟩

private theorem coordinates_of_shape {N : ℕ} {history tail : List ℕ}
    (p : Fin 3 → ℕ) (hshape : history.reverse = p 0 :: p 1 :: p 2 :: tail) :
    primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 history) =
      actualSelectedPrimeCoordinates (N : ℝ) p := by
  have hh : history = tail.reverse ++ [p 2, p 1, p 0] := by
    simpa [List.reverse_cons, List.append_assoc] using congrArg List.reverse hshape
  rw [hh, rosserAncestor_append 3 tail.reverse [p 2, p 1, p 0] (by simp)]
  have hself : rosserAncestor 3 [p 2, p 1, p 0] = [p 2, p 1, p 0] := by simp [rosserAncestor]
  rw [hself]
  funext i
  fin_cases i <;> simp [primeHistoryLogCoordinates, primeHistoryTuple,
    actualPrimeTupleLog, actualSelectedPrimeCoordinates]

/-- Same nonzero attached coefficient, same a/state/q, actual row-zero
least winner, and deterministic original first-slot keyword allocation.
Both capacity branches are proved, and small a goes only to group 3. -/
theorem actual_attached_row_zero_same_keyword
    (e h sigma epsilon : ℝ) (m N : ℕ) (cap : ℕ → ℕ)
    (hN : 2 ≤ N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hsigma0 : 0 ≤ sigma) (hsigma : sigma ≤ e / 64) (heps : epsilon ≤ e / 128)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32) {q : ℕ}
    (hq : attachedUpperCoefficient 1 thirdPrefixRho epsilon
      (fun M => actualExtendedThirdCompactUpperPolicy e h m M false) cap N q ≠ 0) :
    ∃ small k (state : FirstExitDepthState ℕ),
      small ∈ actualSmallRosserSupport N (cap N) ((N : ℝ) ^ (epsilon ^ 2)) ∧
      (small : ℝ) < (N : ℝ) ^ epsilon ∧ state.selectedPrefix.length = k ∧
      state ∈ firstExitDepthFrontier k (actualExtendedThirdCompactUpperPolicy e h m N)
        (fun _ => 1) [] true 1
        (roughPrimeUniverse N (cap N) ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho)) ∧
      q = small * state.selectedPrefix.prod ∧
      ∀ j : ActualExtendedThirdDyadicLabel m, j ∈ actualExtendedThirdCompactCells e h m →
        3 ≤ k → sigma * (k + 1) ≤ e / 2 →
        primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 state.selectedPrefix) ∈
          actualExtendedThirdOwnedCell m j →
        actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e →
        actualExtendedThirdLeastWinningIndex e m j = 0 →
        ∀ (p : Fin 3 → ℕ) (primeTail : List ℕ),
          state.selectedPrefix.reverse = p 0 :: p 1 :: p 2 :: primeTail →
        ∀ (label : ℕ) (rest : List ℕ),
          state.selectedPrefix.reverse ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) (label :: rest) →
        ∀ A : ℝ, 1 ≤ A → A ≤ (N : ℝ) ^ (1 / 3 : ℝ) →
          let out := closeSlots N sigma ((N : ℝ) ^ (actualExtendedThirdBaseParameter e m j - e / 32))
            A label rest
          ∃ ls ms rs,
            ls ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.left ∧
            ms ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.middle ∧
            rs ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.right ∧
            ls.prod * ms.prod * (small * rs.prod) = q ∧ (ls.prod : ℝ) ≤ A ∧
            Monomials (N : ℝ) (e / 128) A (ls.prod : ℝ) (ms.prod : ℝ) (small * rs.prod : ℕ) ∧
            ∀ x : ℝ, 1 < x → LocalMonomials (N : ℝ) x (e / 128) A
              (ls.prod : ℝ) (ms.prod : ℝ) (small * rs.prod : ℕ) := by
  obtain ⟨small, k, state, hsmall, hsize, hlen, hstate, hqprod, hrough, hsupport⟩ :=
    actual_attached_upper_ne_zero_frontier e h epsilon m N cap hq
  have hNnat : 1 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hNnat
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hspos : (0 : ℝ) < small := by exact_mod_cast (Nat.pos_of_mem_divisors hsmall)
  refine ⟨small, k, state, hsmall, hsize, hlen, hstate, hqprod, ?_⟩
  intro j hj hk hwidth howned hfull hwinner p primeTail hshape label rest hatom A hA hAupper
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist k
    (actualExtendedThirdCompactUpperPolicy e h m N) (fun _ => 1)
    (roughPrimeUniverse N (cap N) ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho)) state hstate
  have hp (i : Fin 3) : 0 < p i := by
    have hm : p i ∈ state.selectedPrefix.reverse := by rw [hshape]; fin_cases i <;> simp
    exact (mem_roughPrimeUniverse_prime (hsub.subset hm)).pos
  have hs : actualSelectedPrimeCoordinates (N : ℝ) p ∈ actualExtendedThirdPhysicalCell m j := by
    have hh := actualExtendedThirdOwnedCell_subset_physicalCell m j howned
    rwa [coordinates_of_shape p hshape] at hh
  have hlabel : p 0 ∈ actualPrimeFineLabelFinset N sigma label := by
    rw [hshape] at hatom
    obtain ⟨⟨r, rs⟩, hmem, heq⟩ := Finset.mem_image.mp hatom
    rcases List.cons.inj heq with ⟨rfl, rfl⟩
    exact (Finset.mem_product.mp hmem).1
  have hpoint := actualExtendedThirdSelectedBase_pointwise (0 : Fin 6) hwinner hs
  have htent : actualExtendedThirdBaseParameter e m j + e / 2 ≤
      v (actualSelectedPrimeCoordinates (N : ℝ) p 0) := by
    have hh : actualExtendedThirdBaseParameter e m j + e ≤
        v (actualSelectedPrimeCoordinates (N : ℝ) p 0) := by
      simpa [actualExtendedThirdRobustBaseBranch] using hpoint
    linarith
  obtain ⟨hheadLower, hheadUpper⟩ := fine_head_bounds_of_tent hNnat he0 hsigma p hp label hlabel htent
  have htheta := actualExtendedThirdBaseParameter_range he0 he ⟨_, hs⟩ hfull
  have hlevel := actualExtendedThirdBaseParameter_above_level hfull
  have hbudget : (Real.log (N : ℝ) / Real.log (N : ℝ)) * actualExtendedThirdPhysicalLevel e m j +
      sigma * (k + 1) ≤ actualExtendedThirdBaseParameter e m j - e / 32 := by
    rw [div_self (Real.log_pos hNr).ne']
    linarith
  have hsquares := actual_frontier_fine_word_support e h m N (cap N) k hk
    ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho) (fun _ => 1) state hstate hj howned
    sigma (N : ℝ) sigma (actualExtendedThirdBaseParameter e m j - e / 32)
    (Nat.zero_lt_of_lt hNnat) hNr hsigma0 le_rfl (label :: rest) hatom hbudget
  have hwhole := head_program_atom_monomials N sigma e (actualExtendedThirdBaseParameter e m j) A
    hNnat he0 he htheta.1 htheta.2.le label rest state.selectedPrefix.reverse hatom hA hAupper
    hheadLower hheadUpper hsquares
  obtain ⟨ls, ms, rs, hls, hms, hrs, hprod, hleft, hmono, hattach⟩ := hwhole state.selectedPrefix.reverse hatom
  obtain ⟨hm', hlocal⟩ := hattach small epsilon (Nat.pos_of_mem_divisors hsmall) hsize.le heps
  refine ⟨ls, ms, rs, hls, hms, hrs, ?_, hleft, hm', hlocal⟩
  calc
    ls.prod * ms.prod * (small * rs.prod) = small * (ls.prod * ms.prod * rs.prod) := by ring
    _ = small * state.selectedPrefix.reverse.prod := by rw [hprod]
    _ = q := by rw [List.prod_reverse, ← hqprod]

end

end ImbalancedChen.Part3.ActualRowZeroSmallKeyword
