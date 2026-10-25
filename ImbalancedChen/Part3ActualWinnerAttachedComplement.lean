import ImbalancedChen.Part3ActualSmallAttachmentSupport
import ImbalancedChen.ActualSelectedSubproductParameters

/-!
# Actual winning-pair complement squares with the same small attachment

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Rows 6 and 7 are the actual selected p0*p2 and p1*p2 branches.  Their
remaining-prime square is supplied by the genuine least-winning-row
whole-cell theorem.  All later complement squares are inherited from
the actual rough frontier.  The original small attachment is then added
as a distinguished complement block; its extra initial square is proved
using the literal pair ceiling 2*rho and the actual theta >= 1/2.

The final theorem starts from nonzero attachedUpperCoefficient and keeps
the same a, q, cap, rough state and selected pair.  No arbitrary mask,
selected-square gate, full-square support, or spectral supplier is an
input.  This covers the actual compact pair rows, not all W assignments
or the manuscript's separate full rank-six policy.
-/

namespace ImbalancedChen.Part3.ActualWinnerAttachedComplement

noncomputable section

open ActualAttachedRoughFrontier ActualCompactAllRankSupport ActualSmallAttachmentSupport
open VariableEnvelope

private theorem history_coordinates_of_shape {N : ℕ} {history tail : List ℕ}
    (p : Fin 3 → ℕ) (hshape : history.reverse = p 0 :: p 1 :: p 2 :: tail) :
    primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 history) =
      actualSelectedPrimeCoordinates (N : ℝ) p := by
  have hhistory : history = tail.reverse ++ [p 2, p 1, p 0] := by
    simpa [List.reverse_cons, List.append_assoc] using congrArg List.reverse hshape
  have hancestor : rosserAncestor 3 history = [p 2, p 1, p 0] := by
    rw [hhistory, rosserAncestor_append 3 tail.reverse [p 2, p 1, p 0] (by simp)]
    simp [rosserAncestor]
  rw [hancestor]
  funext i
  fin_cases i <;>
    simp [primeHistoryLogCoordinates, primeHistoryTuple, actualPrimeTupleLog,
      actualSelectedPrimeCoordinates]

private theorem pair_product_le_physical_ceiling {N : ℕ} (hN : (1 : ℝ) < N)
    (p : Fin 3 → ℕ) (hp : ∀ i, 0 < p i) (yz : Bool)
    {m : ℕ} {j : ActualExtendedThirdDyadicLabel m}
    (hs : actualSelectedPrimeCoordinates (N : ℝ) p ∈ actualExtendedThirdPhysicalCell m j) :
    (actualSelectedPairProduct yz p : ℝ) ≤ (N : ℝ) ^ (2 * thirdPrefixRho) := by
  have hpi (i : Fin 3) : (p i : ℝ) ≤ (N : ℝ) ^ thirdPrefixRho := by
    rw [← rpow_actualSelectedPrimeCoordinates (N : ℝ) hN p hp i]
    exact Real.rpow_le_rpow_of_exponent_le hN.le
      ((hs.1 i (Set.mem_univ _)).2.trans (actualExtendedThirdDyadic_bounds m j i).2.2)
  have hpow : (N : ℝ) ^ thirdPrefixRho * (N : ℝ) ^ thirdPrefixRho =
      (N : ℝ) ^ (2 * thirdPrefixRho) := by
    rw [← Real.rpow_add (zero_lt_one.trans hN)]
    congr 1
    ring
  cases yz <;>
    simp only [actualSelectedPairProduct, Bool.false_eq_true, if_false, if_true, Nat.cast_mul]
  · exact (mul_le_mul (hpi 0) (hpi 2) (Nat.cast_nonneg _)
      (Real.rpow_nonneg (zero_lt_one.trans hN).le _)).trans_eq hpow
  · exact (mul_le_mul (hpi 1) (hpi 2) (Nat.cast_nonneg _)
      (Real.rpow_nonneg (zero_lt_one.trans hN).le _)).trans_eq hpow

/-- The actual pair winner pays every complement square, including the
new initial small-block square, at the fixed representative's parameter.
The two original selected primes are unchanged at every later rank. -/
theorem actual_frontier_winner_attached_complement
    (e h epsilon : ℝ) (m N cap k : ℕ) (hkRank : 3 ≤ k)
    (w z : ℝ) (weight : ℕ → ℝ) (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k
      (actualExtendedThirdCompactUpperPolicy e h m N) weight [] true 1
      (roughPrimeUniverse N cap w z))
    (hN : 2 ≤ N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32) (heps : epsilon ≤ e / 128)
    (a : ℕ) (ha : (a : ℝ) ≤ (N : ℝ) ^ epsilon)
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (howned : primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 state.selectedPrefix) ∈
      actualExtendedThirdOwnedCell m j)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (yz : Bool) (hwinner : actualExtendedThirdLeastWinningIndex e m j = if yz then 7 else 6)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (hshape : state.selectedPrefix.reverse = p 0 :: p 1 :: p 2 :: tail) :
    let theta := actualExtendedThirdPairParameter e m j t yz
    let b := actualSelectedPairProduct yz p
    let rest := a :: actualSelectedPairRemainingPrime yz p :: tail
    b * rest.prod = a * state.selectedPrefix.prod ∧
      actualDwellSupport ((N : ℝ) ^ (theta - e / 32) / b) rest := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist k
    (actualExtendedThirdCompactUpperPolicy e h m N) weight
    (roughPrimeUniverse N cap w z) state hstate
  have hp (i : Fin 3) : 0 < p i := by
    have hmem : p i ∈ state.selectedPrefix.reverse := by
      rw [hshape]
      fin_cases i <;> simp
    exact (mem_roughPrimeUniverse_prime (hsub.subset hmem)).pos
  have hs : actualSelectedPrimeCoordinates (N : ℝ) p ∈ actualExtendedThirdPhysicalCell m j := by
    have hphys := actualExtendedThirdOwnedCell_subset_physicalCell m j howned
    rwa [history_coordinates_of_shape p hshape] at hphys
  have hsupport : actualDwellSupport ((N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j)
      (p 0 :: p 1 :: p 2 :: tail) := by
    rw [← hshape]
    exact actual_compact_frontier_all_rank_support e h m N cap k hkRank w z weight
      state hstate hj howned
  obtain ⟨hcover, hgate, _hlower, _hupper⟩ :=
    actualExtendedThirdSelectedPair_arithmeticInputs (κ := 0) (δ := e / 32)
      he0 he (by linarith) le_rfl hmesh hfull ht yz hwinner
      (N : ℝ) hNr p hp hs tail hsupport
  let theta := actualExtendedThirdPairParameter e m j t yz
  let b := actualSelectedPairProduct yz p
  let D := (N : ℝ) ^ (theta - 2 * (e / 32))
  let E := (N : ℝ) ^ (theta - e / 32)
  have hbpos : (0 : ℝ) < b := by
    dsimp [b]
    cases yz <;> simp only [actualSelectedPairProduct, Bool.false_eq_true, if_false, if_true]
    · exact_mod_cast Nat.mul_pos (hp 0) (hp 2)
    · exact_mod_cast Nat.mul_pos (hp 1) (hp 2)
  have hrest : actualDwellSupport (D / b) (actualSelectedPairRemainingPrime yz p :: tail) := by
    cases yz
    · apply actualDwell_selected_p1p3_budget (p 0) (p 1) (p 2) tail (hp 0) (hp 2) hcover
      simpa only [actualSelectedPairProduct, actualSelectedPairRemainingPrime,
        Bool.false_eq_true, if_false, Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using hgate.le
    · apply actualDwell_selected_p2p3_budget (p 0) (p 1) (p 2) tail (hp 1) (hp 2) hcover
      simpa only [actualSelectedPairProduct, actualSelectedPairRemainingPrime,
        if_true, Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using hgate.le
  have htheta : (1 / 2 : ℝ) ≤ theta :=
    (actualExtendedThirdSelectedPair_wholeCell he0 he hmesh hfull ht yz hwinner).1
  have hbceil := pair_product_le_physical_ceiling hNr p hp yz hs
  have hsmallgate : (b : ℝ) * (a : ℝ) ^ 2 ≤ E := by
    calc
      (b : ℝ) * (a : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 * thirdPrefixRho) * ((N : ℝ) ^ epsilon) ^ 2 :=
        mul_le_mul hbceil (pow_le_pow_left₀ (Nat.cast_nonneg a) ha 2)
          (sq_nonneg _) (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) ^ (2 * thirdPrefixRho + 2 * epsilon) := by
        rw [show 2 * epsilon = epsilon + epsilon by ring,
          Real.rpow_add hNpos, Real.rpow_add hNpos]
        ring
      _ ≤ E := by
        apply Real.rpow_le_rpow_of_exponent_le hNr.le
        change 2 * (19 / 96 : ℝ) + 2 * epsilon ≤ theta - e / 32
        linarith
  have hscale : (a : ℝ) * (D / b) ≤ E / b := by
    have hbound : (a : ℝ) * D ≤ E := by
      calc
        (a : ℝ) * D ≤ (N : ℝ) ^ epsilon * D :=
          mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hNpos.le _)
        _ = (N : ℝ) ^ (epsilon + (theta - 2 * (e / 32))) :=
          (Real.rpow_add hNpos _ _).symm
        _ ≤ E := Real.rpow_le_rpow_of_exponent_le hNr.le (by dsimp [E]; linarith)
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hbound hbpos.le
  have hattached := dwell_prepend_block a (actualSelectedPairRemainingPrime yz p :: tail)
    hrest ((le_div_iff₀ hbpos).mpr (by simpa only [mul_comm] using hsmallgate)) hscale
  refine ⟨?_, hattached⟩
  have hprod : state.selectedPrefix.prod = (p 0 :: p 1 :: p 2 :: tail).prod := by
    rw [← List.prod_reverse state.selectedPrefix, hshape]
  cases yz <;>
    simp only [actualSelectedPairProduct, actualSelectedPairRemainingPrime,
      Bool.false_eq_true, if_false, if_true, List.prod_cons, hprod] <;> ring

/-- Same-rho interface: the small block and rough frontier are extracted
from the literal nonzero coefficient before any cell or winning mask is
read.  For rows 6/7, every original complement square is then proved. -/
theorem actual_attached_ne_zero_winner_complement
    (e h epsilon : ℝ) (m N : ℕ) (cap : ℕ → ℕ)
    (hN : 2 ≤ N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32) (heps : epsilon ≤ e / 128)
    {q : ℕ}
    (hq : attachedUpperCoefficient 1 thirdPrefixRho epsilon
      (fun M => actualExtendedThirdCompactUpperPolicy e h m M false) cap N q ≠ 0) :
    ∃ a k (state : FirstExitDepthState ℕ),
      a ∈ actualSmallRosserSupport N (cap N) ((N : ℝ) ^ (epsilon ^ 2)) ∧
      (a : ℝ) < (N : ℝ) ^ epsilon ∧ state.selectedPrefix.length = k ∧
      state ∈ firstExitDepthFrontier k (actualExtendedThirdCompactUpperPolicy e h m N)
        (fun _ => 1) [] true 1
        (roughPrimeUniverse N (cap N) ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho)) ∧
      q = a * state.selectedPrefix.prod ∧
      ∀ j : ActualExtendedThirdDyadicLabel m, j ∈ actualExtendedThirdCompactCells e h m →
        3 ≤ k →
        primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 state.selectedPrefix) ∈
          actualExtendedThirdOwnedCell m j →
        actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e →
        ∀ t ∈ actualExtendedThirdPhysicalCell m j, ∀ yz : Bool,
          actualExtendedThirdLeastWinningIndex e m j = (if yz then 7 else 6) →
          ∀ (p : Fin 3 → ℕ) (tail : List ℕ),
            state.selectedPrefix.reverse = p 0 :: p 1 :: p 2 :: tail →
            let theta := actualExtendedThirdPairParameter e m j t yz
            let b := actualSelectedPairProduct yz p
            let rest := a :: actualSelectedPairRemainingPrime yz p :: tail
            b * rest.prod = q ∧ actualDwellSupport ((N : ℝ) ^ (theta - e / 32) / b) rest := by
  obtain ⟨a, k, state, ha, haL, hlen, hstate, hprod, _hbne, _hactive⟩ :=
    actual_attached_upper_ne_zero_frontier e h epsilon m N cap hq
  refine ⟨a, k, state, ha, haL, hlen, hstate, hprod, ?_⟩
  intro j hj hk howned hfull t ht yz hwinner p tail hshape
  obtain ⟨hidentity, hcomplement⟩ := actual_frontier_winner_attached_complement
    e h epsilon m N (cap N) k hk ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho)
    (fun _ => 1) state hstate hN he0 he hmesh heps a haL.le
    hj howned hfull ht yz hwinner p tail hshape
  exact ⟨hidentity.trans hprod.symm, hcomplement⟩

end

end ImbalancedChen.Part3.ActualWinnerAttachedComplement
