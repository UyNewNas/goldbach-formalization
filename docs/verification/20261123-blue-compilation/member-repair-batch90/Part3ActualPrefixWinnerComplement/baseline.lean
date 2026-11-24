import ImbalancedChen.Part3ActualWinnerAttachedComplement

/-!
# Actual prefix-winning rows 0, 2 and 3 with the original small block

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The selected blocks are exactly p0, p0*p1 and p0*p1*p2.  Their original
complement squares follow by prefix cancellation.  The actual winning
row's tent, rather than an arbitrary-mask support assertion, bounds the
selected product and pays the extra small-block square.  The final
consumer keeps the small factor extracted from the literal nonzero rho.

This closes these three compact prefix branches.  Row 1 is excluded by
the pre-existing least-winner theorem; W gap assignments remain separate.
-/

namespace ImbalancedChen.Part3.ActualPrefixWinnerComplement

noncomputable section

open ActualAttachedRoughFrontier ActualCompactAllRankSupport ActualSmallAttachmentSupport
open VariableEnvelope

def prefixRow (r : Fin 3) : Fin 6 := ![0, 2, 3] r

def prefixSum (r : Fin 3) (s : Fin 3 → ℝ) : ℝ :=
  ![s 0, s 0 + s 1, s 0 + s 1 + s 2] r

def prefixFront (r : Fin 3) (p : Fin 3 → ℕ) : List ℕ :=
  ![[p 0], [p 0, p 1], [p 0, p 1, p 2]] r

def prefixRest (r : Fin 3) (p : Fin 3 → ℕ) (tail : List ℕ) : List ℕ :=
  ![p 1 :: p 2 :: tail, p 2 :: tail, tail] r

theorem prefix_split (r : Fin 3) (p : Fin 3 → ℕ) (tail : List ℕ) :
    prefixFront r p ++ prefixRest r p tail = p 0 :: p 1 :: p 2 :: tail := by
  fin_cases r <;> rfl

private theorem prefix_product_power {N : ℝ} (hN : 1 < N)
    (r : Fin 3) (p : Fin 3 → ℕ) (hp : ∀ i, 0 < p i) :
    N ^ prefixSum r (actualSelectedPrimeCoordinates N p) = ((prefixFront r p).prod : ℝ) := by
  fin_cases r <;>
    simp [prefixSum, prefixFront, Real.rpow_add (zero_lt_one.trans hN),
      rpow_actualSelectedPrimeCoordinates N hN p hp, Nat.cast_mul, mul_assoc]

private theorem original_coordinates {N : ℕ} {history tail : List ℕ}
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

/-- An explicit elementary attachment loss after a selected block.  The
real branch consumer below proves both the selected-product ceiling and
the complete original complement support from its actual winner. -/
theorem selected_complement_attach_small {N e epsilon theta : ℝ}
    (hN : 1 < N) (he0 : 0 ≤ e) (he : e ≤ 1 / 384) (heps : epsilon ≤ e / 128)
    (htheta : 1 / 2 ≤ theta) (a b : ℕ) (hb : 0 < b)
    (ha : (a : ℝ) ≤ N ^ epsilon) (hbceil : (b : ℝ) ≤ N ^ (2 / 5 : ℝ))
    (rest : List ℕ) (hrest : actualDwellSupport (N ^ (theta - e / 16) / b) rest) :
    actualDwellSupport (N ^ (theta - e / 32) / b) (a :: rest) := by
  have hNpos : 0 < N := zero_lt_one.trans hN
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  apply dwell_prepend_block a rest hrest
  · apply (le_div_iff₀ hbpos).mpr
    calc
      (a : ℝ) ^ 2 * b ≤ (N ^ epsilon) ^ 2 * N ^ (2 / 5 : ℝ) :=
        mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg a) ha 2) hbceil
          (Nat.cast_nonneg b) (sq_nonneg _)
      _ = N ^ (2 * epsilon + 2 / 5) := by
        rw [show 2 * epsilon = epsilon + epsilon by ring,
          Real.rpow_add hNpos, Real.rpow_add hNpos]
        ring
      _ ≤ N ^ (theta - e / 32) :=
        Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
  · have hs : (a : ℝ) * N ^ (theta - e / 16) ≤ N ^ (theta - e / 32) := by
      calc
        (a : ℝ) * N ^ (theta - e / 16) ≤ N ^ epsilon * N ^ (theta - e / 16) :=
          mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hNpos.le _)
        _ = N ^ (epsilon + (theta - e / 16)) := (Real.rpow_add hNpos _ _).symm
        _ ≤ N ^ (theta - e / 32) :=
          Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hs hbpos.le

/-- Every actual prefix-winning row supplies its own selected complement.
The critical small-block initial square is paid by the real prefix tent.
No selected-square gate or full support is an input. -/
theorem actual_frontier_prefix_winner_complement
    (e h epsilon : ℝ) (m N cap k : ℕ) (hk : 3 ≤ k) (w z : ℝ) (weight : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k (actualExtendedThirdCompactUpperPolicy e h m N)
      weight [] true 1 (roughPrimeUniverse N cap w z))
    (hN : 2 ≤ N) (he0 : 0 < e) (he : e ≤ 1 / 384) (heps : epsilon ≤ e / 128)
    (a : ℕ) (ha : (a : ℝ) ≤ (N : ℝ) ^ epsilon)
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (howned : primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 state.selectedPrefix) ∈
      actualExtendedThirdOwnedCell m j)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    (r : Fin 3)
    (hwinner : actualExtendedThirdLeastWinningIndex e m j = Fin.castLE (by decide : 6 ≤ 8) (prefixRow r))
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (hshape : state.selectedPrefix.reverse = p 0 :: p 1 :: p 2 :: tail) :
    let b := (prefixFront r p).prod
    b * (a :: prefixRest r p tail).prod = a * state.selectedPrefix.prod ∧
      actualDwellSupport ((N : ℝ) ^ (actualExtendedThirdBaseParameter e m j - e / 32) / b)
        (a :: prefixRest r p tail) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist k
    (actualExtendedThirdCompactUpperPolicy e h m N) weight (roughPrimeUniverse N cap w z) state hstate
  have hp (i : Fin 3) : 0 < p i := by
    have hm : p i ∈ state.selectedPrefix.reverse := by rw [hshape]; fin_cases i <;> simp
    exact (mem_roughPrimeUniverse_prime (hsub.subset hm)).pos
  have hs : actualSelectedPrimeCoordinates (N : ℝ) p ∈ actualExtendedThirdPhysicalCell m j := by
    have hc := actualExtendedThirdOwnedCell_subset_physicalCell m j howned
    rwa [original_coordinates p hshape] at hc
  have htheta := (actualExtendedThirdBaseParameter_range he0 he ⟨_, hs⟩ hfull).1
  have hlevel := actualExtendedThirdBaseParameter_above_level hfull
  have hpoint := actualExtendedThirdSelectedBase_pointwise (prefixRow r) hwinner hs
  have htent : actualExtendedThirdBaseParameter e m j + e ≤
      v (prefixSum r (actualSelectedPrimeCoordinates (N : ℝ) p)) := by
    fin_cases r <;> simpa [prefixRow, prefixSum, actualExtendedThirdRobustBaseBranch] using hpoint
  have hC := htent.trans ((min_le_right _ _).trans (min_le_right _ _))
  change actualExtendedThirdBaseParameter e m j + e ≤
    C (prefixSum r (actualSelectedPrimeCoordinates (N : ℝ) p)) at hC
  have hsum : prefixSum r (actualSelectedPrimeCoordinates (N : ℝ) p) ≤ 2 / 5 := by
    dsimp [C] at hC
    linarith
  have hbceil : ((prefixFront r p).prod : ℝ) ≤ (N : ℝ) ^ (2 / 5 : ℝ) := by
    rw [← prefix_product_power hNr r p hp]
    exact Real.rpow_le_rpow_of_exponent_le hNr.le hsum
  have hb : 0 < (prefixFront r p).prod := by
    have h0 := hp 0
    have h1 := hp 1
    have h2 := hp 2
    fin_cases r
    · simpa [prefixFront] using h0
    · simpa [prefixFront] using Nat.mul_pos h0 h1
    · simpa [prefixFront, mul_assoc] using Nat.mul_pos h0 (Nat.mul_pos h1 h2)
  have hrough := actual_compact_frontier_all_rank_support e h m N cap k hk w z weight
    state hstate hj howned
  have hcover : actualDwellSupport ((N : ℝ) ^ (actualExtendedThirdBaseParameter e m j - e / 16))
      (prefixFront r p ++ prefixRest r p tail) := by
    rw [prefix_split, ← hshape]
    intro i hi
    exact (hrough i hi).trans (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith))
  have hrest := actualDwell_selected_prefix_budget (prefixFront r p) (prefixRest r p tail) hb hcover
  refine ⟨?_, selected_complement_attach_small hNr he0.le he heps htheta a _ hb ha hbceil _ hrest⟩
  have hprod : (prefixFront r p).prod * (prefixRest r p tail).prod = state.selectedPrefix.prod := by
    rw [← List.prod_append, prefix_split, ← hshape, List.prod_reverse]
  simp only [List.prod_cons]
  calc
    (prefixFront r p).prod * (a * (prefixRest r p tail).prod) =
        a * ((prefixFront r p).prod * (prefixRest r p tail).prod) := by ring
    _ = _ := by rw [hprod]

/-- Original nonzero attached coefficient, same a/q/cap/state, with all
three actual prefix rows quantified after extraction of that witness. -/
theorem actual_attached_ne_zero_prefix_complement
    (e h epsilon : ℝ) (m N : ℕ) (cap : ℕ → ℕ)
    (hN : 2 ≤ N) (he0 : 0 < e) (he : e ≤ 1 / 384) (heps : epsilon ≤ e / 128)
    {q : ℕ} (hq : attachedUpperCoefficient 1 thirdPrefixRho epsilon
      (fun M => actualExtendedThirdCompactUpperPolicy e h m M false) cap N q ≠ 0) :
    ∃ a k (state : FirstExitDepthState ℕ),
      a ∈ actualSmallRosserSupport N (cap N) ((N : ℝ) ^ (epsilon ^ 2)) ∧
      (a : ℝ) < (N : ℝ) ^ epsilon ∧ state.selectedPrefix.length = k ∧
      state ∈ firstExitDepthFrontier k (actualExtendedThirdCompactUpperPolicy e h m N)
        (fun _ => 1) [] true 1
        (roughPrimeUniverse N (cap N) ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho)) ∧
      q = a * state.selectedPrefix.prod ∧
      ∀ j : ActualExtendedThirdDyadicLabel m, j ∈ actualExtendedThirdCompactCells e h m → 3 ≤ k →
        primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 state.selectedPrefix) ∈
          actualExtendedThirdOwnedCell m j →
        actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e → ∀ r : Fin 3,
        actualExtendedThirdLeastWinningIndex e m j = Fin.castLE (by decide : 6 ≤ 8) (prefixRow r) →
        ∀ (p : Fin 3 → ℕ) (tail : List ℕ),
          state.selectedPrefix.reverse = p 0 :: p 1 :: p 2 :: tail →
          (prefixFront r p).prod * (a :: prefixRest r p tail).prod = q ∧
          actualDwellSupport ((N : ℝ) ^ (actualExtendedThirdBaseParameter e m j - e / 32) /
            (prefixFront r p).prod) (a :: prefixRest r p tail) := by
  obtain ⟨a, k, state, ha, haL, hlen, hstate, hprod, _hbne, _hactive⟩ :=
    actual_attached_upper_ne_zero_frontier e h epsilon m N cap hq
  refine ⟨a, k, state, ha, haL, hlen, hstate, hprod, ?_⟩
  intro j hj hk howned hfull r hwinner p tail hshape
  obtain ⟨hid, hcomp⟩ := actual_frontier_prefix_winner_complement
    e h epsilon m N (cap N) k hk ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho)
    (fun _ => 1) state hstate hN he0 he heps a haL.le hj howned hfull r hwinner p tail hshape
  exact ⟨hid.trans hprod.symm, hcomp⟩

end

end ImbalancedChen.Part3.ActualPrefixWinnerComplement
