import ImbalancedChen.Part3ActualWFineWordAdapter

/-!
# Actual W-gap margins pay the original fine-key initialization

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual row-4 whole-cell gap supplies the first-prime reserve e/8,
the second-square reserve e/16, and the third-prime reserve e/8.
Canonical floor upper keys cost at most N^sigma per original occurrence.
With sigma <= e/64 these imply the genuine first-bin, second-square and
all-late-key bounds. The final retained-atom consumer has none of those
three bounds as hypotheses. Its complete endpoint support is also derived
from the original retained frontier, with sigma*(k+1) <= e/2.

The physical capacities are transported exactly to a local scale in a
separate theorem. This does not identify the rescaled theta with the
local analytic theta or supply the three analytic monomials. W-close,
small attachment and the final tensor/spectral license remain separate.
-/

namespace ImbalancedChen.Part3.ActualWFineKeyInitialization

noncomputable section

open ActualWFineWordAdapter ActualWThreeCapacityRun ActualWResidualCompletion
open ActualWGapInitialization VariableEnvelope

private theorem key_le_inflated_power {N q label : ℕ} {sigma a : ℝ}
    (hN : 0 < N) (hq : q ∈ actualPrimeFineLabelFinset N sigma label)
    (hpower : (q : ℝ) ≤ (N : ℝ) ^ a) :
    (actualPrimeFineLabelIntegerUpper N sigma label : ℝ) ≤ (N : ℝ) ^ (sigma + a) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ (N : ℝ) ^ sigma * q := fine_key_inflation hN hq
    _ ≤ (N : ℝ) ^ sigma * (N : ℝ) ^ a :=
      mul_le_mul_of_nonneg_left hpower (Real.rpow_nonneg hNr.le _)
    _ = (N : ℝ) ^ (sigma + a) := (Real.rpow_add hNr _ _).symm

/-- The actual W cap also supplies the parameter ceiling required by the
existing successful-three-bin monomial theorem. -/
theorem actual_W_gap_theta_cap {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (hwinner : actualExtendedThirdLeastWinningIndex e m j = 4)
    (hgap : e / 4 < wInner (t 0) (t 1) (t 2) - v (t 0)) :
    actualExtendedThirdRescueParameter e m j t + e / 16 ≤ 153 / 256 := by
  rcases actualExtendedThirdSelectedRescue_wholeCell he0 he hmesh hfull ht false hwinner with
    ⟨hclose, _⟩ | ⟨_, _, _, _, hcell⟩
  · exact (not_lt_of_ge hclose hgap).elim
  · have hh := (hcell t ht).2
    change actualExtendedThirdRescueParameter e m j t + e / 16 ≤
      wInner (t 0) (t 1) (t 2) at hh
    have hB : wInner (t 0) (t 1) (t 2) ≤ B (t 2) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hcap := hh.trans hB
    dsimp [B, cap] at hcap
    linarith [ht.2.1]

/-- All three key initialization inequalities follow from the ACTUAL
winning gap, not from endpoint support or an assumed initialization.
The late statement covers every later prime occurrence and its own label. -/
theorem actual_W_gap_key_bounds {e sigma : ℝ} {m N : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (he0 : 0 < e) (he : e ≤ 1 / 384) (hsigma : sigma ≤ e / 64)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (hwinner : actualExtendedThirdLeastWinningIndex e m j = 4)
    (hgap : e / 4 < wInner (t 0) (t 1) (t 2) - v (t 0))
    (hN : 1 < N) (p labels : Fin 3 → ℕ) (hp : ∀ i, 0 < p i)
    (hs : actualSelectedPrimeCoordinates (N : ℝ) p ∈ actualExtendedThirdPhysicalCell m j)
    (hlabels : ∀ i, p i ∈ actualPrimeFineLabelFinset N sigma (labels i)) :
    let theta := actualExtendedThirdRescueParameter e m j t
    1 / 2 ≤ theta ∧ theta < 5 / 8 ∧
      actualExtendedThirdPhysicalLevel e m j + e ≤ theta ∧
      (actualPrimeFineLabelIntegerUpper N sigma (labels 0) : ℝ) ≤
        (N : ℝ) ^ (2 * theta - 1 - e / 16) ∧
      (actualPrimeFineLabelIntegerUpper N sigma (labels 1) : ℝ) ^ 2 ≤
        (N : ℝ) ^ (1 - theta - e / 32) ∧
      ∀ (q label : ℕ), q ≤ p 2 → q ∈ actualPrimeFineLabelFinset N sigma label →
        (actualPrimeFineLabelIntegerUpper N sigma label : ℝ) ≤
          (N : ℝ) ^ (actualSelectedSubproductUpper 1 theta - (2 * theta - 1) - e / 16) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hNnat : 0 < N := Nat.zero_lt_of_lt hN
  rcases actualExtendedThirdSelectedRescue_wholeCell he0 he hmesh hfull ht false hwinner with
    ⟨hclose, _⟩ | ⟨_hgap, hlo, hhi, hlevel, hcell⟩
  · exact (not_lt_of_ge hclose hgap).elim
  · let theta := actualExtendedThirdRescueParameter e m j t
    obtain ⟨hgate, hW⟩ := hcell _ hs
    have hbelow : actualSelectedPrimeCoordinates (N : ℝ) p 0 ≤ mu := by
      have hh := (hs.1 0 (Set.mem_univ _)).2.trans hfull
      linarith
    rw [v_eq_A hbelow] at hgate
    dsimp [A] at hgate
    change theta + e / 16 ≤ wInner _ _ _ at hW
    simp only [wInner, B, cap, le_min_iff] at hW
    obtain ⟨hW1, hW2, hW3⟩ := hW
    have hfirst : (p 0 : ℝ) ≤ (N : ℝ) ^ (2 * theta - 1 - e / 8) := by
      rw [← rpow_actualSelectedPrimeCoordinates (N : ℝ) hNr p hp 0]
      exact Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith)
    have hsecond : (p 1 : ℝ) ^ 2 ≤ (N : ℝ) ^ (1 - theta - e / 16) := by
      rw [← rpow_actualSelectedPrimeCoordinates (N : ℝ) hNr p hp 1,
        ← Real.rpow_mul_natCast hNpos.le]
      apply Real.rpow_le_rpow_of_exponent_le hNr.le
      norm_num
      linarith
    have hlate : (p 2 : ℝ) ≤
        (N : ℝ) ^ (actualSelectedSubproductUpper 1 theta - (2 * theta - 1) - e / 8) := by
      rw [← rpow_actualSelectedPrimeCoordinates (N : ℝ) hNr p hp 2]
      apply Real.rpow_le_rpow_of_exponent_le hNr.le
      have hu : actualSelectedPrimeCoordinates (N : ℝ) p 2 + (2 * theta - 1) + e / 8 ≤
          actualSelectedSubproductUpper 1 theta := by
        unfold actualSelectedSubproductUpper
        apply le_min <;> linarith
      linarith
    refine ⟨hlo, hhi, hlevel, ?_, ?_, ?_⟩
    · exact (key_le_inflated_power hNnat (hlabels 0) hfirst).trans
        (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith))
    · calc
        _ ≤ ((N : ℝ) ^ sigma * (p 1 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (fine_key_inflation hNnat (hlabels 1)) 2
        _ = ((N : ℝ) ^ sigma) ^ 2 * (p 1 : ℝ) ^ 2 := by ring
        _ ≤ ((N : ℝ) ^ sigma) ^ 2 * (N : ℝ) ^ (1 - theta - e / 16) :=
          mul_le_mul_of_nonneg_left hsecond (sq_nonneg _)
        _ = (N : ℝ) ^ (2 * sigma + (1 - theta - e / 16)) := by
          rw [← Real.rpow_mul_natCast hNpos.le, ← Real.rpow_add hNpos]
          congr 1
          norm_num
          ring
        _ ≤ (N : ℝ) ^ (1 - theta - e / 32) :=
          Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith)
    · intro q label hq hpq
      have hqpower := (by exact_mod_cast hq : (q : ℝ) ≤ p 2).trans hlate
      exact (key_le_inflated_power hNnat hpq hqpower).trans
        (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith))

/-- Exact transport of all paid key margins; no theta or alpha parameter
is silently reset when the complete local scale differs from N. -/
theorem actual_W_gap_keys_local {e sigma : ℝ} {m N : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (he0 : 0 < e) (he : e ≤ 1 / 384) (hsigma : sigma ≤ e / 64)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (hwinner : actualExtendedThirdLeastWinningIndex e m j = 4)
    (hgap : e / 4 < wInner (t 0) (t 1) (t 2) - v (t 0))
    (hN : 1 < N) (p labels : Fin 3 → ℕ) (hp : ∀ i, 0 < p i)
    (hs : actualSelectedPrimeCoordinates (N : ℝ) p ∈ actualExtendedThirdPhysicalCell m j)
    (hlabels : ∀ i, p i ∈ actualPrimeFineLabelFinset N sigma (labels i))
    (x : ℝ) (hx : 1 < x) :
    let theta := actualExtendedThirdRescueParameter e m j t
    let qscale := Real.log (N : ℝ) / Real.log x
    (actualPrimeFineLabelIntegerUpper N sigma (labels 0) : ℝ) ≤
      x ^ (qscale * (2 * theta - 1 - e / 16)) ∧
      (actualPrimeFineLabelIntegerUpper N sigma (labels 1) : ℝ) ^ 2 ≤
        x ^ (qscale * (1 - theta - e / 32)) ∧
      ∀ (q label : ℕ), q ≤ p 2 → q ∈ actualPrimeFineLabelFinset N sigma label →
        (actualPrimeFineLabelIntegerUpper N sigma label : ℝ) ≤
          x ^ (qscale * (actualSelectedSubproductUpper 1 theta - (2 * theta - 1) - e / 16)) := by
  obtain ⟨_, _, _, hfirst, hsecond, hlate⟩ := actual_W_gap_key_bounds
    he0 he hsigma hmesh hfull ht hwinner hgap hN p labels hp hs hlabels
  have hNr : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  simp_rw [ActualCompactInitialSupport.physical_power_eq_local hNr hx] at hfirst hsecond hlate
  exact ⟨hfirst, hsecond, hlate⟩

private theorem mem_slot_cons {ι : Type*} (F : ι → Finset ℕ)
    (i : ι) (word : List ι) (q : ℕ) (qs : List ℕ) :
    q :: qs ∈ actualPrimeSlotBox F (i :: word) ↔ q ∈ F i ∧ qs ∈ actualPrimeSlotBox F word := by
  constructor
  · intro hh
    obtain ⟨⟨r, rs⟩, hmem, heq⟩ := Finset.mem_image.mp hh
    rcases List.cons.inj heq with ⟨rfl, rfl⟩
    exact Finset.mem_product.mp hmem
  · rintro ⟨hq, hqs⟩
    exact Finset.mem_image.mpr ⟨(q, qs), Finset.mem_product.mpr ⟨hq, hqs⟩, rfl⟩

/-- The actual representative provides every late label with its own
prime occurrence. Repeated labels require no representative prime map. -/
theorem late_keys_from_atom {N : ℕ} {sigma U : ℝ} (p2 : ℕ)
    (primeTail labelTail : List ℕ)
    (hatom : primeTail ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) labelTail)
    (horder : ∀ q ∈ primeTail, q ≤ p2)
    (hgate : ∀ q label, q ≤ p2 → q ∈ actualPrimeFineLabelFinset N sigma label →
      (actualPrimeFineLabelIntegerUpper N sigma label : ℝ) ≤ U) :
    ∀ label ∈ labelTail, (actualPrimeFineLabelIntegerUpper N sigma label : ℝ) ≤ U := by
  obtain ⟨paired, hlabels, hvalues, hpair⟩ := atom_pairing
    (actualPrimeFineLabelFinset N sigma) labelTail primeTail hatom
  intro label hlabel
  have hm : label ∈ paired.map Prod.fst := by rwa [hlabels]
  obtain ⟨iq, hiq, rfl⟩ := List.mem_map.mp hm
  have hq : iq.2 ∈ primeTail := by
    rw [← hvalues]
    exact List.mem_map.mpr ⟨iq, hiq, rfl⟩
  exact hgate iq.2 iq.1 (horder iq.2 hq) (hpair iq hiq)

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

/-- Genuine row-4 gap factorization of the whole original fine atom.
The first-key, second-square and late-key hypotheses of the earlier
adapter are now all discharged from this actual retained winner.
The same fixed bins serve every tuple, including repeated label slots. -/
theorem actual_W_gap_frozen_atom
    (e h sigma : ℝ) (m N cap k : ℕ) (hk : 3 ≤ k) (w z : ℝ) (weight : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier k
      (actualExtendedThirdCompactUpperPolicy e h m N) weight [] true 1
      (roughPrimeUniverse N cap w z))
    (hN : 2 ≤ N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hsigma0 : 0 ≤ sigma) (hsigma : sigma ≤ e / 64)
    (hwidth : sigma * (k + 1) ≤ e / 2)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (howned : primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 state.selectedPrefix) ∈
      actualExtendedThirdOwnedCell m j)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (hwinner : actualExtendedThirdLeastWinningIndex e m j = 4)
    (hgap : e / 4 < wInner (t 0) (t 1) (t 2) - v (t 0))
    (p labels : Fin 3 → ℕ) (primeTail labelTail : List ℕ)
    (hshape : state.selectedPrefix.reverse = p 0 :: p 1 :: p 2 :: primeTail)
    (hatom : state.selectedPrefix.reverse ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma)
      (labels 0 :: labels 1 :: labels 2 :: labelTail))
    (A : ℝ) (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ)) :
    let theta := actualExtendedThirdRescueParameter e m j t
    let B := (N : ℝ) ^ (2 * theta - 1)
    let C := (N : ℝ) ^ (1 - theta - e / 32) / A
    let D := (N : ℝ) ^ (theta - e / 32)
    let U := (N : ℝ) ^ (actualSelectedSubproductUpper 1 theta - (2 * theta - 1) - e / 16)
    let key := fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)
    let out := fineSlots N sigma A B C labels labelTail
    (flatten out).Perm (labels 0 :: labels 1 :: labels 2 :: labelTail) ∧
      (Bounded key A B C out ∨
        (B < wp key out.middle ∧ wp key out.middle ≤ B * U ∧
          wp key out.left ≤ A ∧ wp key out.right ≤ D / (A * wp key out.middle))) ∧
      ∀ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma)
          (labels 0 :: labels 1 :: labels 2 :: labelTail),
        ∃ ls ms rs,
          ls ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.left ∧
          ms ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.middle ∧
          rs ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.right ∧
          ls.prod * ms.prod * rs.prod = ps.prod ∧
          (ls.prod : ℝ) ≤ wp key out.left ∧ (ms.prod : ℝ) ≤ wp key out.middle ∧
          (rs.prod : ℝ) ≤ wp key out.right := by
  have hNnat : 1 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast hNnat
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist k
    (actualExtendedThirdCompactUpperPolicy e h m N) weight
    (roughPrimeUniverse N cap w z) state hstate
  have hp (i : Fin 3) : 0 < p i := by
    have hm : p i ∈ state.selectedPrefix.reverse := by
      rw [hshape]
      fin_cases i <;> simp
    exact (mem_roughPrimeUniverse_prime (hsub.subset hm)).pos
  have hs : actualSelectedPrimeCoordinates (N : ℝ) p ∈ actualExtendedThirdPhysicalCell m j := by
    have hh := actualExtendedThirdOwnedCell_subset_physicalCell m j howned
    rwa [coordinates_of_shape p hshape] at hh
  have hatom' : p 0 :: p 1 :: p 2 :: primeTail ∈
      actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma)
        (labels 0 :: labels 1 :: labels 2 :: labelTail) := by rwa [← hshape]
  obtain ⟨hl0, htail0⟩ := (mem_slot_cons _ _ _ _ _).mp hatom'
  obtain ⟨hl1, htail1⟩ := (mem_slot_cons _ _ _ _ _).mp htail0
  obtain ⟨hl2, htailAtom⟩ := (mem_slot_cons _ _ _ _ _).mp htail1
  have hlabels : ∀ i, p i ∈ actualPrimeFineLabelFinset N sigma (labels i) := by
    intro i
    fin_cases i
    · exact hl0
    · exact hl1
    · exact hl2
  obtain ⟨hlo, hhi, hlevel, hkey0, hkey1, hlate⟩ := actual_W_gap_key_bounds
    he0 he hsigma hmesh hfull ht hwinner hgap hNnat p labels hp hs hlabels
  let theta := actualExtendedThirdRescueParameter e m j t
  let B := (N : ℝ) ^ (2 * theta - 1)
  let C := (N : ℝ) ^ (1 - theta - e / 32) / A
  let U := (N : ℝ) ^ (actualSelectedSubproductUpper 1 theta - (2 * theta - 1) - e / 16)
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hAC : A * C = (N : ℝ) ^ (1 - theta - e / 32) := by
    dsimp [C]
    field_simp [hApos.ne']
    <;> ring
  have hC : 1 ≤ C := by
    apply (le_div_iff₀ hApos).mpr
    simpa only [one_mul] using hAupper.trans
      (Real.rpow_le_rpow_of_exponent_le hNr.le (by dsimp [theta]; linarith))
  have hfirst : (actualPrimeFineLabelIntegerUpper N sigma (labels 0) : ℝ) ≤ B :=
    hkey0.trans (Real.rpow_le_rpow_of_exponent_le hNr.le (by dsimp [theta]; linarith))
  have hsecond : (actualPrimeFineLabelIntegerUpper N sigma (labels 1) : ℝ) ^ 2 ≤ A * C := by
    rw [hAC]
    exact hkey1
  have hsort : (p 0 :: p 1 :: p 2 :: primeTail).Pairwise (· > ·) := by
    rw [← hshape]
    exact (roughPrimeUniverse_pairwise_gt N cap w z).sublist hsub
  have hthird := (List.pairwise_cons.mp (List.pairwise_cons.mp hsort).2).2
  have htailorder : ∀ q ∈ primeTail, q ≤ p 2 :=
    fun q hq => ((List.pairwise_cons.mp hthird).1 q hq).le
  have htailKeys := late_keys_from_atom (p 2) primeTail labelTail htailAtom htailorder hlate
  have hlateKeys : ∀ l ∈ labels 2 :: labelTail,
      (actualPrimeFineLabelIntegerUpper N sigma l : ℝ) ≤ U := by
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · exact hlate (p 2) (labels 2) le_rfl hl2
    · exact htailKeys l hl
  have hbudget : (Real.log (N : ℝ) / Real.log (N : ℝ)) *
      actualExtendedThirdPhysicalLevel e m j + sigma * (k + 1) ≤ theta - e / 32 := by
    rw [div_self (Real.log_pos hNr).ne']
    dsimp [theta]
    linarith
  exact actual_frontier_frozen_fine_word e h m N cap k hk w z weight state hstate hj howned
    sigma (N : ℝ) sigma (theta - e / 32) (Nat.zero_lt_of_lt hNnat) hNr hsigma0 le_rfl
    labels labelTail hatom hbudget hA hC hfirst hsecond hlateKeys

end

end ImbalancedChen.Part3.ActualWFineKeyInitialization
