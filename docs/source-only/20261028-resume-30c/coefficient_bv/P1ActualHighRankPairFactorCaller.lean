import ImbalancedChen.P1ActualCompactUpperBVBranchSplit
import ImbalancedChen.Part3ActualAttachedRoughFrontier
import ImbalancedChen.ActualSelectedPairFactorization
import ImbalancedChen.Part3ActualWSmallThirdAttachment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The active high branch from the actual SAME-rho split supplies an original
rough frontier of rank >=3. On the original pair-winning cells (rows6/7),
its actual D-well support supplies the deterministic natural pair allocator.
The SAME small integer attaches to group3, giving the complete q exactly
and positive-reserve monomials before complete-local-scale transport.

This is a necessary internal numerical caller. It does not claim complete
cell coverage, a fixed whole-box slot assignment, a bounded signed tensor,
a moving-alpha spectral estimate, or a high-branch discrepancy estimate.
-/

namespace ImbalancedChen.P1ActualHighRankPairFactorCaller
noncomputable section
open Classical
open P1ActualCompactUpperBVBranchSplit
open ImbalancedChen.Part3.ActualAttachedRoughFrontier
open ImbalancedChen.Part3.ActualCompactAllRankSupport
open ImbalancedChen.Part3.ActualWSameKeyMonomials
open ImbalancedChen.Part3.ActualWSmallThirdAttachment

/-- Data taken from the actual nonzero coefficient, retaining its full q. -/
structure HighFrontier (e h epsilon : ℝ) (m N q : ℕ) where
  small : ℕ
  rank : ℕ
  state : FirstExitDepthState ℕ
  small_mem : small ∈ actualSmallRosserSupport N N ((N : ℝ) ^ (epsilon ^ 2))
  small_size : (small : ℝ) < (N : ℝ) ^ epsilon
  rank_ge : 3 ≤ rank
  length_eq : state.selectedPrefix.length = rank
  original : state ∈ firstExitDepthFrontier rank
    (actualExtendedThirdCompactUpperPolicy e h m N) (fun _ => 1) [] true 1
    (roughPrimeUniverse N N ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho))
  full_product : q = small * state.selectedPrefix.prod
  rough_active : fixedRoughCoefficient (actualExtendedThirdCompactUpperPolicy e h m N false)
    N N ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho)
    state.selectedPrefix.prod ≠ 0

theorem exists_high_frontier {e h epsilon : ℝ} {m N q : ℕ}
    (hq : q ∈ high e h epsilon m N) (hactive : rho e h epsilon m N q ≠ 0) :
    Nonempty (HighFrontier e h epsilon m N q) := by
  obtain ⟨aH, haH, bH, hbH, habH, _, _, hbRank, _⟩ :=
    high_active_integer_witness hq hactive
  have hact : attachedUpperCoefficient 1 thirdPrefixRho epsilon
      (fun M => actualExtendedThirdCompactUpperPolicy e h m M false) (fun M => M) N q ≠ 0 := by
    simpa only [rho, P4ASameRhoCompact.retain] using hactive
  obtain ⟨a, k, state, ha, haSize, hlen, hstate, hprod, hbActive, _⟩ :=
    actual_attached_upper_ne_zero_frontier e h epsilon m N (fun M => M) hact
  have hb : state.selectedPrefix.prod ∈ fixedRoughSupport
      (actualExtendedThirdCompactUpperPolicy e h m N false) N N
      ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho) := by
    by_contra hn
    apply hbActive
    unfold fixedRoughCoefficient
    rw [oddFirstExitRetainedCoefficient_eq_zero_of_not_mem _ _ _ _ hn]
    norm_num
  have hpair : (a, state.selectedPrefix.prod) = (aH, bH) :=
    smallRough_factorization_unique
      (actualSmallRosserSupport_smallPrimeSupportedAt N N _ ha)
      (fixedRoughSupport_roughPrimeSupportedAt
        (actualExtendedThirdCompactUpperPolicy e h m N false) N N _ _ hb)
      (actualSmallRosserSupport_smallPrimeSupportedAt N N _ haH)
      (fixedRoughSupport_roughPrimeSupportedAt
        (actualExtendedThirdCompactUpperPolicy e h m N false) N N _ _ hbH)
      (hprod.symm.trans habH)
  have hbEq : state.selectedPrefix.prod = bH := congrArg Prod.snd hpair
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist k
    (actualExtendedThirdCompactUpperPolicy e h m N) (fun _ => 1)
    (roughPrimeUniverse N N ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho))
    state hstate
  have hnd : state.selectedPrefix.reverse.Nodup :=
    (roughPrimeUniverse_nodup N N _ _).sublist hsub
  have hpf : state.selectedPrefix.reverse.prod.primeFactors =
      state.selectedPrefix.reverse.toFinset := by
    have hprd : state.selectedPrefix.reverse.toFinset.prod id =
        state.selectedPrefix.reverse.prod := by
      simpa using List.prod_toFinset (fun p : ℕ => p) hnd
    rw [← hprd]
    exact Nat.primeFactors_prod (fun p hp => mem_roughPrimeUniverse_prime
      (hsub.subset (List.mem_toFinset.mp hp)))
  have hcard : state.selectedPrefix.prod.primeFactors.card = k := by
    rw [← List.prod_reverse state.selectedPrefix, hpf,
      List.toFinset_card_of_nodup hnd, List.length_reverse, hlen]
  have hk : 3 ≤ k := by
    rw [← hbEq, hcard] at hbRank
    exact hbRank
  exact ⟨⟨a, k, state, ha, haSize, hk, hlen, hstate, hprod, hbActive⟩⟩

/-- A definite actual frontier may be selected before any test function. -/
def actualHighFrontier {e h epsilon : ℝ} {m N q : ℕ}
    (hq : q ∈ high e h epsilon m N) (hactive : rho e h epsilon m N q ≠ 0) :
    HighFrontier e h epsilon m N q := Classical.choice (exists_high_frontier hq hactive)

theorem HighFrontier.prime {e h epsilon : ℝ} {m N q : ℕ}
    (H : HighFrontier e h epsilon m N q) {p : ℕ}
    (hp : p ∈ H.state.selectedPrefix.reverse) : Nat.Prime p := by
  have hsub := mem_firstExitDepthFrontier_selected_reverse_sublist H.rank
    (actualExtendedThirdCompactUpperPolicy e h m N) (fun _ => 1)
    (roughPrimeUniverse N N ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho))
    H.state H.original
  exact mem_roughPrimeUniverse_prime (hsub.subset hp)

theorem HighFrontier.dwell {e h epsilon : ℝ} {m N q : ℕ}
    (H : HighFrontier e h epsilon m N q) {j : ActualExtendedThirdDyadicLabel m}
    (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (howned : primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 H.state.selectedPrefix) ∈
      actualExtendedThirdOwnedCell m j) :
    actualDwellSupport ((N : ℝ) ^ actualExtendedThirdPhysicalLevel e m j)
      H.state.selectedPrefix.reverse :=
  actual_compact_frontier_all_rank_support e h m N N H.rank H.rank_ge _ _
    (fun _ => 1) H.state H.original hj howned

/-- The first three original primes are supplied by high-rank membership;
no independent triple-shape premise is needed to obtain a caller input. -/
theorem HighFrontier.three_head {e h epsilon : ℝ} {m N q : ℕ}
    (H : HighFrontier e h epsilon m N q) :
    ∃ p : Fin 3 → ℕ, ∃ tail : List ℕ,
      H.state.selectedPrefix.reverse = p 0 :: p 1 :: p 2 :: tail := by
  have hlen : 3 ≤ H.state.selectedPrefix.reverse.length := by
    simpa only [List.length_reverse, H.length_eq] using H.rank_ge
  cases hs : H.state.selectedPrefix.reverse with
  | nil => simp only [hs, List.length_nil] at hlen; omega
  | cons p0 rest =>
      cases rest with
      | nil => simp only [hs, List.length_cons, List.length_nil] at hlen; omega
      | cons p1 rest =>
          cases rest with
          | nil => simp only [hs, List.length_cons, List.length_nil] at hlen; omega
          | cons p2 tail =>
              exact ⟨![p0, p1, p2], tail, by simpa using hs⟩

/-- Public coordinate dictionary needed by this caller. The equivalent
existing dictionary in ActualWinnerAttachedComplement is private. -/
theorem coordinates_of_shape {N : ℕ} {history tail : List ℕ}
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
  fin_cases i <;> simp [primeHistoryLogCoordinates, primeHistoryTuple,
    actualPrimeTupleLog, actualSelectedPrimeCoordinates]

/-- The actual pair action, with the SAME actual small block on group3. -/
def attachedPairFactors {e h epsilon : ℝ} {m N q : ℕ}
    (H : HighFrontier e h epsilon m N q) (j : ActualExtendedThirdDyadicLabel m)
    (t : Fin 3 → ℝ) (yz : Bool) (delta A : ℝ) (p : Fin 3 → ℕ) (tail : List ℕ) :
    ℕ × ℕ × ℕ :=
  let abc := actualSelectedPairFactors
    ((N : ℝ) ^ (actualExtendedThirdPairParameter e m j t yz - 2 * delta)) A yz p tail
  (abc.1, abc.2.1, H.small * abc.2.2)

/-- Genuine pair-winning high-branch numerical caller. Support, primality,
small factor, and full q factorization are conclusions of the actual
coefficient construction. Original geometric branch gates remain explicit.
This returns physical monomials and exact local qscale transport; it does
not call a spectral bound with an unproved family/tensor hypothesis. -/
theorem actual_high_pair_factorization {e h epsilon delta A : ℝ} {m N q : ℕ}
    (H : HighFrontier e h epsilon m N q)
    (hN : 1 < N) (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hd0 : 0 < delta) (hd : delta < 1 / 100000) (hdfine : delta ≤ e / 32)
    (heps : epsilon ≤ delta / 4)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    (howned : primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 H.state.selectedPrefix) ∈
      actualExtendedThirdOwnedCell m j)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ VariableEnvelope.mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (yz : Bool) (hwinner : actualExtendedThirdLeastWinningIndex e m j = if yz then 7 else 6)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (hshape : H.state.selectedPrefix.reverse = p 0 :: p 1 :: p 2 :: tail)
    (hAlower : (N : ℝ) ^ delta ≤ A)
    (hAupper : A ≤ (N : ℝ) ^ (1 / 3 - delta / 2)) :
    let abc := attachedPairFactors H j t yz delta A p tail
    abc.1 * abc.2.1 * abc.2.2 = q ∧
      0 < abc.1 ∧ 0 < abc.2.1 ∧ 0 < abc.2.2 ∧ (abc.1 : ℝ) ≤ A ∧
      Monomials (N : ℝ) (delta / 8) A (abc.1 : ℝ) (abc.2.1 : ℝ) (abc.2.2 : ℝ) ∧
      ∀ x : ℝ, 1 < x → LocalMonomials (N : ℝ) x (delta / 8) A
        (abc.1 : ℝ) (abc.2.1 : ℝ) (abc.2.2 : ℝ) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := zero_lt_one.trans hn
  have hpositive : ∀ r ∈ p 0 :: p 1 :: p 2 :: tail, 0 < r := by
    intro r hr
    exact (H.prime (by simpa only [hshape] using hr)).pos
  have hs : actualSelectedPrimeCoordinates (N : ℝ) p ∈ actualExtendedThirdPhysicalCell m j := by
    have hphys := actualExtendedThirdOwnedCell_subset_physicalCell m j howned
    rwa [coordinates_of_shape p hshape] at hphys
  have hsupport := H.dwell hj howned
  rw [hshape] at hsupport
  obtain ⟨hprod, haA, h1, h2, h3⟩ :=
    actualExtendedThirdSelectedPair_factorization (κ := 0)
      he0 he (by linarith) hd0 hd hdfine hmesh hfull ht yz hwinner
      (N : ℝ) hn p hs tail hpositive hsupport hAlower hAupper
  let raw := actualSelectedPairFactors
    ((N : ℝ) ^ (actualExtendedThirdPairParameter e m j t yz - 2 * delta)) A yz p tail
  have hprod' : raw.1 * raw.2.1 * raw.2.2 = (p 0 :: p 1 :: p 2 :: tail).prod := hprod
  have hposProd : 0 < raw.1 * raw.2.1 * raw.2.2 := by
    rw [hprod']
    exact List.prod_pos hpositive
  have haNat : 0 < raw.1 := Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right hposProd)
  have hbNat : 0 < raw.2.1 := Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right hposProd)
  have hcNat : 0 < raw.2.2 := Nat.pos_of_mul_pos_left hposProd
  have ha : (0 : ℝ) < raw.1 := by exact_mod_cast haNat
  have hb : (0 : ℝ) < raw.2.1 := by exact_mod_cast hbNat
  have hc : (0 : ℝ) < raw.2.2 := by exact_mod_cast hcNat
  have hsmallNat : 0 < H.small := Nat.pos_of_ne_zero
    (actualSmallRosserSupport_squarefree N N _ H.small_mem).ne_zero
  have hsmall : (0 : ℝ) < H.small := by exact_mod_cast hsmallNat
  have hA : 0 < A := (Real.rpow_pos_of_pos hn0 delta).trans_le hAlower
  have hmono : Monomials (N : ℝ) (delta / 4) A
      (raw.1 : ℝ) (raw.2.1 : ℝ) (raw.2.2 : ℝ) := by
    refine ⟨h1.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)), ?_,
      h3.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))⟩
    have hh : (N : ℝ) ^ (7 / 32 : ℝ) * A * (raw.1 : ℝ) *
        (raw.2.1 : ℝ) ^ 5 * (raw.2.2 : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 - 3 * delta) := by
      simpa using h2
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))
  have hattach := third_attachment_monomials hn hA ha hb hc hsmall H.small_size.le heps hmono
  have hattached : Monomials (N : ℝ) (delta / 8) A
      (raw.1 : ℝ) (raw.2.1 : ℝ) ((H.small * raw.2.2 : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, show (delta / 4) / 2 = delta / 8 by ring] using hattach
  change raw.1 * raw.2.1 * (H.small * raw.2.2) = q ∧
    0 < raw.1 ∧ 0 < raw.2.1 ∧ 0 < H.small * raw.2.2 ∧ (raw.1 : ℝ) ≤ A ∧ _
  refine ⟨?_, haNat, hbNat, Nat.mul_pos hsmallNat hcNat, haA, hattached, ?_⟩
  · calc
      _ = H.small * (raw.1 * raw.2.1 * raw.2.2) := by ring
      _ = H.small * (p 0 :: p 1 :: p 2 :: tail).prod := by rw [hprod']
      _ = H.small * H.state.selectedPrefix.prod := by
        rw [← hshape, List.prod_reverse]
      _ = q := H.full_product.symm
  · intro x hx
    exact transport hn0 hx hattached

end
end ImbalancedChen.P1ActualHighRankPairFactorCaller
