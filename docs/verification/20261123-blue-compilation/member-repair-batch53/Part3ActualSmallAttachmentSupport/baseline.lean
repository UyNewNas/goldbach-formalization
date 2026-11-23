import ImbalancedChen.Part3ActualAttachedRoughFrontier

/-!
# Explicit square-support cost of the same actual small attachment

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The original small factor a is kept as one distinguished, possibly
composite block before the original decreasing rough vector.  Its own
square costs 2 epsilon; every later original square costs epsilon in
addition to the original physical level lambda.  The actual compact
first-cube margin proves epsilon <= lambda from epsilon <= e, so the
single enlarged level lambda+epsilon pays both costs.

No assertion is made that this list is a decreasing prime list.  The
D-well numerical allocator accepts a list of natural weights; prime-slot
normalization of a tensor must keep this distinguished small block
separate.  Selected-mask gates and signed tensor identities are not
silently inferred from this full-square result.
-/

namespace ImbalancedChen.Part3.ActualSmallAttachmentSupport

noncomputable section

open ActualAttachedRoughFrontier
open ActualCompactInitialSupport

/-- Prepending a distinguished natural block multiplies every old square
by that same block and adds exactly one new initial square. -/
theorem dwell_prepend_block {D E : ℝ} (a : ℕ) (input : List ℕ)
    (hfull : actualDwellSupport D input)
    (hfirst : (a : ℝ) ^ 2 ≤ E) (hscale : (a : ℝ) * D ≤ E) :
    actualDwellSupport E (a :: input) := by
  intro i hi
  cases i with
  | zero => simpa using hfirst
  | succ i =>
      have hi' : i < input.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hi
      have hs := mul_le_mul_of_nonneg_left (hfull i hi') (Nat.cast_nonneg a)
      have hbound := hs.trans hscale
      simpa only [List.take_succ_cons, List.map_cons, List.prod_cons,
        List.getElem_cons_succ, mul_assoc] using hbound

/-- With a <= N^epsilon and epsilon <= lambda the exact loss is epsilon,
not 2epsilon, since the new initial square already lies below the cover. -/
theorem dwell_prepend_small_power {N lam epsilon : ℝ} (hN : 1 < N)
    (a : ℕ) (input : List ℕ) (ha : (a : ℝ) ≤ N ^ epsilon)
    (hepsilon : epsilon ≤ lam) (hfull : actualDwellSupport (N ^ lam) input) :
    actualDwellSupport (N ^ (lam + epsilon)) (a :: input) := by
  have hNpos : 0 < N := zero_lt_one.trans hN
  apply dwell_prepend_block a input hfull
  · calc
      (a : ℝ) ^ 2 ≤ (N ^ epsilon) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg a) ha 2
      _ = N ^ (epsilon + epsilon) := by
        rw [Real.rpow_add hNpos]
        ring
      _ ≤ N ^ (lam + epsilon) :=
        Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
  · calc
      (a : ℝ) * N ^ lam ≤ N ^ epsilon * N ^ lam :=
        mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hNpos.le _)
      _ = N ^ (lam + epsilon) := by rw [Real.rpow_add hNpos]; ring

/-- The actual compact margin supplies the comparison used above.
There is no independent lower bound on its physical level in the input. -/
theorem actual_compact_level_ge_e {e h : ℝ} {m : ℕ}
    (he0 : 0 ≤ e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2)
    {j : ActualExtendedThirdDyadicLabel m} (hj : j ∈ actualExtendedThirdCompactCells e h m)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdOwnedCell m j) :
    e ≤ actualExtendedThirdPhysicalLevel e m j := by
  have hphysical := actualExtendedThirdOwnedCell_subset_physicalCell m j ht
  have hmargin := actualExtendedThirdPhysicalLevel_firstCube_margin he0 he hmesh
    (actualExtendedThirdCompactCells_subset e h m hj) hphysical
  have ht0 : 0 ≤ t 0 :=
    hphysical.2.1.trans (hphysical.2.2.1.trans hphysical.2.2.2)
  linarith

/-- Literal nonzero rho supplies the same a and the same original rough
state.  The full attached modulus is their product and its square budget
is proved at lambda+epsilon on every active compact branch.  The final
endpoint clause charges k+2 copies of tau for k rough slots plus the one
small block and the additional occurrence in a square. -/
theorem actual_attached_upper_ne_zero_block_support
    (e h epsilon : ℝ) (m N : ℕ) (cap : ℕ → ℕ)
    (hN : 2 ≤ N) (he0 : 0 ≤ e) (he : e ≤ 1 / 384)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 2) (hepsilon : epsilon ≤ e)
    {q : ℕ}
    (hq : attachedUpperCoefficient 1 thirdPrefixRho epsilon
      (fun M => actualExtendedThirdCompactUpperPolicy e h m M false) cap N q ≠ 0) :
    ∃ a k (state : FirstExitDepthState ℕ),
      a ∈ actualSmallRosserSupport N (cap N) ((N : ℝ) ^ (epsilon ^ 2)) ∧
      (a : ℝ) < (N : ℝ) ^ epsilon ∧ state.selectedPrefix.length = k ∧
      state ∈ firstExitDepthFrontier k (actualExtendedThirdCompactUpperPolicy e h m N)
        (fun _ => 1) [] true 1
        (roughPrimeUniverse N (cap N) ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho)) ∧
      (a :: state.selectedPrefix.reverse).prod = q ∧
      fixedRoughCoefficient (actualExtendedThirdCompactUpperPolicy e h m N false)
        N (cap N) ((N : ℝ) ^ (epsilon ^ 2)) ((N : ℝ) ^ thirdPrefixRho)
        state.selectedPrefix.prod ≠ 0 ∧
      ∀ j : ActualExtendedThirdDyadicLabel m, j ∈ actualExtendedThirdCompactCells e h m →
        3 ≤ k →
        primeHistoryLogCoordinates (N : ℝ) 3 (rosserAncestor 3 state.selectedPrefix) ∈
          actualExtendedThirdOwnedCell m j →
        actualDwellSupport ((N : ℝ) ^ (actualExtendedThirdPhysicalLevel e m j + epsilon))
          (a :: state.selectedPrefix.reverse) ∧
        ∀ (x tau theta : ℝ) (upper : ℕ → ℕ), 1 < x → 0 ≤ tau →
          (∀ p ∈ a :: state.selectedPrefix.reverse, (upper p : ℝ) ≤ x ^ tau * p) →
          (Real.log (N : ℝ) / Real.log x) *
              (actualExtendedThirdPhysicalLevel e m j + epsilon) + tau * (k + 2) ≤ theta →
          actualDwellSupport (x ^ theta) ((a :: state.selectedPrefix.reverse).map upper) := by
  obtain ⟨a, k, state, ha, haL, hlen, hstate, hprod, hbne, hactive⟩ :=
    actual_attached_upper_ne_zero_frontier e h epsilon m N cap hq
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  refine ⟨a, k, state, ha, haL, hlen, hstate, ?_, hbne, ?_⟩
  · simpa only [List.prod_cons, List.prod_reverse] using hprod.symm
  · intro j hj hk ht
    have hlevel := actual_compact_level_ge_e he0 he hmesh hj ht
    have hs := dwell_prepend_small_power hNr a state.selectedPrefix.reverse haL.le
      (hepsilon.trans hlevel) (hactive j hj hk ht)
    refine ⟨hs, ?_⟩
    intro x tau theta upper hx htau hsize hbudget
    have hlength : (a :: state.selectedPrefix.reverse).length ≤ k + 1 := by
      simp [hlen]
    apply physical_support_upper_local (R := k + 1)
      (lam := actualExtendedThirdPhysicalLevel e m j + epsilon) (theta := theta)
      (zero_lt_one.trans hNr) hx htau id upper (a :: state.selectedPrefix.reverse) hlength hsize
    · simpa using hs
    · simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hbudget

end

end ImbalancedChen.Part3.ActualSmallAttachmentSupport
