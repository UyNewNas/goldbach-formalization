import ImbalancedChen.Part3ActualWCloseFullRepair
import ImbalancedChen.Part3ActualWSameKeyMonomials

/-!
# Same-key W-close monomials in both capacity branches

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The full-vector repair uses only the original A <= N^(1/3), not the
stronger A <= N^(1/3-delta/2). With c=1 its first logarithmic budget is
1/3+theta-2delta <= 23/24-2delta <= 1-4delta for delta<=1/48.
The remaining two estimates use the repaired product and genuine head
ceiling. The selected branch uses the actual first-key critical interval.

The final theorem starts from the retained actual close winner and its
original fine atom. Both branches use the same computed closeSlots bins;
every actual tuple inherits their bounds and exact original product.
Exact local transport preserves qscale everywhere; no analytic local
alpha/theta reset or small attachment is asserted.
-/

namespace ImbalancedChen.Part3.ActualWCloseSameKeyMonomials

noncomputable section

open ActualWThreeCapacityRun ActualWResidualCompletion ActualWFineWordAdapter
open ActualWCloseFineHead ActualWCloseFullRepair ActualWSameKeyMonomials VariableEnvelope

/-- The genuine weak-A full-vector repair estimate, with third factor 1.
No strengthened medium range or target monomial is a premise. -/
theorem weak_medium_repair_monomials {x delta theta A a b : ℝ}
    (hx : 1 < x) (hdelta : delta ≤ 1 / 48) (htheta : theta ≤ 5 / 8)
    (hA : 0 < A) (ha : 0 < a) (hb : 0 < b)
    (hAupper : A ≤ x ^ (1 / 3 : ℝ)) (haA : a ≤ A)
    (hproduct : A * b ≤ x ^ (theta - 2 * delta))
    (hbupper : b ≤ x ^ actualSelectedSubproductUpper 1 theta) :
    Monomials x delta A a b 1 := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hL : 0 < Real.log x := Real.log_pos hx
  have hlogcap := (Real.le_rpow_iff_log_le (mul_pos hA hb) hx0).mp hproduct
  rw [Real.log_mul hA.ne' hb.ne'] at hlogcap
  have hlogA := (Real.le_rpow_iff_log_le hA hx0).mp hAupper
  have hloga := (Real.log_le_log_iff ha hA).mpr haA
  have hlogb := (Real.le_rpow_iff_log_le hb hx0).mp hbupper
  have hb1 : Real.log b ≤ ((32 - 39 * theta) / 34) * Real.log x :=
    hlogb.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hL.le)
  have hb2 : Real.log b ≤ ((2 - 2 * theta - 7 * 1 / 32) / 3) * Real.log x :=
    hlogb.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hL.le)
  have htL := mul_le_mul_of_nonneg_right htheta hL.le
  have hdL := mul_le_mul_of_nonneg_right hdelta hL.le
  simp only [Monomials, one_pow, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · apply Real.le_rpow_of_log_le hx0
    rw [Real.log_mul (pow_ne_zero 2 hA.ne') hb.ne', Real.log_pow]
    nlinarith only [hlogcap, hlogA, htL, hdL]
  · apply Real.le_rpow_of_log_le hx0
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) ha.ne', Real.log_mul (by positivity) hA.ne',
      Real.log_rpow hx0, Real.log_pow]
    nlinarith only [hlogcap, hb2, hloga]
  · apply Real.le_rpow_of_log_le hx0
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) ha.ne', Real.log_mul (by positivity) hA.ne',
      Real.log_rpow (div_pos hA hb), Real.log_div hA.ne' hb.ne', Real.log_pow]
    nlinarith only [hlogcap, hb1, hloga]

private theorem atom_product_pos (N : ℕ) (sigma : ℝ) (word primes : List ℕ)
    (hprimes : primes ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) word) :
    (0 : ℝ) < primes.prod := by
  have hp := actualPrimeSlotBox_prime (actualPrimeFineLabelFinset N sigma) word
    (fun _ _ _ hq => (mem_actualPrimeFineLabelFinset.mp hq).1) primes hprimes
  have hh : 0 < primes.prod := List.prod_pos (fun q hq => (hp q hq).pos)
  exact_mod_cast hh

/-- Same original fixed bins, original weak medium range, BOTH real
capacity branches, and every original atom tuple. No hInit, support or
monomial supplier is accepted. -/
theorem actual_W_close_same_key_monomials
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
    (hclose : wInner (t 0) (t 1) (t 2) - v (t 0) ≤ e / 4)
    (p : Fin 3 → ℕ) (primeTail : List ℕ)
    (hshape : state.selectedPrefix.reverse = p 0 :: p 1 :: p 2 :: primeTail)
    (label : ℕ) (rest : List ℕ)
    (hatom : state.selectedPrefix.reverse ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma)
      (label :: rest))
    (A : ℝ) (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ)) :
    let theta := actualExtendedThirdBaseParameter e m j
    let key := fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)
    let out := closeSlots N sigma ((N : ℝ) ^ (theta - e / 32)) A label rest
    Positive key out ∧ wp key out.left ≤ A ∧
      Monomials (N : ℝ) (e / 64) A (wp key out.left) (wp key out.middle) (wp key out.right) ∧
      (∀ x : ℝ, 1 < x → LocalMonomials (N : ℝ) x (e / 64) A
        (wp key out.left) (wp key out.middle) (wp key out.right)) ∧
      ∀ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) (label :: rest),
        ∃ ls ms rs,
          ls ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.left ∧
          ms ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.middle ∧
          rs ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) out.right ∧
          ls.prod * ms.prod * rs.prod = ps.prod ∧
          (ls.prod : ℝ) ≤ wp key out.left ∧ (ms.prod : ℝ) ≤ wp key out.middle ∧
          (rs.prod : ℝ) ≤ wp key out.right ∧
          Monomials (N : ℝ) (e / 64) A (ls.prod : ℝ) (ms.prod : ℝ) (rs.prod : ℝ) ∧
          ∀ x : ℝ, 1 < x → LocalMonomials (N : ℝ) x (e / 64) A
            (ls.prod : ℝ) (ms.prod : ℝ) (rs.prod : ℝ) := by
  obtain ⟨hDA, hperm, hleft, hcases, hwhole⟩ := actual_W_close_complete_atom
    e h sigma m N cap k hk w z weight state hstate hN he0 he hsigma0 hsigma hwidth hmesh
    hj howned hfull ht hwinner hclose p primeTail hshape label rest hatom A hA hAupper
  obtain ⟨hheadLower, hheadUpper, _, _, _⟩ := actual_close_retained_fine_head
    e h sigma m N cap k hk w z weight state hstate hN he0 he hsigma0 hsigma hwidth hmesh
    hj howned hfull ht hwinner hclose p primeTail hshape label rest hatom
  let theta := actualExtendedThirdBaseParameter e m j
  let key := fun l => (actualPrimeFineLabelIntegerUpper N sigma l : ℝ)
  let out := closeSlots N sigma ((N : ℝ) ^ (theta - e / 32)) A label rest
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans hNr
  have hApos : 0 < A := zero_lt_one.trans_le hA
  obtain ⟨ls0, ms0, rs0, hls0, hms0, hrs0, _, hL0, hM0, hR0⟩ :=
    hwhole state.selectedPrefix.reverse hatom
  have ha : 0 < wp key out.left := (atom_product_pos N sigma _ _ hls0).trans_le hL0
  have hb : 0 < wp key out.middle := (atom_product_pos N sigma _ _ hms0).trans_le hM0
  have hc : 0 < wp key out.right := (atom_product_pos N sigma _ _ hrs0).trans_le hR0
  have htheta : theta ≤ 5 / 8 :=
    (actualExtendedThirdBaseParameter_range he0 he ⟨t, ht⟩ hfull).2.le
  have hdelta : 2 * (e / 64) = e / 32 := by ring
  have hheadCeiling : key label ≤ (N : ℝ) ^ actualSelectedSubproductUpper 1 theta :=
    hheadUpper.trans (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith))
  have hmono : Monomials (N : ℝ) (e / 64) A
      (wp key out.left) (wp key out.middle) (wp key out.right) := by
    rcases hcases with ⟨hC, hmiddle, hright⟩ | ⟨hsmall, hrightEmpty, hmiddleBound, hDAhead⟩
    · have hmiddleKey : wp key out.middle = key label := by rw [hmiddle]; simp [wp]
      have hblower : (N : ℝ) ^ (2 * theta - 1) ≤ wp key out.middle := by
        rw [hmiddleKey]
        exact (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith)).trans hheadLower
      have hbupper : wp key out.middle ≤ (N : ℝ) ^ actualSelectedSubproductUpper 1 theta := by
        rw [hmiddleKey]
        exact hheadCeiling
      have hproduct : A * wp key out.middle * wp key out.right ≤
          (N : ℝ) ^ (theta - 2 * (e / 64)) := by
        rw [← hmiddleKey] at hright
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
      exact weak_medium_repair_monomials hNr (by linarith) htheta
        hApos ha hb hAupper hleft hproduct hbupper
  refine ⟨⟨ha, hb, hc⟩, hleft, hmono, fun x hx => transport hNpos hx hmono, ?_⟩
  intro ps hps
  obtain ⟨ls, ms, rs, hls, hms, hrs, hprod, hL, hM, hR⟩ := hwhole ps hps
  have hm := monomials_downward hNpos hApos (atom_product_pos N sigma _ _ hls)
    (atom_product_pos N sigma _ _ hms) (atom_product_pos N sigma _ _ hrs)
    ha hb hc hL hM hR hmono
  exact ⟨ls, ms, rs, hls, hms, hrs, hprod, hL, hM, hR, hm,
    fun x hx => transport hNpos hx hm⟩

end

end ImbalancedChen.Part3.ActualWCloseSameKeyMonomials
