import ImbalancedChen.P5ZU1011SameRhoCompleteScaleFactors

/-!
# A simultaneous original native / complete-product factorization query

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The physical construction asks for N^kappa <= A <= N^(1/3-kappa/2).
A local complete-product factorization query has the corresponding x
interval. Neither interval contains the other throughout the original
strip c*N^(1-kappa0) <= x <= C*N. This module proves their intersection
is nonempty uniformly, keeping the entire original kappa/kappa0 ranges.
The common choice max(N^kappa,x^kappa) precedes every native coefficient,
outer mask, and mark. Fixed C is absorbed before N and x are quantified.

An HB block may demand a particular query rather than this choice. The
result is an actual simultaneous eligibility primitive; it does not assert
that every block lies in this intersection or supply signed PP.
-/

namespace ImbalancedChen.P5Z.U1011OriginalCompleteScaleQueryIntersection

noncomputable section
open Classical Filter
open U1011OriginalSixteenNearCapCommonSmallParameters (kappaMax)

def commonQuery (N : ℕ) (x kappa : ℝ) : ℝ :=
  max ((N : ℝ) ^ kappa) (x ^ kappa)

/-- The original common native range leaves a strict cross-scale reserve. -/
theorem original_query_exponent_reserves {kappa : ℝ}
    (hk0 : 0 < kappa) (hk : kappa ≤ 1 / 8) :
    kappa < 1 / 3 - kappa / 2 ∧
      (1 + kappa) * kappa < 1 / 3 - kappa / 2 := by
  have hmul : kappa ^ 2 ≤ kappa / 8 := by nlinarith
  constructor <;> nlinarith

/-- Fixed chart constants and target thresholds are chosen before x.
All four bounds concern the SAME A, with the SAME original kappa. -/
theorem exists_simultaneous_query_threshold
    {c C kappa kappa0 : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hk0 : 0 < kappa) (hk : kappa ≤ 1 / 8)
    (ht : kappa0 < kappa / (4 * (1 + kappa))) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - kappa0) ≤ x → x ≤ C * N →
      (N : ℝ) ^ kappa ≤ commonQuery N x kappa ∧
        commonQuery N x kappa ≤ (N : ℝ) ^ (1 / 3 - kappa / 2) ∧
        x ^ kappa ≤ commonQuery N x kappa ∧
        commonQuery N x kappa ≤ x ^ (1 / 3 - kappa / 2) := by
  obtain ⟨hgap, hcrossgap⟩ := original_query_exponent_reserves hk0 hk
  obtain ⟨_, N1, hN1, hscale⟩ :=
    exists_manuscript_restrictedResidueScale_threshold hc hC hk0 ht
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp
    (eventually_const_mul_rpow_le_rpow (C ^ kappa) hgap)
  refine ⟨max N1 N2, hN1.trans (le_max_left _ _), ?_⟩
  intro N hN x hlow hupp
  obtain ⟨hx, _, hresidue⟩ := hscale N ((le_max_left _ _).trans hN) x hlow hupp
  have hNN : 1 < N := lt_of_lt_of_le (by omega : 1 < N1)
    ((le_max_left _ _).trans hN)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt hNN)
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNr
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hNown : (N : ℝ) ^ kappa ≤ (N : ℝ) ^ (1 / 3 - kappa / 2) :=
    Real.rpow_le_rpow_of_exponent_le hNr hgap.le
  have hxown : x ^ kappa ≤ x ^ (1 / 3 - kappa / 2) :=
    Real.rpow_le_rpow_of_exponent_le hx.le hgap.le
  have hNtoX : (N : ℝ) ^ kappa ≤ x ^ (1 / 3 - kappa / 2) := by
    calc
      _ ≤ (x ^ (1 + kappa)) ^ kappa :=
        Real.rpow_le_rpow hNpos.le hresidue hk0.le
      _ = x ^ ((1 + kappa) * kappa) := (Real.rpow_mul hxpos.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le hcrossgap.le
  have hXtoN : x ^ kappa ≤ (N : ℝ) ^ (1 / 3 - kappa / 2) := by
    calc
      _ ≤ (C * (N : ℝ)) ^ kappa := Real.rpow_le_rpow hxpos.le hupp hk0.le
      _ = C ^ kappa * (N : ℝ) ^ kappa := Real.mul_rpow hC.le hNpos.le
      _ ≤ _ := hN2 N ((le_max_right _ _).trans hN)
  exact ⟨le_max_left _ _, max_le hNown hXtoN,
    le_max_right _ _, max_le hNtoX hxown⟩

/-- The actual eta-dependent common native bank supplies the needed
range; no extra smallness restriction is imposed. N0 precedes every target
and x; the displayed common A then precedes all masks and native marks. -/
theorem exists_original_native_common_query_threshold
    (n : ℕ) (eta : ℚ) {c C kappa kappa0 : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hk0 : 0 < kappa)
    (hk : kappa ≤ (kappaMax n eta : ℝ))
    (ht : kappa0 < kappa / (4 * (1 + kappa))) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - kappa0) ≤ x → x ≤ C * N →
      ∃ A : ℝ, A = commonQuery N x kappa ∧
        (N : ℝ) ^ kappa ≤ A ∧ A ≤ (N : ℝ) ^ (1 / 3 - kappa / 2) ∧
        x ^ kappa ≤ A ∧ A ≤ x ^ (1 / 3 - kappa / 2) := by
  have hmax : (kappaMax n eta : ℝ) ≤ 1 / 8 := by
    exact_mod_cast U1011OriginalSixteenNearCapCommonSmallParameters.kappaMax_le_eighth n eta
  obtain ⟨N0, hN0, hquery⟩ := exists_simultaneous_query_threshold hc hC hk0 (hk.trans hmax) ht
  refine ⟨N0, hN0, ?_⟩
  intro N hN x hlow hupp
  exact ⟨commonQuery N x kappa, rfl, hquery N hN x hlow hupp⟩

end
end ImbalancedChen.P5Z.U1011OriginalCompleteScaleQueryIntersection
