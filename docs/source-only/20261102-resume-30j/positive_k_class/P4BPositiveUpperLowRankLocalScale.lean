import ImbalancedChen.P4BPositiveUpperLowRankClass
import ImbalancedChen.P5OriginalHBCompleteProductScale

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The imported I module supplies the COMPLETE outer HB scale from actual
ordered tuples. Only that generic source theorem is used; no W coefficient
or ALL16 lower grouping is imported as a licence for the upper coefficient.
The primitive beta allowance and kappa cap give a fixed half-level gap.
The theorem does not assert an atlas/trim producer or the BV estimate.
-/
namespace ImbalancedChen.P4BPositiveUpperLowRankLocalScale
noncomputable section
open P4BPositiveUpperLowRankClass
open P5Z.OriginalHBCompleteProductScale
open P5Z.HBRightClosedDyadicRoles

/-- One threshold precedes the HB groups, occurrence, blocks, upper policy,
enumeration cap and active modulus. The source supplies actual tuple
membership and its original smooth complete-product trim/support. No N-x
relation or below-half coefficient licence is supplied as a hypothesis. -/
theorem exists_original_upper_low_rank_local_threshold
    {C kappa kappa0 nu epsilon : ℝ}
    (hC : 0 < C) (hkappa : 0 < kappa) (hkappaSmall : kappa ≤ 1/100)
    (htrim : kappa0 < kappa/(4*(1+kappa)))
    (hnu : 0 ≤ nu) (hnu1 : nu ≤ 1)
    (hepsilon : 0 ≤ epsilon) (hepsilonSmall : epsilon ≤ 1/1000) :
    ∃ N0 : ℕ,2 ≤ N0 ∧ ∀ N : ℕ,N0 ≤ N →
      ∀ (gs : List OriginalGroupTuple) (p : ℕ) (b c : Block),
      p ∈ joined gs → Owns b p → Owns c (completeInteger gs/p) →
      (N : ℝ)^(1-kappa0) ≤ (completeInteger gs : ℝ) →
      (completeInteger gs : ℝ) ≤ C*N →
      ∀ (retain : List ℕ → Bool) (cap q : ℕ),
      rankRho retain N cap ((N : ℝ)^(nu*epsilon^2))
        ((N : ℝ)^(nu*(19/96 : ℝ))) ((N : ℝ)^(nu*epsilon)) 2 q ≠ 0 →
      1 < localScale b c ∧ 0 < q ∧ Squarefree q ∧ q.Coprime N ∧
      |rankRho retain N cap ((N : ℝ)^(nu*epsilon^2))
        ((N : ℝ)^(nu*(19/96 : ℝ))) ((N : ℝ)^(nu*epsilon)) 2 q| ≤ 1 ∧
      (q : ℝ) < localScale b c^(9/20 : ℝ) := by
  obtain ⟨N0,hN0,hscale⟩ := exists_actual_HB_residue_threshold hC hkappa htrim
  refine ⟨N0,hN0,?_⟩
  intro N hN gs p b c hp hb hc ht hs retain cap q hq
  have hN2 : 2 ≤ N := hN0.trans hN
  have hN1 : 1 < N := by omega
  obtain ⟨hx,_hlo,hres⟩ := hscale N hN gs p b c hp hb hc ht hs
  have hclass := attached_rank_two_support (fun _ => retain) (fun _ => cap)
    (mul_nonneg hnu (by norm_num : (0 : ℝ) ≤ 19/96)) hN1.le hq
  have hgap : epsilon < 5/48 := by linarith
  have hqN := (original_upper_rank_two_below_half (fun _ => retain) (fun _ => cap)
    hnu hnu1 hepsilon hgap hN1 hq).1
  refine ⟨hx,hclass.1,hclass.2.1,hclass.2.2.1,
    rankRho_abs_le_one _ _ _ _ _ _ _ _,?_⟩
  have ha : (0 : ℝ) ≤ 19/48+epsilon := by linarith
  have hexp : (1+kappa)*(19/48+epsilon) ≤ (9/20 : ℝ) := by
    have hmul := mul_le_mul
      (show 1+kappa ≤ (101/100 : ℝ) by linarith)
      (show 19/48+epsilon ≤ (19/48+1/1000 : ℝ) by linarith)
      ha (by norm_num : (0 : ℝ) ≤ 101/100)
    nlinarith
  calc
    (q : ℝ) < (N : ℝ)^(19/48+epsilon) := hqN
    _ ≤ (localScale b c^(1+kappa))^(19/48+epsilon) :=
      Real.rpow_le_rpow (Nat.cast_nonneg N) hres ha
    _ = localScale b c^((1+kappa)*(19/48+epsilon)) :=
      (Real.rpow_mul (zero_lt_one.trans hx).le _ _).symm
    _ ≤ localScale b c^(9/20 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx.le hexp

end
end ImbalancedChen.P4BPositiveUpperLowRankLocalScale
