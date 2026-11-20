import ImbalancedChen.P4AOriginalR17PaidIntegral

/-! SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
Expose positive physical scales and the actual same-rho majorant using
the beta already selected by the original R17 envelope. No historical
fourth-source or geometric-corner identification is asserted. -/
namespace ImbalancedChen.P2Saving16SameBetaPositiveLicense
noncomputable section
open scoped Classical BigOperators
open P4AOriginalR17PaidIntegral (integralUpper)
open P4AOriginalOrderedThirdActualCoefficient (coefficient keep alignedWidth)
open P4AOriginalFull87RawChronology (cutoff rawRoot)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalNewFifthUnion (data)
open P4AOrderedThirdArithmeticOccurrence (fresh)
open P5OriginalCommonPositivePresieve (normalize)

/-- The original one-beta numerical constraints give strictly positive
presieving, the small Rosser cutoff, and the strict rough cutoff in the
original order. -/
theorem original_beta_physical_scales (N : ℕ) (hN : 1 < (N : ℝ))
    (nu v beta : ℝ) (hnu : 0 < nu) (hbeta : 0 < beta) (h8 : beta < 1/8)
    (hsq : beta^2 < v) (hcut : nu*v = (19/96 : ℝ)) :
    let w := (N : ℝ)^(nu*beta^2)
    let L := (N : ℝ)^(nu*beta)
    let z := cutoff N
    1 < w ∧ w < L ∧ w < z ∧ z ≤ (N : ℝ) := by
  have hb1 : beta < 1 := by linarith
  have hbprod : 0 < beta * (1-beta) := mul_pos hbeta (sub_pos.mpr hb1)
  have hb2 : beta^2 < beta := by nlinarith only [hbprod]
  have hwL : nu*beta^2 < nu*beta := mul_lt_mul_of_pos_left hb2 hnu
  have hwz : nu*beta^2 < (19/96 : ℝ) := by
    have h := mul_lt_mul_of_pos_left hsq hnu
    rw [hcut] at h
    exact h
  dsimp only
  refine ⟨Real.one_lt_rpow hN (mul_pos hnu (sq_pos_of_pos hbeta)),
    Real.rpow_lt_rpow_of_exponent_lt hN hwL, ?_, ?_⟩
  · change (N : ℝ)^(nu*beta^2) < (N : ℝ)^(19/96 : ℝ)
    exact Real.rpow_lt_rpow_of_exponent_lt hN hwz
  · change (N : ℝ)^(19/96 : ℝ) ≤ (N : ℝ)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN.le
      (show (19/96 : ℝ) ≤ 1 by norm_num)

/-- The same beta, mesh, Q, rho, complete compiler expense and both
original count inequalities survive unchanged; positive-w and the
actual same-rho pointwise majorant are added from those parameters. -/
theorem original_envelope_with_same_beta_positive_license (eta : ℝ) (heta : 0 < eta) :
    ∃ r0 : ℕ, ∀ r ≥ r0, ∃ n0 : ℕ, ∀ n ≥ n0,
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
    ∃ q0 : ℕ, 0 < q0 ∧ ∀ q ≥ q0, ∀ a : ℝ, 0 < a → a ≤ 1/100 →
    ∀ nu v u_c betaMax : ℝ, 0 < nu → 0 < v → nu*v = 19/96 → 0 < u_c → 0 < betaMax →
    ∃ beta : ℝ, 0 < beta ∧ beta < 1/8 ∧ beta < betaMax ∧ beta^2 < v ∧
      nu*beta^2 < a ∧ nu*beta < 1/1000 ∧
    ∃ k N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, Even N →
      let omega := nu*beta^2
      let tau := alignedWidth (data e q a).m k
      let w := (N : ℝ)^omega
      let z := cutoff N
      let L := (N : ℝ)^(nu*beta)
      let Q := moduli N w
      let rho := coefficient r n e q a omega N tau L
      let f := keep r n e q a omega N
      let U := integralUpper r n e q a omega eta u_c N
      1 < w ∧ w < L ∧ w < z ∧ z ≤ (N : ℝ) ∧
      (∀ x : ℕ, (if x.Coprime (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho x) ∧
      normalize N (rawRoot (fresh (data e q a) omega N) N) <
          (∑ i, currentUpperEighteenPositive i)+eta ∧
      ((N : ℝ)/Real.log (N : ℝ))*P4AFiniteCapTaggedConstructor.compilerExpense f (fun _ => []) N N w z tau L
          < u_c*singularNormalization N ∧
      physicalDensitySum Q rho < U ∧
      (∀ m : ℕ, rho m ≠ 0 → (m : ℝ) < (N : ℝ)^(599/1000 : ℝ)) ∧
      ∀ b T : ℝ, 0 < b → b < 1 → 0 < T → (Nat.ceil z : ℝ) ≤ T^(b/(1+b)) →
        let mass := ((realHalfProductSource b N T).card : ℝ)
        let err := realPhysicalDistributionError b N T Q rho
        (RealB b N : ℝ) ≤ mass*physicalDensitySum Q rho+err+(Nat.ceil z : ℝ)+(T+1) ∧
        (RealB b N : ℝ) ≤ mass*U+err+(Nat.ceil z : ℝ)+(T+1) := by
  obtain ⟨r0, hr⟩ := P4AOriginalR17PaidIntegral.original_signed_density_and_count eta heta
  refine ⟨r0, ?_⟩
  intro r hrr
  obtain ⟨n0, hn⟩ := hr r hrr
  refine ⟨n0, ?_⟩
  intro n hnn
  obtain ⟨e0, he0, he⟩ := hn n hnn
  refine ⟨e0, he0, ?_⟩
  intro e hepos hee
  obtain ⟨q0, hq0, hq⟩ := he e hepos hee
  refine ⟨q0, hq0, ?_⟩
  intro q hqq a ha ha1 nu v u_c betaMax hnu hv huv hu hbmax
  obtain ⟨beta, hb, hb8, hbmax', hsq, hwa, hL, k, N0, hN0, hsource⟩ :=
    hq q hqq a ha ha1 nu v u_c betaMax hnu hv huv hu hbmax
  refine ⟨beta, hb, hb8, hbmax', hsq, hwa, hL, k, N0, hN0, ?_⟩
  intro N hN hEven
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hs := original_beta_physical_scales N hNr nu v beta hnu hb hb8 hsq huv
  have hmajor := P4AOriginalOrderedThirdActualCoefficient.upper_majorant
    r n e q a (nu*beta^2) N (alignedWidth (data e q a).m k) ((N : ℝ)^(nu*beta))
      (hs.1.trans hs.2.1) hs.2.1.le hs.2.2.1.le hs.2.2.2
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, hmajor, hsource N hN hEven⟩

end
end ImbalancedChen.P2Saving16SameBetaPositiveLicense
