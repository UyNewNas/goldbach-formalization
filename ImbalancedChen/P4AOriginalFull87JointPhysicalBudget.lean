import ImbalancedChen.P4AOriginalFull87CompiledCounting
import ImbalancedChen.P4AFull87CompilerPhysicalPayment

/-! Actual cap=N joint density and count after applying the licensed
compiler estimate. The pending mass is the disjoint inherited first
disagreement sum. Its coefficient is the pre-policy beta constant
divided by the physical small-prime exponent. -/

namespace ImbalancedChen.P4AOriginalFull87JointPhysicalBudget

noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P4AFull87CompilerChangedPartition (Parameters pendingMass)
open P4AFull87CompilerPhysicalPayment (exists_actual_payment_with_inherited_remainder)
open P4AOriginalFull87RawChronology (archiveData licensed rawRoot cutoff)
open P4AOriginalFull87SlotTwoFive (sourceBound exists_paid_original_sources)
open P4AOriginalFull87CompiledCounting (moduli coefficient compiled_modulus_dvd compiler_majorizes_rough_indicator)
open P4AAll22OriginalKLedger20261024zSourceOnly (compilerReserve compilerReserve_pos)
open P5OriginalCommonPositivePresieve (normalize)
open OriginalThirdFiniteReserveSourceOnly (originalDensityReserve)

abbrev parameters (trim : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) : Parameters :=
  ⟨trim, n, e, q, a⟩

/-- Physical upper expression after the paid sources. The remaining
arithmetic terms are displayed under their original signs. -/
def upper (P : Parameters) (eta B omega tau : ℝ) (history : ℕ → List Bool) (N : ℕ) : ℝ :=
  (sourceBound P.delta P.n P.e P.q P.om N + eta + compilerReserve / 2 +
      B / omega * pendingMass P N N history omega (19 / 96) tau) *
    (singularSeries N / Real.log (N : ℝ)) -
    p4aActualPresieveCorrection (P.keep N) N N ((N : ℝ) ^ omega) (cutoff N)

theorem cutoff_le_target (N : ℕ) (hN : 1 ≤ (N : ℝ)) : cutoff N ≤ (N : ℝ) := by
  simpa only [cutoff, Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hN (show (19 / 96 : ℝ) ≤ 1 by norm_num)

private theorem of_normalized_lt {N : ℕ} (hN : 2 ≤ N) {x y : ℝ}
    (h : normalize N x < y) : x < y * (singularSeries N / Real.log (N : ℝ)) := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hcancel : normalize N x * (singularSeries N / Real.log (N : ℝ)) = x := by
    unfold normalize
    field_simp [(singularSeries_pos N).ne', hlog.ne'] <;> ring
  simpa only [hcancel] using mul_lt_mul_of_pos_right h (densityScale_pos hN)

/-- A single licensed producer and beta choice provide a bound for the
compiled density and the real bad-product count. No hdensity, correction,
endpoint, compiler-expense or distribution bound is an input. The real
signed distribution error remains an additive term of the count. -/
theorem exists_joint_physical_budget :
    ∃ B : ℝ, 0 < B ∧ ∀ eta eMax : ℝ, 0 < eta → 0 < eMax →
    ∃ a0 : ℝ, 0 < a0 ∧ a0 ≤ 1 / 800 ∧ a0 < (19 / 96 : ℝ) ∧
      ∀ a : ℝ, 0 < a → a ≤ a0 →
      ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ eMax ∧ e0 ≤ 3 / 51200 ∧
      ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < e0 →
      ∀ qMin mMin : ℕ, ∃ q0 : ℕ, 0 < q0 ∧ qMin ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q →
        let d := archiveData e q a
        mMin ≤ d.m ∧
        (P4ASameRhoCompact.originalOrdinaryRoot + actualExtendedThirdFiniteFunctional (e : ℝ) d.m ≤
          (∑ i, currentUpperEighteenPositive i) + originalDensityReserve / 4) ∧
        ∀ trim : ℝ, 0 < trim → ∀ (n : ℕ) (nu betaMax : ℝ), 0 < nu → 0 < betaMax →
        let P := parameters trim n e q a
        ∃ beta : ℝ, 0 < beta ∧ beta < 1 / 8 ∧ beta < betaMax ∧
          nu * beta ^ 2 < (19 / 96 : ℝ) ∧ nu * beta < 1 / 1000 ∧
        ∃ tau0 : ℝ, 0 < tau0 ∧ ∀ tau : ℝ, 0 < tau → tau ≤ tau0 →
          let omega := nu * beta ^ 2
          (∀ᶠ N : ℕ in atTop, Even N → ∀ history : ℕ → List Bool,
            let w := (N : ℝ) ^ omega
            let L := (N : ℝ) ^ (nu * beta)
            physicalDensitySum (moduli N w) (coefficient trim n e q a history N w tau L) <
              upper P eta B omega tau history N) ∧
          ∀ b kappa : ℝ, 0 < b → b < 1 →
            (19 / 96 : ℝ) < (1 - kappa) * (b / (1 + b)) →
            ∀ᶠ N : ℕ in atTop, Even N → ∀ history : ℕ → List Bool,
              let w := (N : ℝ) ^ omega
              let L := (N : ℝ) ^ (nu * beta)
              let T := manuscriptHalfProductCutoff kappa N
              (RealB b N : ℝ) ≤ ((realHalfProductSource b N T).card : ℝ) *
                upper P eta B omega tau history N +
                realPhysicalDistributionError b N T (moduli N w)
                  (coefficient trim n e q a history N w tau L) +
                (Nat.ceil (cutoff N) : ℝ) + (T + 1) := by
  obtain ⟨B, hB, hcompiler⟩ := exists_actual_payment_with_inherited_remainder
  refine ⟨B, hB, ?_⟩
  intro eta eMax heta heMax
  obtain ⟨a0, ha0, ha0max, ha0rho, hA⟩ := exists_paid_original_sources eta eMax heta heMax
  refine ⟨a0, ha0, ha0max, ha0rho, ?_⟩
  intro a ha haa0
  obtain ⟨e0, he0, he0max, he0bound, hE⟩ := hA a ha haa0
  refine ⟨e0, he0, he0max, he0bound, ?_⟩
  intro e he hee qMin mMin
  obtain ⟨q0, hq0, hmin, hQ⟩ := hE e he hee qMin mMin
  refine ⟨q0, hq0, hmin, ?_⟩
  intro q hq
  obtain ⟨hm, hpositive, hraw⟩ := hQ q hq
  refine ⟨hm, hpositive, ?_⟩
  intro trim htrim n nu betaMax hnu hmax
  let P := parameters trim n e q a
  let r : ℝ := (19 / 96 : ℝ) / nu
  have hr : 0 < r := div_pos (by norm_num) hnu
  have hnr : nu * r = (19 / 96 : ℝ) := by
    dsimp only [r]
    field_simp [hnu.ne'] <;> ring
  obtain ⟨beta, hb, hb8, hbmax, hsq, hbeta, tau0, ht0, Nc, hNc, hpay⟩ :=
    hcompiler P htrim nu r compilerReserve betaMax hnu hr compilerReserve_pos hmax
  let omega := nu * beta ^ 2
  have homega : omega < (19 / 96 : ℝ) := (mul_lt_mul_of_pos_left hsq hnu).trans_eq hnr
  refine ⟨beta, hb, hb8, hbmax, homega, hbeta, tau0, ht0, ?_⟩
  intro tau htau htt
  have hphys : ∀ᶠ N : ℕ in atTop, Even N → ∀ history : ℕ → List Bool,
      let w := (N : ℝ) ^ omega
      let L := (N : ℝ) ^ (nu * beta)
      physicalDensitySum (moduli N w) (coefficient trim n e q a history N w tau L) <
        upper P eta B omega tau history N := by
    filter_upwards [hraw trim n, eventually_ge_atTop Nc] with N hrawN hN
    intro hEven history
    have hN2 := hNc.trans hN
    have hNR : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hz := cutoff_le_target N hNR
    have hcov : (N : ℝ) ^ (nu * r) ≤ (N : ℝ) := by simpa only [hnr] using hz
    have h := (hpay N hN hEven N hcov history tau htau htt).2.2
    dsimp only at h
    simp only [hnr] at h
    let slope := B / omega * pendingMass P N N history omega (19 / 96) tau
    let scale := singularSeries N / Real.log (N : ℝ)
    let correction := p4aActualPresieveCorrection (P.keep N) N N ((N : ℝ) ^ omega) (cutoff N)
    change physicalDensitySum (moduli N ((N : ℝ) ^ omega))
      (coefficient trim n e q a history N ((N : ℝ) ^ omega) tau ((N : ℝ) ^ (nu * beta))) <
      rawRoot (licensed trim n e q a (N : ℝ)) N - correction +
        (compilerReserve / 2 + slope) * scale at h
    have hrN := of_normalized_lt hN2 (hrawN hEven).2
    change rawRoot (licensed trim n e q a (N : ℝ)) N <
      (sourceBound trim n e q a N + eta) * scale at hrN
    change _ < (sourceBound trim n e q a N + eta + compilerReserve / 2 + slope) * scale - correction
    nlinarith only [h, hrN]
  refine ⟨hphys, ?_⟩
  intro b kappa hbpos hb1 hgap
  have hgate := eventually_manuscript_sieve_gate hbpos
    (by norm_num : (0 : ℝ) ≤ 19 / 96) hgap
  filter_upwards [hphys, hgate, eventually_ge_atTop (2 : ℕ)] with N hd hgateN hN2
  intro hEven history
  let w := (N : ℝ) ^ omega
  let L := (N : ℝ) ^ (nu * beta)
  let T := manuscriptHalfProductCutoff kappa N
  have hNR : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL : 1 < L := Real.one_lt_rpow hNR (mul_pos hnu hb)
  have hb1' : beta < 1 := hb8.trans (by norm_num)
  have hwL : w ≤ L := Real.rpow_le_rpow_of_exponent_le hNR.le
    (mul_le_mul_of_nonneg_left (by nlinarith [mul_lt_mul_of_pos_left hb1' hb] : beta ^ 2 ≤ beta) hnu.le)
  have hwz : w ≤ cutoff N := Real.rpow_le_rpow_of_exponent_le hNR.le homega.le
  have hc := RealB_cast_le_same_rho_main_add_distribution_of_gate N (Nat.ceil (cutoff N))
    (moduli N w) (coefficient trim n e q a history N w tau L) hbpos hb1 hgateN.1 hgateN.2
    (fun _ hm _ => compiled_modulus_dvd N w hwz hm)
    (compiler_majorizes_rough_indicator trim n e q a history N w tau L hL hwL hwz
      (cutoff_le_target N hNR.le))
  have hm := mul_le_mul_of_nonneg_left (hd hEven history).le
    (Nat.cast_nonneg (realHalfProductSource b N T).card)
  exact hc.trans (add_le_add_right (add_le_add_right (add_le_add_right hm _) _) _)

end
end ImbalancedChen.P4AOriginalFull87JointPhysicalBudget
