import ImbalancedChen.P4AOriginalFull87SlotTwoFive
import ImbalancedChen.P4AFull87CompilerCapRead
import ImbalancedChen.P4AUpperTaggedContinuationAccounting
import ImbalancedChen.ActualUpperCountingInputs

/-! The cap-reading tag and beta attachment of the licensed full87 policy
in the general real counting interface. The density comparison retains the
literal unestimated signed sources of this policy. -/

namespace ImbalancedChen.P4AOriginalFull87CompiledCounting

noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P4AOriginalFull87RawChronology
open P4AOriginalFull87SlotTwoFive (exists_paid_original_sources sourceBound)
open P5OriginalCommonPositivePresieve (normalize normalize_add)
open OriginalThirdFiniteReserveSourceOnly (originalDensityReserve)
open P4AOriginalVariableFifthPhysicalLedger (raw negative physical smallPlus smallMinus physical_eq_signed_raw)
open P4AUpperTaggedContinuationAccounting
  (positiveChangedMass negativeChangedMass compiled_density_eq_full_plus_beta_and_changed_minus_correction)
open P4AFull87CompilerCapRead (tag)

abbrev moduli (N : ℕ) (w : ℝ) : Finset ℕ :=
  P4AUpperTaggedBetaAttachment.support N N w (cutoff N)

def coefficient (trim : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ)
    (history : ℕ → List Bool) (N : ℕ) (w tau L : ℝ) : ℕ → ℝ :=
  P4AUpperTaggedBetaAttachment.rho (licensed trim n e q a (N : ℝ) false)
    (tag trim n e q a (N : ℝ) history) N N w (cutoff N) tau L

/-- The original raw and negative rough masses integrate the two actual
beta deviations. The two tagged changed masses use their own signed
slopes. The complete upper projection subtracts the continuation once. -/
def signedCompilerSource (trim : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ)
    (history : ℕ → List Bool) (N : ℕ) (w tau L : ℝ) : ℝ :=
  let R := licensed trim n e q a (N : ℝ)
  let t := tag trim n e q a (N : ℝ) history
  let z := cutoff N
  raw R N N w z * (smallPlus N N w L - actualSmallEulerProduct N N w) +
    negative R N N w z * (smallPlus N N w L - smallMinus N N w L) +
    smallPlus N N w L * positiveChangedMass (R false) t N N w z tau +
    smallMinus N N w L * negativeChangedMass (R false) t N N w z tau -
    p4aActualPresieveCorrection (R false) N N w z

theorem physical_density_eq_raw_add_signed_source (trim : ℝ) (n : ℕ)
    (e : ℚ) (q : ℕ) (a : ℝ) (history : ℕ → List Bool) (N : ℕ)
    (w tau L : ℝ) (hwz : w ≤ cutoff N) :
    physicalDensitySum (moduli N w) (coefficient trim n e q a history N w tau L) =
      rawRoot (licensed trim n e q a (N : ℝ)) N +
        signedCompilerSource trim n e q a history N w tau L := by
  let R := licensed trim n e q a (N : ℝ)
  let t := tag trim n e q a (N : ℝ) history
  let z := cutoff N
  have hc := compiled_density_eq_full_plus_beta_and_changed_minus_correction
    (R false) t N N w z tau L hwz
  change physicalDensitySum (moduli N w) (coefficient trim n e q a history N w tau L) =
    rawRoot R N + (physical R N N w z L - actualSmallEulerProduct N N w * raw R N N w z) +
    smallPlus N N w L * positiveChangedMass (R false) t N N w z tau +
    smallMinus N N w L * negativeChangedMass (R false) t N N w z tau -
    p4aActualPresieveCorrection (R false) N N w z at hc
  rw [hc, physical_eq_signed_raw]
  change _ = rawRoot R N +
    (raw R N N w z * (smallPlus N N w L - actualSmallEulerProduct N N w) +
      negative R N N w z * (smallPlus N N w L - smallMinus N N w L) +
      smallPlus N N w L * positiveChangedMass (R false) t N N w z tau +
      smallMinus N N w L * negativeChangedMass (R false) t N N w z tau -
      p4aActualPresieveCorrection (R false) N N w z)
  ring

/-- Every modulus in the compiler's enlarged small-times-rough carrier
divides the literal product. Displayed zero coefficients are included. -/
theorem compiled_modulus_dvd (N : ℕ) (w : ℝ) (hw : w ≤ cutoff N)
    {m : ℕ} (hm : m ∈ moduli N w) : m ∣ sieveProduct N (Nat.ceil (cutoff N)) := by
  let z := cutoff N
  obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨ha, hd⟩ := Finset.mem_product.mp had
  have hsmall := actualSmallRosserSupport_dvd_sieveProduct_ceil N N w z hw ha
  have hsub : (roughPrimeUniverse N N w z).toFinset ⊆ sievePrimes N (Nat.ceil z) := by
    intro p hp
    have hp' := List.mem_toFinset.mp hp
    exact mem_sievePrimes.mpr ⟨Nat.lt_ceil.mpr (mem_roughPrimeUniverse_upper hp'),
      mem_roughPrimeUniverse_prime hp', mem_roughPrimeUniverse_not_dvd hp'⟩
  have heq : (∏ p ∈ (roughPrimeUniverse N N w z).toFinset, p) =
      (roughPrimeUniverse N N w z).prod := by
    simpa using List.prod_toFinset (fun p : ℕ => p) (roughPrimeUniverse_nodup N N w z)
  have hprod : (roughPrimeUniverse N N w z).prod ∣ sieveProduct N (Nat.ceil z) := by
    rw [← heq]
    exact Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p) hsub
  have hdiv : d ∣ (roughPrimeUniverse N N w z).prod := (Nat.mem_divisors.mp hd).1
  have hcop := smallPrimeSupportedAt_coprime_roughPrimeSupportedAt
    (actualSmallRosserSupport_smallPrimeSupportedAt N N w ha)
    (P2LowerFiniteCellRounding.universe_rough N N w z hd)
  exact hcop.mul_dvd_of_dvd_of_dvd hsmall (hdiv.trans hprod)

theorem compiler_majorizes_rough_indicator (trim : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (a : ℝ) (history : ℕ → List Bool) (N : ℕ) (w tau L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ cutoff N) (hzN : cutoff N ≤ (N : ℝ))
    (x : ℕ) :
    (if Nat.Coprime x (sieveProduct N (Nat.ceil (cutoff N))) then (1 : ℝ) else 0) ≤
      physicalDivisorSum (moduli N w) (coefficient trim n e q a history N w tau L) x := by
  have h := P4AUpperTaggedBetaAttachment.rho_majorant (licensed trim n e q a (N : ℝ) false)
    (tag trim n e q a (N : ℝ) history) N N w (cutoff N) tau L hL hwL hwz hzN (x : ℤ)
  rw [actualSmallRoughIndicator_eq_sieveProduct_natAbs] at h
  simpa only [Int.natAbs_natCast] using h

theorem compiler_coprime_correction_zero {b T : ℝ} (trim : ℝ)
    (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (history : ℕ → List Bool) (N : ℕ) (w tau L : ℝ)
    (hb : 0 < b) (hT : 0 < T) (hwz : w ≤ cutoff N)
    (hgate : (Nat.ceil (cutoff N) : ℝ) ≤ T ^ (b / (1 + b))) :
    realPhysicalCoprimeCorrection b N T (moduli N w) (coefficient trim n e q a history N w tau L) = 0 :=
  realPhysicalCoprimeCorrection_eq_zero_of_gate _ _ hb hT hgate
    (fun _ hm _ => compiled_modulus_dvd N w hwz hm)

/-- Same compiled coefficient in the finite real count, actual density
expansion and signed distribution error. Both geometric inputs have
been supplied for this ALL/ANY coefficient. -/
theorem real_count_le_original_sources_add_distribution {b T : ℝ} (trim : ℝ)
    (n : ℕ) (e : ℚ) (q : ℕ) (a : ℝ) (history : ℕ → List Bool) (N : ℕ) (w tau L : ℝ)
    (hb : 0 < b) (hb1 : b < 1) (hT : 0 < T)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ cutoff N) (hzN : cutoff N ≤ (N : ℝ))
    (hgate : (Nat.ceil (cutoff N) : ℝ) ≤ T ^ (b / (1 + b))) :
    (RealB b N : ℝ) ≤ ((realHalfProductSource b N T).card : ℝ) *
        (rawRoot (licensed trim n e q a (N : ℝ)) N + signedCompilerSource trim n e q a history N w tau L) +
      realPhysicalDistributionError b N T (moduli N w) (coefficient trim n e q a history N w tau L) +
      (Nat.ceil (cutoff N) : ℝ) + (T + 1) := by
  have h := RealB_cast_le_same_rho_main_add_distribution_of_gate N (Nat.ceil (cutoff N))
    (moduli N w) (coefficient trim n e q a history N w tau L) hb hb1 hT hgate
    (fun _ hm _ => compiled_modulus_dvd N w hwz hm)
    (compiler_majorizes_rough_indicator trim n e q a history N w tau L hL hwL hwz hzN)
  rw [physical_density_eq_raw_add_signed_source trim n e q a history N w tau L hwz] at h
  exact h

/-- Partial actual density in C_N/log N units. e,q,a and the actual
licensed full87 producer come from the same paid archive schedule as
the two original saving slots. The entire signed compiler expense and
remaining analytic density expression are still visible. -/
theorem exists_physical_density_le_paid_sources (eta eMax : ℝ) (heta : 0 < eta) (heMax : 0 < eMax) :
    ∃ a0 : ℝ, 0 < a0 ∧ a0 ≤ 1 / 800 ∧ a0 < (19 / 96 : ℝ) ∧
      ∀ a : ℝ, 0 < a → a ≤ a0 →
      ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ eMax ∧ e0 ≤ 3 / 51200 ∧
      ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < e0 →
      ∀ qMin mMin : ℕ, ∃ q0 : ℕ, 0 < q0 ∧ qMin ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q →
        let d := archiveData e q a
        mMin ≤ d.m ∧
        (P4ASameRhoCompact.originalOrdinaryRoot + actualExtendedThirdFiniteFunctional (e : ℝ) d.m ≤
          (∑ i, currentUpperEighteenPositive i) + originalDensityReserve / 4) ∧
        ∀ (trim : ℝ) (n : ℕ) (history : ℕ → ℕ → List Bool) (w L : ℕ → ℝ) (tau : ℝ),
        ∀ᶠ N : ℕ in atTop, Even N → w N ≤ cutoff N →
          physicalDensitySum (moduli N (w N)) (coefficient trim n e q a (history N) N (w N) tau (L N)) <
            (sourceBound trim n e q a N + eta +
              normalize N (signedCompilerSource trim n e q a (history N) N (w N) tau (L N))) *
                (singularSeries N / Real.log (N : ℝ)) := by
  obtain ⟨a0, ha0, hacap, harho, hA⟩ := exists_paid_original_sources eta eMax heta heMax
  refine ⟨a0, ha0, hacap, harho, ?_⟩
  intro a ha haa0
  obtain ⟨e0, he0, heMax', heBound, hE⟩ := hA a ha haa0
  refine ⟨e0, he0, heMax', heBound, ?_⟩
  intro e he hee qMin mMin
  obtain ⟨q0, hq0, hMin, hQ⟩ := hE e he hee qMin mMin
  refine ⟨q0, hq0, hMin, ?_⟩
  intro q hq
  obtain ⟨hm, hpos, hraw⟩ := hQ q hq
  refine ⟨hm, hpos, ?_⟩
  intro trim n history w L tau
  filter_upwards [hraw trim n, eventually_ge_atTop (2 : ℕ)] with N hN hN2
  intro hEven hwz
  let S := physicalDensitySum (moduli N (w N)) (coefficient trim n e q a (history N) N (w N) tau (L N))
  let C := signedCompilerSource trim n e q a (history N) N (w N) tau (L N)
  have hsame := congrArg (normalize N)
    (physical_density_eq_raw_add_signed_source trim n e q a (history N) N (w N) tau (L N) hwz)
  rw [normalize_add] at hsame
  have hnormalized : normalize N S < sourceBound trim n e q a N + eta + normalize N C := by
    change normalize N S = normalize N (rawRoot (licensed trim n e q a (N : ℝ)) N) + normalize N C at hsame
    linarith only [hsame, (hN hEven).2]
  have hscale := densityScale_pos hN2
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hcancel : normalize N S * (singularSeries N / Real.log (N : ℝ)) = S := by
    unfold normalize
    field_simp [(singularSeries_pos N).ne', hlog.ne'] <;> ring
  simpa only [hcancel] using mul_lt_mul_of_pos_right hnormalized hscale

end
end ImbalancedChen.P4AOriginalFull87CompiledCounting
