import ImbalancedChen.P2FiniteMarkedGamma5SeedCorrectionPayment
import ImbalancedChen.P4BLogSavingBudget
import Mathlib.Order.Filter.Finite

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

The actual finite Gamma5 atlas consumes one same-coefficient signed
prime-product estimate per fixed entry. This file proves only the finite
aggregation and normalization of that explicit P3 input. It does not
prove the input, replace the full weight by a truncated one, or supply
uniformity for target-dependent geometry.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5SeedSignedPPPayment
noncomputable section

open Filter Finset Real
open P2FiniteMarkedGamma5NativeSeedSum (Index fixedWeight)
open Part5OriginalH430PhysicalRoots (Root)
open P2FiniteMarkedGamma5SeedAtlasFinitePP (Entry rank mark_nonneg)
open P2FiniteMarkedGamma5SeedCorrectionCarrier (actualWeight)
open P4AOriginalFiniteFallbackBank (Bank)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalFull87RawChronology (cutoff)
open P4AOriginalFiniteFallbackPolicy (rho)
open scoped Classical Topology BigOperators

/-- Constants may depend on the fixed entry. Finiteness supplies one
eventual set for all entries; the old logarithmic-saving budget pays
their original positively marked sum. Q and rho are the same in every
entry. In particular, there is no absolute value inside the modulus sum. -/
theorem actual_signed_errors_of_entry_A3
    {n : ℕ} (root : Root) (tau : ℝ) (mesh : Index 430 → ℕ)
    {h : ℝ} (hp : 0 < h) (h8 : h ≤ 1/8)
    (Q : ℕ → Finset ℕ) (R : ℕ → ℕ → ℝ)
    (hPP : ∀ v : Entry n, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, Even N →
        |Part3.primeProductSignedError (rank v) (2*N) N (Q N) (R N)
          (actualWeight v root tau mesh hp h8 N)| ≤
            C * (N : ℝ) / (log (N : ℝ)) ^ (3 : ℕ))
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      |∑ v : Entry n, fixedWeight v.val.1 *
        Part3.primeProductSignedError (rank v) (2*N) N (Q N) (R N)
          (actualWeight v root tau mesh hp h8 N)| ≤
            epsilon * singularNormalization N := by
  choose C hC hbound using hPP
  let B : ℝ := ∑ v : Entry n, fixedWeight v.val.1 * C v
  have hB : 0 ≤ B := sum_nonneg fun v _ => mul_nonneg (mark_nonneg _) (hC v)
  have Hall := eventually_all_finite.mpr hbound
  filter_upwards [Hall,
    eventually_logSaving_le_singularNormalization B hB 3 (by norm_num) epsilon he]
    with N hN hbudget
  intro hEven
  let E := fun v : Entry n =>
    Part3.primeProductSignedError (rank v) (2*N) N (Q N) (R N)
      (actualWeight v root tau mesh hp h8 N)
  change |∑ v : Entry n, fixedWeight v.val.1 * E v| ≤ _
  calc
    _ ≤ ∑ v : Entry n, |fixedWeight v.val.1 * E v| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ v : Entry n, fixedWeight v.val.1 * |E v| := by
      apply sum_congr rfl
      intro v _
      rw [abs_mul, abs_of_nonneg (mark_nonneg _)]
    _ ≤ ∑ v : Entry n, fixedWeight v.val.1 *
        (C v * (N : ℝ) / (log (N : ℝ)) ^ (3 : ℕ)) :=
      sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hN v hEven) (mark_nonneg _)
    _ = B * (N : ℝ) / (log (N : ℝ)) ^ (3 : ℕ) := by
      dsimp only [B]
      rw [sum_mul, sum_div]
      apply sum_congr rfl
      intro v _
      ring
    _ ≤ _ := hbudget.2

/-- The original P3 target, if provided for each actual entry, supplies
exactly the preceding A=3 premise. No common constant over an infinite
geometric parameter space is assumed or extracted. -/
theorem actual_signed_errors_of_uniformPP
    {n : ℕ} (root : Root) (tau : ℝ) (mesh : Index 430 → ℕ)
    {h : ℝ} (hp : 0 < h) (h8 : h ≤ 1/8)
    (Q : ℕ → Finset ℕ) (R : ℕ → ℕ → ℝ)
    (hPP : ∀ v : Entry n,
      Part3.UniformPrimeProductTarget (ι := Unit) (rank v) (fun N => 2*N) Q R
        (fun N _ => actualWeight v root tau mesh hp h8 N))
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      |∑ v : Entry n, fixedWeight v.val.1 *
        Part3.primeProductSignedError (rank v) (2*N) N (Q N) (R N)
          (actualWeight v root tau mesh hp h8 N)| ≤
            epsilon * singularNormalization N := by
  apply actual_signed_errors_of_entry_A3 root tau mesh hp h8 Q R ?_ he
  intro v
  obtain ⟨C,hC,N0,H⟩ := hPP v (3 : ℝ) (by norm_num)
  refine ⟨C,hC.le,?_⟩
  filter_upwards [eventually_ge_atTop N0] with N hN
  intro hEven
  rw [← Real.rpow_natCast (log (N : ℝ)) (3 : ℕ)]
  exact H N hN hEven Unit.unit

/-- All three actual finite-fallback errors are negligible at one fixed
precision. The noncoprime and small-prime payments are proved old
suppliers; only the displayed actual signed A=3 premise remains an
analytic input. The active-support premise is delivered by FineDensity. -/
theorem actual_all_errors_of_entry_A3
    (n : ℕ) (root : Root) (tau : ℝ) (mesh : Index 430 → ℕ)
    {h : ℝ} (hp : 0 < h) (h8 : h ≤ 1/8)
    (B : Bank) (r p : ℕ) (e : ℚ) (q : ℕ) (a omega tauGrid : ℝ) (L : ℕ → ℝ)
    (hsupport : ∀ᶠ N : ℕ in atTop, Even N → ∀ d : ℕ,
      rho B r p e q a omega N tauGrid (L N) d ≠ 0 →
        (d : ℝ) < (N : ℝ) ^ (599/1000 : ℝ))
    (hPP : ∀ v : Entry n, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, Even N →
        |Part3.primeProductSignedError (rank v) (2*N) N
          (moduli N ((N : ℝ)^omega)) (rho B r p e q a omega N tauGrid (L N))
          (actualWeight v root tau mesh hp h8 N)| ≤
            C * (N : ℝ) / (log (N : ℝ)) ^ (3 : ℕ))
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      let D := moduli N ((N : ℝ)^omega)
      let R := rho B r p e q a omega N tauGrid (L N)
      let S := fun v : Entry n => Part3.labelledPrimeTuples (rank v) (2*N)
      let W := fun v : Entry n => actualWeight v root tau mesh hp h8 N
      |∑ v : Entry n, fixedWeight v.val.1 *
        p5z_labelledCoprimeCorrection (S v) Part3.labelledProduct (W v) D R| +
      |∑ v : Entry n, fixedWeight v.val.1 *
        Part3.primeProductSignedError (rank v) (2*N) N D R (W v)| +
      (∑ v : Entry n, fixedWeight v.val.1 *
        p5z_labelledSmallPrimeMass (S v) Part3.labelledProduct (W v) N (Nat.ceil (cutoff N))) ≤
          epsilon * singularNormalization N := by
  have Hsigned := actual_signed_errors_of_entry_A3 root tau mesh hp h8
    (fun N => moduli N ((N : ℝ)^omega))
    (fun N => rho B r p e q a omega N tauGrid (L N)) hPP (half_pos he)
  have Hcorrection :=
    P2FiniteMarkedGamma5SeedCorrectionPayment.actual_fallback_errors
      n root tau mesh hp h8 (half_pos he)
  filter_upwards [Hsigned,Hcorrection,hsupport] with N hsign hcorr hsupp
  intro hEven
  have Hs := hsign hEven
  have Hc := hcorr hEven B r p e q a omega tauGrid (L N) (hsupp hEven)
  dsimp only at Hs Hc ⊢
  linarith only [Hs,Hc]

end
end ImbalancedChen.P2FiniteMarkedGamma5SeedSignedPPPayment
