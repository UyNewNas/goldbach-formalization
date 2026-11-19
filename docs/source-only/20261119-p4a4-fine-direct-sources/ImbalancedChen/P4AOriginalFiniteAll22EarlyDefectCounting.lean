import ImbalancedChen.P4AOriginalFiniteAll22Nineteen
import ImbalancedChen.P4AOriginalFiniteFallbackCanonical

/-!
SOURCE ONLY / UNCOMPILED / NOT KERNEL ACCEPTED.

The nineteen paid slots, one actual final compiler, and the real finite
count share the same parameters and the same Q/rho. The original early
defect and the signed distribution error remain in full. In particular
this is not an unconditional hUpper theorem.
-/
namespace ImbalancedChen.P4AOriginalFiniteAll22EarlyDefectCounting

noncomputable section
open Filter Topology
open scoped Classical BigOperators
open P4AOriginalNewFifthUnion (data)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P4AOriginalFull87CompiledCounting (moduli)
open P4AOriginalOrderedThirdActualCoefficient (alignedWidth)
open P4AOriginalFiniteFallbackCount (jointIndex)
open P4AFallbackCanonicalBanks (bank)
open P4AOriginalFiniteFallbackPolicy (F)
open P4AOriginalFiniteAll22RawLedger (finalPolicy lowerEarlyDefect)
open P4AAll22OriginalKLedger20261024zSourceOnly
  (quotedAll22Raw densityReserve compilerReserve exactSlack)

/-- The original early defect is explicit. The one compiler reserve has
already been included; the density reserve and exact slack are retained. -/
def physicalUpperWithEarlyDefect
    (m r n : ℕ) (e : ℚ) (q : ℕ) (a omega eta : ℝ) (N : ℕ) : ℝ :=
  (currentK - densityReserve - exactSlack + lowerEarlyDefect n e q a omega N + eta) *
      (singularSeries N / Real.log (N : ℝ)) -
    p4aActualPresieveCorrection (F (bank m) (width r) n (data e q a) omega N)
      N N ((N : ℝ) ^ omega) (cutoff N)

/-- Select beta after the common raw schedule, then use the final bank's
single compiler. The conclusion is a true same-Q/rho finite count with
the unpaid early defect and signed error left on its right side. -/
theorem exists_same_coefficient_density_and_count_with_early_defect
    (eta eMax : ℝ) (heta : 0 < eta) (heMax : 0 < eMax) :
    ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
      ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r →
      ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∃ E : ℝ, 0 < E ∧ E ≤ eMax ∧
      ∀ e : ℚ, 0 < (e : ℝ) → (e : ℝ) < E → ∀ qMin : ℕ,
      ∃ q0 : ℕ, 0 < q0 ∧ qMin ≤ q0 ∧ ∀ q : ℕ, q0 ≤ q →
      ∀ a : ℝ, 0 < a → a ≤ 1 / 800 →
      ∀ nu v epsilonMax : ℝ, 0 < nu → 0 < v → nu * v = 19 / 96 → 0 < epsilonMax →
      ∃ eps : ℝ, 0 < eps ∧ eps < 1 / 8 ∧ eps < epsilonMax ∧ eps ^ 2 < v ∧
        nu * eps ^ 2 < a ∧ nu * eps < 1 / 1000 ∧
      ∃ k N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
        let omega := nu * eps ^ 2
        let tau := alignedWidth (jointIndex (bank m) (data e q a).m) k
        let w := (N : ℝ) ^ omega
        let z := cutoff N
        let L := (N : ℝ) ^ (nu * eps)
        let Q := moduli N w
        let rho := P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N tau L
        let f := F (bank m) (width r) n (data e q a) omega N
        ((N : ℝ) / Real.log (N : ℝ)) *
          P4AFiniteCapTaggedConstructor.compilerExpense f (fun _ => []) N N w z tau L <
            compilerReserve * singularNormalization N ∧
        physicalDensitySum Q rho < physicalUpperWithEarlyDefect m r n e q a omega eta N ∧
        (∀ d : ℕ, rho d ≠ 0 → (d : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ)) ∧
        ∀ b T : ℝ, 0 < b → b < 1 → 0 < T →
          (Nat.ceil z : ℝ) ≤ T ^ (b / (1 + b)) →
          (RealB b N : ℝ) ≤
            ((realHalfProductSource b N T).card : ℝ) *
              physicalUpperWithEarlyDefect m r n e q a omega eta N +
            realPhysicalDistributionError b N T Q rho + (Nat.ceil z : ℝ) + (T + 1) := by
  obtain ⟨h, hh, m0, hM⟩ :=
    P4AOriginalFiniteAll22Nineteen.exists_final_raw_upper_with_early_defect
      eta eMax heta heMax
  refine ⟨m0, ?_⟩
  intro m hm
  obtain ⟨r0, hR⟩ := hM m hm
  refine ⟨r0, ?_⟩
  intro r hr
  obtain ⟨n0, hN⟩ := hR r hr
  refine ⟨n0, ?_⟩
  intro n hn
  obtain ⟨E, hE, hEmax, hEall⟩ := hN n hn
  refine ⟨E, hE, hEmax, ?_⟩
  intro e he heE qMin
  obtain ⟨q0, hq0, hqMin, hQ⟩ := hEall e he heE qMin
  refine ⟨q0, hq0, hqMin, ?_⟩
  intro q hq a ha haSmall nu v epsilonMax hnu hv hcut hepsilonMax
  have heRat : 0 ≤ e := by exact_mod_cast he.le
  obtain ⟨eps, heps, heps8, hepsMax, hepsSq, homegaA, hlog,
      k, NC, hNC, hCompiled⟩ :=
    P4AOriginalFiniteFallbackCanonical.paid m r n e heRat q a ha
      nu v compilerReserve (min epsilonMax (h / nu)) hnu hv hcut
      P4AAll22OriginalKLedger20261024zSourceOnly.compilerReserve_pos
      (lt_min hepsilonMax (div_pos hh hnu))
  let omega : ℝ := nu * eps ^ 2
  have homega : 0 < omega := mul_pos hnu (sq_pos_of_pos heps)
  have homegaR : omega < thirdPrefixRho := by
    have hmul := mul_lt_mul_of_pos_left hepsSq hnu
    simpa only [hcut, thirdPrefixRho] using hmul
  have homegaH : omega ≤ h := by
    have hlinear := (lt_div_iff₀ hnu).mp (hepsMax.trans_le (min_le_right _ _))
    have hlinear' : nu * eps < h := by simpa only [mul_comm] using hlinear
    have hepsOne : eps < 1 := by linarith only [heps8]
    have hsq : eps ^ 2 ≤ eps := by nlinarith only [heps.le, hepsOne.le]
    exact (mul_le_mul_of_nonneg_left hsq hnu.le).trans hlinear'.le
  obtain ⟨NR, hRaw⟩ := eventually_atTop.mp
    (hQ q hq a omega homega homegaR homegaA.le homegaH haSmall)
  refine ⟨eps, heps, heps8, hepsMax.trans_le (min_le_left _ _), hepsSq,
    homegaA, hlog, k, max NC NR, hNC.trans (le_max_left _ _), ?_⟩
  intro N hN0 hEven
  have hNC' : NC ≤ N := (le_max_left _ _).trans hN0
  have hNR : NR ≤ N := (le_max_right _ _).trans hN0
  have hN2 : 2 ≤ N := hNC.trans hNC'
  obtain ⟨hNRaw, hRawUpper⟩ := hRaw N hNR hEven
  obtain ⟨hExpense, hDensity, hSupport, hCount⟩ := hCompiled N hNC' hEven
  dsimp only at hExpense hDensity hSupport hCount ⊢
  have hRawScale :
      rawRoot (finalPolicy m r n e q a omega N) N ≤
        (quotedAll22Raw + lowerEarlyDefect n e q a omega N + eta) *
          (singularSeries N / Real.log (N : ℝ)) :=
    (density_le_manuscriptScale_iff_normalized hN2 _ _).mpr hRawUpper.le
  have hCoefficient :
      quotedAll22Raw + lowerEarlyDefect n e q a omega N + eta + compilerReserve =
        currentK - densityReserve - exactSlack + lowerEarlyDefect n e q a omega N + eta := by
    linarith only [P4AAll22OriginalKLedger20261024zSourceOnly.exact_original_budget_identity]
  have hReserve :=
    P4AOriginalFiniteAll22PhysicalLedger.reserve_raw_is_actual_final m r n e q a omega N
  have hUpper :
      physicalDensitySum
        (moduli N ((N : ℝ) ^ omega))
        (P4AOriginalFiniteFallbackPolicy.rho (bank m) r n e q a omega N
          (alignedWidth (jointIndex (bank m) (data e q a).m) k) ((N : ℝ) ^ (nu * eps))) <
        physicalUpperWithEarlyDefect m r n e q a omega eta N := by
    rw [hReserve] at hDensity
    unfold physicalUpperWithEarlyDefect
    have hScale :
        rawRoot (finalPolicy m r n e q a omega N) N +
          compilerReserve * (singularSeries N / Real.log (N : ℝ)) ≤
        (currentK - densityReserve - exactSlack + lowerEarlyDefect n e q a omega N + eta) *
          (singularSeries N / Real.log (N : ℝ)) := by
      calc
        _ ≤ (quotedAll22Raw + lowerEarlyDefect n e q a omega N + eta) *
              (singularSeries N / Real.log (N : ℝ)) +
            compilerReserve * (singularSeries N / Real.log (N : ℝ)) :=
          add_le_add_right hRawScale _
        _ = _ := by rw [← add_mul, hCoefficient]
    linarith only [hDensity, hScale]
  refine ⟨hExpense, hUpper, hSupport, ?_⟩
  intro b T hb hb1 hT hgate
  have hFinite := hCount b T hb hb1 hT hgate
  have hMass := mul_le_mul_of_nonneg_left hUpper.le
    (Nat.cast_nonneg (realHalfProductSource b N T).card)
  exact hFinite.trans
    (add_le_add_right (add_le_add_right (add_le_add_right hMass _) _) _)

end
end ImbalancedChen.P4AOriginalFiniteAll22EarlyDefectCounting
