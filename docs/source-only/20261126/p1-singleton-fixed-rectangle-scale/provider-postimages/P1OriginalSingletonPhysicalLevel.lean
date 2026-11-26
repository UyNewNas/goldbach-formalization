import ImbalancedChen.P1OriginalSingletonPhysicalSupport
import ImbalancedChen.P5ActualLowerNormalizedAtlasOccurrence
import ImbalancedChen.P5OriginalHBCompleteProductScale
import ImbalancedChen.P1OriginalHistoricalTwoLongP2

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The actual normalized singleton profile supplies both the complete-product
trim and the physical upper support. A genuine original HB factor tuple,
one occurrence, and a block of its whole complement instantiate the existing
complete-scale threshold with C = 2. The historical true-d carrier then
supplies its strict physical .599 cutoff; it is transported to the complete
local scale with exponent 1199/2000, without an assumed local-level bound.

The last theorem pays the level premise in the existing finite P2 invoice.
It does not identify its short blocks with the actual two-long complement,
restore roughness, reconstruct the Fourier integral, or close the Atlas.
-/

namespace ImbalancedChen.P1OriginalSingletonPhysicalLevel
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block Owns)
open P5Z.LiteralHeathBrownOccurrenceWords (factorTuples)
open P5Z.ActualRoughHeathBrownWords (Role)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.ActualEtaPsiOccurrenceBudget (eta eta_zero)
open P5Z.ActualLowerNormalizedAtlasOccurrence
  (scalarProfile scalarProfile_eq_ambient scalarProfile_support)
open P5Z.OriginalHBCompleteProductScale
  (OriginalGroupTuple joined completeInteger localScale exists_actual_HB_residue_threshold)
open P1OriginalHistoricalTwoLongP2
  (historicalModuli historicalRowCore historical_rowCore_bound momentBudget)
open Part3.TwoLongHBMellinBrunProfiles (pairCost)
open Part3.TwoLongActualHBShortMass (shortScale)

/-- The complete-scale threshold precedes all profile parameters, charts,
actual tuples, occurrences, complement blocks and historical coefficients.
The strict .599 bound is read from the unchanged historical modulus filter.
In particular neither a trim estimate nor a moving-residue/local-level
estimate is supplied as a premise. -/
theorem eventually_actual_singleton_local_level
    {kappa kap0 zeta : ℝ} (hkappa : 0 < kappa)
    (hsmall : kappa ≤ zeta / 10000) (hzeta : zeta ≤ 1 / 400)
    (htrim : kap0 < kappa / (4 * (1 + kappa))) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ), kap < 1 →
      ∀ (B cj j n : ℕ) (fs : List ℕ),
      fs ∈ factorTuples (2 * (j + 1)) n →
      scalarProfile kap B N cj kap0 n ≠ 0 →
      ∀ (p : ℕ) (b c : Block), p ∈ fs → Owns b p → Owns c (n / p) →
      let x := localScale b c
      1 < x ∧ (1 / 2 : ℝ) * x ≤ N ∧ (N : ℝ) ≤ x ^ (1 + kappa) ∧
        ∀ (levelB : ℝ) (old fresh : List ℕ → Bool) (cap : ℕ) (w z : ℝ) (q : ℕ),
        q ∈ historicalModuli levelB old fresh N cap w z →
        (q : ℝ) < x ^ (1199 / 2000 : ℝ) ∧ q ≤ ⌊x ^ (1199 / 2000 : ℝ)⌋₊ := by
  obtain ⟨N0, hN0, H⟩ := exists_actual_HB_residue_threshold
    (C := (2 : ℝ)) (κ := kappa) (κ₀ := kap0) (by norm_num) hkappa htrim
  filter_upwards [eventually_ge_atTop N0] with N hN
  intro kap hkap B cj j n fs hfs hactive p b c hp hb hc
  obtain ⟨hlo, hhi⟩ := scalarProfile_complete_support kap hkap B N cj kap0
    (by omega) hactive
  let gs : List OriginalGroupTuple :=
    [{ integer := n, row := j, factors := fs, mem := hfs }]
  have hjoined : joined gs = fs := by simp [gs, joined]
  have hcomplete : completeInteger gs = n := by simp [gs, completeInteger]
  have hpjoined : p ∈ joined gs := by simpa only [hjoined] using hp
  have hccomplete : Owns c (completeInteger gs / p) := by
    simpa only [hcomplete] using hc
  have htcomplete : (N : ℝ) ^ (1 - kap0) ≤ (completeInteger gs : ℝ) := by
    simpa only [hcomplete] using hlo.le
  have hscomplete : (completeInteger gs : ℝ) ≤ (2 : ℝ) * N := by
    simpa only [hcomplete] using hhi
  obtain ⟨hx, hxN, hNx⟩ := H N hN gs p b c hpjoined hb hccomplete htcomplete hscomplete
  let x := localScale b c
  refine ⟨hx, by simpa only [one_div] using hxN, hNx, ?_⟩
  intro levelB old fresh cap w z q hq
  have hqN : (q : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) :=
    (Finset.mem_filter.mp hq).2.2
  have hpower : (1 + kappa) * (599 / 1000 : ℝ) ≤ 1199 / 2000 := by
    linarith only [hsmall, hzeta]
  have hqx : (q : ℝ) < x ^ (1199 / 2000 : ℝ) := by
    calc
      (q : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := hqN
      _ ≤ (x ^ (1 + kappa)) ^ (599 / 1000 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hNx (by norm_num)
      _ = x ^ ((1 + kappa) * (599 / 1000 : ℝ)) :=
        (Real.rpow_mul (zero_lt_one.trans hx).le _ _).symm
      _ ≤ x ^ (1199 / 2000 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx.le hpower
  exact ⟨hqx, Nat.le_floor hqx.le⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A concrete local endpoint for the existing finite historical P2 invoice.
Its analytic/short-carrier parameters retain their original conditions.
Their later identification with the actual two-long row is a separate task. -/
theorem eventually_actual_singleton_historical_rowCore_bound
    {kappa kap0 zeta : ℝ} (hkappa : 0 < kappa)
    (hsmall : kappa ≤ zeta / 10000) (hzeta : zeta ≤ 1 / 400)
    (htrim : kap0 < kappa / (4 * (1 + kappa))) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ), kap < 1 →
      ∀ (B cj hbOrder n : ℕ) (fs : List ℕ),
      fs ∈ factorTuples (2 * (hbOrder + 1)) n →
      scalarProfile kap B N cj kap0 n ≠ 0 →
      ∀ (p : ℕ) (b c : Block), p ∈ fs → Owns b p → Owns c (n / p) →
      ∀ (levelB : ℝ) (old fresh : List ℕ → Bool) (cap : ℕ) (w z L : ℝ),
      ∀ {Z X delta U V H t₁ t₂ : ℝ}, 1 ≤ Z → 1 ≤ X →
      0 < delta → delta ≤ 1 / 4 → 0 < U → 0 < V → 0 ≤ H →
      |t₁| ≤ H → |t₂| ≤ H →
      ∀ (brunOrder : ℕ) (b₁ b₂ : Bool) (label : Fin 3) (log₁ log₂ : Bool)
        (bs : ι → Block) (y xi : ι → ℝ) (rs : ι → Role),
      (∀ i, 2 * (lower (bs i) : ℝ) ≤ X) →
      ‖historicalRowCore levelB old fresh N cap w z L Z brunOrder b₁ b₂
        delta U V t₁ t₂ label log₁ log₂ bs y xi rs‖ ≤
      pairCost delta U V H * ((shortScale bs : ℝ) * (Z ^ (2 * brunOrder + 1)) ^ 2) *
        momentBudget ⌊localScale b c ^ (1199 / 2000 : ℝ)⌋₊ *
          (1 + Real.log X) ^ Fintype.card ι := by
  filter_upwards [eventually_actual_singleton_local_level hkappa hsmall hzeta htrim]
    with N hlevel
  intro kap hkap B cj hbOrder n fs hfs hactive p b c hp hb hc
  obtain ⟨_, _, _, hQ⟩ := hlevel kap hkap B cj hbOrder n fs hfs hactive p b c hp hb hc
  intro levelB old fresh cap w z L Z X delta U V H t₁ t₂
    hZ hX hd hs hU hV hH ht₁ ht₂ brunOrder b₁ b₂ label log₁ log₂ bs y xi rs hcap
  exact historical_rowCore_bound levelB old fresh N cap
    ⌊localScale b c ^ (1199 / 2000 : ℝ)⌋₊ w z L
    (fun q hq => (hQ levelB old fresh cap w z q hq).2)
    hZ hX hd hs hU hV hH ht₁ ht₂ brunOrder b₁ b₂ label log₁ log₂ bs y xi rs hcap

end
end ImbalancedChen.P1OriginalSingletonPhysicalLevel
