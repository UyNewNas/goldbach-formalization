import ImbalancedChen.P5OriginalCommonPositivePresieve
import ImbalancedChen.P5OriginalArchiveCommonRawMean

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual original archived fifth charge now enters the positive-cutoff
common-policy physical density. The common fourth baseline is unchanged.
The reserve pays the genuine two-sign beta attachment on the chosen
common tree. Projection is used for a whole upper tree only.

The final common rho is also a consumer, with its exact signed sixth and
eighth raw changes still displayed. No estimate or sign for those changes
is presumed. One fixed-source mean threshold and one beta threshold are
combined, without assuming a full-policy mean or a changing-mesh limit.
-/
namespace ImbalancedChen.P5OriginalArchivePositivePresieveGain
noncomputable section
open Filter Topology
open scoped Classical
open P2OriginalFourthCapProducerInterface
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedSource
open P4AOriginalVariableFifthPhysicalLedger
open P1HistoricalFifthCommonPolicyInputs
open P5OriginalCommonFifthPhysicalCaller P5OriginalFifthArchiveFiniteIdentity
open P5OriginalArchiveCommonRawMean P5OriginalFifthArchiveActualMean
open P5OriginalCommonPositivePresieve

/-- The sixth and eighth entries keep NEW minus CURRENT-parent orientation.
They are literal unchanged-policy densities, not claimed numerical gains. -/
def laterRawLedger (d : OriginalData) (N cap : ℕ) (z : ℝ) : ℝ :=
  normalize N (raw (policy6 d (N : ℝ)) N cap 0 z -
    raw (policy5 d (N : ℝ)) N cap 0 z) +
  normalize N (raw (policy8 d (N : ℝ)) N cap 0 z -
    raw (policy6 d (N : ℝ)) N cap 0 z)

/-- The common fourth baseline minus the independently defined ORIGINAL
tuple charge is exactly the common fifth raw density. Both cube gates,
current parent, archive owners and original licence filters are retained. -/
theorem archive_full_fifth_ledger
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (N cap : ℕ)
    (hN : 1 ≤ (N : ℝ)) (z : ℝ) :
    let d := sourceData rows4 licensed4 e q chi omega
    normalize N (raw (policy5 d (N : ℝ)) N cap 0 z) =
      normalize N (raw (policy4 d (N : ℝ)) N cap 0 z) -
        fifthTupleCharge e chi (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q)
          omega rows4 licensed4
          (P1HistoricalFifthIndexedOwnerArchive.globalOwners e q chi omega)
          (P1HistoricalFifthIndexedOwnerArchive.licensedRows e q chi omega) N cap z := by
  dsimp only
  rw [← commonLiteralCharge_eq_original rows4 licensed4 e q chi omega N cap z]
  have h := normalized_actualCharge_eq_literalCharge
    (sourceData rows4 licensed4 e q chi omega) N cap z
  change normalize N (actualCharge (sourceData rows4 licensed4 e q chi omega) N cap z) =
    commonLiteralCharge rows4 licensed4 e q chi omega N cap z at h
  rw [← raw_fourth_sub_fifth_eq_actualCharge _ N cap hN z, normalize_sub] at h
  linarith

/-- Finite positive-cutoff ledger, with the beta correction displayed as
the actual common attachment error. The next theorem pays that error. -/
theorem archive_positive_fifth_le_original_charge_add_attachment
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (N cap : ℕ)
    (hN : 2 ≤ N) (w z L : ℝ) (hwz : w ≤ z) :
    let d := sourceData rows4 licensed4 e q chi omega
    normalize N (physical (policy5 d (N : ℝ)) N cap w z L) ≤
      normalize N (raw (policy4 d (N : ℝ)) N cap 0 z) -
        fifthTupleCharge e chi (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q)
          omega rows4 licensed4
          (P1HistoricalFifthIndexedOwnerArchive.globalOwners e q chi omega)
          (P1HistoricalFifthIndexedOwnerArchive.licensedRows e q chi omega) N cap z +
        normalize N (attachmentError d .fifth N cap w z L) := by
  dsimp only
  have h := normalized_physical_le_full_add_attachment
    (sourceData rows4 licensed4 e q chi omega) .fifth N cap hN w z L hwz
  change normalize N (physical (policy5 _ _) N cap w z L) ≤
    normalize N (raw (policy5 _ _) N cap 0 z) + _ at h
  rw [archive_full_fifth_ledger rows4 licensed4 e q chi omega N cap
    (by exact_mod_cast (show 1 ≤ N by omega)) z] at h
  exact h

/-- For a fixed original archive source, the actual full fifth integral
is subtracted from the positive-cutoff physical fifth density. The same
epsilon works for the final common rho: only its two later raw changes
remain to be evaluated. The two eta/2 errors use ONE total eta reserve.

The output has the original z=N^(19/96), w=N^(nu*epsilon^2), L=N^(nu*epsilon).
There is no hIntegral, hBeta, hGain, hDensity, or policy-identity premise. -/
theorem exists_archive_positive_presieve_integral_ledger
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (homega : 0 < omega) (homegaRho : omega < (19 / 96 : ℝ))
    (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in P1OriginalFifthMovingScaleLimit.evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ))
    (nu eta epsilonMax : ℝ) (hnu : 0 < nu) (heta : 0 < eta)
    (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ (19 / 96 : ℝ) / nu ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        let d := sourceData rows4 licensed4 e q chi omega
        let w := (N : ℝ) ^ (nu * epsilon ^ 2)
        let z := (N : ℝ) ^ (19 / 96 : ℝ)
        let L := (N : ℝ) ^ (nu * epsilon)
        1 < w ∧
          normalize N (physical (policy5 d (N : ℝ)) N (cap N) w z L) ≤
            normalize N (raw (policy4 d (N : ℝ)) N (cap N) 0 z) -
              archiveFifthIntegral rows4 licensed4 e q chi omega + eta ∧
          normalize N (physicalDensitySum (moduli d N (cap N) w z)
              (rho d N (cap N) w z L)) ≤
            normalize N (raw (policy4 d (N : ℝ)) N (cap N) 0 z) -
              archiveFifthIntegral rows4 licensed4 e q chi omega +
              laterRawLedger d N (cap N) z + eta := by
  let r : ℝ := (19 / 96 : ℝ) / nu
  have hr : 0 < r := div_pos (by norm_num) hnu
  have hnr : nu * r = (19 / 96 : ℝ) := by
    dsimp only [r]
    field_simp [hnu.ne'] <;> ring
  have heta2 : 0 < eta / 2 := half_pos heta
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      Nbeta, hNbeta, hbeta⟩ := exists_common_positive_presieve_reserve
    nu r (eta / 2) epsilonMax hnu hr heta2 hepsilonMax
  have hmean := eventually_actual_common_rawDifference_error
    rows4 licensed4 e he q chi omega homega homegaRho cap hcap (eta / 2) heta2
  rw [Filter.eventually_inf_principal] at hmean hcap
  obtain ⟨Nmean, hNmean⟩ := eventually_atTop.mp (hmean.and hcap)
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
    max Nbeta Nmean, hNbeta.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hNb : Nbeta ≤ N := (le_max_left _ _).trans hN
  have hNm : Nmean ≤ N := (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := hNbeta.trans hNb
  have hpos : 0 < N ∧ Even N := ⟨by omega, hEven⟩
  have hgain := (abs_lt.mp ((hNmean N hNm).1 hpos)).1
  have hcapN := (hNmean N hNm).2 hpos
  let d := sourceData rows4 licensed4 e q chi omega
  let w := (N : ℝ) ^ (nu * epsilon ^ 2)
  let z := (N : ℝ) ^ (19 / 96 : ℝ)
  let L := (N : ℝ) ^ (nu * epsilon)
  have hc : (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ) := by
    simpa only [hnr] using hcapN
  have h5 := hbeta N hNb hEven (cap N) hc d .fifth
  have h8 := hbeta N hNb hEven (cap N) hc d .eighth
  dsimp only at h5 h8
  simp only [hnr] at h5 h8
  have h5bound := h5.2.2.2.2
  have h8bound := h8.2.2.2.2
  change normalize N (physical (policy5 d (N : ℝ)) N (cap N) w z L) ≤
    normalize N (raw (policy5 d (N : ℝ)) N (cap N) 0 z) + eta / 2 at h5bound
  change normalize N (physicalDensitySum (moduli d N (cap N) w z)
      (rho d N (cap N) w z L)) ≤
    normalize N (raw (policy8 d (N : ℝ)) N (cap N) 0 z) + eta / 2 at h8bound
  have h5ledger : normalize N (raw (policy5 d (N : ℝ)) N (cap N) 0 z) =
      normalize N (raw (policy4 d (N : ℝ)) N (cap N) 0 z) -
        normalizedRawDifference rows4 licensed4 e q chi omega N (cap N) := by
    dsimp only [normalizedRawDifference, normalize, d, z]
    ring
  have h8ledger : normalize N (raw (policy8 d (N : ℝ)) N (cap N) 0 z) =
      normalize N (raw (policy4 d (N : ℝ)) N (cap N) 0 z) -
        normalizedRawDifference rows4 licensed4 e q chi omega N (cap N) +
        laterRawLedger d N (cap N) z := by
    rw [laterRawLedger, normalize_sub, normalize_sub]
    linarith [h5ledger]
  change 1 < w ∧
    normalize N (physical (policy5 d (N : ℝ)) N (cap N) w z L) ≤
      normalize N (raw (policy4 d (N : ℝ)) N (cap N) 0 z) -
        archiveFifthIntegral rows4 licensed4 e q chi omega + eta ∧
    normalize N (physicalDensitySum (moduli d N (cap N) w z)
        (rho d N (cap N) w z L)) ≤
      normalize N (raw (policy4 d (N : ℝ)) N (cap N) 0 z) -
        archiveFifthIntegral rows4 licensed4 e q chi omega +
        laterRawLedger d N (cap N) z + eta
  refine ⟨h5.1, ?_, ?_⟩
  · rw [h5ledger] at h5bound
    linarith
  · rw [h8ledger] at h8bound
    linarith

end
end ImbalancedChen.P5OriginalArchivePositivePresieveGain
