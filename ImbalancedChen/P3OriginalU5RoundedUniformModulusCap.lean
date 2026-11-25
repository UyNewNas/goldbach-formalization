import ImbalancedChen.P3OriginalU5RoundedModulusCap

/-!
# The original U5 physical support for every sufficiently fine mesh

Pending strict compilation, independent kernel replay and full declaration audit.

The existing rounded-rho supplier gives the explicit exponent inflation
`rawRank epsilon * tau`. This consumer chooses a positive upper mesh from
the original physical reserve and retains that bound for every finer mesh.
The same signed rounded coefficient, external pair and small beta level are
used throughout. No monotonicity of rounded coefficients is assumed.
-/

namespace ImbalancedChen.P3OriginalU5RoundedUniformModulusCap

noncomputable section
open scoped Classical
open P2OriginalPairSourceReceiver (PairRange)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalSelectedPairNativeData (selectedPolicy)
open P2OriginalLowerCompactStartCapConstructor (topCap)
open P3OriginalU5PhysicalModulusCap (buffered_cap_lt_theta)
open P3OriginalU5RoundedCountInsertion (roundedRho)
open P3OriginalU5RoundedModulusCap (rawRank selected_U5_raw_level_and_rank)
open P5OriginalU5CausalFinite (attachmentNu cutoff pairSupport smallCutoff)
open P5OriginalU5PlateauPrimeBV (markedProduct fullModulus)

/-- The support mesh is chosen before every later mesh, receiver, bank,
target and pair. It therefore can be refined to meet another finite reserve
while retaining the original rounded-rho construction and complete physical
modulus. Coefficient values themselves may depend on the chosen mesh. -/
theorem exists_uniform_finer_rounded_U5_modulus_cap
    (buffer : ℚ) (hb : 0 ≤ buffer) (hb' : buffer ≤ 1 / 1000)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (halloc : attachmentNu * epsilon ≤ (buffer : ℝ)) :
    ∃ tau0 : ℝ, 0 < tau0 ∧ ∀ tau : ℝ, 0 < tau → tau ≤ tau0 →
      ∀ (R : PairRange) (mesh : ℕ) (bank : CandidateBank mesh),
      ∀ N : ℕ, 2 ≤ N → ∀ t ∈ pairSupport N, ∀ k : ℕ,
        roundedRho N epsilon tau (selectedPolicy R bank buffer false N t) k ≠ 0 →
          (fullModulus t k : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := by
  have hgap : topCap + attachmentNu * epsilon < (599 / 1000 : ℝ) :=
    (add_le_add_left halloc topCap).trans_lt (buffered_cap_lt_theta buffer hb')
  let gap : ℝ := 599 / 1000 - (topCap + attachmentNu * epsilon)
  have hgap_pos : 0 < gap := sub_pos.mpr hgap
  let tau0 : ℝ := gap / ((rawRank epsilon : ℝ) + 1)
  have hden : 0 < (rawRank epsilon : ℝ) + 1 := by positivity
  have htau0 : 0 < tau0 := div_pos hgap_pos hden
  have hbudget : tau0 * ((rawRank epsilon : ℝ) + 1) = gap := by
    exact div_mul_cancel₀ gap hden.ne'
  refine ⟨tau0, htau0, ?_⟩
  intro tau htau hsmall R mesh bank N hN t ht k hk
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hinflation : (rawRank epsilon : ℝ) * tau < gap := by
    have hmul := mul_le_mul_of_nonneg_left hsmall
      (Nat.cast_nonneg (rawRank epsilon) : (0 : ℝ) ≤ rawRank epsilon)
    nlinarith
  have hexponent : topCap + attachmentNu * epsilon +
      (rawRank epsilon : ℝ) * tau < (599 / 1000 : ℝ) := by
    dsimp only [gap] at hinflation
    linarith
  have hbound := P2RoundedCausalFibreLossAndLevel.rounded_rho_full_level
    hNr (selectedPolicy R bank buffer false N t) (Nat.ceil (cutoff N))
    (markedProduct t) (rawRank epsilon) (smallCutoff N epsilon) (cutoff N)
    topCap (attachmentNu * epsilon) htau
    (fun r hr => selected_U5_raw_level_and_rank R bank buffer hb hb'
      epsilon hepsilon hN ht (Nat.ceil (cutoff N)) hr) hk
  exact hbound.trans_lt ((Real.rpow_lt_rpow_left_iff hNr).mpr hexponent)

end
end ImbalancedChen.P3OriginalU5RoundedUniformModulusCap
