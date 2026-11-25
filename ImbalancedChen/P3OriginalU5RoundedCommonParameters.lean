import ImbalancedChen.P3OriginalU5WarmRoundingPayment
import ImbalancedChen.P3OriginalU5RoundedUniformModulusCap
import ImbalancedChen.P3OriginalU5RoundedBetaReserve

/-!
# Common parameters for the same original rounded U5 coefficient

SOURCE ONLY / UNCOMPILED / NO FORMAL ACCEPTANCE.

Fix a coarse mesh, positive rough-box and beta reserves, and a positive
epsilon upper request.  The existing beta supplier first chooses epsilon
below min(epsilonMax, 1/272).  Two existing all-finer-mesh suppliers then
choose one common positive tau bound, and their target thresholds combine
with the beta threshold.  These choices precede N, R, bank, pair and tau.

At the original cap ceil(cutoff N), the resulting conclusion simultaneously
pays the literal rough roundingLoss, pays the literal beta attachment gap,
and bounds every nonzero complete physical modulus of the same roundedRho.
The fixed buffer is 1/1000.  The beta parameters are exactly nu=34/125 and
r=417/1360, whose product is the original cutoff exponent 417/5000.

No beta scalar estimate, Mertens bound or small/rough factorization is
reproved.  No coefficient identity between different meshes is asserted.
This does not evaluate raw density, combine the errors into a main-term
lower bound, supply physical common Q, or conclude a tensor or PP theorem.
-/

namespace ImbalancedChen.P3OriginalU5RoundedCommonParameters

noncomputable section
open scoped Classical
open P2OriginalPairSourceReceiver (PairRange)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalSelectedPairNativeData (selectedPolicy)
open P2LowerFiniteCellRounding («universe» coefficient roundingLoss)
open P3OriginalU5RoundedCountInsertion (roundedSupport roundedRho)
open P3OriginalU5WarmRoundingPayment
open P3OriginalU5RoundedUniformModulusCap
open P3OriginalU5RoundedBetaReserve
open P5OriginalU5CausalFinite (attachmentNu cutoff pairSupport smallCutoff smallLevel)
open P5OriginalU5PlateauPrimeBV (fullModulus)

/-- The literal existing beta attachment gap at the original U5 carrier.
The rough coefficient and physical rounded rho use the same policy and tau. -/
abbrev betaGap (N : ℕ) (epsilon tau : ℝ) (policy : List ℕ → Bool) : ℝ :=
  actualSmallEulerProduct N (Nat.ceil (cutoff N)) (smallCutoff N epsilon) *
    reciprocalTotientDensity
      («universe» N (Nat.ceil (cutoff N)) (smallCutoff N epsilon) (cutoff N))
      (coefficient policy N (Nat.ceil (cutoff N))
        (smallCutoff N epsilon) (cutoff N) tau) -
    physicalDensitySum (roundedSupport N epsilon) (roundedRho N epsilon tau policy)

/-- Epsilon, a positive upper fine width and a common target threshold are
chosen before every actual target, receiver, bank, pair and finer mesh.
All three conclusions refer to the original buffer 1/1000 and the same
rounded coefficient at that chosen finer mesh. -/
theorem exists_rounded_U5_common_parameters
    (mesh : ℕ) (etaBox etaBeta epsilonMax : ℝ)
    (hbox : 0 < etaBox) (hbeta : 0 < etaBeta) (hmax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon < 1 / 272 ∧
      ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
        ∀ N : ℕ, N0 ≤ N → Even N →
          ∀ (R : PairRange) (bank : CandidateBank mesh),
            ∀ t ∈ pairSupport N, ∀ tau : ℝ, 0 < tau → tau ≤ tau0 →
              roundingLoss (selectedPolicy R bank (1 / 1000) false N t)
                  N (Nat.ceil (cutoff N)) (smallCutoff N epsilon) (cutoff N) tau < etaBox ∧
              (0 ≤ betaGap N epsilon tau (selectedPolicy R bank (1 / 1000) false N t) ∧
                betaGap N epsilon tau (selectedPolicy R bank (1 / 1000) false N t) ≤
                  etaBeta * singularSeries N / Real.log (N : ℝ)) ∧
              ∀ k : ℕ,
                roundedRho N epsilon tau
                    (selectedPolicy R bank (1 / 1000) false N t) k ≠ 0 →
                  (fullModulus t k : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := by
  have hnu : 0 < attachmentNu := by norm_num [attachmentNu]
  have hr : 0 < (417 / 1360 : ℝ) := by norm_num
  have hproduct : attachmentNu * (417 / 1360 : ℝ) = (417 / 5000 : ℝ) := by
    norm_num [attachmentNu]
  have hrequest : 0 < min epsilonMax (1 / 272 : ℝ) :=
    lt_min hmax (by norm_num)
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonRequest, _hepsilonr,
      Nbeta, hNbeta, hbetaSupply⟩ :=
    exists_beta_error_le_target_reserve attachmentNu (417 / 1360)
      etaBeta (min epsilonMax (1 / 272)) hnu hr hbeta hrequest
  have hepsilonMax : epsilon < epsilonMax :=
    hepsilonRequest.trans_le (min_le_left _ _)
  have hepsilon272 : epsilon < (1 / 272 : ℝ) :=
    hepsilonRequest.trans_le (min_le_right _ _)
  have halloc : attachmentNu * epsilon ≤ ((1 / 1000 : ℚ) : ℝ) := by
    calc
      attachmentNu * epsilon ≤ attachmentNu * (1 / 272 : ℝ) :=
        mul_le_mul_of_nonneg_left hepsilon272.le hnu.le
      _ = ((1 / 1000 : ℚ) : ℝ) := by norm_num [attachmentNu]
  have hsquare : epsilon ^ 2 < (1 / 8 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hepsilon8 hepsilon.le (by norm_num)
  have hcut : attachmentNu * epsilon ^ 2 < (417 / 5000 : ℝ) := by
    calc
      attachmentNu * epsilon ^ 2 < attachmentNu * (1 / 8 : ℝ) ^ 2 :=
        mul_lt_mul_of_pos_left hsquare hnu
      _ < (417 / 5000 : ℝ) := by norm_num [attachmentNu]
  have hb : (0 : ℚ) ≤ 1 / 1000 := by norm_num
  obtain ⟨tauSupport, htauSupport, hsupport⟩ :=
    exists_uniform_finer_rounded_U5_modulus_cap
      (1 / 1000) hb le_rfl epsilon hepsilon halloc
  obtain ⟨tauBox, htauBox, Nbox, _hNbox, hboxSupply⟩ :=
    exists_uniform_selected_U5_roundingLoss_lt mesh epsilon hepsilon hcut etaBox hbox
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax, hepsilon272,
    min tauSupport tauBox, lt_min htauSupport htauBox,
    max Nbeta Nbox, hNbeta.trans (le_max_left _ _), ?_⟩
  intro N hN hEven R bank t ht tau htau hsmall
  have hNbeta' : Nbeta ≤ N := (le_max_left _ _).trans hN
  have hNbox' : Nbox ≤ N := (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := hNbeta.trans hNbeta'
  have htauSupport' : tau ≤ tauSupport := hsmall.trans (min_le_left _ _)
  have htauBox' : tau ≤ tauBox := hsmall.trans (min_le_right _ _)
  refine ⟨hboxSupply N hNbox' hEven R bank (1 / 1000) hb le_rfl t ht
    (Nat.ceil (cutoff N)) tau htau htauBox', ?_, ?_⟩
  · have hcap : (N : ℝ) ^ (attachmentNu * (417 / 1360 : ℝ)) ≤
        (Nat.ceil (cutoff N) : ℝ) := by
      rw [hproduct]
      exact Nat.le_ceil _
    have h := hbetaSupply N hNbeta' hEven (Nat.ceil (cutoff N)) hcap
      (selectedPolicy R bank (1 / 1000) false N t) tau
    dsimp only at h
    rw [hproduct] at h
    simpa only [betaGap, roundedSupport, roundedRho, smallCutoff, smallLevel, cutoff] using h
  · intro k hk
    exact hsupport tau htau htauSupport' R mesh bank N hN2 t ht k hk

end
end ImbalancedChen.P3OriginalU5RoundedCommonParameters
