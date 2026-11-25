import ImbalancedChen.P3OriginalU5PhysicalModulusCap
import ImbalancedChen.P5OriginalU5ClassicalComplement

/-!
# The selected U5 policy in the actual surviving classical complement

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

This is a consumer of the existing original U5 count theorem, not a new
coefficient or a conditional version of the final PP estimate. The exact
projected main term, projection reserve, actual medium/no-medium branches,
and original nonzero integer-rho carrier are retained.

The existing count theorem chooses the attachment precision below 1/272.
With the literal receiver buffer 1/1000, its small-factor allocation is
derived inside the proof. The new physical cap is then applied to every
nonzero modulus that survives in THAT count's classical complement.

All constants and the attachment precision precede N, the actual range,
the finite candidate bank, and the atlas parameter. No estimate of the
remaining branches, full (S)/(F) admission, or common-Q coverage is claimed.
-/

namespace ImbalancedChen.P3OriginalU5SelectedClassicalComplement

noncomputable section

open P2OriginalPairSourceReceiver (PairRange)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalSelectedPairNativeData (selectedPolicy)
open P5OriginalU5CausalFinite
open P5OriginalU5PlateauPrimeBV (Policy integerRho)
open P5OriginalU5ClassicalComplement (beyond)
open P5OriginalU5AllMarkHBReserves (branches)
open MathlibNt.SieveTheory.LiuWeight (panModulusCutoff)

/-- The literal selected policy in the original projected count, with all
surviving nonzero physical moduli in the displayed range above the classical
cutoff. The
unpaid `branches` term is preserved with its sign and its original rho.
The returned range, squarefreeness, primitivity and one-bound concern the
same carrier that occurs in this count inequality. -/
theorem exists_selected_original_count_beyond_classical
    (t tau : ℝ) (ht : 0 < t) (ht1 : t < 1) (htau : t < tau) (K : ℕ)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ C : ℝ, 0 < C ∧
      ∃ e : ℝ, 0 < e ∧ e < 1 / 8 ∧ e < 1 / 272 ∧
        ∃ M : ℕ, 2 ≤ M ∧
          ∀ N : ℕ, M ≤ N → Even N →
          ∀ (R : PairRange) (mesh : ℕ) (bank : CandidateBank mesh) (zeta : ℝ),
            let P : Policy := selectedPolicy R bank (1 / 1000 : ℚ) false N
            (fullProjectedMainSum N P - projectionReserve N eta +
              (branches t tau zeta 6 N K e P (beyond B N e P)).re -
              C * (N : ℝ) / (Real.log (N : ℝ)) ^ 3 ≤ currentChenUpsilon5 N) ∧
            ∀ q ∈ beyond B N e P,
              panModulusCutoff N B < q ∧ integerRho N e P q ≠ 0 ∧
                0 < q ∧ Squarefree q ∧ N.Coprime q ∧
                |(integerRho N e P q : ℝ)| ≤ 1 ∧
                (q : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := by
  classical
  obtain ⟨B, hB, C, hC, e, he, he8, heMax, M, hM, hcount⟩ :=
    P5OriginalU5ClassicalComplement.exists_original_count_beyond_classical
      t tau ht ht1 htau K (eta := eta) (eMax := (1 / 272 : ℝ))
      heta (by norm_num)
  have halloc : attachmentNu * e ≤ ((1 / 1000 : ℚ) : ℝ) := by
    norm_num [attachmentNu]
    linarith only [heMax]
  refine ⟨B, hB, C, hC, e, he, he8, heMax, M, hM, ?_⟩
  intro N hN hev R mesh bank zeta
  let P : Policy := selectedPolicy R bank (1 / 1000 : ℚ) false N
  refine ⟨hcount N hN hev P zeta, ?_⟩
  intro q hq
  have hN2 : 2 ≤ N := hM.trans hN
  have hmember := Finset.mem_filter.mp hq
  have hdata := P5OriginalU5AllMarkCosts.full_modulus_data hN2 P
    (attachment_gates hN2 he he8).2.2 hmember.1
  have hdiv := Nat.dvd_of_mem_divisors hdata.1
  refine ⟨hmember.2.1, hmember.2.2, Nat.pos_of_mem_divisors hdata.1,
    (sieveProduct_squarefree N N).squarefree_of_dvd hdiv,
    (coprime_of_dvd_sieveProduct hdiv).symm, hdata.2.1, ?_⟩
  exact P3OriginalU5PhysicalModulusCap.selected_integerRho_nonzero_modulus_lt_theta
    R bank (1 / 1000 : ℚ) (by norm_num) (by norm_num) e he he8 halloc
    hN2 hmember.2.2

end
end ImbalancedChen.P3OriginalU5SelectedClassicalComplement
