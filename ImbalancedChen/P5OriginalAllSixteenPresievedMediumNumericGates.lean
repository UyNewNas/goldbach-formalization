import ImbalancedChen.P5OriginalJointPresievedWMediumNumericGates

/-!
# A numerical Medium query for every active physical ALL16 presieved modulus

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The caller supplies only an actual nonzero explicitly NEW jointPresievedSigma
coefficient, after fixing its actual common beta parameters. Original joint
source membership supplies its physical mark. On ordinary15 marks the exact
row identities identify its coefficient with the corresponding ordinary15
presieved coefficient; on W marks the actual W factor supplier is used.
The extracted natural factors have product EXACT q and meet ALL FOUR strict
Medium NUMERICAL inequalities for every prescribed original HB length.

One threshold precedes N,x,U,E,q. The original eta-dependent zeta/sigma and
analytic kappa/trim ranges are retained. No old all-prime sigma is identified,
and no factorability solver, atomwise fixed groups, coefficient SW, or signed
Medium/PP conclusion is an input or a claim.
-/

namespace ImbalancedChen.P5Z.OriginalAllSixteenPresievedMediumNumericGates

noncomputable section
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open U1011OriginalSixteenStaticNativeCompiler (selectedPolicy ownerBox)
open OriginalCommonBetaActualParameters OriginalJointCommonBetaModel
open OriginalOrdinaryPresievedSigma OriginalJointPresievedCompiler
open U1011OriginalFifteenMediumNumericGates
open OriginalPresievedMediumNumericGates OriginalJointPresievedWMediumNumericGates

/-- Actual all-source coefficient -> physical mark -> exact row -> original
constructed factors. All size gates are conclusions at one common threshold. -/
theorem exists_actual_all16_medium_numeric_threshold
    (n : ℕ) (eta : ℚ) (heta : 0 < eta) (nu0 epsilon : ℝ)
    (hnu : 0 < nu0) (hepsilon : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu0)
    {c C kappa kappa0 : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hk0 : 0 < kappa) (hk : kappa ≤ sigma n eta / 200)
    (ht0 : 0 < kappa0) (ht : kappa0 < kappa / (4 * (1 + kappa))) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - kappa0) ≤ x → x ≤ C * N →
      1 < x ∧ C⁻¹ * x ≤ N ∧ (N : ℝ) ≤ x ^ (1 + kappa) ∧
      ∀ U : ℝ, x ^ (2 * zeta n eta) ≤ U → U ≤ x ^ (1 / 3 + zeta n eta / 2) →
      ∀ (E : ℕ × ℕ → Prop) (q : ℕ),
      jointPresievedSigma n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2))
        ((N : ℝ) ^ (nu0 * epsilon)) E q ≠ 0 →
      ∃ a b c : ℕ, a * b * c = q ∧
        NumericGates N x U (a : ℝ) (b : ℝ) (c : ℝ) (sigma n eta) := by
  obtain ⟨NO, hNO, hordinary⟩ := exists_actual_presieved_medium_numeric_threshold
    n eta heta nu0 epsilon hnu hepsilon heBudget hc hC hk0 hk ht0 ht
  obtain ⟨NW, hNW, hWquery⟩ := exists_W_medium_numeric_threshold
    n eta heta nu0 epsilon hnu hepsilon heBudget hc hC hk0 hk ht0 ht
  refine ⟨max NO NW, hNO.trans (le_max_left _ _), ?_⟩
  intro N hN x hlow hupp
  have hNOrd : NO ≤ N := (le_max_left _ _).trans hN
  have hNW' : NW ≤ N := (le_max_right _ _).trans hN
  have hNN : 1 < N := lt_of_lt_of_le (by omega : 1 < NO) hNOrd
  obtain ⟨hx, hlo, hhi, hOrdU⟩ := hordinary N hNOrd x hlow hupp
  obtain ⟨_, _, _, hWU⟩ := hWquery N hNW' x hlow hupp
  refine ⟨hx, hlo, hhi, ?_⟩
  intro U hUlo hUhi E q hq
  have hmem : q ∈ jointSupport n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2)) E := by
    by_contra hn
    exact hq (jointSigma_zero_off_support n N eta
      ((N : ℝ) ^ (nu0 * epsilon ^ 2)) ((N : ℝ) ^ (nu0 * epsilon)) E hn)
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hmem
  obtain ⟨htuple, hrow⟩ := Finset.mem_sigma.mp hm
  have hwJoint : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      (N : ℝ) ^ (nu0 * epsilon ^ 2) ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t := by
    intro t htup
    exact (parameters_on_joint_row hNN heta hnu hepsilon heBudget htup).1
  by_cases hp : (selectedPolicy n N m.1).val < 15
  · have hmOrd : m ∈ marks n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2)) E := by
      refine Finset.mem_sigma.mpr ⟨?_, hrow⟩
      exact Finset.mem_filter.mpr ⟨htuple, hp⟩
    have hwOrd : ∀ t ∈ tuples n N E,
        (N : ℝ) ^ (nu0 * epsilon ^ 2) ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t := by
      intro t htup
      exact hwJoint t (Finset.mem_filter.mp htup).1
    have hOrdEq : presievedSigma n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2))
        ((N : ℝ) ^ (nu0 * epsilon)) E (modulus m) =
        jointPresievedSigma n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2))
          ((N : ℝ) ^ (nu0 * epsilon)) E (modulus m) := by
      rw [presievedSigma_eq_row hNN heta hwOrd hmOrd,
        jointSigma_eq_row hNN heta hwJoint hm]
    have hOrdNonzero : presievedSigma n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2))
        ((N : ℝ) ^ (nu0 * epsilon)) E (modulus m) ≠ 0 := by
      rw [hOrdEq]
      exact hq
    obtain ⟨t, htup, e, d, hqeq, hproduct, hgates⟩ :=
      hOrdU U hUlo hUhi E (modulus m) hOrdNonzero
    let abc := U1011OriginalFifteenJointSmallBeta.attachedFactors
      (selectedPolicy n N t) (ownerBox n N t) eta N
      (innerQuery x U (zeta n eta)) t d e
    exact ⟨abc.1, abc.2.1, abc.2.2, hproduct, hgates⟩
  · have hW : selectedPolicy n N m.1 = wPolicy := by
      apply Fin.ext
      have hlt := (selectedPolicy n N m.1).isLt
      dsimp [wPolicy]
      omega
    exact hWU U hUlo hUhi E m.1 m.2 htuple hW hrow hq

end
end ImbalancedChen.P5Z.OriginalAllSixteenPresievedMediumNumericGates
