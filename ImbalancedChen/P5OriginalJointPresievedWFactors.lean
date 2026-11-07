import ImbalancedChen.P5OriginalPresievedWCanonicalTail
import ImbalancedChen.P5OriginalJointCommonBetaModel

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The DISTINCT W mark of the explicitly NEW ALL16 jointPresievedSigma yields
its actual e,d and the canonical ORIGINAL rough tail. Existing W completion
and existing W third-group beta attachment supply the exact full physical
modulus and positive physical-delta monomials. No old native sigma is
identified, and no generic attachment algebra or rough-rank/finebox proof
is repeated. The actual finite common-beta budget supplies all choices.
-/

namespace ImbalancedChen.P5Z.OriginalJointPresievedWFactors

noncomputable section
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler (selectedPolicy ownerBox boxPolicy_certificate)
open OriginalOrdinaryCommonBetaModel OriginalOrdinaryResidualArithmeticFactor
open OriginalOrdinaryPresievedSigma OriginalJointPresievedCompiler
open OriginalCommonBetaActualParameters OriginalJointCommonBetaModel
open OriginalPresievedRoughPrimeSlots OriginalPresievedWCanonicalTail
open U1011OriginalW16SmallBetaMonomials (SmallBetaActive)

/-- An explicit ACTIVE W mark of the true new ALL16 coefficient has the
same original W completed factors with its ACTUAL common-beta integer only
in group3. No small-size, D-well, factorization or monomial licence is an
input. All A and the full W kappa interval use these same natural factors. -/
theorem active_joint_W_mark_factors {n N r : ℕ} {eta : ℚ} {nu0 epsilon : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (hnu0 : 0 < nu0) (heps : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu0) (E : ℕ × ℕ → Prop)
    {t : Four} (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hW : selectedPolicy n N t = wPolicy)
    (hr : r ∈ rowSupport n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2)) t)
    (hq : jointPresievedSigma n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2))
      ((N : ℝ) ^ (nu0 * epsilon)) E (fullPrefix t * r) ≠ 0) :
    ∃ e ∈ actualSmallRosserSupport N
        (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
        ((N : ℝ) ^ (nu0 * epsilon ^ 2)),
      ∃ d ∈ fixedRoughSupport
          (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
          (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
          ((N : ℝ) ^ (nu0 * epsilon ^ 2)) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t),
        r = e * d ∧
        SmallBetaActive N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
          e ((N : ℝ) ^ (nu0 * epsilon ^ 2)) (nu0 * epsilon) ∧
        0 < (U1011OriginalW16NearCapNative.delta (ownerBox n N t) eta : ℝ) ∧
        let tail := canonicalSlots N
          (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
          ((N : ℝ) ^ (nu0 * epsilon ^ 2)) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) d
        actualDwellSupport (U1011OriginalW16NearCapNative.D (ownerBox n N t) eta N) tail ∧
          tail.prod = d ∧
          ∀ A : ℝ, 1 ≤ A → A ≤ (N : ℝ) ^ (1 / 3 : ℝ) →
            let abc := U1011OriginalW16JointSmallBeta.attachedFactors (ownerBox n N t) eta N t A tail e
            let delt := (U1011OriginalW16NearCapNative.delta (ownerBox n N t) eta : ℝ)
            abc.1 * abc.2.1 * abc.2.2 = fullPrefix t * r ∧
              0 < abc.1 ∧ 0 < abc.2.1 ∧ 0 < abc.2.2 ∧ (abc.1 : ℝ) ≤ A ∧
              ∀ kappa : ℝ, 0 ≤ kappa → kappa ≤ delt →
                A ^ 2 * (abc.2.1 : ℝ) * (abc.2.2 : ℝ) ^ 2 ≤ (N : ℝ) ^ (1 - 3 * delt) ∧
                (N : ℝ) ^ (7 * (1 + 3 * kappa) / 32) * A * (abc.1 : ℝ) *
                  (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 - 3 * delt) ∧
                (A * (abc.2.2 : ℝ) / (abc.2.1 : ℝ)) ^ (7 / 16 : ℝ) * A *
                  (abc.1 : ℝ) * (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤
                    (N : ℝ) ^ (2 - 2 * delt) := by
  have hw (u : Four) (hu : u ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E) :=
    (parameters_on_joint_row hN heta hnu0 heps heBudget hu).1
  have hm : (⟨t,r⟩ : Mark) ∈ jointMarks n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2)) E :=
    Finset.mem_sigma.mpr ⟨ht,hr⟩
  have hrow : rowCoefficient n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2))
      ((N : ℝ) ^ (nu0 * epsilon)) t r ≠ 0 := by
    rw [← jointSigma_eq_row hN heta hw hm]
    exact hq
  have hlegal := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht
  obtain ⟨e,he,d,hd,her,heB,hdc⟩ := actualSmallRoughRho_ne_zero_factors
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
    ((N : ℝ) ^ (nu0 * epsilon ^ 2)) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    ((N : ℝ) ^ (nu0 * epsilon)) hrow
  have hvalue := presieved_coefficient_value (B := (N : ℝ) ^ (nu0 * epsilon)) hlegal.2.1 he hd
  change presievedCoefficient N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
    ((N : ℝ) ^ (nu0 * epsilon ^ 2)) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) ((N : ℝ) ^ (nu0 * epsilon)) r ≠ 0 at hrow
  rw [her,hvalue] at hrow
  have hbeta := (mul_ne_zero_iff.mp hrow).2
  have heActive : SmallBetaActive N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) e
      ((N : ℝ) ^ (nu0 * epsilon ^ 2)) (nu0 * epsilon) := by
    unfold commonSmallWeight at hbeta
    by_cases hsign : 0 ≤ roughWeight N
        (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
        ((N : ℝ) ^ (nu0 * epsilon ^ 2)) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
        (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) d
    · rw [if_pos hsign] at hbeta
      exact Or.inl hbeta
    · rw [if_neg hsign] at hbeta
      exact Or.inr hbeta
  have hs := (Finset.mem_filter.mp ht).1
  have htag := (Finset.mem_filter.mp ht).2
  have hcell := owner_mem n (U1011OriginalFifteenJointNativeRows.joint_coordinates_cube hN hs)
  have hbox := cell_subset_closed_box n _ hcell
  have hvalid : (ownerBox n N t).Valid := gridBox_valid n _
  have hpositive : 0 < (ownerBox n N t).lo 3 := gridBox_lower_positive n _ 3
  have hcert := (boxPolicy_certificate (ownerBox n N t) htag).2
  change wholeBoxEligibleTest (selectedPolicy n N t) (ownerBox n N t) = true at hcert
  rw [hW] at hcert
  have hZ : U1011OriginalSixteenJointNearCapCompiler.Z n N eta t =
      U1011OriginalW16NearCapNative.Z (ownerBox n N t) eta N := by
    change U1011OriginalSixteenJointNearCapCompiler.rowZ (selectedPolicy n N t) (ownerBox n N t) eta N = _
    rw [hW]
    exact (U1011OriginalSixteenJointNearCapCompiler.W_native_binding (ownerBox n N t) eta N).1
  have hD : U1011OriginalSixteenJointNearCapCompiler.D n N eta t =
      U1011OriginalW16NearCapNative.D (ownerBox n N t) eta N := by
    change U1011OriginalSixteenJointNearCapCompiler.rowD (selectedPolicy n N t) (ownerBox n N t) eta N = _
    rw [hW]
    exact (U1011OriginalSixteenJointNearCapCompiler.W_native_binding (ownerBox n N t) eta N).2.1
  have hdelta : (U1011OriginalSixteenNearCapBoxProfiles.delta
      (selectedPolicy n N t) (ownerBox n N t) eta : ℝ) =
      (U1011OriginalW16NearCapNative.delta (ownerBox n N t) eta : ℝ) := by
    rw [hW]
    simp only [U1011OriginalSixteenNearCapBoxProfiles.delta,
      U1011OriginalSixteenNearCapBoxProfiles.G, U1011OriginalW16NearCapNative.delta,
      wPolicy, show ¬ (15 : ℕ) < 15 by omega, if_false]
  have hell := (parameters_on_joint_row hN heta hnu0 heps heBudget ht).2.2
  rw [hdelta] at hell
  have hellpos : 0 < nu0 * epsilon := mul_pos hnu0 heps
  have hdeltaPos : 0 < (U1011OriginalW16NearCapNative.delta (ownerBox n N t) eta : ℝ) := by linarith
  have hellW : nu0 * epsilon ≤ (U1011OriginalW16NearCapNative.delta (ownerBox n N t) eta : ℝ) / 2 := by
    linarith
  have htail := canonical_rough_tail_data hlegal.2.1 (hw t ht) hd
  have hwellW := htail.1
  rw [hD] at hwellW
  have hroughW : ∀ p ∈ canonicalSlots N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
      ((N : ℝ) ^ (nu0 * epsilon ^ 2)) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) d,
      Nat.Prime p ∧ (p : ℝ) < U1011OriginalW16NearCapNative.Z (ownerBox n N t) eta N := by
    simpa only [hZ] using htail.2.2
  refine ⟨e,he,d,hd,her,heActive,hdeltaPos,hwellW,htail.2.1,?_⟩
  intro A hA hAupper
  have ha := U1011OriginalW16JointSmallBeta.fixed_beta_attached_monomials hN hs
    (ownerBox n N t) eta heta hvalid hpositive hcert hbox A hA hAupper
    (canonicalSlots N (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
      ((N : ℝ) ^ (nu0 * epsilon ^ 2)) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) d)
    hwellW hroughW ((N : ℝ) ^ (nu0 * epsilon ^ 2)) (nu0 * epsilon) hellpos hellW heActive
  dsimp only at ha ⊢
  refine ⟨?_,ha.2⟩
  calc
    _ = e * (fullPrefix t * (canonicalSlots N
        (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
        ((N : ℝ) ^ (nu0 * epsilon ^ 2)) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) d).prod) := ha.1
    _ = fullPrefix t * r := by rw [canonicalSlots_prod hd,her]; ring

end
end ImbalancedChen.P5Z.OriginalJointPresievedWFactors

