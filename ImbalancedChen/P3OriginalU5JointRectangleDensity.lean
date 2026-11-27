import ImbalancedChen.P3OriginalU5JointBetaReserve
import ImbalancedChen.P3OriginalU5JointModulusCap
import ImbalancedChen.P3OriginalU5JointRoughRoundingPayment
import ImbalancedChen.P3OriginalU5RectanglePolicyAgreement

/-! A positive full-modulus reciprocal-totient sum for the joint signed
coefficient on the physical rectangle. The rough perturbation is paid with
the absolute full-pair loss. The small Rosser reserve and modulus bound use
the identical joint beta attachment. -/

namespace ImbalancedChen.P3OriginalU5JointRectangleDensity

noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2GammaU5PlateauGeometry (rectangle rectangle_subset_pairSupport)
open P2LowerFiniteCellBetaCompiler (raw_density_on_universe)
open P2OriginalLowerCompactStartCapConstructor (topCap)
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank)
open P2OriginalPairSourceReceiver (PairRange)
open P3OriginalU5CoarseRootV (meshStep)
open P3OriginalU5CommonPhysicalRoot (policy)
open P3OriginalU5JointBetaAttachment (rho)
open P3OriginalU5JointCellCoefficient (carrier roughCarrier coefficient rawCoefficient
  coefficient_abs_le_one coefficient_le_raw roundingLoss)
open P3OriginalU5JointPrimeWallPayment (rowWeight_eq_full)
open P3OriginalU5RoundedCountInsertion (roundedSupport)
open P3OriginalU5RoundedPairDensity (fullModulus_density_eq)
open P3OriginalU5RoundedPlateauFamily (rectangle_harmonic_limit)
open P5OriginalU5CausalFinite (attachmentNu attachmentR attachmentNu_mul_attachmentR
  attachment_gates cutoff fullDensity pairSupport smallCutoff)
open P5OriginalU5PlateauPrimeBV (fullModulus)

private def rowLoss (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ)
    (m N : ℕ) (epsilon tau : ℝ) (t : ℕ × ℕ) : ℝ :=
  ∑ d ∈ roughCarrier N epsilon,
    |coefficient R bank b m N epsilon tau (t,d) - rawCoefficient R bank b m N epsilon (t,d)| /
      (Nat.totient (fullModulus t d) : ℝ)

private theorem rowLoss_eq (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ)
    (m : ℕ) {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ} (he : 0 < epsilon) (he8 : epsilon < 1/8)
    (tau : ℝ) {t : ℕ × ℕ} (ht : t ∈ pairSupport N) :
    (reciprocalTotientDensity (roughCarrier N epsilon) (fun d => rawCoefficient R bank b m N epsilon (t,d)) -
      reciprocalTotientDensity (roughCarrier N epsilon) (fun d => coefficient R bank b m N epsilon tau (t,d))) /
        (Nat.totient (t.1*t.2) : ℝ) = rowLoss R bank b m N epsilon tau t := by
  unfold reciprocalTotientDensity rowLoss
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  dsimp only
  rw [abs_of_nonpos (sub_nonpos.mpr (coefficient_le_raw R bank b m N epsilon tau ht d))]
  have hw := rowWeight_eq_full hN he he8
    (show (t,d) ∈ carrier N epsilon from Finset.mem_product.mpr ⟨ht, hd⟩)
  change (1 / (Nat.totient (t.1*t.2) : ℝ)) * (1 / (Nat.totient d : ℝ)) =
    1 / (Nat.totient (fullModulus t d) : ℝ) at hw
  let a := rawCoefficient R bank b m N epsilon (t,d)
  let f := coefficient R bank b m N epsilon tau (t,d)
  calc
    (a / (Nat.totient d : ℝ) - f / (Nat.totient d : ℝ)) / (Nat.totient (t.1*t.2) : ℝ) = (a - f) *
        ((1 / (Nat.totient (t.1*t.2) : ℝ)) * (1 / (Nat.totient d : ℝ))) := by ring
    _ = _ := by rw [hw]; dsimp only [a, f]; ring

/-- For any selected collection of marked pairs, its perturbation is
bounded by the complete joint absolute loss. Both marks stay in the
denominator through the rough perturbation and the small attachment. -/
theorem subset_density_lower (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh) (b : ℚ)
    (m : ℕ) {N : ℕ} (hN : 2 ≤ N) (hEven : Even N)
    {epsilon : ℝ} (he : 0 < epsilon) (he8 : epsilon < 1/8) (tau : ℝ)
    (T : Finset (ℕ × ℕ)) (hT : T ⊆ pairSupport N) (A E : ℝ)
    (hraw : ∀ t ∈ T, A + E ≤ fullDensity N (policy R bank b m N t))
    (hbeta : ∀ t ∈ T,
      actualSmallEulerProduct N (Nat.ceil (cutoff N)) (smallCutoff N epsilon) *
        reciprocalTotientDensity (roughCarrier N epsilon) (fun d => coefficient R bank b m N epsilon tau (t,d)) -
        physicalDensitySum (roundedSupport N epsilon) (rho R bank b m N epsilon tau t) ≤ E) :
    A * (∑ t ∈ T, 1 / (Nat.totient (t.1 * t.2) : ℝ)) ≤
      (∑ t ∈ T, ∑ k ∈ roundedSupport N epsilon, rho R bank b m N epsilon tau t k /
        (Nat.totient (fullModulus t k) : ℝ)) +
      actualSmallEulerProduct N (Nat.ceil (cutoff N)) (smallCutoff N epsilon) *
        roundingLoss R bank b m N epsilon tau := by
  let V := actualSmallEulerProduct N (Nat.ceil (cutoff N)) (smallCutoff N epsilon)
  have hV : 0 ≤ V := (actualSmallEulerProduct_pos N _ _ hEven).le
  have hsub : ∑ t ∈ T, rowLoss R bank b m N epsilon tau t ≤ roundingLoss R bank b m N epsilon tau :=
    Finset.sum_le_sum_of_subset_of_nonneg hT (fun t _ _ =>
      Finset.sum_nonneg (fun d _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)))
  calc
    _ = ∑ t ∈ T, A / (Nat.totient (t.1*t.2) : ℝ) := by
      simp only [Finset.mul_sum, div_eq_mul_inv, one_mul]
    _ ≤ ∑ t ∈ T, ((∑ k ∈ roundedSupport N epsilon, rho R bank b m N epsilon tau t k /
        (Nat.totient (fullModulus t k) : ℝ)) + V * rowLoss R bank b m N epsilon tau t) := by
      apply Finset.sum_le_sum
      intro t ht
      let P := policy R bank b m N t
      let X := reciprocalTotientDensity (roughCarrier N epsilon) (fun d => rawCoefficient R bank b m N epsilon (t,d))
      let Y := reciprocalTotientDensity (roughCarrier N epsilon) (fun d => coefficient R bank b m N epsilon tau (t,d))
      let D := physicalDensitySum (roundedSupport N epsilon) (rho R bank b m N epsilon tau t)
      have hx : fullDensity N P ≤ V * X := by
        dsimp only [X, rawCoefficient]
        rw [raw_density_on_universe]
        exact fixedEvenRoughDensity_presieveProjection P N _ _ _ (attachment_gates hN he he8).2.2
      have hr : A + E ≤ fullDensity N P := hraw t ht
      have hb : V * Y - D ≤ E := hbeta t ht
      have hledger : A ≤ D + V * (X-Y) := by linarith only [hr, hx, hb]
      rw [fullModulus_density_eq hN he he8 (hT ht), ← rowLoss_eq R bank b m hN he he8 tau (hT ht)]
      calc
        _ ≤ (D + V * (X-Y)) / (Nat.totient (t.1*t.2) : ℝ) :=
          div_le_div_of_nonneg_right hledger (Nat.cast_nonneg _)
        _ = _ := by dsimp only [D, X, Y]; ring
    _ = (∑ t ∈ T, ∑ k ∈ roundedSupport N epsilon, rho R bank b m N epsilon tau t k /
        (Nat.totient (fullModulus t k) : ℝ)) + V * (∑ t ∈ T, rowLoss R bank b m N epsilon tau t) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hsub hV)

/-- For fixed R the positive constant precedes epsilon, both meshes and
the bank. Each fixed physical bank has one width and target threshold for
all finer widths. The same signed rho has the full physical modulus cap. -/
theorem exists_joint_rectangle_positive_density (R : PairRange) :
    ∃ c : ℝ, 0 < c ∧ ∀ epsilonMax : ℝ, 0 < epsilonMax →
      ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1/8 ∧ epsilon < epsilonMax ∧ epsilon < 1/272 ∧
        ∀ m : ℕ, meshStep R m ≤ 1/32000 → ∀ {mesh : ℕ} (bank : CandidateBank mesh),
          ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
            ∀ tau : ℝ, 0 < tau → tau ≤ tau0 → ∀ N ≥ N0, Even N →
              c * singularSeries N / Real.log (N : ℝ) ≤
                (∑ t ∈ rectangle N, ∑ k ∈ roundedSupport N epsilon, rho R bank (1/1000) m N epsilon tau t k /
                  (Nat.totient (fullModulus t k) : ℝ)) ∧
              ∀ (t : ℕ × ℕ) (k : ℕ), rho R bank (1/1000) m N epsilon tau t k ≠ 0 →
                (fullModulus t k : ℝ) < (N : ℝ) ^ (599/1000 : ℝ) := by
  obtain ⟨c, hc, Ns, hNs, hselected⟩ := P3OriginalU5SelectedDensityLower.exists_original_U5_selected_row_lower R
  let M := Real.log (11/10 : ℝ) * Real.log (13/12 : ℝ)
  have hM : 0 < M := rectangle_harmonic_limit.1
  let a := c*M/8
  have ha : 0 < a := by dsimp only [a]; positivity
  obtain ⟨Nm, hmass⟩ := eventually_atTop.mp
    (rectangle_harmonic_limit.2.eventually (lt_mem_nhds (show M/2 < M by linarith only [hM])))
  refine ⟨a, ha, ?_⟩
  intro epsilonMax hmax
  have hnu : 0 < attachmentNu := by norm_num [attachmentNu]
  obtain ⟨epsilon, he, he8, hemin, _, Nb, _, hbeta⟩ := P3OriginalU5JointBetaReserve.exists_beta_error_le_target_reserve
    attachmentNu attachmentR (c/2) (min epsilonMax (1/272)) hnu (by norm_num [attachmentR, attachmentNu])
      (half_pos hc) (lt_min hmax (by norm_num))
  have he272 := hemin.trans_le (min_le_right _ _)
  obtain ⟨B, hB, hEuler⟩ := exists_actualSmallEulerProduct_le_singularSeries_log
  let eta := a * (attachmentNu * epsilon^2) / B
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hbudget : topCap + attachmentNu * epsilon < 599/1000 := by
    calc
      _ < topCap + attachmentNu * (1/272 : ℝ) :=
        add_lt_add_of_le_of_lt le_rfl (mul_lt_mul_of_pos_left he272 hnu)
      _ < _ := by norm_num [topCap, attachmentNu]
  obtain ⟨tauCap, htauCap, hcap⟩ := P3OriginalU5JointModulusCap.exists_uniform_joint_cap he hbudget
  have htend : Tendsto (fun N : ℕ => smallCutoff N epsilon) atTop atTop :=
    (tendsto_rpow_atTop (mul_pos hnu (pow_pos he 2))).comp tendsto_natCast_atTop_atTop
  obtain ⟨Nfour, hfour⟩ := eventually_atTop.mp (htend.eventually (eventually_ge_atTop (4 : ℝ)))
  refine ⟨epsilon, he, he8, hemin.trans_le (min_le_left _ _), he272, ?_⟩
  intro m hm mesh bank
  have hb : (0 : ℚ) ≤ 1/1000 := by norm_num
  obtain ⟨tauBox, htauBox, Nx, _, hbox⟩ :=
    P3OriginalU5JointRoughRoundingPayment.exists_joint_rough_rounding_payment R bank (1/1000) hb m he he8 heta
  let N0 := max (max Ns Nm) (max Nb (max Nx Nfour))
  have hNs0 : Ns ≤ N0 := (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨min tauBox tauCap, lt_min htauBox htauCap, N0, hNs.trans hNs0, ?_⟩
  intro tau htau hwidth N hN hEven
  have hsN := hNs0.trans hN
  have hN2 := hNs.trans hsN
  have hNmN : Nm ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hbN : Nb ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hxf : max Nx Nfour ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  let cap := Nat.ceil (cutoff N)
  let V := actualSmallEulerProduct N cap (smallCutoff N epsilon)
  let S := singularSeries N / Real.log (N : ℝ)
  let A := (c/2) * S
  have hS : 0 < S := div_pos (singularSeries_pos N) (Real.log_pos hNr)
  have hA : 0 ≤ A := (mul_pos (half_pos hc) hS).le
  have hz : (N : ℝ) ^ (attachmentNu * attachmentR) ≤ (cap : ℝ) := by
    rw [attachmentNu_mul_attachmentR]
    exact Nat.le_ceil _
  have hraw (t) (ht : t ∈ rectangle N) : A + A ≤ fullDensity N (policy R bank (1/1000) m N t) := by
    rw [P3OriginalU5RectanglePolicyAgreement.rectangle_policy_eq R hm bank (1/1000) hN2 ht]
    have hp := hselected N hsN hEven bank (1/1000) hb le_rfl t (rectangle_subset_pairSupport hN2 ht)
    calc
      _ = c * singularSeries N / Real.log (N : ℝ) := by dsimp only [A, S]; ring
      _ ≤ _ := hp
  have hbetaRow (t : ℕ × ℕ) (_ : t ∈ rectangle N) :
      V * reciprocalTotientDensity (roughCarrier N epsilon) (fun d => coefficient R bank (1/1000) m N epsilon tau (t,d)) -
        physicalDensitySum (roundedSupport N epsilon) (rho R bank (1/1000) m N epsilon tau t) ≤ A := by
    let f (d : ℕ) := coefficient R bank (1/1000) m N epsilon tau (t,d)
    have h := (hbeta N hbN hEven cap hz f (fun d _ => coefficient_abs_le_one R bank (1/1000) m N epsilon tau (t,d))).2
    rw [attachmentNu_mul_attachmentR] at h
    calc
      _ ≤ (c/2) * singularSeries N / Real.log (N : ℝ) := h
      _ = A := by dsimp only [A, S]; ring
  have hVpos : 0 ≤ V := (actualSmallEulerProduct_pos N cap _ hEven).le
  have hVupper : V ≤ B * singularSeries N / ((attachmentNu * epsilon^2) * Real.log (N : ℝ)) := by
    have h := hEuler N cap (by omega) hEven (smallCutoff N epsilon) (hfour N ((le_max_right _ _).trans hxf))
      ((attachment_gates hN2 he he8).2.2.trans (Nat.le_ceil _))
    rwa [P5OriginalU5CausalFinite.smallCutoff, Real.log_rpow (zero_lt_one.trans hNr)] at h
  have hboxPaid : V * roundingLoss R bank (1/1000) m N epsilon tau ≤ a*S := by
    calc
      _ ≤ V * eta := mul_le_mul_of_nonneg_left
        (hbox ((le_max_left _ _).trans hxf) htau (hwidth.trans (min_le_left _ _))).le hVpos
      _ ≤ (B * singularSeries N / ((attachmentNu * epsilon^2) * Real.log (N : ℝ))) * eta :=
        mul_le_mul_of_nonneg_right hVupper heta.le
      _ = _ := by
        dsimp only [eta, S]
        field_simp [hB.ne', hnu.ne', he.ne', (Real.log_pos hNr).ne']
  have hsum := subset_density_lower R bank (1/1000) m hN2 hEven he he8 tau (rectangle N)
    (rectangle_subset_pairSupport hN2) A A hraw hbetaRow
  have hmLower : (a*S) + (a*S) ≤ A * (∑ t ∈ rectangle N, 1 / (Nat.totient (t.1*t.2) : ℝ)) := by
    calc
      _ = A * (M/2) := by dsimp only [a, A]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hmass N hNmN).le hA
  refine ⟨?_, hcap tau htau (hwidth.trans (min_le_right _ _)) R bank (1/1000) hb m N hN2⟩
  rw [mul_div_assoc]
  change a*S ≤ _
  change A * _ ≤ _ + V * roundingLoss R bank (1/1000) m N epsilon tau at hsum
  linarith only [hmLower, hsum, hboxPaid]

end
end ImbalancedChen.P3OriginalU5JointRectangleDensity
