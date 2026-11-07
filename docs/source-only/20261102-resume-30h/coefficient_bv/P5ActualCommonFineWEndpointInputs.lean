import ImbalancedChen.P5All16MarkedCommonFineSource
import ImbalancedChen.P5ActualInnerWholeEndpointCapacity
import ImbalancedChen.P5OriginalWWholeRealAssignment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual ALL16 whole-cell owner, common prime-label upper endpoints and
original W winner supply the G real-W program's hypotheses. No capacity,
allocation, arithmetic representative or SW bound is assumed. The marked
mesh and residual mesh costs are explicit, and the full third endpoint
includes the one fixed beta level N^epsilon, not a chosen small factor.
-/

namespace ImbalancedChen.P5Z.ActualCommonFineWEndpointInputs
noncomputable section
open Classical Filter Topology
open scoped BigOperators
open ImbalancedChen U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenNearCapBoxProfiles
open OriginalNearCapRealEndpointGeometry
open PresievedRoughGateMeshReserve PresievedRoughSlotAffineGates
open All16MarkedCommonFineSource ActualInnerWholeEndpointCapacity

/-- A single sufficiently fine mesh pays both geometric costs at every
physical rank up to R. Its threshold depends on the fixed owner and R,
and is independent of N, arithmetic primes, beta and A. -/
theorem eventually_W_owner_mesh_costs {n : ℕ} (R : ℕ) (c : CoarseGrid n)
    (eta : ℚ) (heta : 0 < eta)
    (htag : U1011OriginalSixteenStaticCellWinner.chosenTag
      (U1011OriginalFifteenNativeGridCells.gridBox n c) ≠ 0)
    (hW : U1011OriginalSixteenStaticNativeCompiler.boxPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n c) = wPolicy) :
    ∀ᶠ m : ℕ in atTop,
      logPrimeMeshStep 0 1 m ≤ endpointPadding wPolicy
        (U1011OriginalFifteenNativeGridCells.gridBox n c) eta ∧
      ∀ r ≤ R, roughWidth r m ≤ (delta wPolicy
        (U1011OriginalFifteenNativeGridCells.gridBox n c) eta : ℝ) := by
  let B := U1011OriginalFifteenNativeGridCells.gridBox n c
  have hv := U1011OriginalFifteenNativeGridCells.gridBox_valid n c
  have hw := U1011OriginalFifteenNativeGridCells.gridBox_lower_positive n c 3
  have hc := (U1011OriginalSixteenStaticNativeCompiler.boxPolicy_certificate B htag).2
  rw [hW] at hc
  have hd : (0 : ℝ) < (delta wPolicy B eta : ℝ) := by
    exact_mod_cast (rational_parameters wPolicy B eta hv hw hc heta).2.2.1
  have hp := (endpointPadding_positive wPolicy B eta hv hw hc heta).1
  have hlim : Tendsto (fun m => (R + 3 : ℝ) * logPrimeMeshStep 0 1 m)
      atTop (nhds 0) := by
    simpa only [mul_zero] using (tendsto_logPrimeMeshStep 0 1).const_mul (R + 3 : ℝ)
  filter_upwards [(tendsto_logPrimeMeshStep 0 1).eventually (gt_mem_nhds hp),
    hlim.eventually (gt_mem_nhds hd)] with m hm1 hm2
  refine ⟨hm1.le, ?_⟩
  intro r hr
  have hrR : (r : ℝ) ≤ R := by exact_mod_cast hr
  exact (mul_le_mul_of_nonneg_right (by linarith : (r + 3 : ℝ) ≤ R + 3)
    (logPrimeMeshStep_pos (by norm_num : (0 : ℝ) < 1) m).le).trans hm2.le

/-- The finite set of actual coarse owners shares ONE fine-mesh
threshold. No separate N-dependent choice is made for each atom. -/
theorem eventually_all_W_owner_mesh_costs (n R : ℕ) (eta : ℚ) (heta : 0 < eta) :
    ∀ᶠ m : ℕ in atTop, ∀ c : CoarseGrid n,
      U1011OriginalSixteenStaticCellWinner.chosenTag
        (U1011OriginalFifteenNativeGridCells.gridBox n c) ≠ 0 →
      U1011OriginalSixteenStaticNativeCompiler.boxPolicy
        (U1011OriginalFifteenNativeGridCells.gridBox n c) = wPolicy →
      logPrimeMeshStep 0 1 m ≤ endpointPadding wPolicy
        (U1011OriginalFifteenNativeGridCells.gridBox n c) eta ∧
      ∀ r ≤ R, roughWidth r m ≤ (delta wPolicy
        (U1011OriginalFifteenNativeGridCells.gridBox n c) eta : ℝ) := by
  apply eventually_all.mpr
  intro c
  by_cases ht : U1011OriginalSixteenStaticCellWinner.chosenTag
      (U1011OriginalFifteenNativeGridCells.gridBox n c) = 0
  · exact Eventually.of_forall (fun m htag => (htag ht).elim)
  by_cases hW : U1011OriginalSixteenStaticNativeCompiler.boxPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n c) = wPolicy
  · filter_upwards [eventually_W_owner_mesh_costs R c eta heta ht hW] with m hm
    exact fun _ _ => hm
  · exact Eventually.of_forall (fun m _ hw => (hW hw).elim)

/-- These are the literal data of the independently defined original
owner and WholeCell. Fine endpoints are never replaced by prime values. -/
theorem actual_W_cell_endpoint_inputs {n m r : ℕ} {eta : ℚ} {rho : ℝ}
    {M : Set (ℝ × ℝ)} {c : CoarseGrid n} {a : Grid 4 m} {j : Grid r m}
    (h : WholeCell eta rho M c a j)
    (hW : U1011OriginalSixteenStaticNativeCompiler.boxPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n c) = wPolicy)
    (hmesh : logPrimeMeshStep 0 1 m ≤ endpointPadding wPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n c) eta) :
    let B := U1011OriginalFifteenNativeGridCells.gridBox n c
    let u := logPrimeMeshHi 0 1 m a
    let v := logPrimeMeshHi 0 1 m j
    wholeBoxEligibleTest wPolicy B = true ∧
      (∀ i, (B.lo i : ℝ) ≤ u i) ∧
      (∀ i, u i ≤ (B.hi i : ℝ) + endpointPadding wPolicy B eta) ∧
      0 ≤ u 2 ∧ u 1 ≤ u 0 ∧ u 3 ≤ u 2 ∧
      (∀ i, 0 ≤ v i) ∧ Antitone v ∧ (∀ i, v i ≤ u 2) ∧
      (∀ i : Fin r, Even i.val →
        cube v i < (physicalResidual wPolicy B eta : ℝ) + roughWidth r m) := by
  let B := U1011OriginalFifteenNativeGridCells.gridBox n c
  have hcert := (U1011OriginalSixteenStaticNativeCompiler.boxPolicy_certificate B h.tag).2
  rw [hW] at hcert
  have hlo : logPrimeMeshLo 0 1 m a ∈ cell 0 1 m a := by
    apply mem_logPrimeMeshCell.mpr
    intro i
    exact ⟨le_rfl, (logPrimeMeshLoHi_bounds (by norm_num : (0 : ℝ) < 1) m a i).2.1⟩
  have howner := U1011OriginalFifteenNativeGridCells.cell_subset_closed_box n c (h.owner hlo)
  have hanti := (h.prefix _ hlo).2.2.2.1
  have hell : cellEll n eta c = (physicalResidual wPolicy B eta : ℝ) := by
    simp only [cellEll, hW, B]
  obtain ⟨hv0, hvanti, hcubes⟩ := actual_inner_endpoint_inputs (cellEll n eta c) h.inner
  refine ⟨hcert, ?_, ?_, ?_, ?_, ?_, hv0, hvanti, ?_, ?_⟩
  · intro i
    exact (howner.1 i).trans
      (logPrimeMeshLoHi_bounds (by norm_num : (0 : ℝ) < 1) m a i).2.1.le
  · intro i
    rw [logPrimeMeshHi_eq_lo_add_step]
    exact add_le_add (howner.2 i) hmesh
  · exact (logPrimeMeshLoHi_bounds (by norm_num : (0 : ℝ) < 1) m a 2).1.trans
      (logPrimeMeshLoHi_bounds (by norm_num : (0 : ℝ) < 1) m a 2).2.1.le
  · rw [logPrimeMeshHi_eq_lo_add_step, logPrimeMeshHi_eq_lo_add_step]
    exact add_le_add_right (hanti (by norm_num : (0 : Fin 4) < 1)).le _
  · rw [logPrimeMeshHi_eq_lo_add_step, logPrimeMeshHi_eq_lo_add_step]
    exact add_le_add_right (hanti (by norm_num : (2 : Fin 4) < 3)).le _
  · intro i
    exact (h.residualUpper i).trans ((h.markedLower 2).trans
      (logPrimeMeshLoHi_bounds (by norm_num : (0 : ℝ) < 1) m a 2).2.1.le)
  · simpa only [hell] using hcubes

/-- The actual W owner licenses the same program's endpoint triple with
the ENTIRE beta support N^epsilon attached in group 3. This pays the
endpoint length needed by the normalized convolution, uniformly in e. -/
theorem actual_W_cell_beta_endpoint_monomials {n N m r : ℕ} (hN : 1 < N)
    {eta : ℚ} (heta : 0 < eta) {rho epsilon : ℝ} {M : Set (ℝ × ℝ)}
    {c : CoarseGrid n} {a : Grid 4 m} {j : Grid r m}
    (h : WholeCell eta rho M c a j)
    (hW : U1011OriginalSixteenStaticNativeCompiler.boxPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n c) = wPolicy)
    (hmesh : logPrimeMeshStep 0 1 m ≤ endpointPadding wPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n c) eta)
    (hwidth : roughWidth r m ≤ (delta wPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n c) eta : ℝ))
    (A : ℝ) (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    {kappa : ℝ} (hk0 : 0 ≤ kappa)
    (hk : kappa ≤ (delta wPolicy (U1011OriginalFifteenNativeGridCells.gridBox n c) eta : ℝ) / 64)
    (hepsilon : epsilon ≤ (delta wPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n c) eta : ℝ) / 4) :
    let B := U1011OriginalFifteenNativeGridCells.gridBox n c
    let abc := OriginalWWholeRealAssignment.endpointFactors N
      (logPrimeMeshHi 0 1 m a) (logPrimeMeshHi 0 1 m j) B eta A
    let d : ℝ := (delta wPolicy B eta : ℝ)
    let C := (N : ℝ) ^ epsilon * abc.2.2
    abc.1 ≤ A ∧
      A ^ 2 * abc.2.1 * C ^ 2 ≤ (N : ℝ) ^ (1 - 3 * d) ∧
      (N : ℝ) ^ (7 * (1 + 3 * kappa) / 32) * A * abc.1 * abc.2.1 ^ 5 * C ^ 2 ≤
        (N : ℝ) ^ (2 - 3 * d) ∧
      (A * C / abc.2.1) ^ (7 / 16 : ℝ) * A * abc.1 * abc.2.1 ^ 5 * C ^ 2 ≤
        (N : ℝ) ^ (2 - 4 * d) := by
  let B := U1011OriginalFifteenNativeGridCells.gridBox n c
  have hv := U1011OriginalFifteenNativeGridCells.gridBox_valid n c
  have hw := U1011OriginalFifteenNativeGridCells.gridBox_lower_positive n c 3
  obtain ⟨hc, hlo, hhi, hu2, hu10, hu32, hv0, hvanti, hvlate, hcubes⟩ :=
    actual_W_cell_endpoint_inputs h hW hmesh
  obtain ⟨hleft, h1, h2, h3⟩ := OriginalWWholeRealAssignment.actual_W_whole_real_monomials
    hN B eta hv hw hc heta _ hlo hhi hu2 hu10 hu32 _ hv0 hvanti hvlate hwidth hcubes
    A hA hAupper hk0 hk
  obtain ⟨ha, hb, hcpos⟩ := OriginalWWholeRealAssignment.endpointFactors_positive
    hN (logPrimeMeshHi 0 1 m a) (logPrimeMeshHi 0 1 m j) B eta A
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := zero_lt_one.trans hn
  have hd : (0 : ℝ) < (delta wPolicy B eta : ℝ) := by
    exact_mod_cast (rational_parameters wPolicy B eta hv hw hc heta).2.2.1
  obtain ⟨h1', h2', h3'⟩ := ActualSmallBetaMonomialCost.third_factor_beta_cost hn
    (zero_lt_one.trans_le hA) ha hb hcpos (Real.rpow_pos_of_pos hn0 epsilon)
    (le_rfl : (N : ℝ) ^ epsilon ≤ (N : ℝ) ^ epsilon) h1 h2 h3
  exact ⟨hleft,
    h1'.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)),
    h2'.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)),
    h3'.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))⟩

end
end ImbalancedChen.P5Z.ActualCommonFineWEndpointInputs
