import ImbalancedChen.P5ActualCommonFineWEndpointInputs
import ImbalancedChen.P5All16ComputedWholeWordAssignment
import ImbalancedChen.P5ActualMarkedSameAssignmentTensor

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The SAME computed W lists used by the independent marked Cartesian source
have their literal real support endpoints and beta cost proved here.
Original per-label gamma and the residual restoring scalar are unchanged.
Support is proved for NONZERO coefficients: the broad small divisor
carrier itself is not incorrectly claimed to lie below the beta level.
-/

namespace ImbalancedChen.P5Z.ActualComputedWNormalizedLicence
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenNearCapBoxProfiles OriginalNearCapRealEndpointGeometry
open PresievedRoughGateMeshReserve
open All16MarkedCommonFineSource All16MarkedFineScalarBudget
open All16ComputedWholeWordAssignment ActualInnerPerLabelGamma
open SameWholeAssignmentPerLabel ActualCommonFineWEndpointInputs
open ActualAll16UnrestrictedResidualConvolution

def labelUpper (N m : ℕ) (i : Fin (m + 1)) : ℝ :=
  (N : ℝ) ^ logPrimeMeshPoint 0 1 m (i.val + 1)

def labelEndpoint (N m : ℕ) (word : List (Fin (m + 1))) : ℝ :=
  (word.map (labelUpper N m)).prod

/-- Real endpoints, without integer ceiling inflation. -/
theorem prime_box_real_product_le {ι : Type*} (B : ι → Finset ℕ)
    (upper : ι → ℝ) (hupper : ∀ i, 0 ≤ upper i)
    (hsize : ∀ i, ∀ p ∈ B i, (p : ℝ) ≤ upper i) (word : List ι) :
    ∀ ps ∈ actualPrimeSlotBox B word, (ps.prod : ℝ) ≤ (word.map upper).prod := by
  induction word with
  | nil => simp [actualPrimeSlotBox]
  | cons i word ih =>
      intro ps hps
      obtain ⟨⟨p, qs⟩, hpqs, rfl⟩ := Finset.mem_image.mp hps
      obtain ⟨hp, hqs⟩ := Finset.mem_product.mp hpqs
      simp only [List.prod_cons, List.map_cons, Nat.cast_mul]
      exact mul_le_mul (hsize i p hp) (ih qs hqs) (Nat.cast_nonneg _) (hupper i)

theorem gamma_nonzero_mem_support {ι : Type*} [DecidableEq ι]
    (B : ι → Finset ℕ) (word : List ι) {d : ℕ} (hd : gamma B word d ≠ 0) :
    d ∈ support B word := by
  have hc : actualPrimeTupleCoefficient (actualPrimeSlotBox B word) d ≠ 0 := by
    intro hz
    apply hd
    simp only [gamma, hz, Nat.cast_zero, zero_div]
  obtain ⟨ps, hps⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
  obtain ⟨hbox, hprod⟩ := Finset.mem_filter.mp hps
  exact Finset.mem_image.mpr ⟨ps, hbox, hprod⟩

theorem common_support_endpoint (N m : ℕ) (word : List (Fin (m + 1)))
    {d : ℕ} (hd : d ∈ support (commonAlphabet N m) word) :
    0 < d ∧ (d : ℝ) ≤ labelEndpoint N m word := by
  obtain ⟨ps, hps, rfl⟩ := Finset.mem_image.mp hd
  have hprime := actualPrimeSlotBox_prime (commonAlphabet N m) word
    (fun i hi p hp => (mem_roughPrimeFinset.mp
      (ActualInnerMeshSeparatedGamma.mesh_prime_rough hp)).2.1) ps hps
  refine ⟨List.prod_pos (fun p hp => (hprime p hp).pos), ?_⟩
  exact prime_box_real_product_le (commonAlphabet N m) (labelUpper N m)
    (fun i => Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (fun i p hp => (Finset.mem_filter.mp hp).2.2.le) word ps hps

/-- Unique small/rough factorization exposes the actual active beta,
rather than using the larger divisor enumeration as a beta support. -/
theorem attached_nonzero_factors {ι : Type*} [DecidableEq ι]
    (B : ι → Finset ℕ) (word : List ι) (N cap r : ℕ) (w L : ℝ)
    (hrough : ∀ d ∈ support B word, RoughPrimeSupportedAt w d)
    {q : ℕ} (hq : attachedGamma B word N cap r w L q ≠ 0) :
    ∃ e ∈ actualSmallRosserSupport N cap w, ∃ d ∈ support B word,
      q = e * d ∧ rawBetaWeight N cap r w L e ≠ 0 := by
  have hmem : q ∈ attachedSupport B word N cap w := by
    by_contra hn
    exact hq (smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hn)
  obtain ⟨⟨e, d⟩, hed, hprod⟩ := Finset.mem_image.mp hmem
  obtain ⟨he, hd⟩ := Finset.mem_product.mp hed
  have hvalue := smallRoughRho_mul
    (fun e he => actualSmallRosserSupport_smallPrimeSupportedAt N cap w he)
    hrough (gamma B word) (rawBetaWeight N cap r w L) (rawBetaWeight N cap r w L) he hd
  have hpair : smallRoughPairCoefficient (gamma B word)
      (rawBetaWeight N cap r w L) (rawBetaWeight N cap r w L) (e, d) ≠ 0 := by
    rw [← hvalue, hprod]
    exact hq
  have hnonzero : gamma B word d * rawBetaWeight N cap r w L e ≠ 0 := by
    simpa only [smallRoughPairCoefficient, signAttachedCoefficient, ite_self] using hpair
  exact ⟨e, he, d, hd, hprod.symm, (mul_ne_zero_iff.mp hnonzero).2⟩

/-- All three ORIGINAL normalized coefficients have the real endpoints
of the independent computed assignment. This includes empty groups and
the whole common beta sum. No arithmetic tuple determines the groups. -/
theorem actual_computed_active_support {n N m r : ℕ} (hN : 1 < N)
    {eta : ℚ} {rho epsilon : ℝ} {M : Set (ℝ × ℝ)}
    (k : Key n m r) (h : WholeCell eta rho M k.1 k.2.1 k.2.2)
    (hcut : rho ≤ cellZeta n eta k.1) (A : ℝ) :
    let g := labelGroups n N m r eta A k
    (∀ x, gamma (commonAlphabet N m) g.1 x ≠ 0 →
      0 < x ∧ (x : ℝ) ≤ labelEndpoint N m g.1) ∧
    (∀ y, gamma (commonAlphabet N m) g.2.1 y ≠ 0 →
      0 < y ∧ (y : ℝ) ≤ labelEndpoint N m g.2.1) ∧
    (∀ q3, attachedGamma (commonAlphabet N m) g.2.2
      N (cellCap n N eta k.1) r ((N : ℝ) ^ rho) ((N : ℝ) ^ epsilon) q3 ≠ 0 →
      0 < q3 ∧ (q3 : ℝ) ≤ (N : ℝ) ^ epsilon * labelEndpoint N m g.2.2) := by
  let g := labelGroups n N m r eta A k
  refine ⟨fun x hx => common_support_endpoint N m g.1
      (gamma_nonzero_mem_support _ _ hx),
    fun y hy => common_support_endpoint N m g.2.1
      (gamma_nonzero_mem_support _ _ hy), ?_⟩
  intro q3 hq3
  have hword : ∀ i ∈ g.2.2, i ∈ fullWord k.2.1 k.2.2 := by
    intro i hi
    apply (labelGroups_partition n N m r eta A k).mem_iff.mp
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hi)))
  have hr : ∀ d ∈ support (commonAlphabet N m) g.2.2,
      RoughPrimeSupportedAt ((N : ℝ) ^ rho) d := by
    intro d hd
    exact whole_subword_product_rough hN h hcut g.2.2 hword hd
  obtain ⟨e, he, d, hd, rfl, hbeta⟩ := attached_nonzero_factors
    (commonAlphabet N m) g.2.2 N (cellCap n N eta k.1) r
    ((N : ℝ) ^ rho) ((N : ℝ) ^ epsilon) hr hq3
  obtain ⟨hepos, heupper⟩ := ActualSmallBetaMonomialCost.actual_raw_beta_endpoint hbeta
  obtain ⟨hdpos, hdupper⟩ := common_support_endpoint N m g.2.2 hd
  refine ⟨Nat.mul_pos hepos hdpos, ?_⟩
  rw [Nat.cast_mul]
  exact mul_le_mul heupper.le hdupper (Nat.cast_nonneg _)
    (Real.rpow_nonneg (Nat.cast_nonneg N) _)

/-- The endpoint products of the SAME computed gamma words are exactly
the three products in G's original W proof. No separate assignment or
ceiling-based surrogate endpoint is used. -/
theorem computed_W_endpoint_products {n N m r : ℕ} (eta : ℚ) (A : ℝ)
    (k : Key n m r)
    (hW : U1011OriginalSixteenStaticNativeCompiler.boxPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n k.1) = wPolicy) :
    let g := labelGroups n N m r eta A k
    (labelEndpoint N m g.1, labelEndpoint N m g.2.1, labelEndpoint N m g.2.2) =
      OriginalWWholeRealAssignment.endpointFactors N
        (logPrimeMeshHi 0 1 m k.2.1) (logPrimeMeshHi 0 1 m k.2.2)
        (U1011OriginalFifteenNativeGridCells.gridBox n k.1) eta A := by
  have hweight : ∀ i : Fin 4 ⊕ Fin r,
      labelUpper N m (occurrenceLabels k.2.1 k.2.2 i) =
        SelectedRealWholeAtomGroups.weight N
          (logPrimeMeshHi 0 1 m k.2.1) (logPrimeMeshHi 0 1 m k.2.2) i := by
    intro i
    cases i <;> rfl
  rw [labelGroups_of_W eta A k hW]
  simp only [labelEndpoint, List.map_map, Function.comp_def, hweight,
    OriginalWWholeRealAssignment.groups, OriginalWWholeRealAssignment.endpointFactors,
    Part3.ActualWThreeCapacityRun.wp]

/-- W capacities for the actual normalized marked Cartesian words.
The SOURCE scalar and coefficients are the G source objects consumed by
the independent H signed assembly; only their numerical licence is paid.
This is at original N scale and is not a local-scale or SW theorem. -/
theorem actual_computed_W_beta_monomials {n N m r : ℕ} (hN : 1 < N)
    {eta : ℚ} (heta : 0 < eta) {rho epsilon : ℝ} {M : Set (ℝ × ℝ)}
    (k : Key n m r) (h : WholeCell eta rho M k.1 k.2.1 k.2.2)
    (hW : U1011OriginalSixteenStaticNativeCompiler.boxPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n k.1) = wPolicy)
    (hmesh : logPrimeMeshStep 0 1 m ≤ endpointPadding wPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n k.1) eta)
    (hwidth : ActualInnerWholeEndpointCapacity.roughWidth r m ≤ (delta wPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n k.1) eta : ℝ))
    (A : ℝ) (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    {kappa : ℝ} (hk0 : 0 ≤ kappa)
    (hk : kappa ≤ (delta wPolicy (U1011OriginalFifteenNativeGridCells.gridBox n k.1) eta : ℝ) / 64)
    (hepsilon : epsilon ≤ (delta wPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n k.1) eta : ℝ) / 4) :
    let g := labelGroups n N m r eta A k
    let a := labelEndpoint N m g.1
    let b := labelEndpoint N m g.2.1
    let C := (N : ℝ) ^ epsilon * labelEndpoint N m g.2.2
    let d : ℝ := (delta wPolicy (U1011OriginalFifteenNativeGridCells.gridBox n k.1) eta : ℝ)
    a ≤ A ∧ A ^ 2 * b * C ^ 2 ≤ (N : ℝ) ^ (1 - 3 * d) ∧
      (N : ℝ) ^ (7 * (1 + 3 * kappa) / 32) * A * a * b ^ 5 * C ^ 2 ≤
        (N : ℝ) ^ (2 - 3 * d) ∧
      (A * C / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * C ^ 2 ≤
        (N : ℝ) ^ (2 - 4 * d) := by
  have hp := computed_W_endpoint_products eta A k hW
  have h1 := congrArg (fun t : ℝ × ℝ × ℝ => t.1) hp
  have h2 := congrArg (fun t : ℝ × ℝ × ℝ => t.2.1) hp
  have h3 := congrArg (fun t : ℝ × ℝ × ℝ => t.2.2) hp
  dsimp only at h1 h2 h3 ⊢
  rw [h1, h2, h3]
  exact actual_W_cell_beta_endpoint_monomials hN heta h hW hmesh hwidth
    A hA hAupper hk0 hk hepsilon

end
end ImbalancedChen.P5Z.ActualComputedWNormalizedLicence
