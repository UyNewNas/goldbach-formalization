import ImbalancedChen.P5ActualComputedWLocalScale

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact half-open dyadic restrictions of the SAME normalized H coefficient;
the dyadic LOWER lengths pay no factor of two in the Medium inequalities.
The original residual-only factorial, all marked slots, and the entire
common small beta are retained. The final equality uses the independently
defined original labelled-prime-product count-minus-coprime-mean test.
There is no prime-product estimate, source-class transfer, or SW premise.
-/
namespace ImbalancedChen.P5Z.ActualComputedWDyadicConsumer
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen ImbalancedChen.Part3
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenNearCapBoxProfiles
open PresievedRoughGateMeshReserve
open All16FineMeshGateScalar
open All16MarkedCommonFineSource All16MarkedFineScalarBudget
open All16MarkedCommonFineAssembly All16ComputedWholeWordAssignment
open ActualInnerPerLabelGamma SameWholeAssignmentPerLabel
open ActualComputedWNormalizedLicence ActualComputedWLocalScale
open U1011OriginalFifteenMediumNumericGates
open UniqueHalfOpenDyadicFactors

def coefficients (n N m r : ℕ) (eta : ℚ) (rho epsilon A : ℝ) (k : Key n m r) :
    (ℕ → ℝ) × (ℕ → ℝ) × (ℕ → ℝ) :=
  let g := labelGroups n N m r eta A k
  (gamma (commonAlphabet N m) g.1, gamma (commonAlphabet N m) g.2.1,
    attachedGamma (commonAlphabet N m) g.2.2 N (cellCap n N eta k.1) r
      ((N : ℝ) ^ rho) ((N : ℝ) ^ epsilon))

def endpoints (n N m r : ℕ) (eta : ℚ) (epsilon A : ℝ) (k : Key n m r) : ℝ × ℝ × ℝ :=
  let g := labelGroups n N m r eta A k
  (labelEndpoint N m g.1, labelEndpoint N m g.2.1,
    (N : ℝ) ^ epsilon * labelEndpoint N m g.2.2)

/-- Product of all three endpoints includes all FOUR marked slots, every
residual occurrence, and the full small-prime level. No prefix is removed
from the length budget when the residual-only factorial is used. -/
theorem full_marked_beta_endpoint_product (n N m r : ℕ) (eta : ℚ) (epsilon A : ℝ)
    (k : Key n m r) :
    let Q := endpoints n N m r eta epsilon A k
    Q.1 * Q.2.1 * Q.2.2 =
      (N : ℝ) ^ epsilon * labelEndpoint N m (fullWord k.2.1 k.2.2) := by
  let g := labelGroups n N m r eta A k
  have hp := (labelGroups_partition n N m r eta A k).map (labelUpper N m)
  have he := hp.prod_eq
  simp only [List.map_append, List.prod_append] at he
  have he' : labelEndpoint N m g.1 * labelEndpoint N m g.2.1 * labelEndpoint N m g.2.2 =
      labelEndpoint N m (fullWord k.2.1 k.2.2) := by
    simpa only [labelEndpoint, mul_assoc] using he
  change labelEndpoint N m g.1 * labelEndpoint N m g.2.1 *
      ((N : ℝ) ^ epsilon * labelEndpoint N m g.2.2) = _
  calc
    _ = (N : ℝ) ^ epsilon *
        (labelEndpoint N m g.1 * labelEndpoint N m g.2.1 * labelEndpoint N m g.2.2) := by ring
    _ = _ := congrArg ((N : ℝ) ^ epsilon * ·) he'

/-- The support theorem is for active coefficients, including beta. It
does not falsely bound every member of the broad beta divisor carrier. -/
theorem active_support {n N m r : ℕ} (hN : 1 < N) {eta : ℚ} {rho epsilon A : ℝ}
    {M : Set (ℝ × ℝ)} {k : Key n m r} (hk : k ∈ certifiedKeys n m r eta rho M) :
    let f := coefficients n N m r eta rho epsilon A k
    let Q := endpoints n N m r eta epsilon A k
    (∀ q, f.1 q ≠ 0 → 0 < q ∧ (q : ℝ) ≤ Q.1) ∧
    (∀ q, f.2.1 q ≠ 0 → 0 < q ∧ (q : ℝ) ≤ Q.2.1) ∧
    (∀ q, f.2.2 q ≠ 0 → 0 < q ∧ (q : ℝ) ≤ Q.2.2) := by
  have h := (Finset.mem_filter.mp hk).2
  exact actual_computed_active_support hN k h.1 h.2 A

/-- Every dyadic piece is an EXACT function identity on all integers.
The indices depend on endpoint data, never on arithmetic error signs. -/
theorem dyadic_reconstruct {n N m r : ℕ} (hN : 1 < N) {eta : ℚ} {rho epsilon A : ℝ}
    {M : Set (ℝ × ℝ)} {k : Key n m r} (hk : k ∈ certifiedKeys n m r eta rho M) (q : ℕ) :
    let f := coefficients n N m r eta rho epsilon A k
    let Q := endpoints n N m r eta epsilon A k
    (∑ i ∈ indices Q.1, piece f.1 i q) = f.1 q ∧
    (∑ i ∈ indices Q.2.1, piece f.2.1 i q) = f.2.1 q ∧
    (∑ i ∈ indices Q.2.2, piece f.2.2 i q) = f.2.2 q := by
  let f := coefficients n N m r eta rho epsilon A k
  let Q := endpoints n N m r eta epsilon A k
  have hs := active_support (epsilon := epsilon) (A := A) hN hk
  have zero_of_support (g : ℕ → ℝ) (B : ℝ)
      (h : ∀ q, g q ≠ 0 → 0 < q ∧ (q : ℝ) ≤ B) : g 0 = 0 := by
    by_contra hn
    exact (Nat.lt_irrefl 0) (h 0 hn).1
  exact ⟨reconstruct f.1 Q.1 (zero_of_support _ _ hs.1) (fun q hq => (hs.1 q hq).2) q,
    reconstruct f.2.1 Q.2.1 (zero_of_support _ _ hs.2.1) (fun q hq => (hs.2.1 q hq).2) q,
    reconstruct f.2.2 Q.2.2 (zero_of_support _ _ hs.2.2) (fun q hq => (hs.2.2 q hq).2) q⟩

/-- A supported dyadic block inherits the strict numerical gates, its
actual carrier, and its one-bound from the literal original sequences.
The numerical input is the result of the preceding local-scale theorem. -/
theorem active_dyadic_licence {n N m r : ℕ} (hN : 1 < N) {eta : ℚ} {rho epsilon A x U s : ℝ}
    {M : Set (ℝ × ℝ)} {k : Key n m r} (hk : k ∈ certifiedKeys n m r eta rho M)
    (hU : 0 ≤ U)
    (hg : let Q := endpoints n N m r eta epsilon A k
      NumericGates N x U Q.1 Q.2.1 Q.2.2 s)
    {i1 i2 i3 q1 q2 q3 : ℕ}
    (h1 : piece (coefficients n N m r eta rho epsilon A k).1 i1 q1 ≠ 0)
    (h2 : piece (coefficients n N m r eta rho epsilon A k).2.1 i2 q2 ≠ 0)
    (h3 : piece (coefficients n N m r eta rho epsilon A k).2.2 i3 q3 ≠ 0) :
    NumericGates N x U (length i1) (length i2) (length i3) s ∧
    q1 ∈ factorCarrier (length i1) ∧ q2 ∈ factorCarrier (length i2) ∧
    q3 ∈ factorCarrier (length i3) ∧
    (∀ q, |piece (coefficients n N m r eta rho epsilon A k).1 i1 q| ≤ 1) ∧
    (∀ q, |piece (coefficients n N m r eta rho epsilon A k).2.1 i2 q| ≤ 1) ∧
    (∀ q, |piece (coefficients n N m r eta rho epsilon A k).2.2 i3 q| ≤ 1) := by
  have hs := active_support (epsilon := epsilon) (A := A) hN hk
  have hQ1 := active_length_le h1 (hs.1 q1 (piece_nonzero h1).1).2
  have hQ2 := active_length_le h2 (hs.2.1 q2 (piece_nonzero h2).1).2
  have hQ3 := active_length_le h3 (hs.2.2 q3 (piece_nonzero h3).1).2
  have hbounds := All16ComputedMarkedTensorBudget.computed_gamma_one_bounds
    (B := (N : ℝ) ^ epsilon) hN hk A
  exact ⟨numeric_downward hU (by linarith [length_one_le i1])
      (by linarith [length_one_le i2]) (by linarith [length_one_le i3]) hQ1 hQ2 hQ3 hg,
    piece_support h1, piece_support h2, piece_support h3,
    piece_unit _ hbounds.1 i1, piece_unit _ hbounds.2.1 i2, piece_unit _ hbounds.2.2 i3⟩

/-- Original HB tuple support supplies the complete scale used by the
SAME computed W coefficient. No local monomial or N--x relation is a
premise. The trim/support are the original outer source restrictions.
Every active lower-length dyadic modulus block inherits the four gates. -/
theorem exists_actual_HB_W_dyadic_threshold
    (n : ℕ) (eta : ℚ) (heta : 0 < eta) {C kappa kappa0 : ℝ}
    (hC : 0 < C) (hk0 : 0 < kappa) (hk : kappa ≤ sigma n eta / 200)
    (ht0 : 0 < kappa0) (ht : kappa0 < kappa / (4 * (1 + kappa))) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
    ∀ (gs : List OriginalHBCompleteProductScale.OriginalGroupTuple) (p : ℕ)
      (b v : HBRightClosedDyadicRoles.Block),
    p ∈ OriginalHBCompleteProductScale.joined gs →
    HBRightClosedDyadicRoles.Owns b p →
    HBRightClosedDyadicRoles.Owns v (OriginalHBCompleteProductScale.completeInteger gs / p) →
    (N : ℝ) ^ (1 - kappa0) ≤ (OriginalHBCompleteProductScale.completeInteger gs : ℝ) →
    (OriginalHBCompleteProductScale.completeInteger gs : ℝ) ≤ C * N →
    let x := OriginalHBCompleteProductScale.localScale b v
    let U : ℝ := ActualHBDyadicProductWindow.lower b
    x ^ (2 * zeta n eta) ≤ U → U ≤ x ^ (1 / 3 + zeta n eta / 2) →
    1 < x ∧ C⁻¹ * x ≤ N ∧ (N : ℝ) ≤ x ^ (1 + kappa) ∧
    ∀ (m r : ℕ) (rho epsilon : ℝ) (M : Set (ℝ × ℝ)) (k : Key n m r),
    k ∈ certifiedKeys n m r eta rho M →
    U1011OriginalSixteenStaticNativeCompiler.boxPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n k.1) = wPolicy →
    logPrimeMeshStep 0 1 m ≤ OriginalNearCapRealEndpointGeometry.endpointPadding wPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n k.1) eta →
    ActualInnerWholeEndpointCapacity.roughWidth r m ≤ (delta wPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n k.1) eta : ℝ) →
    epsilon ≤ (delta wPolicy
      (U1011OriginalFifteenNativeGridCells.gridBox n k.1) eta : ℝ) / 4 →
    let A := innerQuery x U (zeta n eta)
    let f := coefficients n N m r eta rho epsilon A k
    let Q := endpoints n N m r eta epsilon A k
    NumericGates N x U Q.1 Q.2.1 Q.2.2 (sigma n eta) ∧
    ∀ i1 i2 i3 q1 q2 q3 : ℕ,
      piece f.1 i1 q1 ≠ 0 → piece f.2.1 i2 q2 ≠ 0 → piece f.2.2 i3 q3 ≠ 0 →
      NumericGates N x U (length i1) (length i2) (length i3) (sigma n eta) := by
  obtain ⟨N0, hN0, hnum⟩ := exists_computed_W_medium_numeric_threshold n eta heta
    (by norm_num : (0 : ℝ) < 1 / 4) hC hk0 hk ht0 ht
  refine ⟨N0, hN0, ?_⟩
  intro N hN gs p b v hp hb hv htrim hs
  let x := OriginalHBCompleteProductScale.localScale b v
  let U : ℝ := ActualHBDyadicProductWindow.lower b
  intro hUlo hUhi
  have hw := OriginalHBCompleteProductScale.actual_trimmed_complete_scale gs hp hb hv htrim hs
  obtain ⟨hx, hlo, hhi, hUs⟩ := hnum N hN x hw.1 hw.2
  obtain ⟨hA1, hAupper, hWnum⟩ := hUs U hUlo hUhi
  refine ⟨hx, hlo, hhi, ?_⟩
  intro m r rho epsilon M k hcert hW hmesh hwidth heps
  have hg := hWnum m r rho epsilon M k (Finset.mem_filter.mp hcert).2.1 hW hmesh hwidth heps
  have hNN : 1 < N := lt_of_lt_of_le (by omega : 1 < N0) hN
  have hU : 0 ≤ U := Nat.cast_nonneg _
  refine ⟨hg, ?_⟩
  intro i1 i2 i3 q1 q2 q3 h1 h2 h3
  exact (active_dyadic_licence hNN hcert hU hg h1 h2 h3).1

/-- The scalar used in this exact source is still divided by M_res ONLY.
The four marked primes were already in the state. -/
theorem restoring_scalar_original (n N m r : ℕ) (eta : ℚ) (epsilon A : ℝ) (k : Key n m r) :
    let g := labelGroups n N m r eta A k
    All16ComputedMarkedTensorBudget.scalar n N m r eta epsilon A k =
      epsilon * (-1 : ℝ) ^ r * (multiplicity g.1 : ℝ) *
        (multiplicity g.2.1 : ℝ) * (multiplicity g.2.2 : ℝ) /
        (meshMultiplicity k.2.2 : ℝ) := by rfl

/-- Independently defined ORIGINAL prime-product discrepancy at one
physical modulus. Both terms use the same weight and exact coprime mean. -/
def primeProductModulusError (k P N : ℕ)
    (W : (Fin k → Fin (P + 1)) → ℝ) (q : ℕ) : ℝ :=
  ∑ t ∈ labelledPrimeTuples k P, W t *
    ((if Nat.ModEq q (labelledProduct t) N then (1 : ℝ) else 0) -
      (if Nat.Coprime (labelledProduct t) q then (1 : ℝ) else 0) / (Nat.totient q : ℝ))

/-- This is the existing original PP signed-error definition, not a new
analytic source declared equal to the desired output. -/
theorem primeProductSignedError_eq (k P N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (W : (Fin k → Fin (P + 1)) → ℝ) :
    primeProductSignedError k P N Q rho W = ∑ q ∈ Q, rho q * primeProductModulusError k P N W q := by
  rfl

/-- Actual SAME lower ALL16 coefficient -> PP test, including its genuine
arithmetic remainder. No assertion of PP, an upper-K coefficient, or a
bound on the unlicensed remainder is introduced. -/
theorem original_all16_PP_consumer (R n N m : ℕ) (hN : 1 < N)
    (eta : ℚ) (heta : 0 < eta) (rho epsilon : ℝ) (M : Set (ℝ × ℝ))
    (A : ∀ r, Key n m r → ℝ) (k P : ℕ) (W : (Fin k → Fin (P + 1)) → ℝ) :
    primeProductSignedError k P N
      (OriginalJointPresievedCompiler.jointSupport n N eta ((N : ℝ) ^ rho)
        (U1011OriginalPairedRowPrimeTests.nativeMask M N))
      (OriginalJointPresievedCompiler.jointPresievedSigma n N eta ((N : ℝ) ^ rho)
        ((N : ℝ) ^ epsilon) (U1011OriginalPairedRowPrimeTests.nativeMask M N)) W =
      (∑ r ∈ Finset.range (R + 1), ∑ a ∈ certifiedKeys n m r eta rho M,
        All16ComputedMarkedTensorBudget.scalar n N m r eta 1 (A r a) a *
          All16ComputedMarkedTensorBudget.tensor n N m r eta rho ((N : ℝ) ^ epsilon) (A r a) a
            (primeProductModulusError k P N W)) +
      ∑ q ∈ remainderSupport R n N m eta rho M,
        remainderRho R n N m eta rho ((N : ℝ) ^ epsilon) M q * primeProductModulusError k P N W q := by
  rw [primeProductSignedError_eq]
  exact All16ComputedMarkedTensorBudget.actual_all16_computed_tensor_plus_remainder
    R n N m hN eta heta rho ((N : ℝ) ^ epsilon) M A (primeProductModulusError k P N W)

end
end ImbalancedChen.P5Z.ActualComputedWDyadicConsumer
