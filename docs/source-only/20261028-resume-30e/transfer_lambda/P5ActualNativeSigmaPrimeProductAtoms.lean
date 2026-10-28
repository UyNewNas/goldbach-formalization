import ImbalancedChen.P5ZU1011ActualSigmaBoxAtomAssembly
import ImbalancedChen.Part3DistributionTargets

/-!
SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
This consumes the production FULL16 STATIC near-cap coefficient sigma.
It is not a candidate lower CapPlan and not jointPresievedSigma.
The external PP test word u remains independent of the physical four
prefix primes and their original residual divisor d in physicalTest.
-/
namespace ImbalancedChen.P5Z.ActualNativeSigmaPrimeProductAtoms

noncomputable section
open Classical Set
open scoped BigOperators
open U11Integral U11Canonical
open U1011OriginalSixteenArithmeticProducts U1011OriginalSixteenNativeHarmonic
open U1011OriginalFifteenNativeGridCells U1011OriginalSixteenAffineState
open U1011OriginalSixteenJointNearCapCompiler
open U1011OriginalSixteenJointNearCapModulusConvolution
open U1011OriginalSixteenStaticNativeCompiler
  (boxPolicy boxPolicy_certificate ownerBox selectedPolicy tupleTag)
open U1011OriginalMaskSmoothBoxRealization
open U1011FourDimensionalSmoothBoxAtoms U1011AffineSmoothBoxCover
open U1011NativeMaskPhysicalBoxAtoms U1011NativeUnmaskedLowBoxAtoms
open U1011ActualSigmaBoxAtomAssembly

-- Linearity is in the COEFFICIENT, with the original count/mean bracket
-- unchanged. This is not a geometric licence for arbitrary test weights.
theorem signedError_coefficient_sum {ι : Type*} [Fintype ι]
    (r P N : ℕ) (Q : Finset ℕ)
    (rho : ι → ℕ → ℝ) (W : (Fin r → Fin (P+1)) → ℝ) :
    Part3.primeProductSignedError r P N Q (fun q => ∑ i : ι, rho i q) W =
      ∑ i : ι, Part3.primeProductSignedError r P N Q (rho i) W := by
  unfold Part3.primeProductSignedError
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

theorem signedError_coefficient_add (r P N : ℕ) (Q : Finset ℕ)
    (rho tau : ℕ → ℝ) (W : (Fin r → Fin (P+1)) → ℝ) :
    Part3.primeProductSignedError r P N Q (fun q => rho q + tau q) W =
      Part3.primeProductSignedError r P N Q rho W +
        Part3.primeProductSignedError r P N Q tau W := by
  simp only [Part3.primeProductSignedError, add_mul, Finset.sum_add_distrib]

theorem signedError_coefficient_sub (r P N : ℕ) (Q : Finset ℕ)
    (rho tau : ℕ → ℝ) (W : (Fin r → Fin (P+1)) → ℝ) :
    Part3.primeProductSignedError r P N Q (fun q => rho q - tau q) W =
      Part3.primeProductSignedError r P N Q rho W -
        Part3.primeProductSignedError r P N Q tau W := by
  simp only [Part3.primeProductSignedError, sub_mul, Finset.sum_sub_distrib]

theorem signedError_coefficient_finset_sum {ι : Type*} (I : Finset ι)
    (r P N : ℕ) (Q : Finset ℕ) (rho : ι → ℕ → ℝ)
    (W : (Fin r → Fin (P+1)) → ℝ) :
    Part3.primeProductSignedError r P N Q (fun q => ∑ i ∈ I, rho i q) W =
      ∑ i ∈ I, Part3.primeProductSignedError r P N Q (rho i) W := by
  unfold Part3.primeProductSignedError
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

theorem signedError_coefficient_if (b : Prop) [Decidable b]
    (r P N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (W : (Fin r → Fin (P+1)) → ℝ) :
    Part3.primeProductSignedError r P N Q (fun q => if b then 0 else rho q) W =
      if b then 0 else Part3.primeProductSignedError r P N Q rho W := by
  by_cases hb : b
  · simp [hb, Part3.primeProductSignedError]
  · simp only [if_neg hb]

-- Every ACTUAL nonfallback source mark reads one original native owner,
-- and that owner supplies the TRUE whole-box branch certificate.
theorem actual_mark_native_owner_licence {m N : ℕ} (hN : 1 < N)
    (eta : ℚ) (E : ℕ × ℕ → Prop) (a : Mark)
    (ha : a ∈ marks m N eta E) :
    ∃ k : Grid m,
      coordinates N a.1 ∈ cell m k ∧
      U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) ≠ 0 ∧
      selectedPolicy m N a.1 = boxPolicy (gridBox m k) ∧
      U1011OriginalSixteenPolicyBank.BoxCertificates.wholeBoxEligibleTest
        (boxPolicy (gridBox m k)) (gridBox m k) = true ∧
      support m N eta a.1 = rowSupport (boxPolicy (gridBox m k)) (gridBox m k) eta N ∧
      (∀ d, coefficient m N eta a.1 d =
        rowCoefficient (boxPolicy (gridBox m k)) (gridBox m k) eta N d) := by
  obtain ⟨ht, hd⟩ := Finset.mem_sigma.mp ha
  obtain ⟨hjoint, htag⟩ := Finset.mem_filter.mp ht
  have hv := U1011OriginalFifteenJointNativeRows.joint_coordinates_cube hN hjoint
  let k := owner m (coordinates N a.1)
  have hcell : coordinates N a.1 ∈ cell m k := owner_mem m hv
  have hactive : U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) ≠ 0 := by
    simpa only [tupleTag, ownerBox, k] using htag
  have hcert := (boxPolicy_certificate (gridBox m k) hactive).2
  obtain ⟨hsupp, hcoeff⟩ := compiled_static_on_cell m N eta hcell
  refine ⟨k, hcell, hactive, ?_, hcert, hsupp, hcoeff⟩
  simp only [selectedPolicy, ownerBox, k]

-- This is the independently defined source coefficient's actual exact
-- state/cell cover, lifted to the SAME signed PP count and exact mean.
theorem actual_sigma_primeProduct_physical_tests {N : ℕ} (hN : 1 < N)
    (S : Finset Row) (m : ℕ) (eta : ℚ) (r P : ℕ) (Q : Finset ℕ)
    (W : (Fin r → Fin (P+1)) → ℝ) :
    Part3.primeProductSignedError r P N Q (sigma m N eta (actualE S N)) W =
      ∑ k : Grid m,
        if U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) = 0 then 0 else
          ∑ s : State,
            Part3.primeProductSignedError r P N Q
              (physicalTest m N eta k (regionIndicator (lowGates s m k))) W +
            Part3.primeProductSignedError r P N Q
              (physicalTest m N eta k (retainedIndicator S s m k)) W := by
  have hfun : sigma m N eta (actualE S N) = fun q =>
      ∑ k : Grid m,
        if U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) = 0 then 0 else
          ∑ s : State,
            physicalTest m N eta k (regionIndicator (lowGates s m k)) q +
            physicalTest m N eta k (retainedIndicator S s m k) q := by
    funext q
    exact actual_sigma_eq_physical_tests hN S m eta q
  rw [hfun, signedError_coefficient_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [signedError_coefficient_if]
  split_ifs
  · rfl
  · rw [signedError_coefficient_sum]
    apply Finset.sum_congr rfl
    intro s hs
    exact signedError_coefficient_add r P N Q _ _ W

-- The finite atom inventory is extracted from the ORIGINAL low/base/
-- removed-row box sets. Signs and duplicate occurrences are retained.
-- All physical atoms here have their genuine four original prefix slots;
-- no residual rough rank is reinterpreted as the external test rank r.
theorem smooth_sigma_primeProduct_box_atoms
    (inner : Bool) (S : Finset Row) (m N : ℕ) (eta : ℚ) (n : ℕ) (δ : ℝ)
    (r P : ℕ) (Q : Finset ℕ) (W : (Fin r → Fin (P+1)) → ℝ) :
    Part3.primeProductSignedError r P N Q (smoothSigma inner S m N eta n δ) W =
      ∑ k : Grid m,
        if U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) = 0 then 0 else
          ∑ s : State,
            (∑ j ∈ (if inner then innerCells (lowGates s m k) n
                else outerCells (lowGates s m k) n),
              Part3.primeProductSignedError r P N Q
                (physicalBoxAtom inner δ n j m N eta k) W) +
            ((∑ j ∈ (if inner then innerCells (baseGates s m k) n
                else outerCells (baseGates s m k) n),
              Part3.primeProductSignedError r P N Q
                (physicalBoxAtom inner δ n j m N eta k) W) -
              ∑ row ∈ S, ∑ j ∈ (if inner then outerCells (removedGates s m k row) n
                  else innerCells (removedGates s m k row) n),
                Part3.primeProductSignedError r P N Q
                  (physicalBoxAtom (!inner) δ n j m N eta k) W) := by
  unfold smoothSigma
  rw [signedError_coefficient_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [signedError_coefficient_if]
  split_ifs
  · rfl
  · rw [signedError_coefficient_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [signedError_coefficient_add]
    have hl : physicalTest m N eta k (lowSmoothCover inner s m k n δ) = fun q =>
        ∑ j ∈ (if inner then innerCells (lowGates s m k) n
          else outerCells (lowGates s m k) n), physicalBoxAtom inner δ n j m N eta k q := by
      funext q
      exact low_smooth_physical_atoms inner s m N eta k n δ q
    have hh : physicalTest m N eta k (signedSmoothCover inner S s m k n δ) = fun q =>
        (∑ j ∈ (if inner then innerCells (baseGates s m k) n
          else outerCells (baseGates s m k) n), physicalBoxAtom inner δ n j m N eta k q) -
        ∑ row ∈ S, ∑ j ∈ (if inner then outerCells (removedGates s m k row) n
          else innerCells (removedGates s m k row) n), physicalBoxAtom (!inner) δ n j m N eta k q := by
      funext q
      exact signed_smooth_physical_atoms inner S s m N eta k n δ q
    rw [hl, hh, signedError_coefficient_finset_sum, signedError_coefficient_sub,
      signedError_coefficient_finset_sum, signedError_coefficient_finset_sum]
    have hRows :
        (∑ row ∈ S, Part3.primeProductSignedError r P N Q
          (fun q => ∑ j ∈ (if inner then outerCells (removedGates s m k row) n
            else innerCells (removedGates s m k row) n),
              physicalBoxAtom (!inner) δ n j m N eta k q) W) =
        ∑ row ∈ S, ∑ j ∈ (if inner then outerCells (removedGates s m k row) n
          else innerCells (removedGates s m k row) n),
            Part3.primeProductSignedError r P N Q
              (physicalBoxAtom (!inner) δ n j m N eta k) W := by
      apply Finset.sum_congr rfl
      intro row hrow
      exact signedError_coefficient_finset_sum _ r P N Q _ W
    rw [hRows]

def reserveSigma (inner : Bool) (S : Finset Row) (m N : ℕ) (eta : ℚ)
    (n : ℕ) (δ : ℝ) (q : ℕ) : ℝ :=
  ∑ k : Grid m,
    if U1011OriginalSixteenStaticCellWinner.chosenTag (gridBox m k) = 0 then 0 else
      ∑ s : State,
        physicalTest m N eta k
          (fun v => lowSmoothCover inner s m k n δ v - regionIndicator (lowGates s m k) v) q +
        physicalTest m N eta k
          (fun v => signedSmoothCover inner S s m k n δ v - retainedIndicator S s m k v) q

theorem actual_sigma_smooth_minus_reserve {N : ℕ} (hN : 1 < N)
    (inner : Bool) (S : Finset Row) (m : ℕ) (eta : ℚ) (n : ℕ) (δ : ℝ) :
    sigma m N eta (actualE S N) =
      fun q => smoothSigma inner S m N eta n δ q - reserveSigma inner S m N eta n δ q := by
  funext q
  have h := actual_sigma_smooth_reserve_identity hN inner S m eta n δ q
  change _ = smoothSigma inner S m N eta n δ q - reserveSigma inner S m N eta n δ q
  change smoothSigma inner S m N eta n δ q - sigma m N eta (actualE S N) q =
    reserveSigma inner S m N eta n δ q at h
  linarith

theorem actual_sigma_primeProduct_smooth_reserve {N : ℕ} (hN : 1 < N)
    (inner : Bool) (S : Finset Row) (m : ℕ) (eta : ℚ) (n : ℕ) (δ : ℝ)
    (r P : ℕ) (Q : Finset ℕ) (W : (Fin r → Fin (P+1)) → ℝ) :
    Part3.primeProductSignedError r P N Q (sigma m N eta (actualE S N)) W =
      Part3.primeProductSignedError r P N Q (smoothSigma inner S m N eta n δ) W -
        Part3.primeProductSignedError r P N Q (reserveSigma inner S m N eta n δ) W := by
  rw [actual_sigma_smooth_minus_reserve hN inner S m eta n δ,
    signedError_coefficient_sub]

-- Literal original 17572-row mask, not an arbitrary mask renamed to it.
theorem actual17572_primeProduct_smooth_reserve {N : ℕ} (hN : 1 < N)
    (inner : Bool) (m : ℕ) (eta : ℚ) (n : ℕ) (δ : ℝ)
    (r P : ℕ) (Q : Finset ℕ) (W : (Fin r → Fin (P+1)) → ℝ) :
    Part3.primeProductSignedError r P N Q
      (sigma m N eta (Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ))) W =
      Part3.primeProductSignedError r P N Q
        (smoothSigma inner Finset.univ m N eta n δ) W -
      Part3.primeProductSignedError r P N Q
        (reserveSigma inner Finset.univ m N eta n δ) W := by
  simpa only [actualE, U1011OriginalPairedFixedMaskHarmonic.outerUnion_all,
    U1011OriginalPairedRowPrimeTests.nativeMask_actual_adopted] using
      actual_sigma_primeProduct_smooth_reserve hN inner (Finset.univ : Finset Row)
        m eta n δ r P Q W

end
end ImbalancedChen.P5Z.ActualNativeSigmaPrimeProductAtoms
