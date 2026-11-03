import ImbalancedChen.P2GammaJointComplementBlockNorms

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.

Exact original outside-pair source as a family of ACTUAL head-interval
rectangles, with the joint complementary coefficients already constructed.
Unoccupied pairs have an empty head key because their original row is
proved zero. No arithmetic mask is added to a prime row and no differing
head intervals are declared identical. The same original upper rho and
the exact q-coprime mean are preserved before taking any norm.

This constructs the correct family for a future family conductor estimate.
It does not sum a per-block C*x/log^A error without paying the block family.
-/

namespace ImbalancedChen.P2GammaJointSameRhoBlockSource
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2GammaJointRetainedComplement P2GammaJointComplementBlockNorms
open P2GammaRetainedSameRhoRows P2GammaRetainedCompleteScale
open P2GammaRetainedPhysicalRows P2GammaRetainedActualNorms
open P2GammaRetainedInteriorGeometry P2GammaOriginalCartesianMask
open P2OriginalGammaUpperLowRankConsumer P2OriginalU5WholeGroupCapacity
open P2GammaSmallConductorIntervalBridge P2GammaExactConductorRegrouping
open P2GammaConvolutionLargeConductor P2GammaPrimeCharacterSW
open P2GammaSmoothLogGrid P2GammaChosenLogGridBudget
open P4BPositiveUpperLowRankClass
open P5OriginalU5CausalFinite (pairSupport)

/-- A concrete key, not a hypothesis identifying arbitrary head windows.
The empty key is harmless: every corresponding original row is zero. -/
def headKey (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l : ℕ)
    (t : ℕ × ℕ) : Finset ℕ :=
  if Occupied N t c cs H δ j l then actualPrimeCarrier N t c δ j else ∅

def blockSource (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l : ℕ)
    (sigma : (ℕ × ℕ) → ℂ) (q : ℕ) : ℂ :=
  ∑ a ∈ blockKeys N (headKey N c cs H δ j l),
    naturalRectangleDiscrepancy a (jointRetainedProducts N c cs H δ j l)
      (primeHeadCoefficient N δ j)
      (blockBeta N c cs H δ j l (headKey N c cs H δ j l) sigma a) N q

/-- Reverse the two finite natural coordinates without changing their
product or the AP-minus-q-coprime-mean kernel. -/
private theorem rectangle_eq_beta_test (S T : Finset ℕ) (a b : ℕ → ℂ)
    (N q : ℕ) :
    naturalRectangleDiscrepancy S T a b N q =
      ∑ m ∈ T,b m * ∑ p ∈ S,a p * (gammaKernel N q (p*m) : ℂ) := by
  unfold naturalRectangleDiscrepancy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Existing exact dictionaries are invoked on the literal Cartesian row.
No positivity or coprimality of q is needed before the character conversion. -/
private theorem cartesian_eq_natural {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (ht : t ∈ pairSupport N) {H δ : ℝ} (hδ : 0 < δ)
    (hwidth : 2*δ ≤ Real.log 2) (j l : ℕ) (hM : 1 ≤ lower δ j)
    (ho : Occupied N t c cs H δ j l) (q : ℕ) :
    cartesianRow N t c cs H δ j l q =
      naturalRectangleDiscrepancy (actualPrimeCarrier N t c δ j)
        (retainedComplementSupport N t c cs H δ j l)
        (primeHeadCoefficient N δ j) (retainedBeta N t c cs H δ j l) N q := by
  have h := original_retained_row_eq_actual_rows ht hδ hwidth j l hM ho
    (fun m => (gammaKernel N q m : ℂ))
  rw [original_retained_row_eq_cartesian ht c cs hδ j l] at h
  simpa only [cartesianRow,naturalRectangleDiscrepancy,Nat.mul_comm] using h

/-- Exact joint finite-source regrouping. The old pair is no longer an
external error index; it is inside the actual complementary coefficient. -/
theorem original_joint_row_eq_blocks (N c : ℕ) (cs : List ℕ) (H : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) (j l : ℕ)
    (hM : ∀ t ∈ pairSupport N,Occupied N t c cs H δ j l → 1 ≤ lower δ j)
    (sigma : (ℕ × ℕ) → ℂ) (q : ℕ) :
    (∑ t ∈ pairSupport N,sigma t * cartesianRow N t c cs H δ j l q) =
      blockSource N c cs H δ j l sigma q := by
  calc
    _ = ∑ t ∈ pairSupport N,sigma t *
        naturalRectangleDiscrepancy (headKey N c cs H δ j l t)
          (retainedComplementSupport N t c cs H δ j l)
          (primeHeadCoefficient N δ j) (retainedBeta N t c cs H δ j l) N q := by
      apply Finset.sum_congr rfl
      intro t ht
      by_cases ho : Occupied N t c cs H δ j l
      · rw [headKey,if_pos ho,cartesian_eq_natural ht hδ hwidth j l (hM t ht ho) ho q]
      · simp only [headKey,if_neg ho,cartesianRow_eq_zero ho q,
          naturalRectangleDiscrepancy,Finset.sum_empty,mul_zero]
    _ = _ := by
      simp only [blockSource,rectangle_eq_beta_test]
      exact (block_test_eq_pair N c cs H δ j l (headKey N c cs H δ j l) sigma
        (fun a m => ∑ p ∈ a,primeHeadCoefficient N δ j p *
          (gammaKernel N q (p*m) : ℂ))).symm

theorem headKey_subset_cap {N c : ℕ} {cs : List ℕ} {H δ : ℝ}
    (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) (j l : ℕ)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) :
    headKey N c cs H δ j l t ⊆ Finset.Icc 1 (Nat.floor (2*lower δ j)) := by
  by_cases ho : Occupied N t c cs H δ j l
  · rw [headKey,if_pos ho]
    exact (actual_rows_supported ht hδ hwidth j l ho).1
  · simp only [headKey,if_neg ho,Finset.empty_subset]

def blockCharacterSource (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l : ℕ)
    (sigma : (ℕ × ℕ) → ℂ) (q : ℕ) : ℂ :=
  ∑ a ∈ blockKeys N (headKey N c cs H δ j l),
    rectangleCharacterDiscrepancy
      (paddedRow a (primeHeadCoefficient N δ j))
      (paddedRow (jointRetainedProducts N c cs H δ j l)
        (blockBeta N c cs H δ j l (headKey N c cs H δ j l) sigma a))
      0 0 (Nat.floor (2*lower δ j)) (Nat.floor (2*lower δ l)) q
      ((N : ZMod q)⁻¹)

/-- Principal cancellation uses exactly the original q-coprime mean,
with the actual moving target residue and both original coefficient rows. -/
theorem blockSource_eq_character (N c : ℕ) (cs : List ℕ) (H : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) (j l : ℕ)
    (sigma : (ℕ × ℕ) → ℂ) {q : ℕ} (hq : 0 < q) (hNq : N.Coprime q) :
    blockSource N c cs H δ j l sigma q =
      blockCharacterSource N c cs H δ j l sigma q := by
  unfold blockSource blockCharacterSource
  apply Finset.sum_congr rfl
  intro a ha
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp ha
  exact naturalRectangleDiscrepancy_eq_character _ _ _ _ _ _ N q
    (headKey_subset_cap hδ hwidth j l ht)
    (jointRetainedProducts_subset_cap N c cs H hδ hwidth j l) hq hNq

/-- The original same integer coefficient is kept throughout. Coprimality
and positive modulus are consequences of ACTIVITY, not new caller licences.
No bound on the number of blocks is used to infer a distribution estimate. -/
theorem signed_original_eq_block_char {N : ℕ} (hN : 1 ≤ N)
    (c : ℕ) (cs : List ℕ) (H : ℝ) {δ nu : ℝ}
    (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) (hnu : 0 ≤ nu)
    (epsilon : ℝ) (j l : ℕ)
    (hM : ∀ t ∈ pairSupport N,Occupied N t c cs H δ j l → 1 ≤ lower δ j)
    (retain : List ℕ → Bool) (cap : ℕ) (Q : Finset ℕ)
    (sigma : (ℕ × ℕ) → ℂ) :
    (∑ q ∈ Q,(upperRho N nu epsilon retain cap q : ℂ) *
      ∑ t ∈ pairSupport N,sigma t * cartesianRow N t c cs H δ j l q) =
      ∑ q ∈ Q,(upperRho N nu epsilon retain cap q : ℂ) *
        blockCharacterSource N c cs H δ j l sigma q := by
  apply Finset.sum_congr rfl
  intro q hqQ
  by_cases hr : upperRho N nu epsilon retain cap q = 0
  · simp only [hr,Complex.ofReal_zero,zero_mul]
  · have hs := attached_rank_two_support (fun _ => retain) (fun _ => cap)
      (mul_nonneg hnu (by norm_num : (0 : ℝ) ≤ 19/96)) hN hr
    rw [original_joint_row_eq_blocks N c cs H hδ hwidth j l hM sigma q,
      blockSource_eq_character N c cs H hδ hwidth j l sigma hs.1 hs.2.2.1.symm]

/-- For the actual chosen grid the remaining row-length premise is
supplied by the existing complete-scale theorem at ONE original-N threshold,
before every pair, word, chart, selector and later actual coefficient. -/
theorem eventually_chosen_signed_block_source (B : ℕ) (hB : 0 < B)
    (kappa : ℝ) (hk : kappa < 1) :
    ∀ᶠ N : ℕ in atTop,∀ c : ℕ,∀ cs : List ℕ,∀ j l : ℕ,
      ∀ nu : ℝ,0 ≤ nu → ∀ epsilon : ℝ,
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (Q : Finset ℕ)
        (sigma : (ℕ × ℕ) → ℂ),
      (∑ q ∈ Q,(upperRho N nu epsilon retain cap q : ℂ) *
        ∑ t ∈ pairSupport N,sigma t *
          cartesianRow N t c cs (2*(N : ℝ)^(1-kappa))
            (boundaryLogMesh B N) j l q) =
      ∑ q ∈ Q,(upperRho N nu epsilon retain cap q : ℂ) *
        blockCharacterSource N c cs (2*(N : ℝ)^(1-kappa))
          (boundaryLogMesh B N) j l sigma q := by
  obtain ⟨T,hT,hscale⟩ := exists_trim_occupied_scale_threshold kappa hk
  filter_upwards [eventually_ge_atTop (Nat.ceil T),eventually_ge_atTop (2 : ℕ),
    eventually_chosen_mesh_factor_two hB] with N hNT hN hm
  intro c cs j l nu hnu epsilon retain cap Q sigma
  have hTN : T ≤ (N : ℝ) := (Nat.le_ceil T).trans (by exact_mod_cast hNT)
  apply signed_original_eq_block_char (by omega : 1 ≤ N) c cs _
    hm.2.1 hm.2.2 hnu epsilon j l _ retain cap Q sigma
  intro t ht ho
  exact (hscale N hTN t ht c cs _ hm.2.1 hm.2.2 j l ho).2.1

/-- The norm supplier is instantiated on the very same concrete head key
used by the exact original-source and character identities above. -/
theorem actual_head_block_beta_norms (N c : ℕ) (cs : List ℕ) (H : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) (j l : ℕ)
    (hV : 1 ≤ lower δ l) (sigma : (ℕ × ℕ) → ℂ) {height : ℝ}
    (hh : 0 ≤ height) (hs : ∀ t ∈ pairSupport N,‖sigma t‖ ≤ height) :
    let key := headKey N c cs H δ j l
    let S := jointRetainedProducts N c cs H δ j l
    (∑ a ∈ blockKeys N key,rowMass S (blockBeta N c cs H δ j l key sigma a)) ≤
        height*(2*lower δ l)*(1+Real.log (2*lower δ l))^(cs.length+2) ∧
    (∑ a ∈ blockKeys N key,
      rowEnergy (paddedRow S (blockBeta N c cs H δ j l key sigma a))
        0 (Nat.floor (2*lower δ l))) ≤
        height^2*(2*lower δ l)*(1+Real.log (2*lower δ l))^((cs.length+3)^2-1) :=
  actual_block_raw_norms N c cs H hδ hwidth j l hV
    (headKey N c cs H δ j l) sigma hh hs

/-- Distinct original head intervals may overlap. This exact remaining
quantity is NOT claimed logarithmic or bounded by one. -/
def headMultiplicity (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l p : ℕ) : ℕ :=
  ((blockKeys N (headKey N c cs H δ j l)).filter (fun a => p ∈ a)).card

/-- The precise head-side cost left for a family conductor theorem.
Joint beta norms alone do not remove this overlap from Cauchy/large sieve. -/
theorem total_head_energy_eq_overlap (N c : ℕ) (cs : List ℕ) (H : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) (j l : ℕ) :
    (∑ a ∈ blockKeys N (headKey N c cs H δ j l),
      rowEnergy (paddedRow a (primeHeadCoefficient N δ j))
        0 (Nat.floor (2*lower δ j))) =
      ∑ p ∈ Finset.Icc 1 (Nat.floor (2*lower δ j)),
        (headMultiplicity N c cs H δ j l p : ℝ) *
          ‖primeHeadCoefficient N δ j p‖^2 := by
  let I := Finset.Icc 1 (Nat.floor (2*lower δ j))
  let K := blockKeys N (headKey N c cs H δ j l)
  have hsub : ∀ a ∈ K,a ⊆ I := by
    intro a ha
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp ha
    exact headKey_subset_cap hδ hwidth j l ht
  calc
    _ = ∑ a ∈ K,∑ p ∈ I,
        if p ∈ a then ‖primeHeadCoefficient N δ j p‖^2 else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [paddedRow_energy _ _ _ (hsub a ha)]
      have hf : I.filter (fun p => p ∈ a) = a := by
        ext p
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2,fun h => ⟨hsub a ha h,h⟩⟩
      rw [← Finset.sum_filter,hf]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul,headMultiplicity,K]

end
end ImbalancedChen.P2GammaJointSameRhoBlockSource
