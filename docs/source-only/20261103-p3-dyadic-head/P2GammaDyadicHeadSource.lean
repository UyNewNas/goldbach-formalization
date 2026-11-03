import ImbalancedChen.P2GammaDyadicHeadIntervals

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
The actual varying head intervals are replaced by an exact signed binary
prefix expansion. This changes the analytic organization, not rootQ, rho,
any mother occurrence, or any complementary label. Every scale uses
shared disjoint integer intervals. The two endpoints remain two lanes.
-/

namespace ImbalancedChen.P2GammaDyadicHeadSource
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2GammaDyadicHeadIntervals P2GammaJointSameRhoBlockSource
open P2GammaJointRetainedComplement P2GammaJointComplementBlockNorms
open P2GammaRetainedSameRhoRows P2GammaRetainedActualNorms
open P2GammaRetainedPhysicalRows P2GammaRetainedCompleteScale
open P2GammaHeadWindowDictionary P2GammaSmallConductorIntervalBridge
open P2GammaExactConductorRegrouping P2GammaOriginalCartesianMask
open P2GammaRetainedInteriorGeometry P2GammaSmoothLogGrid
open P2OriginalGammaUpperLowRankConsumer P4BPositiveUpperLowRankClass
open P2GammaPrimeCharacterSW P2GammaChosenLogGridBudget
open P5OriginalU5CausalFinite (pairSupport)

def ambientLo (δ : ℝ) (j : ℕ) : ℕ := Nat.floor (lower δ j)
def ambientHi (δ : ℝ) (j : ℕ) : ℕ := Nat.floor (2*lower δ j)

/-- A nonoccupied row gets equal endpoints at the common lower cut. -/
def endpointLo (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l : ℕ)
    (t : ℕ × ℕ) : ℕ :=
  if Occupied N t c cs H δ j l then Nat.floor (clipLo N t c (lower δ j))
  else ambientLo δ j

def endpointHi (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l : ℕ)
    (t : ℕ × ℕ) : ℕ :=
  if Occupied N t c cs H δ j l then Nat.floor (clipHi N t c (lower δ j))
  else ambientLo δ j

theorem endpoint_bounds {N c : ℕ} {cs : List ℕ} {H δ : ℝ}
    (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) (j l : ℕ)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N) :
    ambientLo δ j ≤ endpointLo N c cs H δ j l t ∧
    endpointLo N c cs H δ j l t ≤ endpointHi N c cs H δ j l t ∧
    endpointHi N c cs H δ j l t ≤ ambientHi δ j := by
  by_cases ho : Occupied N t c cs H δ j l
  · obtain ⟨hc,hs⟩ := occupied_head_geometry hδ hwidth ho
    obtain ⟨hlo,hab,hhi⟩ := source_nonempty_geometry hc hs
    simp only [endpointLo,endpointHi,if_pos ho,ambientLo,ambientHi]
    exact ⟨Nat.floor_mono hlo,Nat.floor_mono hab,Nat.floor_mono hhi⟩
  · simp only [endpointLo,endpointHi,if_neg ho,le_refl,true_and]
    exact Nat.floor_mono (by nlinarith [lower_pos δ j] : lower δ j ≤ 2*lower δ j)

theorem headKey_eq_endpoints (N c : ℕ) (cs : List ℕ) (H δ : ℝ)
    (j l : ℕ) (t : ℕ × ℕ) :
    headKey N c cs H δ j l t =
      Finset.Ioc (endpointLo N c cs H δ j l t) (endpointHi N c cs H δ j l t) := by
  by_cases ho : Occupied N t c cs H δ j l <;>
    simp [headKey,endpointLo,endpointHi,actualPrimeCarrier,primeSWInterval,ho]

/-- At a fixed scale, a prefix has ONE key and a zero/one activity gate. -/
def selectedKey (d : ℕ) (endpoint : (ℕ × ℕ) → ℕ) (t : ℕ × ℕ) : ℕ :=
  prefixKey d (endpoint t)

def selectedSigma (d : ℕ) (endpoint : (ℕ × ℕ) → ℕ)
    (sigma : (ℕ × ℕ) → ℂ) (t : ℕ × ℕ) : ℂ :=
  if Active d (endpoint t) then sigma t else 0

def dyadicKeys (N d : ℕ) (endpoint : (ℕ × ℕ) → ℕ) : Finset ℕ :=
  blockKeys N (selectedKey d endpoint)

def dyadicBeta (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l d : ℕ)
    (endpoint : (ℕ × ℕ) → ℕ) (sigma : (ℕ × ℕ) → ℂ) (b m : ℕ) : ℂ :=
  blockBeta N c cs H δ j l (selectedKey d endpoint)
    (selectedSigma d endpoint sigma) b m

def dyadicAlpha (N : ℕ) (δ : ℝ) (j d b : ℕ) : ℤ → ℂ :=
  paddedRow (clippedCell (ambientLo δ j) (ambientHi δ j) d b)
    (primeHeadCoefficient N δ j)

def levelSource (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l d : ℕ)
    (endpoint : (ℕ × ℕ) → ℕ) (sigma : (ℕ × ℕ) → ℂ) (q : ℕ) : ℂ :=
  ∑ b ∈ dyadicKeys N d endpoint,
    naturalRectangleDiscrepancy
      (clippedCell (ambientLo δ j) (ambientHi δ j) d b)
      (jointRetainedProducts N c cs H δ j l)
      (primeHeadCoefficient N δ j) (dyadicBeta N c cs H δ j l d endpoint sigma b) N q

private theorem rectangle_beta_test (S T : Finset ℕ) (a b : ℕ → ℂ) (N q : ℕ) :
    naturalRectangleDiscrepancy S T a b N q =
      ∑ m ∈ T,b m * ∑ p ∈ S,a p*(gammaKernel N q (p*m) : ℂ) := by
  unfold naturalRectangleDiscrepancy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- The old-pair labels are INSIDE each dyadic beta, with exact product
collisions and no imposed equality of the original head windows. -/
theorem levelSource_eq_pairs (N c : ℕ) (cs : List ℕ) (H δ : ℝ)
    (j l d : ℕ) (endpoint : (ℕ × ℕ) → ℕ) (sigma : (ℕ × ℕ) → ℂ) (q : ℕ) :
    levelSource N c cs H δ j l d endpoint sigma q =
      ∑ t ∈ pairSupport N,selectedSigma d endpoint sigma t *
        naturalRectangleDiscrepancy
          (clippedCell (ambientLo δ j) (ambientHi δ j) d (selectedKey d endpoint t))
          (retainedComplementSupport N t c cs H δ j l)
          (primeHeadCoefficient N δ j) (retainedBeta N t c cs H δ j l) N q := by
  simp only [levelSource,dyadicBeta,dyadicKeys,rectangle_beta_test]
  exact block_test_eq_pair N c cs H δ j l (selectedKey d endpoint)
    (selectedSigma d endpoint sigma)
    (fun b m => ∑ p ∈ clippedCell (ambientLo δ j) (ambientHi δ j) d b,
      primeHeadCoefficient N δ j p*(gammaKernel N q (p*m) : ℂ))

/-- One original pair becomes two signed prefix ladders. All tests remain
literal AP-minus-q-coprime-mean kernels, including q=0 at this algebraic stage. -/
theorem cartesianRow_eq_prefix_difference {N c : ℕ} {cs : List ℕ}
    {H δ : ℝ} (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) (j l : ℕ)
    {t : ℕ × ℕ} (ht : t ∈ pairSupport N)
    (hM : Occupied N t c cs H δ j l → 1 ≤ lower δ j) (q : ℕ) :
    cartesianRow N t c cs H δ j l q =
      ∑ d ∈ Finset.range (depth (ambientHi δ j)),
        ((if Active d (endpointHi N c cs H δ j l t) then
          naturalRectangleDiscrepancy
            (clippedCell (ambientLo δ j) (ambientHi δ j) d
              (prefixKey d (endpointHi N c cs H δ j l t)))
            (retainedComplementSupport N t c cs H δ j l)
            (primeHeadCoefficient N δ j) (retainedBeta N t c cs H δ j l) N q else 0)-
        (if Active d (endpointLo N c cs H δ j l t) then
          naturalRectangleDiscrepancy
            (clippedCell (ambientLo δ j) (ambientHi δ j) d
              (prefixKey d (endpointLo N c cs H δ j l t)))
            (retainedComplementSupport N t c cs H δ j l)
            (primeHeadCoefficient N δ j) (retainedBeta N t c cs H δ j l) N q else 0)) := by
  have hc : cartesianRow N t c cs H δ j l q =
      naturalRectangleDiscrepancy
        (Finset.Ioc (endpointLo N c cs H δ j l t) (endpointHi N c cs H δ j l t))
        (retainedComplementSupport N t c cs H δ j l)
        (primeHeadCoefficient N δ j) (retainedBeta N t c cs H δ j l) N q := by
    by_cases ho : Occupied N t c cs H δ j l
    · have hh := original_retained_row_eq_actual_rows ht hδ hwidth j l (hM ho) ho
        (fun m => (gammaKernel N q m : ℂ))
      rw [original_retained_row_eq_cartesian ht c cs hδ j l] at hh
      simpa only [endpointLo,endpointHi,if_pos ho,actualPrimeCarrier,primeSWInterval,
        naturalRectangleDiscrepancy,cartesianRow,Nat.mul_comm] using hh
    · simp [cartesianRow_eq_zero ho q,endpointLo,endpointHi,ho,naturalRectangleDiscrepancy]
  obtain ⟨hLa,hab,hbP⟩ := endpoint_bounds hδ hwidth j l ht
  rw [hc]
  exact clipped_interval_expansion hLa hab hbP
    (fun p => ∑ m ∈ retainedComplementSupport N t c cs H δ j l,
      primeHeadCoefficient N δ j p*retainedBeta N t c cs H δ j l m*
        (gammaKernel N q (p*m) : ℂ))

/-- Full outside source, with no selector mass or head-block count hidden
in an estimate. This is a proved equality before any absolute value. -/
theorem original_joint_eq_dyadic (N c : ℕ) (cs : List ℕ) (H : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) (j l : ℕ)
    (hM : ∀ t ∈ pairSupport N,Occupied N t c cs H δ j l → 1 ≤ lower δ j)
    (sigma : (ℕ × ℕ) → ℂ) (q : ℕ) :
    (∑ t ∈ pairSupport N,sigma t*cartesianRow N t c cs H δ j l q) =
      ∑ d ∈ Finset.range (depth (ambientHi δ j)),
        (levelSource N c cs H δ j l d (endpointHi N c cs H δ j l) sigma q-
         levelSource N c cs H δ j l d (endpointLo N c cs H δ j l) sigma q) := by
  calc
    _ = ∑ t ∈ pairSupport N,sigma t*
        ∑ d ∈ Finset.range (depth (ambientHi δ j)),
          ((if Active d (endpointHi N c cs H δ j l t) then
            naturalRectangleDiscrepancy
              (clippedCell (ambientLo δ j) (ambientHi δ j) d
                (prefixKey d (endpointHi N c cs H δ j l t)))
              (retainedComplementSupport N t c cs H δ j l)
              (primeHeadCoefficient N δ j) (retainedBeta N t c cs H δ j l) N q else 0)-
           (if Active d (endpointLo N c cs H δ j l t) then
            naturalRectangleDiscrepancy
              (clippedCell (ambientLo δ j) (ambientHi δ j) d
                (prefixKey d (endpointLo N c cs H δ j l t)))
              (retainedComplementSupport N t c cs H δ j l)
              (primeHeadCoefficient N δ j) (retainedBeta N t c cs H δ j l) N q else 0)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [cartesianRow_eq_prefix_difference hδ hwidth j l ht (hM t ht) q]
    _ = _ := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [levelSource_eq_pairs,levelSource_eq_pairs,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      simp only [selectedSigma,selectedKey]
      split_ifs <;> ring

def levelCharacterSource (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l d : ℕ)
    (endpoint : (ℕ × ℕ) → ℕ) (sigma : (ℕ × ℕ) → ℂ) (q : ℕ) : ℂ :=
  ∑ b ∈ dyadicKeys N d endpoint,
    rectangleCharacterDiscrepancy (dyadicAlpha N δ j d b)
      (paddedRow (jointRetainedProducts N c cs H δ j l)
        (dyadicBeta N c cs H δ j l d endpoint sigma b))
      0 0 (ambientHi δ j) (ambientHi δ l) q ((N : ZMod q)⁻¹)

theorem levelSource_eq_character (N c : ℕ) (cs : List ℕ) (H : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) (j l d : ℕ)
    (endpoint : (ℕ × ℕ) → ℕ) (sigma : (ℕ × ℕ) → ℂ)
    {q : ℕ} (hq : 0 < q) (hNq : N.Coprime q) :
    levelSource N c cs H δ j l d endpoint sigma q =
      levelCharacterSource N c cs H δ j l d endpoint sigma q := by
  unfold levelSource levelCharacterSource
  apply Finset.sum_congr rfl
  intro b hb
  exact naturalRectangleDiscrepancy_eq_character _ _ _ _ _ _ N q
    (clippedCell_subset _ _ _ _)
    (jointRetainedProducts_subset_cap N c cs H hδ hwidth j l) hq hNq

/-- No analytic level replaces the physical integer rho. Active-modulus
coprimality is supplied before requesting principal-character cancellation. -/
theorem same_rho_dyadic_source {N : ℕ} (hN : 1 ≤ N) (c : ℕ) (cs : List ℕ)
    (H : ℝ) {δ nu : ℝ} (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2)
    (hnu : 0 ≤ nu) (epsilon : ℝ) (j l : ℕ)
    (hM : ∀ t ∈ pairSupport N,Occupied N t c cs H δ j l → 1 ≤ lower δ j)
    (retain : List ℕ → Bool) (cap : ℕ) (Q : Finset ℕ)
    (sigma : (ℕ × ℕ) → ℂ) :
    (∑ q ∈ Q,(upperRho N nu epsilon retain cap q : ℂ)*
      ∑ t ∈ pairSupport N,sigma t*cartesianRow N t c cs H δ j l q) =
      ∑ q ∈ Q,(upperRho N nu epsilon retain cap q : ℂ)*
        ∑ d ∈ Finset.range (depth (ambientHi δ j)),
          (levelCharacterSource N c cs H δ j l d (endpointHi N c cs H δ j l) sigma q-
           levelCharacterSource N c cs H δ j l d (endpointLo N c cs H δ j l) sigma q) := by
  apply Finset.sum_congr rfl
  intro q hqQ
  by_cases hr : upperRho N nu epsilon retain cap q = 0
  · simp only [hr,Complex.ofReal_zero,zero_mul]
  · have hs := attached_rank_two_support (fun _ => retain) (fun _ => cap)
      (mul_nonneg hnu (by norm_num : (0 : ℝ) ≤ 19/96)) hN hr
    rw [original_joint_eq_dyadic N c cs H hδ hwidth j l hM sigma q]
    have hchar (d : ℕ) (e : (ℕ × ℕ) → ℕ) :=
      levelSource_eq_character N c cs H hδ hwidth j l d e sigma hs.1 hs.2.2.1.symm
    simp_rw [hchar]

end
end ImbalancedChen.P2GammaDyadicHeadSource
