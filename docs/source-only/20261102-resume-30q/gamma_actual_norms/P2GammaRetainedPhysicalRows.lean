import ImbalancedChen.P2GammaRetainedCompleteScale
import ImbalancedChen.P2GammaHeadWindowDictionary

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Attach Q15's actually implemented head-colour interval to the actual
retained complementary rows and their proved norms. No interval dictionary,
generic large sieve, conductor sum, or scale-transport proof is rewritten.
This is an exact-source and norm supplier, not a full Gamma BV theorem.
-/

namespace ImbalancedChen.P2GammaRetainedPhysicalRows
noncomputable section
open scoped Classical BigOperators
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P2OriginalGammaDivisorNorm P2GammaOriginalCartesianMask
open P2GammaSmoothLogGrid P2GammaRetainedInteriorGeometry
open P2GammaRetainedActualNorms P2GammaRetainedCompleteScale
open P2GammaHeadWindowDictionary P2GammaSmallConductorIntervalBridge
open P2GammaConvolutionLargeConductor P2GammaPrimeCharacterSW
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open Wu2008DoubleSieve
open P5OriginalU5CausalFinite (pairSupport)

def actualPrimeCarrier (N : ℕ) (t : ℕ × ℕ) (c : ℕ) (δ : ℝ) (j : ℕ) : Finset ℕ :=
  primeSWInterval (clipLo N t c (lower δ j)) (clipHi N t c (lower δ j))

def actualAlpha (N : ℕ) (t : ℕ × ℕ) (c : ℕ) (δ : ℝ) (j : ℕ) : ℤ → ℂ :=
  paddedRow (actualPrimeCarrier N t c δ j) (primeHeadCoefficient N δ j)

def actualBeta (N : ℕ) (t : ℕ × ℕ) (c : ℕ) (cs : List ℕ)
    (H δ : ℝ) (j l : ℕ) : ℤ → ℂ :=
  paddedRow (retainedComplementSupport N t c cs H δ j l)
    (retainedBeta N t c cs H δ j l)

/-- Nonzero original retained rows provide the actual colour range and
nonempty clipped head. Neither fact is an added distribution premise. -/
theorem occupied_head_geometry {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    {H δ : ℝ} (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) {j l : ℕ}
    (ho : Occupied N t c cs H δ j l) :
    c ≤ 3 ∧ (source N t c (lower δ j)).Nonempty := by
  obtain ⟨p,hp,y,hy,hw⟩ := ho
  have hwp : weight δ j p ≠ 0 := by
    intro hz
    exact hw (by simp [complexWeight,hz])
  have hp0 : (0 : ℝ) < p := by
    exact_mod_cast (headCarrier_prime_and_target_deleted hp).1.pos
  obtain ⟨hlo,hhi⟩ := weight_nonzero_support hδ hp0 j hwp
  exact ⟨headCarrier_colour_le_three hp,
    ⟨p,Finset.mem_filter.mpr ⟨hp,hlo,hhi.le.trans (upper_le_two_lower hwidth j)⟩⟩⟩

/-- The literal original row is exactly the natural rectangle whose rows
receive the estimates below. F may be the progression-minus-q-coprime-mean
kernel, an induced character product, or any other later arithmetic test.
All original beta labels with the same complete product are SUMMED. -/
theorem original_retained_row_eq_actual_rows {N c : ℕ} {t : ℕ × ℕ}
    {cs : List ℕ} (ht : t ∈ pairSupport N) {H δ : ℝ} (hδ : 0 < δ)
    (hwidth : 2*δ ≤ Real.log 2) (j l : ℕ) (hM : 1 ≤ lower δ j)
    (ho : Occupied N t c cs H δ j l) (F : ℕ → ℂ) :
    (∑ x ∈ rootLabels N t (c::cs),
      (complexWeight δ j (labelHead x) *
        betaLabel N t H δ j l (labelComplement x)) *
          F (product (t.1*t.2) x)) =
      ∑ p ∈ actualPrimeCarrier N t c δ j,
        ∑ m ∈ retainedComplementSupport N t c cs H δ j l,
          (primeHeadCoefficient N δ j p * retainedBeta N t c cs H δ j l m) *
            F (m*p) := by
  obtain ⟨hc,hs⟩ := occupied_head_geometry hδ hwidth ho
  rw [original_retained_row_eq_prime_interval ht hc hδ hwidth j l hM hs F]
  apply Finset.sum_congr rfl
  intro p hp
  have hgroup := retained_complement_test_eq_grouped N t c cs H δ j l
    (fun m => F (m*p))
  have h := congrArg (fun z : ℂ => primeHeadCoefficient N δ j p*z) hgroup
  simpa only [primeHeadCoefficient,Finset.mul_sum,mul_assoc] using h

/-- The two positive natural carriers satisfy the precise caps consumed
by the existing integer bridge. The quotient projectors are added later. -/
theorem actual_rows_supported {N c : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (ht : t ∈ pairSupport N) {H δ : ℝ} (hδ : 0 < δ)
    (hwidth : 2*δ ≤ Real.log 2) (j l : ℕ)
    (ho : Occupied N t c cs H δ j l) :
    actualPrimeCarrier N t c δ j ⊆ Finset.Icc 1 (Nat.floor (2*lower δ j)) ∧
    retainedComplementSupport N t c cs H δ j l ⊆
      Finset.Icc 1 (Nat.floor (2*lower δ l)) := by
  obtain ⟨hc,hs⟩ := occupied_head_geometry hδ hwidth ho
  have hv := (source_nonempty_geometry hc hs).2.2
  exact ⟨primeInterval_subset_cap hv,retainedComplementSupport_subset_cap ht hδ hwidth j l⟩

/-- COMPLETE actual norm/length instance at ONE original target threshold.
No L1, L2, energyProduct, interval-source identity or complete-scale bound
appears among the premises. The only selected rows are nonzero original
retained rows; the complementary theorem makes every other row zero.

For P's local consumer use eta=34/1135, ea=2, eb=2*3^D, c=2,
em=2*3^E, C=D, Hmass=E, Ctarget=1/(1-kappa). A later assembly must still
pay the actual profile/chart budget and certify the post-loss modulus gap.
-/
theorem exists_physical_rows_norm_threshold (kappa : ℝ) (hk : kappa < 1) :
    ∃ T0 : ℝ, 2 ≤ T0 ∧ ∀ N : ℕ, T0 ≤ (N : ℝ) →
      ∀ t ∈ pairSupport N, ∀ i ∈ secondFunctionalMotherPrefixIndices,
      ∀ c : ℕ, ∀ cs : List ℕ, (c::cs) ∈ secondFunctionalMotherGammaWords i →
      ∀ δ : ℝ, 0 < δ → 2*δ ≤ Real.log 2 → ∀ j l : ℕ,
      Occupied N t c cs (2*(N : ℝ)^(1-kappa)) δ j l →
      let M := lower δ j
      let B := lower δ l
      let x := M*B
      let D := ((c::cs).length+1)^2-1
      let E := (c::cs).length
      x^(34/1135 : ℝ) ≤ M ∧ x^(34/1135 : ℝ) ≤ B ∧
      (N : ℝ)^(1-kappa) ≤ x ∧ x ≤ (N : ℝ) ∧
      (N : ℝ) ≤ x^(1/(1-kappa)) ∧
      rowEnergy (actualAlpha N t c δ j) 0 (Nat.floor (2*M)) ≤
        (2 : ℝ)^2*M*(Real.log x)^D ∧
      rowEnergy (actualBeta N t c cs (2*(N : ℝ)^(1-kappa)) δ j l)
        0 (Nat.floor (2*B)) ≤ (2*(3 : ℝ)^D)^2*B*(Real.log x)^D ∧
      rowMass (retainedComplementSupport N t c cs (2*(N : ℝ)^(1-kappa)) δ j l)
        (retainedBeta N t c cs (2*(N : ℝ)^(1-kappa)) δ j l) ≤
        (2*(3 : ℝ)^E)*B*(Real.log x)^E ∧
      (Nat.floor (2*M) : ℝ) ≤ (2 : ℝ)^2*M ∧
      (Nat.floor (2*B) : ℝ) ≤ (2 : ℝ)^2*B := by
  obtain ⟨T0,hT0,hscale⟩ := exists_trim_occupied_scale_threshold kappa hk
  refine ⟨T0,hT0,?_⟩
  intro N hN t ht i hi c cs hcs δ hδ hwidth j l ho
  obtain ⟨hlog,hM,hB,hMpow,hBpow,hlower,hupper,htarget⟩ :=
    hscale N hN t ht c cs δ hδ hwidth j l ho
  obtain ⟨hc,hs⟩ := occupied_head_geometry hδ hwidth ho
  have hv := (source_nonempty_geometry hc hs).2.2
  have hnorm := actual_retained_norm_data ht hi hcs hδ hwidth j l hM hB hlog
    (u:=clipLo N t c (lower δ j)) hv
  exact ⟨hMpow,hBpow,hlower,hupper,htarget,hnorm⟩

end
end ImbalancedChen.P2GammaRetainedPhysicalRows
