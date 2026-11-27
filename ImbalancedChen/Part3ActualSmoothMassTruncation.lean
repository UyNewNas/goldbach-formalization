import ImbalancedChen.Part3ActualCompletedHardTailCore
import ImbalancedChen.Part3ActualSmoothMassCommonLanes

/-!
# A common hard cutoff for the actual six smooth pieces

This module connects the accepted common signed Poisson lanes to the recovered
hard-window tail estimates. The analytic decay estimate is supplied by the
original hard-tail modules; only window identification, finite source assembly
and the six-piece composition are new here.

All primary tails are assembled before taking a norm. They are exactly one
weighted sum over nonzeroSource S, with no keys.card factor. The y=0 source
keeps its full integer-frequency kernel. The finite truncated kernel retains
m=0 and both signs of every common block, with the original Fourier argument.

For the six scales B and 2*B, the hard-tail parameters are respectively R and
2*R, yielding the same J=ceil(10*C*R/B). The outer c carrier always uses C,
while its smooth scale is allowed to be C, 2*C or 4*C. The resulting bound
keeps the genuine sourceAbsMass of the original lambda and omega. No norm-one
coefficient premise, OriginalData identification or full-family x-error
estimate is introduced. This is the finite common-cutoff step of the 1106
analytic appendix, lines 700-703.
-/

namespace ImbalancedChen.Part3.ActualSmoothMassTruncation20261127

noncomputable section
open Classical Finset
open scoped BigOperators
open CommonSmoothCutoff OriginalSmoothPoissonTail
open OriginalSmoothPoissonTail.HardCompletedSchwartz20261026b
open ActualReciprocalSquarePoissonSourceOnly ActualCompletedSquarePushforwardSourceOnly
open ActualCompletedHardTailMass20261026b OriginalCommonPoissonLanes20261102
open ActualSeparatedRowPacketMatchSourceOnly ActualPositiveLatticeSmoothCoverSourceOnly
open ActualModeCommonPoissonLanes20261126 ActualSmoothMassCommonLanes20261127
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly

/-- The accepted signed block window is the literal closed integer interval. -/
theorem mWindow_eq_Icc (J : ℕ) : mWindow J = Icc (-(J : ℤ)) (J : ℤ) := by
  ext m
  rw [mem_mWindow_iff, mem_Icc]
  constructor
  · intro hm
    have h : (m.natAbs : ℤ) ≤ (J : ℤ) := by exact_mod_cast hm
    rw [Int.natCast_natAbs] at h
    exact abs_le.mp h
  · intro hm
    have h : |m| ≤ (J : ℤ) := abs_le.mpr hm
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h

theorem mWindow_eq_commonHardWindow (C M R : ℝ) :
    mWindow (Nat.ceil (10 * C * R / M)) = commonHardWindow C M R :=
  mWindow_eq_Icc _

/-- Doubling the b scale and physical tail threshold leaves the integer cutoff
unchanged; this equality is used before comparing any tail norms. -/
theorem common_cutoff_double_scale (C B R : ℝ) (hB : 0 < B) :
    Nat.ceil (10 * C * (2 * R) / (2 * B)) = Nat.ceil (10 * C * R / B) := by
  congr 1
  field_simp [hB.ne']

/-- The existing subtype tail is the difference of the full convergent series
and its finite window. Summability is provided by the actual frequency. -/
theorem poissonTail_eq_tsum_sub_window {M : ℝ} (hM : 0 < M)
    (c : ℕ) (hc : 0 < c) (J : ℕ) (a y z : ℤ) :
    poissonTail J M c a y z = (∑' m : ℤ, frequency M c a y z m) -
      ∑ m ∈ mWindow J, frequency M c a y z m := by
  have hs := frequency_summable M hM c hc a y z
  apply eq_sub_iff_add_eq.mpr
  simpa only [poissonTail, add_comm] using hs.sum_add_tsum_subtype_compl (mWindow J)

/-- The common-lanes tail is exactly the recovered hard-window kernel error. -/
theorem tailKernel_eq_completed_sub_hard {M : ℝ} (hM : 0 < M)
    (N C R : ℝ) (a : ℤ) (zy : Output) :
    tailKernel (Nat.ceil (10 * C * R / M)) M N C a zy =
      completedKernel M N C a zy - hardCompletedKernel M N C R a zy := by
  unfold tailKernel weightedC completedKernel hardCompletedKernel
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro c hc
  by_cases hcz : c.Coprime zy.1
  · simp only [if_pos hcz]
    rw [poissonTail_eq_tsum_sub_window hM c (mem_Ioc.mp hc).1,
      mWindow_eq_commonHardWindow]
    ring
  · simp only [if_neg hcz, sub_self]

/-- The finite zero/positive/negative common-block kernel, with no tail. -/
def truncatedKernel (J : ℕ) (M N C : ℝ) (a : ℤ) (zy : Output) : ℂ :=
  zeroMKernel M N C a zy + ∑ j ∈ blockIndices J,
    (blockKernel J j false M N C a zy + blockKernel J j true M N C a zy)

theorem completedKernel_eq_truncated_add_tail {M : ℝ} (hM : 0 < M)
    (J : ℕ) (N C : ℝ) (a : ℤ) (zy : Output) :
    completedKernel M N C a zy =
      truncatedKernel J M N C a zy + tailKernel J M N C a zy :=
  completedKernel_eq_m_lanes hM J N C a zy

theorem truncatedKernel_eq_hardCompletedKernel {M : ℝ} (hM : 0 < M)
    (N C R : ℝ) (a : ℤ) (zy : Output) :
    truncatedKernel (Nat.ceil (10 * C * R / M)) M N C a zy =
      hardCompletedKernel M N C R a zy := by
  have h := completedKernel_eq_truncated_add_tail hM
    (Nat.ceil (10 * C * R / M)) N C a zy
  rw [tailKernel_eq_completed_sub_hard hM] at h
  linear_combination -h

/-- The literal tails of all existing primary blocks, before any norm. -/
def primaryTail (a : ℤ) (S : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (J : ℕ) (M N C : ℝ) : ℂ :=
  ∑ key ∈ keys a S, ∑ zy ∈ (block a S key).image output,
    beta (block a S key) lambda omega zy * tailKernel J M N C a zy

/-- No block-count loss: weighted pushforward and the exact existing primary
partition combine all tails into one sum on the original nonzero source. -/
theorem primaryTail_eq_source (a : ℤ) (S : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (J : ℕ) (M N C : ℝ) :
    primaryTail a S lambda omega J M N C =
      ∑ s ∈ nonzeroSource S, weight lambda omega s * tailKernel J M N C a (output s) := by
  symm
  rw [finite_source_assembly a S]
  unfold primaryTail
  apply sum_congr rfl
  intro key _hkey
  exact weighted_pushforward (block a S key) lambda omega (tailKernel J M N C a)

theorem primaryTail_eq_completed_sub_hard (a : ℤ) (S : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) {M : ℝ} (hM : 0 < M) (N C R : ℝ) :
    primaryTail a S lambda omega (Nat.ceil (10 * C * R / M)) M N C =
      (∑ s ∈ nonzeroSource S, weight lambda omega s * completedKernel M N C a (output s)) -
        hardSourcePiece (nonzeroSource S) lambda omega M N C R a := by
  rw [primaryTail_eq_source]
  simp_rw [tailKernel_eq_completed_sub_hard hM]
  simp only [mul_sub, sum_sub_distrib, hardSourcePiece]

/-- The recovered analytic constant precedes all scales and all source data. -/
theorem primaryTail_common_hard_bound (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : ℝ, 0 < C → ∀ M : ℝ, 0 < M →
      ∀ R : ℝ, 0 < R → ∀ N : ℝ, ∀ a : ℤ, ∀ S : Finset Source,
      ∀ (lambda : ℕ → ℂ) (omega : ℤ → ℂ),
        ‖primaryTail a S lambda omega (Nat.ceil (10 * C * R / M)) M N C‖ ≤
          (A * C ^ 2 / R ^ (r - 1)) * sourceAbsMass (nonzeroSource S) lambda omega := by
  obtain ⟨A, hA, htail⟩ := source_common_hard_tail r hr
  refine ⟨A, hA, ?_⟩
  intro C hC M hM R hR N a S lambda omega
  rw [primaryTail_eq_completed_sub_hard a S lambda omega hM N C R]
  exact htail C hC M hM R hR N a (nonzeroSource S) lambda omega

/-- The actual zero-y source remains complete. Only the nonzero-y source is
evaluated on the literal finite common-block kernel. -/
def actualTruncatedPiece (e : MediumAtom) (D delta g l : ℕ) (Z : ℝ)
    (residueNegative : Bool) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (J : ℕ) (M N C : ℝ) : ℂ :=
  let a := signedResidue residueNegative e.residue
  let S := actualSource e D delta g l Z residueNegative
  (∑ zy ∈ (zeroSource S).image output,
    beta (zeroSource S) lambda omega zy * completedKernel M N C a zy) +
    ∑ s ∈ nonzeroSource S, weight lambda omega s * truncatedKernel J M N C a (output s)

theorem actualPieceLanes_sub_truncated_eq_primaryTail
    (e : MediumAtom) (D delta g l : ℕ) (Z : ℝ) (residueNegative : Bool)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) {M : ℝ} (hM : 0 < M)
    (J : ℕ) (N C : ℝ) :
    actualPieceLanes e D delta g l Z residueNegative lambda omega J M N C -
      actualTruncatedPiece e D delta g l Z residueNegative lambda omega J M N C =
      primaryTail (signedResidue residueNegative e.residue)
        (actualSource e D delta g l Z residueNegative) lambda omega J M N C := by
  unfold actualPieceLanes actualTruncatedPiece
  dsimp only
  rw [add_sub_add_left_eq_sub,
    ← nonzero_source_eq_primary_m_lanes _ _ lambda omega hM J N C,
    primaryTail_eq_source, ← sum_sub_distrib]
  apply sum_congr rfl
  intro s _hs
  rw [completedKernel_eq_truncated_add_tail hM J N C
    (signedResidue residueNegative e.residue) (output s)]
  ring

/-- The actual single-piece error is precisely the assembled primary tail. -/
theorem actual_smoothMass_sub_truncated_eq_primaryTail
    (e : MediumAtom) (D delta g l : ℕ) (Z : ℝ) (residueNegative : Bool)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) {M B : ℝ}
    (hM : 0 < M) (hMB : M ≤ 2 * B) (J : ℕ) (N C : ℝ) :
    (smoothMass M N (packetBox B C (scaleF e D g))
      (finiteReciprocalRow (g * l) (signedResidue residueNegative e.residue)
        (baseCarrier e (D / delta)) (e.sharedSmoothFrequencyBound Z D)
        lambda omega) : ℂ) -
      actualTruncatedPiece e D delta g l Z residueNegative lambda omega J M N C =
      primaryTail (signedResidue residueNegative e.residue)
        (actualSource e D delta g l Z residueNegative) lambda omega J M N C := by
  rw [actual_smoothMass_eq_common_m_lanes e D delta g l Z residueNegative
    lambda omega hM hMB J N C]
  exact actualPieceLanes_sub_truncated_eq_primaryTail
    e D delta g l Z residueNegative lambda omega hM J N C

theorem actual_smoothMass_common_hard_tail (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : ℝ, 0 < C → ∀ M : ℝ, 0 < M →
      ∀ B : ℝ, M ≤ 2 * B → ∀ R : ℝ, 0 < R → ∀ N : ℝ,
      ∀ (e : MediumAtom) (D delta g l : ℕ) (Z : ℝ) (residueNegative : Bool)
        (lambda : ℕ → ℂ) (omega : ℤ → ℂ),
        ‖(smoothMass M N (packetBox B C (scaleF e D g))
          (finiteReciprocalRow (g * l) (signedResidue residueNegative e.residue)
            (baseCarrier e (D / delta)) (e.sharedSmoothFrequencyBound Z D)
            lambda omega) : ℂ) -
          actualTruncatedPiece e D delta g l Z residueNegative lambda omega
            (Nat.ceil (10 * C * R / M)) M N C‖ ≤
          (A * C ^ 2 / R ^ (r - 1)) *
            sourceAbsMass (nonzeroSource (actualSource e D delta g l Z residueNegative))
              lambda omega := by
  obtain ⟨A, hA, htail⟩ := primaryTail_common_hard_bound r hr
  refine ⟨A, hA, ?_⟩
  intro C hC M hM B hMB R hR N e D delta g l Z residueNegative lambda omega
  rw [actual_smoothMass_sub_truncated_eq_primaryTail e D delta g l Z residueNegative
    lambda omega hM hMB (Nat.ceil (10 * C * R / M)) N C]
  exact htail C hC M hM R hR N (signedResidue residueNegative e.residue)
    (actualSource e D delta g l Z residueNegative) lambda omega

/-- The same original six scale pairs, all at one J and one actual source. -/
def actualTruncatedSix (e : MediumAtom) (D delta g l : ℕ) (Z : ℝ)
    (residueNegative : Bool) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (J : ℕ) (B C : ℝ) : ℂ :=
  actualTruncatedPiece e D delta g l Z residueNegative lambda omega J B C C +
  actualTruncatedPiece e D delta g l Z residueNegative lambda omega J B (2 * C) C +
  actualTruncatedPiece e D delta g l Z residueNegative lambda omega J B (4 * C) C +
  actualTruncatedPiece e D delta g l Z residueNegative lambda omega J (2 * B) C C +
  actualTruncatedPiece e D delta g l Z residueNegative lambda omega J (2 * B) (2 * C) C +
  actualTruncatedPiece e D delta g l Z residueNegative lambda omega J (2 * B) (4 * C) C

/-- A common cutoff for all six actual pieces. The honest source mass remains
explicit, and the six is only the finite triangle-inequality factor. -/
theorem actual_sixSmoothMass_common_hard_tail (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ ∀ B : ℝ, 0 < B → ∀ C : ℝ, 0 < C →
      ∀ R : ℝ, 0 < R →
      ∀ (e : MediumAtom) (D delta g l : ℕ) (Z : ℝ) (residueNegative : Bool)
        (lambda : ℕ → ℂ) (omega : ℤ → ℂ),
        ‖(sixSmoothMass B C (packetBox B C (scaleF e D g))
          (finiteReciprocalRow (g * l) (signedResidue residueNegative e.residue)
            (baseCarrier e (D / delta)) (e.sharedSmoothFrequencyBound Z D)
            lambda omega) : ℂ) -
          actualTruncatedSix e D delta g l Z residueNegative lambda omega
            (Nat.ceil (10 * C * R / B)) B C‖ ≤
          (6 * A * C ^ 2 / R ^ (r - 1)) *
            sourceAbsMass (nonzeroSource (actualSource e D delta g l Z residueNegative))
              lambda omega := by
  obtain ⟨A, hA, htail⟩ := primaryTail_common_hard_bound r hr
  refine ⟨A, hA, ?_⟩
  intro B hB C hC R hR e D delta g l Z residueNegative lambda omega
  let J := Nat.ceil (10 * C * R / B)
  let S := actualSource e D delta g l Z residueNegative
  let a := signedResidue residueNegative e.residue
  let E (M N : ℝ) :=
    actualPieceLanes e D delta g l Z residueNegative lambda omega J M N C -
      actualTruncatedPiece e D delta g l Z residueNegative lambda omega J M N C
  let K := (A * C ^ 2 / R ^ (r - 1)) * sourceAbsMass (nonzeroSource S) lambda omega
  have hmass : 0 ≤ sourceAbsMass (nonzeroSource S) lambda omega := by
    unfold sourceAbsMass
    exact sum_nonneg (fun _ _ => norm_nonneg _)
  have hscale : A * C ^ 2 / (2 * R) ^ (r - 1) ≤ A * C ^ 2 / R ^ (r - 1) :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos hR _)
      (pow_le_pow_left₀ hR.le (by linarith : R ≤ 2 * R) _)
  have hfirst (N : ℝ) : ‖E B N‖ ≤ K := by
    dsimp only [E]
    rw [actualPieceLanes_sub_truncated_eq_primaryTail
      e D delta g l Z residueNegative lambda omega hB J N C]
    exact htail C hC B hB R hR N a S lambda omega
  have hsecond (N : ℝ) : ‖E (2 * B) N‖ ≤ K := by
    have h := htail C hC (2 * B) (by positivity) (2 * R) (by positivity)
      N a S lambda omega
    rw [common_cutoff_double_scale C B R hB] at h
    dsimp only [E]
    rw [actualPieceLanes_sub_truncated_eq_primaryTail
      e D delta g l Z residueNegative lambda omega (by positivity : 0 < 2 * B) J N C]
    exact h.trans (mul_le_mul_of_nonneg_right hscale hmass)
  have herr :
      (sixSmoothMass B C (packetBox B C (scaleF e D g))
        (finiteReciprocalRow (g * l) (signedResidue residueNegative e.residue)
          (baseCarrier e (D / delta)) (e.sharedSmoothFrequencyBound Z D)
          lambda omega) : ℂ) -
        actualTruncatedSix e D delta g l Z residueNegative lambda omega J B C =
        E B C + E B (2 * C) + E B (4 * C) +
          E (2 * B) C + E (2 * B) (2 * C) + E (2 * B) (4 * C) := by
    rw [actual_sixSmoothMass_eq_common_m_lanes e D delta g l Z residueNegative
      lambda omega hB J C]
    dsimp only [actualTruncatedSix, E]
    ring
  change ‖_ - actualTruncatedSix e D delta g l Z residueNegative lambda omega J B C‖ ≤ _
  rw [herr]
  calc
    _ ≤ ‖E B C‖ + ‖E B (2 * C)‖ + ‖E B (4 * C)‖ +
        ‖E (2 * B) C‖ + ‖E (2 * B) (2 * C)‖ + ‖E (2 * B) (4 * C)‖ := by
      have h1 := norm_add_le (E B C) (E B (2 * C))
      have h2 := norm_add_le (E B C + E B (2 * C)) (E B (4 * C))
      have h3 := norm_add_le (E B C + E B (2 * C) + E B (4 * C)) (E (2 * B) C)
      have h4 := norm_add_le (E B C + E B (2 * C) + E B (4 * C) + E (2 * B) C)
        (E (2 * B) (2 * C))
      have h5 := norm_add_le
        (E B C + E B (2 * C) + E B (4 * C) + E (2 * B) C + E (2 * B) (2 * C))
        (E (2 * B) (4 * C))
      linarith only [h1, h2, h3, h4, h5]
    _ ≤ K + K + K + K + K + K := by
      linarith only [hfirst C, hfirst (2 * C), hfirst (4 * C),
        hsecond C, hsecond (2 * C), hsecond (4 * C)]
    _ = _ := by dsimp only [K, S]; ring

end

end ImbalancedChen.Part3.ActualSmoothMassTruncation20261127
