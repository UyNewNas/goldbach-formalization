import ImbalancedChen.P5OriginalBetaPrimeSource
import ImbalancedChen.P5RoughSquareWeightedBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Genuine k=1 SW for the original beta-attached singleton THIRD word.
Prime cancellation is inherited only for the explicit Ico prime source.
The entire actual beta convolution is summed with its 1/e harmonic
weight.  No SW assertion for arbitrary divisor-bounded coefficients,
or for beta alone, is used.  One extra logarithmic accuracy pays beta.
-/

namespace ImbalancedChen.P5Z.OriginalBetaPrimeSW
noncomputable section
open Classical Finset Filter Set
open scoped BigOperators Topology
open ImbalancedChen ImbalancedChen.Part3
open All16MarkedCommonFineSource All16MarkedFineScalarBudget All16FineMeshGateScalar
open All16ComputedWholeWordAssignment All16ComputedMarkedTensorBudget
open ActualAll16UnrestrictedResidualConvolution ActualInnerPerLabelGamma
open SameWholeAssignmentPerLabel OriginalSingletonPrimeSource OriginalSingletonPrimeSW
open ComputedSingletonPrimeSWConsumer OriginalBetaPrimeSource
open PrimeMellinProfileVariation20261026b

/-- Active beta terms, not its very large displayed divisor support,
are below the literal strict Rosser level. -/
theorem active_beta_harmonic_le {N cap r : ℕ} (hN : 1 ≤ N) (w B : ℝ)
    (hB : B ≤ N) :
    (∑ e ∈ (actualSmallRosserSupport N cap w).filter
      (fun e => rawBetaWeight N cap r w B e ≠ 0), 1/(e : ℝ)) ≤
      1 + Real.log (N : ℝ) := by
  have hsub : (actualSmallRosserSupport N cap w).filter
      (fun e => rawBetaWeight N cap r w B e ≠ 0) ⊆ Finset.Icc 1 N := by
    intro e he
    obtain ⟨hepos,heB⟩ := ActualSmallBetaMonomialCost.actual_raw_beta_endpoint
      (Finset.mem_filter.mp he).2
    refine Finset.mem_Icc.mpr ⟨hepos,?_⟩
    have hle : (e : ℝ) ≤ N := heB.le.trans hB
    exact_mod_cast hle
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  calc
    _ ≤ ∑ e ∈ Finset.Icc 1 N, 1/(e : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ _ := by
      simpa only [RoughSquareWeightedBudget.logBudget,max_eq_right hNr] using
        RoughSquareWeightedBudget.harmonic_Icc_le_logBudget N

/-- A nonempty scaled prime fibre derives both the analytic dyadic lower
bound and its original-N power size from the actual label. -/
theorem occupied_scaled_source {N m e : ℕ} (hN : 1 < N)
    (i : Fin (m+1)) {rho U : ℝ} (hlower : (N : ℝ)^rho ≤ lower N m i)
    (hs : (source N m i (U/(e : ℝ))).Nonempty) :
    1 ≤ U/(e : ℝ) ∧ (N : ℝ)^rho ≤ 2*(U/(e : ℝ)) := by
  obtain ⟨p,hp⟩ := hs
  obtain ⟨hp,hlo,hhi⟩ := Finset.mem_filter.mp hp
  have hlabel := (mem_commonAlphabet_iff hN i).mp hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hlabel.1.two_le
  exact ⟨by linarith, (hlower.trans hlabel.2.2.1).trans hhi⟩

/-- Fixed C1 profile and fixed logarithmic Mellin bandwidth.  C and the
N threshold precede every rank, beta support, label, full-product dyadic
length, frequency, progression modulus and primitive residue. -/
theorem beta_prime_profile_SW (Phi : ℝ → ℝ) (hPhi : ContDiff ℝ 1 Phi)
    {rho : ℝ} (hrho : 0 < rho) (J L : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ cap m r : ℕ, ∀ i : Fin (m+1), ∀ w B : ℝ,
      w ≤ lower N m i → (N : ℝ)^rho ≤ lower N m i → B ≤ N →
      ∀ U : ℝ, 0 < U → ∀ t : ℝ, |t| ≤ Real.log (N : ℝ)^L →
      ∀ q b : ℕ, 0 < q → b.Coprime q →
      ‖auxiliarySWError (carrier N cap m i w U)
        (value N cap m r i w B Phi t U) 1 q b‖ ≤
          C*U/Real.log (N : ℝ)^J := by
  obtain ⟨C,hC,hSW⟩ := singleton_profile_SW Phi hPhi hrho (J+1) L
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hSW,eventually_one_le_nat_log,eventually_ge_atTop (2 : ℕ)]
    with N hSW hlog hN
  intro cap m r i w B hw hlower hB U hU t ht q b hq hb
  let S := (actualSmallRosserSupport N cap w).filter
    (fun e => rawBetaWeight N cap r w B e ≠ 0)
  let E : ℕ → ℂ := fun e =>
    if e.Coprime q then
      auxiliarySWError (source N m i (U/(e : ℝ)))
        (coefficient N m [i] Phi t (U/(e : ℝ))) 1 q (pulledResidue e q b)
    else 0
  have hlp : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  have hE : ∀ e ∈ S, ‖E e‖ ≤ (C*U/Real.log (N : ℝ)^(J+1))*(1/(e : ℝ)) := by
    intro e he
    have hepos := (ActualSmallBetaMonomialCost.actual_raw_beta_endpoint
      (Finset.mem_filter.mp he).2).1
    have heR : (0 : ℝ) < e := by exact_mod_cast hepos
    by_cases heq : e.Coprime q
    · dsimp only [E]
      rw [if_pos heq]
      by_cases hs : (source N m i (U/(e : ℝ))).Nonempty
      · obtain ⟨hscaled,hpower⟩ := occupied_scaled_source (by omega) i hlower hs
        have hh := hSW m i (U/(e : ℝ)) hscaled hpower t ht q
          (pulledResidue e q b) hq (pulledResidue_coprime heq hb)
        convert hh using 1 <;> ring
      · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
        simp only [auxiliarySWError,Finset.sum_empty,zero_div,sub_zero,norm_zero]
        positivity
    · simp only [E,if_neg heq,norm_zero]
      positivity
  have hsource : auxiliarySWError (carrier N cap m i w U)
      (value N cap m r i w B Phi t U) 1 q b =
      ∑ e ∈ S, (rawBetaWeight N cap r w B e : ℂ)*E e := by
    rw [original_beta_prime_error (by omega) i hw Phi t U hb]
    simp only [S,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hbeta : rawBetaWeight N cap r w B e = 0
    · simp [hbeta]
    · simp only [hbeta,not_false_eq_true,if_true,E]
  rw [hsource]
  calc
    _ ≤ ∑ e ∈ S, ‖(rawBetaWeight N cap r w B e : ℂ)*E e‖ := norm_sum_le _ _
    _ ≤ ∑ e ∈ S, (C*U/Real.log (N : ℝ)^(J+1))*(1/(e : ℝ)) := by
      apply Finset.sum_le_sum
      intro e he
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right (raw_beta_abs_le_one N cap r w B e)
        (norm_nonneg _)).trans (by simpa only [one_mul] using hE e he)
    _ = (C*U/Real.log (N : ℝ)^(J+1)) * ∑ e ∈ S, 1/(e : ℝ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (C*U/Real.log (N : ℝ)^(J+1))*(1+Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (active_beta_harmonic_le (by omega) w B hB) (by positivity)
    _ ≤ (C*U/Real.log (N : ℝ)^(J+1))*(2*Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (2*C)*U/Real.log (N : ℝ)^J := by
      rw [pow_succ]
      field_simp [hlp.ne',(pow_pos hlp J).ne']
      <;> ring

/-- The missing THIRD-word power condition is derived from the SAME
computed whole-word partition. All four original marked occurrences
are still in that partition. -/
theorem computed_third_lower {n N m r : ℕ} (hN : 1 < N)
    {eta : ℚ} {rho : ℝ} {M : Set (ℝ × ℝ)} {k : Key n m r}
    (h : WholeCell eta rho M k.1 k.2.1 k.2.2)
    (hcut : rho ≤ cellZeta n eta k.1) (A : ℝ) {i : Fin (m+1)}
    (hi : (labelGroups n N m r eta A k).2.2 = [i]) :
    (N : ℝ)^rho ≤ lower N m i := by
  apply wholeWord_lower hN h hcut
  apply (labelGroups_partition n N m r eta A k).mem_iff.mp
  apply List.mem_append_right
  apply List.mem_append_right
  rw [hi]
  simp

/-- The already existing tensor, expanded at its genuine beta-third
source.  F may contain an arbitrary physical marked prefix or count/mean
kernel; no source equality is supplied by the caller. -/
theorem actual_tensor_beta_third {n N m r : ℕ} (hN : 1 < N)
    {eta : ℚ} {rho : ℝ} {M : Set (ℝ × ℝ)} {k : Key n m r}
    (h : WholeCell eta rho M k.1 k.2.1 k.2.2)
    (hcut : rho ≤ cellZeta n eta k.1) (B A : ℝ) {i : Fin (m+1)}
    (hi : (labelGroups n N m r eta A k).2.2 = [i]) (F : ℕ → ℝ) :
    tensor n N m r eta rho B A k F =
      ∑ x ∈ support (commonAlphabet N m) (labelGroups n N m r eta A k).1,
        ∑ y ∈ support (commonAlphabet N m) (labelGroups n N m r eta A k).2.1,
          ∑ e ∈ actualSmallRosserSupport N (cellCap n N eta k.1) ((N : ℝ)^rho),
            ∑ p ∈ commonAlphabet N m i,
              gamma (commonAlphabet N m) (labelGroups n N m r eta A k).1 x *
                gamma (commonAlphabet N m) (labelGroups n N m r eta A k).2.1 y *
                rawBetaWeight N (cellCap n N eta k.1) r ((N : ℝ)^rho) B e *
                F (x*y*(e*p)) := by
  unfold tensor
  dsimp only
  rw [hi]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  let c := gamma (commonAlphabet N m) (labelGroups n N m r eta A k).1 x *
    gamma (commonAlphabet N m) (labelGroups n N m r eta A k).2.1 y
  have hh := original_beta_prime_test (cap := cellCap n N eta k.1) (r := r)
    (B := B) hN i (computed_third_lower hN h hcut A hi)
    (fun d => c * F (x*y*d))
  calc
    _ = ∑ d ∈ attachedSupport (commonAlphabet N m) [i]
        N (cellCap n N eta k.1) ((N : ℝ)^rho),
        SameWholeAssignmentPerLabel.attachedGamma (commonAlphabet N m) [i]
          N (cellCap n N eta k.1) r ((N : ℝ)^rho) B d * (c * F (x*y*d)) := by
      apply Finset.sum_congr rfl
      intro d hd
      dsimp [c]
      ring
    _ = _ := hh
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro p hp
      dsimp [c]
      ring

/-- Actual third factor of H's tensor, with its entire original beta at
N^epsilon. The very mild epsilon≤1 is discharged by every original
small-beta choice; no beta-support-cardinality bound is assumed. -/
theorem actual_computed_beta_third_SW (Phi : ℝ → ℝ) (hPhi : ContDiff ℝ 1 Phi)
    {rho : ℝ} (hrho : 0 < rho) (J L : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ n m r : ℕ, ∀ eta : ℚ, ∀ M : Set (ℝ × ℝ), ∀ k : Key n m r,
      WholeCell eta rho M k.1 k.2.1 k.2.2 → rho ≤ cellZeta n eta k.1 →
      ∀ A epsilon : ℝ, epsilon ≤ 1 → ∀ i : Fin (m+1),
      (labelGroups n N m r eta A k).2.2 = [i] →
      ∀ U : ℝ, 0 < U → ∀ t : ℝ, |t| ≤ Real.log (N : ℝ)^L →
      ∀ q b : ℕ, 0 < q → b.Coprime q →
      ‖auxiliarySWError
        ((attachedSupport (commonAlphabet N m) (labelGroups n N m r eta A k).2.2
          N (cellCap n N eta k.1) ((N : ℝ)^rho)).filter
          (fun d => U < (d : ℝ) ∧ (d : ℝ) ≤ 2*U))
        (fun d => physicalProfile Phi t U d *
          (SameWholeAssignmentPerLabel.attachedGamma (commonAlphabet N m)
            (labelGroups n N m r eta A k).2.2 N (cellCap n N eta k.1) r
            ((N : ℝ)^rho) ((N : ℝ)^epsilon) d : ℂ)) 1 q b‖ ≤
        C*U/Real.log (N : ℝ)^J := by
  obtain ⟨C,hC,hSW⟩ := beta_prime_profile_SW Phi hPhi hrho J L
  refine ⟨C,hC,?_⟩
  filter_upwards [hSW,eventually_ge_atTop (2 : ℕ)] with N hSW hN
  intro n m r eta M k h hcut A epsilon hepsilon i hi U hU t ht q b hq hb
  have hlow := computed_third_lower (by omega) h hcut A hi
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hB : (N : ℝ)^epsilon ≤ N :=
    (Real.rpow_le_rpow_of_exponent_le hNr hepsilon).trans_eq (Real.rpow_one _)
  rw [hi]
  exact hSW (cellCap n N eta k.1) m r i ((N : ℝ)^rho) ((N : ℝ)^epsilon)
    hlow hlow hB U hU t ht q b hq hb

end
end ImbalancedChen.P5Z.OriginalBetaPrimeSW
