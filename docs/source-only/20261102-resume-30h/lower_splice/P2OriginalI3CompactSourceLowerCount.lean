import ImbalancedChen.P2OriginalI3AdmittedPrimeTupleSource
import ImbalancedChen.P2OriginalNewLowerTruePrimeCompilation

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual compact ordinary-plus error is summed with a proved bounded
prime-box mass. The complete raw source is then restored by its literal
complement, and is consumed by ONE NEW-policy projection/attachment lower
count. There is no assumption of global compact coverage, integral
convergence, AP savings, or a difference of old/new projection defects.
-/
namespace ImbalancedChen.P2OriginalI3CompactSourceLowerCount
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2OriginalLowerCompactStartCapConstructor
open P2OriginalMixedThirdSignedFrontier
open P2OriginalI3ActualSmallRosserAttachment
open P2OriginalI3ProjectionAttachmentDefects
open P2OriginalI3ActualCompactKernel
open P2OriginalI3AdmittedPrimeTupleSource
open P2OriginalI3TruePrimeSource
open P2OriginalNewLowerTruePrimeCompilation

/-- A subset chosen by literal geometric membership; no coverage premise
is imposed on the remaining complete raw I3 source. -/
def compactTuples {mesh : ℕ} (D : ThirdStage mesh) (N cap : ℕ) (z a b : ℝ)
    (T : Set (ℝ × ℝ)) : Finset (Fin 3 → ℕ) :=
  (tuples D N cap z).filter fun p =>
    p ∈ actualPrimeBoxTuples N (fun _ => a) (fun _ => b) ∧
    actualRosserQuotientParameters (N : ℝ) ((history p).prod : ℝ)
      ((history p).headD 0 : ℝ) (baselineCap D.rho) ∈ T ∧
    actualRosserQuotientParameters (N : ℝ) ((history p).prod : ℝ)
      ((history p).headD 0 : ℝ) (newCap D N (history p)) ∈ T

def compactRaw {mesh : ℕ} (D : ThirdStage mesh) (N cap : ℕ) (z a b : ℝ)
    (T : Set (ℝ × ℝ)) : ℝ :=
  ∑ p ∈ compactTuples D N cap z a b T, tupleWeight p * rawKernel D N cap (history p)

def compactProfile {mesh : ℕ} (D : ThirdStage mesh) (N cap : ℕ) (z a b : ℝ)
    (T : Set (ℝ × ℝ)) : ℝ :=
  ∑ p ∈ compactTuples D N cap z a b T, tupleWeight p * profileKernel D N (history p)

/-- The omitted part is the unchanged actual signed raw source, including
small-prime and residual-boundary atoms and every actual branch label. -/
def outsideRaw {mesh : ℕ} (D : ThirdStage mesh) (N cap : ℕ) (z a b : ℝ)
    (T : Set (ℝ × ℝ)) : ℝ :=
  ∑ p ∈ tuples D N cap z \ compactTuples D N cap z a b T,
    tupleWeight p * rawKernel D N cap (history p)

theorem complete_raw_eq_compact_add_outside {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (z a b : ℝ) (T : Set (ℝ × ℝ)) (hN : 1 < (N : ℝ)) :
    rawDensity (thirdRetain D N) N cap 0 z =
      rawDensity (seedRetain D N) N cap 0 z +
        compactRaw D N cap z a b T + outsideRaw D N cap z a b T := by
  have hraw := complete_raw_I3_eq_admitted_tuple_sum D N cap z hN
  have hsplit := Finset.sum_sdiff
    (f := fun p => tupleWeight p * rawKernel D N cap (history p))
    (show compactTuples D N cap z a b T ⊆ tuples D N cap z from Finset.filter_subset _ _)
  change outsideRaw D N cap z a b T + compactRaw D N cap z a b T = _ at hsplit
  linarith

/-- The actual compact frontier mass is bounded by the independently
defined prime-box mass, rather than by its cardinality or an assumed bound. -/
theorem compact_mass_le_actual_box {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (z a b : ℝ) (T : Set (ℝ × ℝ)) :
    (∑ p ∈ compactTuples D N cap z a b T, tupleWeight p) ≤
      actualPrimeBoxMass N (fun _ : Fin 3 => a) (fun _ => b) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.1
  · intro p hp _
    exact actualPrimeBoxWeight_nonneg hp

/-- G's pointwise estimate now controls the actual summed source. The
threshold is before D, cap, z and the membership-selected compact subset. -/
theorem exists_compact_raw_profile_error_threshold
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hlegal : ∀ q ∈ T, 0 < q.2 ∧ q.2 < q.1)
    (a b delta : ℝ) (ha : 0 < a) (hab : a < b) (hdelta : 0 < delta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ mesh : ℕ, ∀ D : ThirdStage mesh, ∀ cap : ℕ, ∀ z : ℝ,
        |compactRaw D N cap z a b T * Real.log (N : ℝ) / singularSeries N -
          compactProfile D N cap z a b T| ≤ delta := by
  let M : ℝ := ∏ _i : Fin 3, Real.log (b/a)
  let B : ℝ := |M| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let eta : ℝ := delta / B
  have heta : 0 < eta := div_pos hdelta hB
  obtain ⟨N1,hN1,hpoint⟩ := exists_actual_full_I3_compact_kernel_threshold
    T hT hlegal eta heta
  have hmass : ∀ᶠ N : ℕ in atTop,
      actualPrimeBoxMass N (fun _ : Fin 3 => a) (fun _ => b) ≤ B := by
    have hlim := tendsto_actualPrimeBoxMass (fun _ : Fin 3 => a) (fun _ => b)
      (fun _ => ha) (fun _ => hab)
    have he := Metric.tendsto_nhds.mp hlim 1 (by norm_num)
    filter_upwards [he] with N hN
    have hh : |actualPrimeBoxMass N (fun _ : Fin 3 => a) (fun _ => b) - M| < 1 := by
      simpa only [Real.dist_eq, M] using hN
    have hu := (abs_lt.mp hh).2
    dsimp only [B]
    linarith [le_abs_self M]
  obtain ⟨N2,hN2⟩ := eventually_atTop.mp hmass
  refine ⟨max N1 N2, hN1.trans (le_max_left _ _), ?_⟩
  intro N hN hEven mesh D cap z
  have hbound (p : Fin 3 → ℕ) (hp : p ∈ compactTuples D N cap z a b T) :
      |tupleWeight p * rawKernel D N cap (history p) * Real.log (N : ℝ) /
          singularSeries N - tupleWeight p * profileKernel D N (history p)| ≤
        tupleWeight p * eta := by
    obtain ⟨hpSource,hpBox,hpOld,hpNew⟩ := Finset.mem_filter.mp hp
    obtain ⟨state,hs,hpre,hmass⟩ := exists_state_of_mem_tuples D N cap z p hpSource
    have ho : actualRosserQuotientParameters (N : ℝ) (state.selectedPrefix.prod : ℝ)
        (state.selectedPrefix.headD 0 : ℝ) (baselineCap D.rho) ∈ T := by
      simpa only [hpre] using hpOld
    have hn : actualRosserQuotientParameters (N : ℝ) (state.selectedPrefix.prod : ℝ)
        (state.selectedPrefix.headD 0 : ℝ) (newCap D N state.selectedPrefix) ∈ T := by
      simpa only [hpre] using hpNew
    have hb := hpoint N ((le_max_left _ _).trans hN) hEven mesh D cap z state hs ho hn
    have hw : 0 ≤ tupleWeight p := actualPrimeBoxWeight_nonneg hpBox
    simpa only [P2OriginalI3FullRawActualPlusDensity.actualFullI3PlusTerm,
      actualFullI3ProfileTerm, rawKernel, profileKernel, newCap, hpre, hmass,
      abs_of_nonneg hw] using hb
  calc
    _ = |∑ p ∈ compactTuples D N cap z a b T,
        (tupleWeight p * rawKernel D N cap (history p) * Real.log (N : ℝ) /
          singularSeries N - tupleWeight p * profileKernel D N (history p))| := by
      rw [compactRaw, compactProfile, Finset.sum_mul, Finset.sum_div,
        Finset.sum_sub_distrib]
    _ ≤ ∑ p ∈ compactTuples D N cap z a b T,
        |tupleWeight p * rawKernel D N cap (history p) * Real.log (N : ℝ) /
          singularSeries N - tupleWeight p * profileKernel D N (history p)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ compactTuples D N cap z a b T, tupleWeight p * eta :=
      Finset.sum_le_sum hbound
    _ = eta * ∑ p ∈ compactTuples D N cap z a b T, tupleWeight p := by
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ eta * actualPrimeBoxMass N (fun _ : Fin 3 => a) (fun _ => b) :=
      mul_le_mul_of_nonneg_left (compact_mass_le_actual_box D N cap z a b T) heta.le
    _ ≤ eta * B := mul_le_mul_of_nonneg_left
      (hN2 N ((le_max_right _ _).trans hN)) heta.le
    _ = delta := div_mul_cancel₀ _ hB.ne'

/-- The complete NEW raw density has this lower bound without discarding
the outside source or assuming that any fixed compact covers the frontier. -/
theorem complete_raw_lower_of_compact_error {mesh : ℕ} (D : ThirdStage mesh)
    (N cap : ℕ) (z a b delta : ℝ) (T : Set (ℝ × ℝ)) (hN : 1 < (N : ℝ))
    (herr : |compactRaw D N cap z a b T * Real.log (N : ℝ) / singularSeries N -
      compactProfile D N cap z a b T| ≤ delta) :
    rawDensity (seedRetain D N) N cap 0 z +
        (singularSeries N / Real.log (N : ℝ)) * (compactProfile D N cap z a b T - delta) +
        outsideRaw D N cap z a b T ≤ rawDensity (thirdRetain D N) N cap 0 z := by
  have hl : compactProfile D N cap z a b T - delta ≤
      compactRaw D N cap z a b T * Real.log (N : ℝ) / singularSeries N := by
    have hb := (abs_le.mp herr).1
    linarith
  have hs : 0 < singularSeries N / Real.log (N : ℝ) :=
    div_pos (singularSeries_pos N) (Real.log_pos hN)
  have hscaled := mul_le_mul_of_nonneg_left hl hs.le
  have hcancel : (singularSeries N / Real.log (N : ℝ)) *
      (compactRaw D N cap z a b T * Real.log (N : ℝ) / singularSeries N) =
      compactRaw D N cap z a b T := by
    field_simp [(singularSeries_pos N).ne', (Real.log_pos hN).ne']
  rw [hcancel] at hscaled
  rw [complete_raw_eq_compact_add_outside D N cap z a b T hN]
  linarith

/-- One common threshold pays the compact ordinary-plus error and the
single NEW-policy projection/attachment reserve in the genuine prime
count. The original same-rho AP error and prime-divisor correction remain
literal. No OLD physical coefficient is used in this lower comparison. -/
theorem exists_true_prime_lower_from_compact_profile_and_outside
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hlegal : ∀ q ∈ T, 0 < q.2 ∧ q.2 < q.1)
    (a b delta nu r eta epsilonMax : ℝ)
    (ha : 0 < a) (hab : a < b) (hdelta : 0 < delta)
    (hnu : 0 < nu) (hr : 0 < r) (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1/8 ∧ epsilon < epsilonMax ∧
      epsilon^2 ≤ r ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ cap : ℕ, (N : ℝ)^(nu*r) ≤ (cap : ℝ) →
      ∀ mesh : ℕ, ∀ D : ThirdStage mesh,
        let y := (N : ℝ)^(nu*epsilon^2)
        let z := (N : ℝ)^(nu*r)
        let L := (N : ℝ)^(nu*epsilon)
        let reserve := eta * singularSeries N / Real.log (N : ℝ)
        ((chenAdditivePrimeCarrier N).card : ℝ) *
          (rawDensity (seedRetain D N) N cap 0 z +
            (singularSeries N / Real.log (N : ℝ)) *
              (compactProfile D N cap z a b T - delta) +
            outsideRaw D N cap z a b T - reserve) -
          newPrimeCoprimeCorrection D N cap y z L + newPrimeSignedError D N cap y z L ≤
        ((chenSiftedPrimeSource N z).card : ℝ) := by
  obtain ⟨Nc,hNc,hcompact⟩ := exists_compact_raw_profile_error_threshold
    T hT hlegal a b delta ha hab hdelta
  obtain ⟨epsilon,hepsilon,hepsilon8,hepsilonMax',hepsilonr,Np,hNp,hprime⟩ :=
    exists_new_true_prime_lower_compilation nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon,hepsilon,hepsilon8,hepsilonMax',hepsilonr,max Np Nc,
    hNp.trans (le_max_left _ _),?_⟩
  intro N hN hEven cap hcap mesh D
  have hN1 : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have herr := hcompact N ((le_max_right _ _).trans hN) hEven mesh D cap ((N : ℝ)^(nu*r))
  have hraw := complete_raw_lower_of_compact_error D N cap ((N : ℝ)^(nu*r))
    a b delta T hN1 herr
  have hb := hprime N ((le_max_left _ _).trans hN) hEven cap hcap mesh D
  have hm : (0 : ℝ) ≤ (chenAdditivePrimeCarrier N).card := Nat.cast_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hraw hm
  dsimp only at hb ⊢
  linarith

end
end ImbalancedChen.P2OriginalI3CompactSourceLowerCount
