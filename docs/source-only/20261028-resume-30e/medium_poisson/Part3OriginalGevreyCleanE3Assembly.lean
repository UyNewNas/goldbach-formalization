import ImbalancedChen.Part3OriginalGevreyPreliminaryE2Partition
import Mathlib.Tactic

/-!
Source only; uncompiled; zero formal credit.

The complete clean raw Poisson summand is now assembled, rather than
merely listing its phase/profile/denominator components. It equals V/d
times the independently defined typed E3 summand. Summing over the exact
clean carrier and dividing by original V gives E3/d. The entire nonclean
raw sum from the preceding partition remains a separate unchanged term.
No source binder, E2 conclusion or full-clean hypothesis is introduced.
-/

noncomputable section
open Classical Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3
open ImbalancedChen.Part3.OriginalGevreyActualPsiFourierIBP20261028
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
open ImbalancedChen.Part3.OriginalMediumPhysicalE3Block
open ImbalancedChen.Part3.OriginalMediumPhysicalE3RowReindex
open ImbalancedChen.Part3.OriginalGevreyPreliminaryE2Partition20261028

namespace ImbalancedChen.Part3.OriginalGevreyCleanE3Assembly20261028

theorem cleanCarrier_data {B : FixedBlock} {t : Index}
    (ht : t ∈ B.carrier) :
    0 < t.q ∧ 0 < t.w1 ∧ 0 < t.w2 ∧ t.h ≠ 0 := by
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp (carrier_subset_rawBox_image B ht)
  rcases r with ⟨q, w1, w2, n1, n2, h⟩
  simp only [rawBox, Finset.mem_product] at hr
  obtain ⟨hq, hw1, hw2, hn1, hn2, hh⟩ := hr
  have hq0 : (0 : ℝ) < q := B.q0_pos.trans_le
    (B.qLo_block.trans (by exact_mod_cast (Finset.mem_Icc.mp hq).1))
  have hfactor {Q : ℝ} (hQ : 0 < Q) {n : ℕ}
      (hn : n ∈ factorCarrier Q) : 0 < n :=
    (Nat.ceil_pos.mpr hQ).trans_le (Finset.mem_Icc.mp hn).1
  have hh0 : h ≠ 0 := by
    have hmem := (Finset.mem_filter.mp hh).2.1
    intro heq
    subst h
    simp at hmem
  change 0 < q ∧ 0 < w1 ∧ 0 < w2 ∧ h ≠ 0
  exact ⟨by exact_mod_cast hq0, hfactor B.rough_pos hw1, hfactor B.rough_pos hw2, hh0⟩

/-- Exact V/d normalization on the same physical complete lcm. -/
theorem cleanPoisson_scalar_eq {B : FixedBlock} {t : Index}
    (ht : t ∈ B.carrier) :
    (((B.atom.V / (fullPhysicalL B t : ℝ)) : ℝ) : ℂ) =
      (((B.atom.V / (B.d : ℝ)) : ℝ) : ℂ) /
        ((t.q * t.w1 * t.w2 : ℕ) : ℂ) := by
  have hc : B.clean t := (Finset.mem_filter.mp ht).2
  obtain ⟨hq, hw1, hw2, hh⟩ := cleanCarrier_data ht
  have hqC : (t.q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hdC : (B.d : ℂ) ≠ 0 := by exact_mod_cast B.d_pos.ne'
  have h1C : (t.w1 : ℂ) ≠ 0 := by exact_mod_cast hw1.ne'
  have h2C : (t.w2 : ℂ) ≠ 0 := by exact_mod_cast hw2.ne'
  rw [E3_clean_complete_lcm hc]
  push_cast
  field_simp [hqC, hdC, h1C, h2C]
  ring

/-- The original complete CRT residue, actual paperPsi Fourier profile,
positive q factor, both actual Lambda/alpha coefficients and the retained
slow phase all occur on the two sides of this equality. -/
theorem actual_clean_raw_summand_eq_V_div_d_E3 (B : FixedBlock) (z : ℝ)
    {t : Index} (ht : t ∈ B.carrier) :
    fullPhysicalTerm B z t =
      (((B.atom.V / (B.d : ℝ)) : ℝ) : ℂ) *
        ((actualBlock B z).coeff t * (actualBlock B z).weight t) := by
  have hc : B.clean t := (Finset.mem_filter.mp ht).2
  have hcompat := E3_clean_CRT_compatible hc
  obtain ⟨hq, hw1, hw2, hh⟩ := cleanCarrier_data ht
  have hphase := actual_E3_CRT_phase_eq_typed B ht
  have hscalar := cleanPoisson_scalar_eq ht
  have harg : (B.atom.V / (fullPhysicalL B t : ℝ)) * (t.h : ℝ) =
      (t.h : ℝ) * B.atom.V / ((t.q * B.d * t.w1 * t.w2 : ℕ) : ℝ) := by
    rw [E3_clean_complete_lcm hc]
    push_cast
    ring
  unfold fullPhysicalTerm
  rw [if_pos hcompat]
  unfold paperPsiNonzeroMode
  rw [if_neg hh, hphase]
  rw [Complex.real_smul, hscalar, harg]
  rw [actualBlock_coeff, actualBlock_weight]
  simp only [div_eq_mul_inv]
  ring

/-- Exact clean raw sum on the independently defined typed E3 carrier.
No compatibility or phase identity is supplied by the caller. -/
theorem actual_clean_raw_sum_eq_V_div_d_E3 (B : FixedBlock) (z : ℝ) :
    cleanPhysicalSum B z =
      (((B.atom.V / (B.d : ℝ)) : ℝ) : ℂ) * (actualBlock B z).E3 := by
  rw [cleanPhysicalSum_eq_E3_carrier]
  unfold FixedBlock.E3
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact actual_clean_raw_summand_eq_V_div_d_E3 B z
    (by simpa only [actualBlock_carrier] using ht)

/-- This is the manuscript E2 normalization: dividing the raw Poisson W
by original V yields E3/d, rather than E3 with an extra d denominator. -/
theorem actual_clean_raw_div_V_eq_E3_div_d (B : FixedBlock) (z : ℝ) :
    cleanPhysicalSum B z / (B.atom.V : ℂ) =
      (actualBlock B z).E3 / (B.d : ℂ) := by
  rw [actual_clean_raw_sum_eq_V_div_d_E3]
  have hV : (B.atom.V : ℂ) ≠ 0 := by exact_mod_cast B.V_pos.ne'
  have hd : (B.d : ℂ) ≠ 0 := by exact_mod_cast B.d_pos.ne'
  push_cast
  field_simp [hV, hd]
  ring

/-- Full actual raw block, with its entire nonclean general-D/root
payload still present. A clean-only E2 conclusion is not asserted. -/
theorem actual_full_raw_div_V_eq_E3_plus_nonclean (B : FixedBlock) (z : ℝ) :
    fullPhysicalSum B z / (B.atom.V : ℂ) =
      (actualBlock B z).E3 / (B.d : ℂ) +
        noncleanPhysicalSum B z / (B.atom.V : ℂ) := by
  rw [fullPhysicalSum_eq_clean_add_nonclean, add_div,
    actual_clean_raw_div_V_eq_E3_div_d]

end ImbalancedChen.Part3.OriginalGevreyCleanE3Assembly20261028
