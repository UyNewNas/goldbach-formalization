import ImbalancedChen.Part3OriginalGevreyPoissonPacket
import ImbalancedChen.Part3OriginalGevreyActualPsiSignedLatticeTail
import Mathlib.Tactic

/-!
Source only, uncompiled, zero formal credit.

The two imported source-only modules give, separately, exact Poisson for the
actual paperPsi and a uniform scalar norm tail. This file connects them. It
keeps the signed residue phase; it truncates the actual complex packet,
not a different smooth cutoff. The physical complete-modulus inequality
D*L <= 32*Q*R^2*S^2 supplies the tail cutoff, rather than a premise asserting
that the packet error is small. All fixed-power thresholds are uniform in
positive V,L and in the residue. Polynomially many weighted packets are
then summed with the same threshold. No medium or spectral conclusion is
assumed.
-/

noncomputable section

open Classical Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
open ImbalancedChen.Part3.OriginalGevreyActualPsiFourierIBP20261028
open ImbalancedChen.Part3.OriginalGevreyPoissonPacket20261028
open ImbalancedChen.Part3.OriginalGevreyActualPsiSignedLatticeTail20261028
open ImbalancedChen.Part3.OriginalPhysicalGevreyFrequencyScale20261028

namespace ImbalancedChen.Part3.OriginalPhysicalPoissonTruncation20261028

/-- Both signs, including zero (whose nonzero-mode coefficient is zero). -/
def signedWindow (H : ℕ) : Finset ℤ := Finset.Icc (-(H : ℤ)) H

@[simp] theorem mem_signedWindow (H : ℕ) (h : ℤ) :
    h ∈ signedWindow H ↔ h.natAbs ≤ H := by
  simp only [signedWindow, Finset.mem_Icc]
  constructor
  · intro hh
    have habs : |h| ≤ (H : ℤ) := abs_le.mpr hh
    have hcast : (h.natAbs : ℤ) ≤ (H : ℤ) := by
      simpa only [Int.natCast_natAbs] using habs
    exact_mod_cast hcast
  · intro hh
    have hcast : (h.natAbs : ℤ) ≤ (H : ℤ) := by exact_mod_cast hh
    rw [Int.natCast_natAbs] at hcast
    exact abs_le.mp hcast

/-- The actual complex omitted term retains the original residue phase. -/
def omittedPacket (t H x : ℝ) (h : ℤ) : ℂ :=
  if H < (h.natAbs : ℝ) then paperPsiNonzeroMode t x h else 0

/-- No lower bound H>=1 is needed: zero is excluded whenever H>=0. -/
theorem norm_omittedPacket {t H : ℝ} (ht : 0 < t) (hH : 0 ≤ H)
    (x : ℝ) (h : ℤ) :
    ‖omittedPacket t H x h‖ = actualPsiOmittedTerm t H h := by
  by_cases hh : h = 0
  · subst h
    simp [omittedPacket, actualPsiOmittedTerm, not_lt.mpr hH]
  · by_cases hcut : H < (h.natAbs : ℝ)
    · simp only [omittedPacket, actualPsiOmittedTerm, if_pos hcut,
        paperPsiNonzeroMode, if_neg hh, norm_mul, norm_smul,
        Real.norm_eq_abs, abs_of_pos ht, fourier_apply,
        Circle.norm_coe, mul_one]
    · simp [omittedPacket, actualPsiOmittedTerm, hcut]

/-- This summability comes from the genuine complex Poisson series and
therefore needs no asymptotic scale or cutoff condition. -/
theorem omittedPacket_summable_norm {t : ℝ} (ht : 0 < t) (H x : ℝ) :
    Summable (fun h : ℤ => ‖omittedPacket t H x h‖) := by
  apply (paperPsiNonzeroMode_summable_norm ht x).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro h
  by_cases hh : H < (h.natAbs : ℝ)
  · simp only [omittedPacket, if_pos hh, le_refl]
  · simp only [omittedPacket, if_neg hh, norm_zero]
    exact norm_nonneg _

/-- Truncation is an identity of the same absolutely summable series.
In particular it does not replace signed coefficients by their absolute
values before applying Poisson. -/
theorem nonzero_packet_truncation_identity {t : ℝ} (ht : 0 < t)
    (H : ℕ) (x : ℝ) :
    (∑' h : ℤ, paperPsiNonzeroMode t x h) -
        (∑ h ∈ signedWindow H, paperPsiNonzeroMode t x h) =
      ∑' h : ℤ, omittedPacket t H x h := by
  have hf := (paperPsiNonzeroMode_summable_norm ht x).of_norm
  have hg := (omittedPacket_summable_norm ht (H : ℝ) x).of_norm
  have hfinite :
      (∑' h : ℤ, paperPsiNonzeroMode t x h - omittedPacket t H x h) =
        ∑ h ∈ signedWindow H, paperPsiNonzeroMode t x h := by
    calc
      _ = ∑ h ∈ signedWindow H,
          (paperPsiNonzeroMode t x h - omittedPacket t H x h) := by
        apply tsum_eq_sum
        intro h hh
        have hn : H < h.natAbs := by
          simpa only [mem_signedWindow, not_le] using hh
        have hnR : (H : ℝ) < (h.natAbs : ℝ) := by exact_mod_cast hn
        simp only [omittedPacket, if_pos hnR, sub_self]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro h hh
        have hn : h.natAbs ≤ H := (mem_signedWindow H h).mp hh
        have hnR : (h.natAbs : ℝ) ≤ (H : ℝ) := by exact_mod_cast hn
        simp only [omittedPacket, if_neg (not_lt.mpr hnR), sub_zero]
  rw [hf.tsum_sub hg] at hfinite
  linear_combination hfinite

/-- Finite original residue count minus its exact zero mode and retained
signed frequencies. All occurrences use the constructed paperPsi. -/
def finitePacketError (V : ℝ) (L : ℕ) (b : ℤ) (H : ℕ) : ℂ :=
  (∑ m ∈ paperPsiNaturalCarrier V,
      if Int.ModEq L (m : ℤ) b then scaledPaperPsi V m else 0) -
    ((V / (L : ℝ)) • (𝓕 paperPsiComplex) 0 +
      ∑ h ∈ signedWindow H,
        paperPsiNonzeroMode (V / (L : ℝ)) ((b : ℝ) / L) h)

/-- The residual of the actual finite natural-point packet is exactly
its omitted Fourier series, for every integer residue representative. -/
theorem finitePacketError_eq_omitted {V : ℝ} (hV : 0 < V)
    {L : ℕ} (hL : 0 < L) (b : ℤ) (H : ℕ) :
    finitePacketError V L b H =
      ∑' h : ℤ,
        omittedPacket (V / (L : ℝ)) H ((b : ℝ) / L) h := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  unfold finitePacketError
  rw [paperPsi_finite_residue_poisson_packet hV hL b]
  have he := nonzero_packet_truncation_identity (div_pos hV hLr) H
    ((b : ℝ) / L)
  linear_combination he

/-- Removing the phase costs exactly the scalar omitted norm tail, with
no assumption H>=1 and no relation L<=V or L<=x. -/
theorem norm_finitePacketError_le_signedTail {V : ℝ} (hV : 0 < V)
    {L : ℕ} (hL : 0 < L) (b : ℤ) (H : ℕ) :
    ‖finitePacketError V L b H‖ ≤
      actualPsiSignedTail (V / (L : ℝ)) H := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have ht := div_pos hV hLr
  rw [finitePacketError_eq_omitted hV hL b H]
  calc
    _ ≤ ∑' h : ℤ,
        ‖omittedPacket (V / (L : ℝ)) H ((b : ℝ) / L) h‖ :=
      norm_tsum_le_tsum_norm (omittedPacket_summable_norm ht _ _)
    _ = _ := by
      apply tsum_congr
      intro h
      exact norm_omittedPacket ht (Nat.cast_nonneg H) _ h

/-- The physical complete-modulus bound gives the original logarithmic
cutoff directly. `band` may be zero; only positive scales are required. -/
theorem physicalH_scalar_cutoff {band Q R S V L : ℝ} {D : ℕ}
    (hband : 0 ≤ band) (hQ : 0 < Q) (hR : 0 < R) (hS : 0 < S)
    (hV : 0 < V) (hL : 0 < L) (hD : 0 < D)
    (hDL : (D : ℝ) * L ≤ 32 * Q * R ^ 2 * S ^ 2) :
    band / (V / L) ≤ (physicalH band Q R S V D : ℝ) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hden : 0 < (D : ℝ) * V := mul_pos hDr hV
  have hmul := mul_le_mul_of_nonneg_left hDL hband
  have hmulV := mul_le_mul_of_nonneg_right hmul hV.le
  have hgeo : 0 ≤ 32 * band * Q * R ^ 2 * S ^ 2 * V := by positivity
  calc
    band / (V / L) = band * L / V := by
      field_simp [hV.ne', hL.ne']
    _ ≤ 64 * band * Q * R ^ 2 * S ^ 2 / ((D : ℝ) * V) := by
      apply (div_le_div_iff₀ hV hden).2
      nlinarith only [hmulV, hgeo]
    _ ≤ (physicalH band Q R S V D : ℝ) := Nat.le_ceil _

/-- Fix the desired power first. The one threshold then works for every
scale, modulus, residue and physical geometry licensed by the lcm bound.
Polynomial l>x and any polynomial V are included without extra premises. -/
theorem physical_finite_packet_all_fixed_powers (A : ℝ) (hA : 0 ≤ A) :
    ∃ x0 : ℝ, 1 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
      ∀ (Q R S V : ℝ) (L D : ℕ) (b : ℤ),
        0 < Q → 0 < R → 0 < S → 0 < V → 0 < L → 0 < D →
        (D : ℝ) * L ≤ 32 * Q * R ^ 2 * S ^ 2 →
        ‖finitePacketError V L b
          (physicalH (Real.log x ^ 5) Q R S V D)‖ ≤ x ^ (-A) := by
  obtain ⟨x0, hx0, htail⟩ := actualPsiSignedTail_all_fixed_powers A hA
  refine ⟨x0, hx0, fun x hxx Q R S V L D b hQ hR hS hV hL hD hDL => ?_⟩
  have hx : 1 ≤ x := hx0.trans hxx
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hcut := physicalH_scalar_cutoff
    (pow_nonneg (Real.log_nonneg hx) 5) hQ hR hS hV hLr hD hDL
  exact (norm_finitePacketError_le_signedTail hV hL b _).trans
    (htail x hxx (V / (L : ℝ)) _ (div_pos hV hLr) hcut)

/-- The same physical cutoff also deals with a general real window H<1:
this is the actual complex signed packet, including the first h equal to plus/minus one,
with no artificial H>=1 restriction in the scalar-tail application. -/
theorem omitted_complex_all_fixed_powers (A : ℝ) (hA : 0 ≤ A) :
    ∃ x0 : ℝ, 1 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
      ∀ t H phase : ℝ, 0 < t → Real.log x ^ 5 / t ≤ H →
        ‖∑' h : ℤ, omittedPacket t H phase h‖ ≤ x ^ (-A) := by
  obtain ⟨x0, hx0, htail⟩ := actualPsiSignedTail_all_fixed_powers A hA
  refine ⟨x0, hx0, fun x hxx t H phase ht hcut => ?_⟩
  have hx : 1 ≤ x := hx0.trans hxx
  have hH : 0 ≤ H :=
    (div_nonneg (pow_nonneg (Real.log_nonneg hx) 5) ht.le).trans hcut
  calc
    _ ≤ ∑' h : ℤ, ‖omittedPacket t H phase h‖ :=
      norm_tsum_le_tsum_norm (omittedPacket_summable_norm ht H phase)
    _ = actualPsiSignedTail t H := by
      apply tsum_congr
      intro h
      exact norm_omittedPacket ht hH phase h
    _ ≤ x ^ (-A) := htail x hxx t H ht hcut

/-- Explicit outer aggregation: the polynomial exponent K is fixed before
x0. Only the actual coefficient l1 budget is required; no packet-error or
medium-estimate premise is inserted. This absorbs polynomially many
physical packets and polynomial coefficients with a single threshold. -/
theorem weighted_physical_packets_all_fixed_powers {ι : Type*}
    (A K : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K) :
    ∃ x0 : ℝ, 1 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
      ∀ (I : Finset ι) (c : ι → ℂ) (Q R S V : ι → ℝ)
        (L D : ι → ℕ) (b : ι → ℤ),
        (∀ i ∈ I, 0 < Q i ∧ 0 < R i ∧ 0 < S i ∧ 0 < V i ∧
          0 < L i ∧ 0 < D i ∧
          (D i : ℝ) * L i ≤ 32 * Q i * R i ^ 2 * S i ^ 2) →
        (∑ i ∈ I, ‖c i‖) ≤ x ^ K →
        ‖∑ i ∈ I, c i * finitePacketError (V i) (L i) (b i)
            (physicalH (Real.log x ^ 5) (Q i) (R i) (S i) (V i) (D i))‖
          ≤ x ^ (-A) := by
  obtain ⟨x0, hx0, hpacket⟩ :=
    physical_finite_packet_all_fixed_powers (A + K) (add_nonneg hA hK)
  refine ⟨x0, hx0, fun x hxx I c Q R S V L D b hgeom hmass => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one (hx0.trans hxx)
  have hpoint (i : ι) (hi : i ∈ I) :
      ‖finitePacketError (V i) (L i) (b i)
          (physicalH (Real.log x ^ 5) (Q i) (R i) (S i) (V i) (D i))‖ ≤
        x ^ (-(A + K)) := by
    obtain ⟨hQ, hR, hS, hV, hL, hD, hDL⟩ := hgeom i hi
    exact hpacket x hxx (Q i) (R i) (S i) (V i) (L i) (D i) (b i)
      hQ hR hS hV hL hD hDL
  calc
    _ ≤ ∑ i ∈ I,
        ‖c i * finitePacketError (V i) (L i) (b i)
          (physicalH (Real.log x ^ 5) (Q i) (R i) (S i) (V i) (D i))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ I, ‖c i‖ * x ^ (-(A + K)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hpoint i hi) (norm_nonneg _)
    _ = (∑ i ∈ I, ‖c i‖) * x ^ (-(A + K)) :=
      (Finset.sum_mul ..).symm
    _ ≤ x ^ K * x ^ (-(A + K)) :=
      mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg hxpos.le _)
    _ = x ^ (-A) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring

end ImbalancedChen.Part3.OriginalPhysicalPoissonTruncation20261028
