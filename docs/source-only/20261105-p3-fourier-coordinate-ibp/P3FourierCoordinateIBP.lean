import ImbalancedChen.P3FourierRealComplex
import ImbalancedChen.P3FourierSignedSquare
import ImbalancedChen.P3FourierDPointwise
import Mathlib.Algebra.BigOperators.Fin

/-!
P3.6 / MANUSCRIPT-INTERNAL / SOURCE_ONLY / UNCOMPILED.
The exact 2S Fourier multiplier of the ACTUAL original Point d mixed derivative.
No imported distribution estimate, no surrogate frequency identity premise,
no claim that the original Point d measure has been normalized.
The only assumptions are finite-order smoothness and integrability needed
by the genuine pinned Fourier derivative theorem.
-/

namespace ImbalancedChen.P3FourierCoordinateIBP
noncomputable section

open MeasureTheory
open scoped Classical BigOperators FourierTransform RealInnerProductSpace
open P3FourierDPointwise P3FourierSubsetExpansion
open P3FourierFrechetIBP P3FourierSignedSquare
open P3FourierRealComplex P3U5ChartMixedL1Budget

/-- A single full Fourier phase coefficient, including each minus sign,
agrees with the physical signed-square monomial on the literal doubled S.
This lemma is purely finite algebra over the actual standard coordinates. -/
theorem frechet_phase_eq_signed_square {d : ℕ}
    (S : Finset (Fin d)) (eta : FourierSpace d) :
    (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (doubled S).length *
      (((∏ j : Fin (doubled S).length,
        (-innerSL ℝ) eta (subsetDirections S j) : ℝ)) : ℂ) =
      (-1 : ℂ) ^ S.card *
        complexMonomial S (physicalFrequency (fun i => eta i)) := by
  classical
  let phase : ℂ := -(2 * (Real.pi : ℂ) * Complex.I)
  let b : Fin (doubled S).length → ℝ :=
    fun j => (-innerSL ℝ) eta (subsetDirections S j)
  have hb (j : Fin (doubled S).length) :
      b j = -(eta ((doubled S)[j])) := by
    simp [b, subsetDirections, inner_basisDirection]
  have hterm (j : Fin (doubled S).length) :
      phase * ((b j : ℝ) : ℂ) =
        coordinateWave (fun i => eta i) ((doubled S)[j]) := by
    dsimp [phase]
    rw [hb]
    exact coordinateWave_from_real_phase (fun i => eta i) ((doubled S)[j])
  have hcast :
      (((∏ j : Fin (doubled S).length, b j : ℝ)) : ℂ) =
        ∏ j : Fin (doubled S).length, ((b j : ℝ) : ℂ) := by
    norm_cast
  change phase ^ (doubled S).length *
      (((∏ j : Fin (doubled S).length, b j : ℝ)) : ℂ) = _
  calc
    phase ^ (doubled S).length *
        (((∏ j : Fin (doubled S).length, b j : ℝ)) : ℂ) =
      (∏ j : Fin (doubled S).length, phase) *
        (∏ j : Fin (doubled S).length, ((b j : ℝ) : ℂ)) := by
          rw [hcast, Finset.prod_const, Fintype.card_fin]
    _ = ∏ j : Fin (doubled S).length, phase * ((b j : ℝ) : ℂ) := by
      rw [Finset.prod_mul_distrib]
    _ = ((doubled S).map
        (coordinateWave (fun i => eta i))).prod := by
      rw [← Fin.prod_univ_fun_getElem]
      apply Finset.prod_congr rfl
      intro j hj
      exact hterm j
    _ = (-1 : ℂ) ^ S.card *
        complexMonomial S (physicalFrequency (fun i => eta i)) :=
          doubled_wave_finset S (fun i => eta i)

/-- Genuine Fourier transform of the ORIGINAL mixed derivative, with
the physical signed-square coefficient. The hypotheses contain no Fourier
identity and no desired majorant, only ordinary ContDiff and integrability
of the actual complex chart derivatives. -/
theorem actual_mixed_fourier_signed {d : ℕ}
    (w : P3AffineTransitionJets.Point d → ℝ)
    (S : Finset (Fin d))
    (hsmooth : ContDiff ℝ ((doubled S).length : ℕ∞) (chartLift w))
    (hintegrable : ∀ k : ℕ, k ≤ (doubled S).length →
      Integrable (iteratedFDeriv ℝ k (complexChartLift w)))
    (eta : FourierSpace d) :
    𝓕 (actualMixedFamily w S) eta =
      ((-1 : ℂ) ^ S.card *
        complexMonomial S (physicalFrequency (fun i => eta i))) *
          𝓕 (complexChartLift w) eta := by
  have hFourier := actualMixed_fourier_frechet w S hsmooth hintegrable eta
  have hphase := frechet_phase_eq_signed_square S eta
  -- Convert the REAL scalar product to complex scalar multiplication.
  -- The real-linear Fourier theorem is not replaced by a complex derivative.
  calc
    𝓕 (actualMixedFamily w S) eta =
        (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (doubled S).length *
          (((∏ j : Fin (doubled S).length,
            (-innerSL ℝ) eta (subsetDirections S j) : ℝ)) : ℂ) *
            𝓕 (complexChartLift w) eta := by
        simpa only [← Complex.coe_smul, smul_eq_mul, mul_assoc] using hFourier
    _ = ((-1 : ℂ) ^ S.card *
          complexMonomial S (physicalFrequency (fun i => eta i))) *
          𝓕 (complexChartLift w) eta := by rw [hphase]

/-- Unlike the previously conditional CoordinateFourierIBP interface, this
gives the genuine identity for every subset, on the explicit smooth
and integrable domain of the actual original physical weight. -/
theorem actual_coordinate_fourierIBP {d : ℕ}
    (w : P3AffineTransitionJets.Point d → ℝ)
    (hsmooth : ∀ S : Finset (Fin d),
      ContDiff ℝ ((doubled S).length : ℕ∞) (chartLift w))
    (hintegrable : ∀ S : Finset (Fin d), ∀ k : ℕ,
      k ≤ (doubled S).length →
        Integrable (iteratedFDeriv ℝ k (complexChartLift w)))
    (eta : FourierSpace d) :
    CoordinateFourierIBP d (actualMixedFamily w) eta := by
  intro S
  have hz :
      𝓕 (actualMixedFamily w ∅) eta =
        𝓕 (complexChartLift w) eta := by
    have h := actualMixed_fourier_signed w ∅
      (hsmooth ∅) (hintegrable ∅) eta
    simpa using h
  have hS := actual_mixed_fourier_signed w S
    (hsmooth S) (hintegrable S) eta
  rw [hS, hz]
  have hsquare : (-1 : ℂ) ^ S.card * (-1 : ℂ) ^ S.card = 1 := by
    calc
      _ = (-1 : ℂ) ^ (2 * S.card) := by
        rw [← pow_add]
        congr 1
        omega
      _ = 1 := by simp [pow_mul]
  calc
    (-1 : ℂ) ^ S.card *
      (((-1 : ℂ) ^ S.card *
        complexMonomial S (physicalFrequency (fun i => eta i))) *
          𝓕 (complexChartLift w) eta) =
        ((-1 : ℂ) ^ S.card * (-1 : ℂ) ^ S.card) *
          (complexMonomial S (physicalFrequency (fun i => eta i)) *
            𝓕 (complexChartLift w) eta) := by ring
    _ = complexMonomial S (physicalFrequency (fun i => eta i)) *
            𝓕 (complexChartLift w) eta := by rw [hsquare, one_mul]

/-- Pointwise (F) numerator paid by actual 2S L1 derivatives, not by an
unproved Fourier-IBP premise. Point/Euclidean measure alignment and the
physical W_T family admission remain separate internal obligations. -/
theorem actual_mixed_physical_product_bound {d : ℕ}
    (w : P3AffineTransitionJets.Point d → ℝ)
    (hsmooth : ∀ S : Finset (Fin d),
      ContDiff ℝ ((doubled S).length : ℕ∞) (chartLift w))
    (hintegrable : ∀ S : Finset (Fin d), ∀ k : ℕ,
      k ≤ (doubled S).length →
        Integrable (iteratedFDeriv ℝ k (complexChartLift w)))
    (eta : FourierSpace d) :
    physicalDenom (physicalFrequency (fun i => eta i)) *
      ‖𝓕 (actualMixedFamily w ∅) eta‖ ≤
        derivativeD d (actualMixedFamily w) := by
  exact actual_chart_D_pointwise w eta
    (actual_coordinate_fourierIBP w hsmooth hintegrable eta)

/-- The corresponding pointwise inverse-product bound; no uniform
arithmetical modulus estimate is asserted. -/
theorem actual_mixed_physical_decay {d : ℕ}
    (w : P3AffineTransitionJets.Point d → ℝ)
    (hsmooth : ∀ S : Finset (Fin d),
      ContDiff ℝ ((doubled S).length : ℕ∞) (chartLift w))
    (hintegrable : ∀ S : Finset (Fin d), ∀ k : ℕ,
      k ≤ (doubled S).length →
        Integrable (iteratedFDeriv ℝ k (complexChartLift w)))
    (eta : FourierSpace d) :
    ‖𝓕 (actualMixedFamily w ∅) eta‖ ≤
      derivativeD d (actualMixedFamily w) /
        physicalDenom (physicalFrequency (fun i => eta i)) := by
  exact physical_product_decay d (actualMixedFamily w) eta
    (actual_coordinate_fourierIBP w hsmooth hintegrable eta)

end
end ImbalancedChen.P3FourierCoordinateIBP
