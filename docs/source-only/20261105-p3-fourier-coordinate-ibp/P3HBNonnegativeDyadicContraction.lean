import ImbalancedChen.P3HBOriginalGroupTrimPolynomialAllOrder
import Mathlib.Tactic

/-!
P3.6 — derive the missing dyadic contraction from the ORIGINAL
nonnegative real-valued smooth dyadic partition, rather than adding a
second arbitrary norm assumption.

Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
§2 (exact smooth nonnegative dyadic partition), §4(F).

For the plateau cutoff f, put psi(t)=f(t)-f(2*t). We prove
0<=psi(t)<=1 from psi>=0 and the ORIGINAL two plateaux. The upper
bound does not require a new global monotonicity premise: on (1/2,1]
the two pieces psi(t)+psi(2*t) telescope to 1, and on (1,2)
psi(t/2)+psi(t) telescope to 1. Outside (1/2,2) psi=0.
For a genuinely real-valued complex chi this proves the actual
hpsi needed by the earlier polynomial bound.

This is a real mathematical reduction of the INTERNAL dyadic condition,
not a proof of existence/selection of the frozen manuscript's particular
C-infinity cutoff, faithful half-line eta extension, full W_T, Fourier
budget, arithmetic PP, or same-integer rho. SOURCE_ONLY, NOT COMPILED,
KERNEL NOT VERIFIED. No new theorem from outside the manuscript.
-/

namespace ImbalancedChen.P3HBNonnegativeDyadicContraction
noncomputable section
open ImbalancedChen.P3HBOriginalGroupTrimPolynomialAllOrder

/-- Nonnegativity of the actual dyadic difference and the two plateaux
already force amplitude at most one. No assumption f antitone is needed.
The translated scales t/2 and 2*t are the same original dyadic system. -/
theorem real_dyadic_piece_between_zero_one
    (f : ℝ → ℝ)
    (hsmall : ∀ t : ℝ, t ≤ 1 → f t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → f t = 0)
    (hnonneg : ∀ t : ℝ, 0 ≤ f t - f (2 * t))
    (t : ℝ) :
    0 ≤ f t - f (2 * t) ∧ f t - f (2 * t) ≤ 1 := by
  refine ⟨hnonneg t, ?_⟩
  by_cases hleft : t ≤ (1 / 2 : ℝ)
  · have h2 : 2 * t ≤ 1 := by linarith
    rw [hsmall t (by linarith), hsmall (2 * t) h2]
    norm_num
  · by_cases hright : 2 ≤ t
    · have h2 : 2 ≤ 2 * t := by linarith
      rw [hlarge t hright, hlarge (2 * t) h2]
      norm_num
    · by_cases hcenter : t ≤ 1
      · have hfour : 2 ≤ 2 * (2 * t) := by linarith
        have hnext := hnonneg (2 * t)
        have hzero : f (2 * (2 * t)) = 0 :=
          hlarge (2 * (2 * t)) hfour
        rw [hzero] at hnext
        have hone : f t = 1 := hsmall t hcenter
        rw [hone]
        linarith
      · have hhalf : t / 2 ≤ 1 := by linarith
        have hprev := hnonneg (t / 2)
        have hone : f (t / 2) = 1 := hsmall (t / 2) hhalf
        have hdouble : 2 * (t / 2) = t := by ring
        rw [hone, hdouble] at hprev
        have h2 : 2 ≤ 2 * t := by linarith
        have hzero : f (2 * t) = 0 := hlarge (2 * t) h2
        rw [hzero]
        linarith

/-- The preceding REAL nonnegative original partition yields exactly
the COMPLEX-valued hpsi required by the existing physical group source.
The equality chi(t)=ofReal(f(t)) is explicit: nonnegative is not defined
for an arbitrary complex-valued cutoff. -/
theorem complex_original_dyadic_contraction
    (f : ℝ → ℝ) (chi : ℝ → ℂ)
    (hreal : ∀ t : ℝ, chi t = (f t : ℂ))
    (hsmall : ∀ t : ℝ, t ≤ 1 → f t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → f t = 0)
    (hnonneg : ∀ t : ℝ, 0 ≤ f t - f (2 * t)) :
    ∀ t : ℝ, ‖chi t - chi (2 * t)‖ ≤ 1 := by
  intro t
  obtain ⟨hp, hu⟩ :=
    real_dyadic_piece_between_zero_one f hsmall hlarge hnonneg t
  rw [hreal t, hreal (2 * t)]
  have hcast : (f t : ℂ) - (f (2 * t) : ℂ) =
      ((f t - f (2 * t) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast]
  simpa [Complex.norm_real, abs_of_nonneg hp] using hu

/-- Feed the literal nonnegative ORIGINAL dyadic partition into the
ALREADY EXISTING actual original-group × single-complete-product-trim
ordered-polynomial theorem. No stand-in derivative, physical group,
extra arithmetic input, or independent hpsi premise is introduced.

The chosen actual f still needs to be exhibited from the manuscript's
admitted nonnegative C-infinity dyadic partition. This theorem does NOT
claim complete PP or a complete mixed W_T L1 bound. -/
theorem original_group_trim_polynomial_of_nonnegative_dyadic
    (f : ℝ → ℝ) (chi eta : ℝ → ℂ)
    (hreal : ∀ t : ℝ, chi t = (f t : ℂ))
    (hsmallReal : ∀ t : ℝ, t ≤ 1 → f t = 1)
    (hlargeReal : ∀ t : ℝ, 2 ≤ t → f t = 0)
    (hnonneg : ∀ t : ℝ, 0 ≤ f t - f (2 * t))
    (hchi : ContDiff ℝ ⊤ chi) (heta : ContDiff ℝ ⊤ eta)
    (hetaSmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (hetaLarge : ∀ t : ℝ, 2 ≤ t → eta t = 1)
    (K : ℕ) :
    ∃ B Ceta : ℝ, 1 ≤ B ∧ 1 ≤ Ceta ∧
      ∀ (g k : ℕ) (c : Fin g → ℝ)
        (J : Fin g → Finset (Fin 6)), (∀ j, 0 < c j) →
        ∀ (s : ℝ), 0 < s →
        ∀ (axes : Fin k → Fin 6), k ≤ K →
        ∀ (u : Fin 6 → ℝ),
          ‖ImbalancedChen.P3HBOriginalGroupCoordinateMixed.originalOrderedAxisDeriv
                (List.ofFn axes)
              (ImbalancedChen.P3HBOriginalGroupPhysicalTrimFirst.originalGroupPhysicalTrim
                chi eta c J s) u‖ ≤
            (2 : ℝ) ^ k * (((g : ℝ) + 1) * B) ^ k * Ceta := by
  have hsmallC : ∀ t : ℝ, t ≤ 1 → chi t = 1 := by
    intro t ht
    rw [hreal t, hsmallReal t ht]
    norm_num
  have hlargeC : ∀ t : ℝ, 2 ≤ t → chi t = 0 := by
    intro t ht
    rw [hreal t, hlargeReal t ht]
    norm_num
  exact originalGroupPhysicalTrim_ordered_polynomial
    chi eta hchi heta hsmallC hlargeC
    (complex_original_dyadic_contraction f chi hreal
      hsmallReal hlargeReal hnonneg)
    hetaSmall hetaLarge K

end
end ImbalancedChen.P3HBNonnegativeDyadicContraction
