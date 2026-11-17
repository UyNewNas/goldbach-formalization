import ImbalancedChen.P3HBActualCompleteProductTrim
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-!
P3.6 — the actual manuscript full-product trim has ONE fixed finite-order
log-Euler jet bound at ALL positive physical scales.

This pays the previously missing quantitative bound for the LITERAL
eta(c * exp(sum of all six original log coordinates)), where c is the
positive physical product-of-chart-scales / T^(1-kappa0). The original
eta is zero below 1, one above 2, and smooth in between.

The key distinction is that zeroth order can be ONE on the upper plateau:
only strictly positive derivative orders vanish there. We bound EVERY
order 0 <= k <= K by a common constant >= 1, first on the genuine compact
[0, log 2] interval, then on both exact exterior plateaus. Translation
in log c makes this bound INDEPENDENT of c. No size-dependent factor c^k
is inserted.

Pinned paper: UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt,
section 2 and section 4 (F).

This is only one true component of physical W_T. It does not yield the
full W_T mixed 2S L1 bound, the growing-m threshold, Fourier tails,
same-integer-rho modulus discrepancy or the product-equals-T exception.
Lean v4.33.0-rc1, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3HBActualCompleteProductTrimUniform
noncomputable section
open ImbalancedChen.P3HBActualCompleteProductTrim
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBCanonicalGeometryDerivative

/-- C-infinity of the exact canonical logarithmic trim comes from the
actual smooth eta and exp, not a separately assumed jet family. -/
theorem baseTrimLogProfile_contDiff
    (eta : ℝ → ℂ) (heta : ContDiff ℝ ⊤ eta) :
    ContDiff ℝ ⊤ (baseTrimLogProfile eta) := by
  have he : ContDiff ℝ ⊤ (fun s : ℝ => Real.exp s) := by
    fun_prop
  unfold baseTrimLogProfile
  exact heta.comp he

/-- On the genuine closed transition window, each finite-order
logarithmic derivative has a finite norm ceiling. -/
private theorem oneOrder_window_bound
    (eta : ℝ → ℂ) (heta : ContDiff ℝ ⊤ eta) (k : ℕ) :
    ∃ B : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) (Real.log 2),
      ‖iteratedDeriv k (baseTrimLogProfile eta) s‖ ≤ B := by
  have hc : Continuous (iteratedDeriv k (baseTrimLogProfile eta)) :=
    (baseTrimLogProfile_contDiff eta heta).continuous_iteratedDeriv k le_top
  exact isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn

/-- Every fixed order has a GLOBAL ceiling >=1. Outside [0,log2]
the genuine trim is constant: order zero is 0 or 1, whereas all
positive-order actual jets are zero. -/
theorem baseTrimLogProfile_oneOrder_global_bound
    (eta : ℝ → ℂ) (heta : ContDiff ℝ ⊤ eta)
    (hsmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (hlarge : ∀ t : ℝ, 2 ≤ t → eta t = 1)
    (k : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ s : ℝ, ‖iteratedDeriv k (baseTrimLogProfile eta) s‖ ≤ C := by
  obtain ⟨B, hB⟩ := oneOrder_window_bound eta heta k
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro s
  by_cases hs : s ∈ Set.Icc (0 : ℝ) (Real.log 2)
  · exact (hB s hs).trans (le_max_right _ _)
  · have hout : s < 0 ∨ Real.log 2 < s := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hs
    have hzero : (0 : ℝ) ≤ max 1 B :=
      (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
    rcases hout with hlo | hhi
    · by_cases hk : k = 0
      · subst k
        have he : Real.exp s < 1 := by
          simpa using (Real.exp_strictMono hlo)
        have hv : baseTrimLogProfile eta s = 0 :=
          hsmall _ (le_of_lt he)
        simpa [iteratedDeriv_zero, hv] using hzero
      · have hv := baseTrim_jet_zero_low eta hsmall k
          (Nat.pos_of_ne_zero hk) s hlo
        simpa [hv] using hzero
    · by_cases hk : k = 0
      · subst k
        have he : (2 : ℝ) < Real.exp s := by
          simpa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
            (Real.exp_strictMono hhi)
        have hv : baseTrimLogProfile eta s = 1 :=
          hlarge _ (le_of_lt he)
        simpa [iteratedDeriv_zero, hv] using
          (le_max_left (1 : ℝ) B)
      · have hv := baseTrim_jet_zero_high eta hlarge k
          (Nat.pos_of_ne_zero hk) s hhi
        simpa [hv] using hzero

/-- One constant depends ONLY on the selected fixed eta and finite K,
not on the target, the original chart's physical scale or any position.
The k=0 upper plateau is correctly charged by C>=1. -/
theorem baseTrimLogProfile_uniform_finite_order
    (eta : ℝ → ℂ) (heta : ContDiff ℝ ⊤ eta)
    (hsmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (hlarge : ∀ t : ℝ, 2 ≤ t → eta t = 1)
    (K : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (k : ℕ), k ≤ K →
        ∀ (s : ℝ), ‖iteratedDeriv k (baseTrimLogProfile eta) s‖ ≤ C := by
  induction K with
  | zero =>
      obtain ⟨C, hC, hbound⟩ :=
        baseTrimLogProfile_oneOrder_global_bound eta heta hsmall hlarge 0
      refine ⟨C, hC, ?_⟩
      intro k hk s
      have h0 : k = 0 := by omega
      subst k
      exact hbound s
  | succ K ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      obtain ⟨B, hB, hnew⟩ :=
        baseTrimLogProfile_oneOrder_global_bound eta heta hsmall hlarge (K + 1)
      refine ⟨max C B, hC.trans (le_max_left _ _), ?_⟩
      intro k hk s
      by_cases hle : k ≤ K
      · exact (hbound k hle s).trans (le_max_left _ _)
      · have heq : k = K + 1 := by omega
        subst k
        exact (hnew s).trans (le_max_right _ _)

/-- All ACTUAL ordered and repeating six-coordinate jets of the literal
full-product trim share a finite-order ceiling independent of physical
c>0. Unlike the original group psi profile, k=0 is NOT zero above the
upper transition. This does not bound any other W_T multiplier. -/
theorem physicalTrim_uniform_ordered_jets
    (eta : ℝ → ℂ) (heta : ContDiff ℝ ⊤ eta)
    (hsmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (hlarge : ∀ t : ℝ, 2 ≤ t → eta t = 1)
    (K : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (c : ℝ), 0 < c →
        ∀ (axes : List (Fin 6)), axes.length ≤ K →
          ∀ (u : Fin 6 → ℝ),
            ‖originalOrderedAxisDeriv axes (physicalTrim eta c) u‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    baseTrimLogProfile_uniform_finite_order eta heta hsmall hlarge K
  refine ⟨C, hC, ?_⟩
  intro c hc axes hk u
  rw [physicalTrim_orderedDeriv_exact eta c axes u]
  rw [trimLogProfile_iteratedDeriv_translate eta c hc]
  exact hbound axes.length hk _

end
end ImbalancedChen.P3HBActualCompleteProductTrimUniform
