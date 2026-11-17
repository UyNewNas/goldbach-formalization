import ImbalancedChen.P3HBOriginalGroupCoordinateMixed
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
P3.6 — the LITERAL full-product smooth trim from the frozen manuscript:
    eta((product p_i)/T^(1-kappa0)).
On one fixed original 6-position logarithmic chart this equals
    eta(c * exp(sum_i u_i)), c = (product R_i)/T^(1-kappa0) > 0.

Unlike the dyadic psi factor, the trim is 0 on the LOWER half-line
and 1 on the UPPER half-line: its zeroth derivative is NOT compactly
supported. Only positive-order jets vanish off the translated
transition strip. The real-valued physical eta is embedded in C.

Frozen manuscript UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt §2,
and §4 (F). Lean v4.33.0-rc1, Mathlib
e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

This file only pays literal trim chart identities and positive-order
support, not the complete W_T product Leibniz, a uniform T,m(N) bound,
Fourier L1/H, arithmetic discrepancy, or same-rho PP.
SOURCE_ONLY / NOT COMPILED / KERNEL UNVERIFIED.
-/

namespace ImbalancedChen.P3HBActualCompleteProductTrim
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBOriginalGroupCoordinateMixed
open ImbalancedChen.P3HBCanonicalGeometryDerivative

/-- Real manuscript eta represented in complex scalar weights without
changing the original physical product or adding a cutoff. -/
def physicalTrimReal (eta : ℝ → ℝ) (c : ℝ)
    (u : Fin 6 → ℝ) : ℂ :=
  (eta (c * Real.exp (originalGroupSum Finset.univ u)) : ℂ)

/-- The full-product trim on the six original LOG coordinates. -/
def physicalTrim (eta : ℝ → ℂ) (c : ℝ)
    (u : Fin 6 → ℝ) : ℂ :=
  eta (c * Real.exp (originalGroupSum Finset.univ u))

/-- Exact embedding of the paper's REAL eta; the same actual c is used. -/
theorem physicalTrimReal_eq_complex (eta : ℝ → ℝ) (c : ℝ)
    (u : Fin 6 → ℝ) :
    physicalTrimReal eta c u =
      physicalTrim (fun t : ℝ => (eta t : ℂ)) c u := rfl

def trimLogProfile (eta : ℝ → ℂ) (c s : ℝ) : ℂ :=
  eta (c * Real.exp s)

def baseTrimLogProfile (eta : ℝ → ℂ) (s : ℝ) : ℂ :=
  eta (Real.exp s)

/-- Positive physical c is a TRANSLATION, including for the noncompact
zeroth-order eta profile. -/
theorem trimLogProfile_eq_translate (eta : ℝ → ℂ)
    (c : ℝ) (hc : 0 < c) (s : ℝ) :
    trimLogProfile eta c s =
      baseTrimLogProfile eta (s + Real.log c) := by
  unfold trimLogProfile baseTrimLogProfile
  rw [Real.exp_add, Real.exp_log hc]
  congr 1
  ring

/-- Translation commutes with EVERY actual scalar iterated derivative. -/
theorem trimLogProfile_iteratedDeriv_translate (eta : ℝ → ℂ)
    (c : ℝ) (hc : 0 < c) (k : ℕ) (s : ℝ) :
    iteratedDeriv k (trimLogProfile eta c) s =
      iteratedDeriv k (baseTrimLogProfile eta) (s + Real.log c) := by
  have hfun :
      trimLogProfile eta c =
        (fun t : ℝ => baseTrimLogProfile eta (t + Real.log c)) := by
    funext t
    exact trimLogProfile_eq_translate eta c hc t
  rw [hfun]
  exact congrFun
    (iteratedDeriv_comp_add_const k (baseTrimLogProfile eta) (Real.log c)) s

/-- ALL six literal positional coordinates contribute one unit to
the logarithm of the COMPLETE product. The word may repeat an axis. -/
theorem physicalTrim_orderedDeriv_exact
    (eta : ℝ → ℂ) (c : ℝ) (axes : List (Fin 6)) :
    ∀ u : Fin 6 → ℝ,
      originalOrderedAxisDeriv axes (physicalTrim eta c) u =
        iteratedDeriv axes.length (trimLogProfile eta c)
          (originalGroupSum Finset.univ u) := by
  induction axes with
  | nil =>
      intro u
      simp [originalOrderedAxisDeriv, physicalTrim,
        trimLogProfile, iteratedDeriv_zero]
  | cons i rest ih =>
      intro u
      change actualAxisDeriv
        (originalOrderedAxisDeriv rest (physicalTrim eta c)) i u = _
      have hrest :
          originalOrderedAxisDeriv rest (physicalTrim eta c) =
            (fun v => iteratedDeriv rest.length (trimLogProfile eta c)
              (originalGroupSum Finset.univ v)) := by
        funext v
        exact ih v
      rw [hrest, actualAxisDeriv_comp_groupSum]
      simp [List.length_cons, iteratedDeriv_succ]

/-- Below the FULL physical product threshold, trim is exactly zero. -/
theorem physicalTrim_eq_zero_of_small
    (eta : ℝ → ℂ)
    (hsmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (c : ℝ) (u : Fin 6 → ℝ)
    (h : c * Real.exp (originalGroupSum Finset.univ u) ≤ 1) :
    physicalTrim eta c u = 0 := hsmall _ h

/-- Beyond twice the FULL physical threshold trim is exactly one,
not zero. This asymmetry is essential for its zeroth derivative. -/
theorem physicalTrim_eq_one_of_large
    (eta : ℝ → ℂ)
    (hlarge : ∀ t : ℝ, 2 ≤ t → eta t = 1)
    (c : ℝ) (u : Fin 6 → ℝ)
    (h : 2 ≤ c * Real.exp (originalGroupSum Finset.univ u)) :
    physicalTrim eta c u = 1 := hlarge _ h

private theorem baseTrim_eq_zero_low (eta : ℝ → ℂ)
    (hsmall : ∀ t : ℝ, t ≤ 1 → eta t = 0) :
    Set.EqOn (baseTrimLogProfile eta) (fun _ : ℝ => (0 : ℂ))
      (Set.Iio 0) := by
  intro s hs
  have he : Real.exp s < 1 := by
    simpa using (Real.exp_strictMono hs)
  change eta (Real.exp s) = 0
  exact hsmall _ (le_of_lt he)

private theorem baseTrim_eq_one_high (eta : ℝ → ℂ)
    (hlarge : ∀ t : ℝ, 2 ≤ t → eta t = 1) :
    Set.EqOn (baseTrimLogProfile eta) (fun _ : ℝ => (1 : ℂ))
      (Set.Ioi (Real.log 2)) := by
  intro s hs
  have he : (2 : ℝ) < Real.exp s := by
    simpa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
      (Real.exp_strictMono hs)
  change eta (Real.exp s) = 1
  exact hlarge _ (le_of_lt he)

/-- Higher derivatives of a literal constant are zero; k=0 is excluded. -/
private theorem iteratedDeriv_const_pos
    (z : ℂ) (k : ℕ) (hk : 0 < k) (s : ℝ) :
    iteratedDeriv k (fun _ : ℝ => z) s = 0 := by
  cases k with
  | zero => omega
  | succ n => simp [iteratedDeriv_succ]

/-- The LOWER plateau has no positive-order logarithmic derivatives. -/
theorem baseTrim_jet_zero_low (eta : ℝ → ℂ)
    (hsmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (k : ℕ) (hk : 0 < k) (s : ℝ) (hs : s < 0) :
    iteratedDeriv k (baseTrimLogProfile eta) s = 0 := by
  have heq := (iteratedDerivWithin_congr (n := k)
    (baseTrim_eq_zero_low eta hsmall)) s hs
  have hl := (iteratedDerivWithin_of_isOpen (n := k) isOpen_Iio) hs
  have hr := (iteratedDerivWithin_of_isOpen (n := k) isOpen_Iio) hs
  calc
    iteratedDeriv k (baseTrimLogProfile eta) s =
        iteratedDerivWithin k (baseTrimLogProfile eta) (Set.Iio 0) s := hl.symm
    _ = iteratedDerivWithin k (fun _ : ℝ => (0 : ℂ)) (Set.Iio 0) s := heq
    _ = iteratedDeriv k (fun _ : ℝ => (0 : ℂ)) s := hr
    _ = 0 := iteratedDeriv_const_pos 0 k hk s

/-- The UPPER plateau is one, so ONLY positive-order jets vanish there.
The zeroth-order trim remains one and cannot be discarded. -/
theorem baseTrim_jet_zero_high (eta : ℝ → ℂ)
    (hlarge : ∀ t : ℝ, 2 ≤ t → eta t = 1)
    (k : ℕ) (hk : 0 < k) (s : ℝ) (hs : Real.log 2 < s) :
    iteratedDeriv k (baseTrimLogProfile eta) s = 0 := by
  have heq := (iteratedDerivWithin_congr (n := k)
    (baseTrim_eq_one_high eta hlarge)) s hs
  have hl := (iteratedDerivWithin_of_isOpen (n := k) isOpen_Ioi) hs
  have hr := (iteratedDerivWithin_of_isOpen (n := k) isOpen_Ioi) hs
  calc
    iteratedDeriv k (baseTrimLogProfile eta) s =
        iteratedDerivWithin k (baseTrimLogProfile eta)
          (Set.Ioi (Real.log 2)) s := hl.symm
    _ = iteratedDerivWithin k (fun _ : ℝ => (1 : ℂ))
          (Set.Ioi (Real.log 2)) s := heq
    _ = iteratedDeriv k (fun _ : ℝ => (1 : ℂ)) s := hr
    _ = 0 := iteratedDeriv_const_pos 1 k hk s

/-- Any positive-order REAL six-coordinate trim derivative vanishes
outside the genuine translated full-product transition strip.
No false conclusion is made for the k=0 upper plateau. -/
theorem physicalTrim_orderedDeriv_zero_outside
    (eta : ℝ → ℂ)
    (hsmall : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (hlarge : ∀ t : ℝ, 2 ≤ t → eta t = 1)
    (c : ℝ) (hc : 0 < c)
    (axes : List (Fin 6)) (hk : 0 < axes.length)
    (u : Fin 6 → ℝ)
    (hout : originalGroupSum Finset.univ u + Real.log c ∈
      Set.Iio 0 ∪ Set.Ioi (Real.log 2)) :
    originalOrderedAxisDeriv axes (physicalTrim eta c) u = 0 := by
  rw [physicalTrim_orderedDeriv_exact eta c axes u]
  rw [trimLogProfile_iteratedDeriv_translate eta c hc]
  rcases Set.mem_union.mp hout with hl | hr
  · exact baseTrim_jet_zero_low eta hsmall axes.length hk _ hl
  · exact baseTrim_jet_zero_high eta hlarge axes.length hk _ hr

end
end ImbalancedChen.P3HBActualCompleteProductTrim
