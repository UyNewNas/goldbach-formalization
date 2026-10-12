import ImbalancedChen.ActualPrimeIcoCellTestFunctions
import ImbalancedChen.PrimeOwnCubeAffineGates

/-!
# Actual own-cube residual integrals on Ico cells

The cell has its original half-open ownership. The proved arithmetic
residual error is combined with the actual mixed-gate prime integral.
Both level-dependent own-cube indicators remain in every difference.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology MeasureTheory Set
open scoped Classical BigOperators

def primeOwnCubeIcoIntegral {k r : ℕ} (a b lambda : ℝ) (m : ℕ)
    (j : Fin (k + 1) → Fin (m + 1))
    (L : Fin r → (Fin (k + 1) → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) : ℝ :=
  ∫ t in logPrimeMeshCell a b m j ∩
      primeAffineGateRegion (primeOwnCubeGateForms L) (primeOwnCubeGateBounds lambda c),
    primeTupleMinusProfile lambda t * ∏ i, 1 / t i

def primeOwnCubeGatedProfile {k : ℕ} (lambda : ℝ) (t : Fin (k + 1) → ℝ) : ℝ :=
  if primeTupleOwnCubeForm t < lambda then primeTupleMinusProfile lambda t else 0

private theorem measurableSet_ownCubeGate (k : ℕ) (lambda : ℝ) :
    MeasurableSet {t : Fin (k + 1) → ℝ | primeTupleOwnCubeForm t < lambda} := by
  exact (isOpen_lt (by unfold primeTupleOwnCubeForm; fun_prop)
    (continuous_const : Continuous (fun _ : Fin (k + 1) → ℝ => lambda))).measurableSet

/-- This identity keeps each strict own-cube indicator inside the same
Ico cell and caller region. -/
theorem primeOwnCubeIcoIntegral_eq_gated {k r : ℕ} (a b lambda : ℝ) (m : ℕ)
    (j : Fin (k + 1) → Fin (m + 1))
    (L : Fin r → (Fin (k + 1) → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) :
    primeOwnCubeIcoIntegral a b lambda m j L c =
      ∫ t in logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c,
        primeOwnCubeGatedProfile lambda t * ∏ i, 1 / t i := by
  have hset : logPrimeMeshCell a b m j ∩
      primeAffineGateRegion (primeOwnCubeGateForms L) (primeOwnCubeGateBounds lambda c) =
      (logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c) ∩
        {t | primeTupleOwnCubeForm t < lambda} := by
    ext t
    simp only [mem_inter_iff, mem_primeOwnCubeGateRegion, mem_ofPred_eq]
    tauto
  rw [primeOwnCubeIcoIntegral, hset, ← setIntegral_indicator (measurableSet_ownCubeGate k lambda)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    by_cases hg : primeTupleOwnCubeForm t < lambda <;>
      simp [Set.indicator, primeOwnCubeGatedProfile, hg])

theorem integrableOn_primeOwnCubeGatedProfile_IcoCell {k r : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (lambda : ℝ) (m : ℕ)
    (j : Fin (k + 1) → Fin (m + 1))
    (L : Fin r → (Fin (k + 1) → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) :
    IntegrableOn (fun t => primeOwnCubeGatedProfile lambda t * ∏ i, 1 / t i)
      (logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c) := by
  have hf := (integrableOn_logPrimeBox_test_cube ha (primeTupleMinusProfile lambda)
    (continuousOn_primeTupleMinusProfile ha lambda)).mono_set
      (show logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c ⊆
        logPrimeBox (fun _ : Fin (k + 1) => a) (fun _ => b) from
        fun _ hx => logPrimeMeshCell_subset_box hab m j hx.1)
  have heq : (fun t : Fin (k + 1) → ℝ => primeOwnCubeGatedProfile lambda t * ∏ i, 1 / t i) =
      {t : Fin (k + 1) → ℝ | primeTupleOwnCubeForm t < lambda}.indicator
        (fun t => primeTupleMinusProfile lambda t * ∏ i, 1 / t i) := by
    funext t
    by_cases hg : primeTupleOwnCubeForm t < lambda <;>
      simp [Set.indicator, primeOwnCubeGatedProfile, hg]
  rw [heq]
  exact hf.indicator (measurableSet_ownCubeGate k lambda)

theorem primeOwnCubeIcoIntegral_sub_eq_integral {k r : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (lambdaOld lambdaNew : ℝ) (m : ℕ)
    (j : Fin (k + 1) → Fin (m + 1))
    (L : Fin r → (Fin (k + 1) → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ) :
    primeOwnCubeIcoIntegral a b lambdaNew m j L c -
      primeOwnCubeIcoIntegral a b lambdaOld m j L c =
      ∫ t in logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c,
        (primeOwnCubeGatedProfile lambdaNew t - primeOwnCubeGatedProfile lambdaOld t) *
          ∏ i, 1 / t i := by
  rw [primeOwnCubeIcoIntegral_eq_gated, primeOwnCubeIcoIntegral_eq_gated,
    ← integral_sub (integrableOn_primeOwnCubeGatedProfile_IcoCell ha hab lambdaNew m j L c)
      (integrableOn_primeOwnCubeGatedProfile_IcoCell ha hab lambdaOld m j L c)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by ring)

/-- The actual normalized minus residual on one fixed cell converges
without assuming positivity of the finite lower sieve density. -/
theorem tendsto_actualPrimeBoxOwnCubeMinusSum_IcoCell_affineGates
    (k : ℕ) {r : ℕ} (a b lambda : ℝ) (ha : 0 < a) (hab : a < b)
    (m : ℕ) (j : Fin (k + 1) → Fin (m + 1))
    (L : Fin r → (Fin (k + 1) → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (hL : ∀ i, L i ≠ 0) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ b ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => actualPrimeBoxOwnCubeMinusSum k N (cap N) a b lambda
      (logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (primeOwnCubeIcoIntegral a b lambda m j L c)) := by
  have herror := tendsto_actualPrimeBoxOwnCubeMinus_error k a b lambda ha hab
    (logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c) cap hcap
  have hfixed := (tendsto_actualPrimeBoxTestSum_cube_IcoCell_affineGates ha hab m j
    (primeOwnCubeGateForms L) (primeOwnCubeGateBounds lambda c)
    (primeOwnCubeGateForms_ne_zero L hL)
    (primeTupleMinusProfile lambda) (continuousOn_primeTupleMinusProfile ha lambda)).mono_left
      (show (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) ≤ atTop from inf_le_left)
  have hind : (logPrimeMeshCell a b m j ∩
      primeAffineGateRegion (primeOwnCubeGateForms L) (primeOwnCubeGateBounds lambda c)).indicator
        (primeTupleMinusProfile lambda) =
      (fun t => if t ∈ logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c then
        (if primeTupleOwnCubeForm t < lambda then primeTupleMinusProfile lambda t else 0) else 0) := by
    funext t
    by_cases hc : t ∈ logPrimeMeshCell a b m j <;>
      by_cases hR : t ∈ primeAffineGateRegion L c <;>
      by_cases hg : primeTupleOwnCubeForm t < lambda <;>
      simp [Set.indicator, mem_primeOwnCubeGateRegion, hc, hR, hg]
  rw [hind] at hfixed
  have hh := herror.add hfixed
  change Tendsto _ _ (𝓝 (0 + primeOwnCubeIcoIntegral a b lambda m j L c)) at hh
  rw [zero_add] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun N : ℕ => by
    dsimp only
    simp only [mem_inter_iff, ite_and, sub_add_cancel])

/-- New and old own-cube gates are kept separately in the actual
difference; no level comparison is required for this limit. -/
theorem tendsto_actualPrimeBoxOwnCubeMinus_difference_IcoCell_affineGates
    (k : ℕ) {r : ℕ} (a b lambdaOld lambdaNew : ℝ) (ha : 0 < a) (hab : a < b)
    (m : ℕ) (j : Fin (k + 1) → Fin (m + 1))
    (L : Fin r → (Fin (k + 1) → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (hL : ∀ i, L i ≠ 0) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ b ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualPrimeBoxOwnCubeMinusSum k N (cap N) a b lambdaNew
        (logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c) -
      actualPrimeBoxOwnCubeMinusSum k N (cap N) a b lambdaOld
        (logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (primeOwnCubeIcoIntegral a b lambdaNew m j L c -
        primeOwnCubeIcoIntegral a b lambdaOld m j L c)) := by
  exact (tendsto_actualPrimeBoxOwnCubeMinusSum_IcoCell_affineGates k a b lambdaNew ha hab
    m j L c hL cap hcap).sub (tendsto_actualPrimeBoxOwnCubeMinusSum_IcoCell_affineGates
      k a b lambdaOld ha hab m j L c hL cap hcap)

/-- Expanded arithmetic sum and a single integral of the two separately
gated profiles. This is the cell supplier for a finite actual selector. -/
theorem tendsto_actualPrimeBoxOwnCubeMinus_weighted_difference_IcoCell_affineGates
    (k : ℕ) {r : ℕ} (a b lambdaOld lambdaNew : ℝ) (ha : 0 < a) (hab : a < b)
    (m : ℕ) (j : Fin (k + 1) → Fin (m + 1))
    (L : Fin r → (Fin (k + 1) → ℝ) →L[ℝ] ℝ) (c : Fin r → ℝ)
    (hL : ∀ i, L i ≠ 0) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ b ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin (k + 1) => a) (fun _ => b),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c
          then actualPrimeTupleOwnCubeMinus N (cap N) lambdaNew p -
            actualPrimeTupleOwnCubeMinus N (cap N) lambdaOld p else 0))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (∫ t in logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c,
        (primeOwnCubeGatedProfile lambdaNew t - primeOwnCubeGatedProfile lambdaOld t) *
          ∏ i, 1 / t i)) := by
  rw [← primeOwnCubeIcoIntegral_sub_eq_integral ha hab lambdaOld lambdaNew m j L c]
  apply (tendsto_actualPrimeBoxOwnCubeMinus_difference_IcoCell_affineGates
    k a b lambdaOld lambdaNew ha hab m j L c hL cap hcap).congr'
  exact Eventually.of_forall (fun N => by
    dsimp only
    unfold actualPrimeBoxOwnCubeMinusSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    by_cases hp : actualPrimeTupleLog N p ∈ logPrimeMeshCell a b m j ∩ primeAffineGateRegion L c <;>
      simp [hp, mul_sub])

end

end ImbalancedChen
