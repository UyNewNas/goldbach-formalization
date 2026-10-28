import ImbalancedChen.Part3MediumActualPsiPreliminaryDispersion
import Mathlib.Tactic

/-! Source only; uncompiled; zero formal credit.
Retain the ORIGINAL primitive first-factor gate BEFORE Cauchy. The earlier
unfiltered positive enlargement remains a valid bound, but is not silently
used as a primitive CRT/Shiu source. General beta keeps its actual L2 sum.
-/
namespace ImbalancedChen.Part3.MediumPrimitivePsiSource20261028
noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3.MediumActualPsiPreliminaryDispersion20261028
open ImbalancedChen.Part3.MediumActualPreliminaryCauchy20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumCanonicalFixedBlock20261028
open ImbalancedChen.Part3.MediumOwnedCanonicalReindex20261028
open ImbalancedChen.Part3.MediumInstalledFactorChoiceMap20261028

def primitiveOuter (atom : MediumAtom) (k : Key) : Finset OuterIndex :=
  (outerCarrier atom k).filter (fun t => t.1.Coprime atom.residue.natAbs)

def primitiveSmoothOuter (atom : MediumAtom) (k : Key) : Finset OuterIndex :=
  (smoothOuterCarrier atom k).filter (fun t => t.1.Coprime atom.residue.natAbs)

theorem blockSource_eq_primitive_outer (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hg : ∀ q ∈ factorCarrier atom.Q1,
      atom.gamma1 q ≠ 0 → q.Coprime atom.residue.natAbs) :
    blockSource atom z y k = ∑ t ∈ primitiveOuter atom k,
      outerCoefficient atom t * preliminaryRow atom z y k t.1 t.2.1 t.2.2 := by
  unfold blockSource
  symm
  apply sum_subset (filter_subset _ _)
  intro t ht hn
  have hq := (mem_product.mp ht).1
  have hbad : ¬t.1.Coprime atom.residue.natAbs := by
    intro hcop
    exact hn (mem_filter.mpr ⟨ht, hcop⟩)
  have hgamma : atom.gamma1 t.1 = 0 := by
    by_contra hne
    exact hbad (hg t.1 hq hne)
  simp [outerCoefficient, hgamma]

theorem primitiveOuter_subset_smooth {atom : MediumAtom} {k : Key}
    (hQ : 0 < atom.Q1) (hM : 0 < atom.V) :
    primitiveOuter atom k ⊆ primitiveSmoothOuter atom k := by
  intro t ht
  obtain ⟨ht, hcop⟩ := mem_filter.mp ht
  exact mem_filter.mpr ⟨outerCarrier_subset_smooth hQ hM ht, hcop⟩

/-- Export the actual smooth q support and primitive residue together. -/
theorem primitiveSmoothOuter_q_data {atom : MediumAtom} {k : Key}
    (hQ : 0 < atom.Q1) {t : OuterIndex} (ht : t ∈ primitiveSmoothOuter atom k) :
    atom.Q1 / 2 ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) ≤ 5 * atom.Q1 / 2 ∧
      t.1.Coprime atom.residue.natAbs ∧ 0 < t.1 := by
  obtain ⟨ht, hcop⟩ := mem_filter.mp ht
  have hq := (mem_product.mp ht).1
  obtain ⟨hlo, hhi⟩ := mem_Icc.mp hq
  have hloR : atom.Q1 / 2 ≤ (t.1 : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hlo)
  have hhiR : (t.1 : ℝ) ≤ 5 * atom.Q1 / 2 :=
    (show (t.1 : ℝ) ≤ (Nat.floor (5 * atom.Q1 / 2) : ℝ) by exact_mod_cast hhi).trans
      (Nat.floor_le (by linarith))
  have hqR : (0 : ℝ) < t.1 := lt_of_lt_of_le (by linarith) hloR
  exact ⟨hloR, hhiR, hcop, by exact_mod_cast hqR⟩

def primitiveQuadratic (atom : MediumAtom) (z y : ℝ) (k : Key) : ℝ :=
  ∑ t ∈ primitiveSmoothOuter atom k, jointPsi atom t *
    ‖preliminaryRow atom z y k t.1 t.2.1 t.2.2‖ ^ 2

theorem blockSource_norm_sq_le_primitivePsi (atom : MediumAtom) (z y : ℝ) (k : Key)
    (hQ : 0 < atom.Q1) (hM : 0 < atom.V)
    (hg : ∀ q ∈ factorCarrier atom.Q1,
      atom.gamma1 q ≠ 0 → q.Coprime atom.residue.natAbs) :
    ‖blockSource atom z y k‖ ^ 2 ≤
      (∑ t ∈ outerCarrier atom k, ‖outerCoefficient atom t‖ ^ 2) *
        primitiveQuadratic atom z y k := by
  rw [blockSource_eq_primitive_outer atom z y k hg]
  have hc := complex_finset_cauchy_norm_sq (primitiveOuter atom k) (outerCoefficient atom)
    (fun t => preliminaryRow atom z y k t.1 t.2.1 t.2.2)
  have hl2 : (∑ t ∈ primitiveOuter atom k, ‖outerCoefficient atom t‖ ^ 2) ≤
      ∑ t ∈ outerCarrier atom k, ‖outerCoefficient atom t‖ ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)
  have hquad : (∑ t ∈ primitiveOuter atom k,
      ‖preliminaryRow atom z y k t.1 t.2.1 t.2.2‖ ^ 2) ≤
      primitiveQuadratic atom z y k := by
    calc
      _ = ∑ t ∈ primitiveOuter atom k, jointPsi atom t *
          ‖preliminaryRow atom z y k t.1 t.2.1 t.2.2‖ ^ 2 := by
        apply sum_congr rfl
        intro t ht
        rw [jointPsi_eq_one_original hQ hM (mem_filter.mp ht).1, one_mul]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (primitiveOuter_subset_smooth hQ hM)
        (fun t ht hnot => mul_nonneg (jointPsi_nonneg atom t) (sq_nonneg _))
  exact hc.trans (mul_le_mul hl2 hquad (sum_nonneg fun _ _ => sq_nonneg _)
    (sum_nonneg fun _ _ => sq_nonneg _))

/-- Nonzero actual coefficient implies the COMPLETE preliminary tail d*r
is primitive for the moving residue. This is derived from the original
gamma2/gamma3 gates on actual choices, not assumed for all d or r. -/
theorem lambdaTrim_support_residue_product
    {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom)
    (z y : ℝ) (k : Key) (d r : ℕ)
    (hn : lambdaTrim atom z y k d r ≠ 0) :
    (d * r).Coprime atom.residue.natAbs := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hG1, hG2, hG3⟩ := hA
  by_contra hbad
  apply hn
  unfold lambdaTrim
  apply sum_eq_zero
  intro p hp
  have hpChoice := (mem_filter.mp hp).1
  obtain ⟨hd, hr, ha⟩ := choice_products hpChoice
  obtain ⟨hQ2, hQ3, hw⟩ := ha
  by_contra hterm
  change atom.gamma2 (p.u * p.s) * atom.gamma3 (p.v * p.t) ≠ 0 at hterm
  obtain ⟨h2, h3⟩ := mul_ne_zero_iff.mp hterm
  have hc2 := (hG2 (p.u * p.s) hQ2).2 h2
  have hc3 := (hG3 (p.v * p.t) hQ3).2 h3
  have hprod : d * r = (p.u * p.s) * (p.v * p.t) := by rw [← hd, ← hr]; ring
  have hcop : (d * r).Coprime atom.residue.natAbs := by
    rw [hprod]
    exact Nat.coprime_mul_iff_left.mpr ⟨hc2, hc3⟩
  exact hbad hcop

theorem lambdaTrim_support_residue
    {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom)
    (z y : ℝ) (k : Key) (d r : ℕ)
    (hn : lambdaTrim atom z y k d r ≠ 0) :
    d.Coprime atom.residue.natAbs ∧ r.Coprime atom.residue.natAbs :=
  Nat.coprime_mul_iff_left.mp (lambdaTrim_support_residue_product hA z y k d r hn)

end
end ImbalancedChen.Part3.MediumPrimitivePsiSource20261028
