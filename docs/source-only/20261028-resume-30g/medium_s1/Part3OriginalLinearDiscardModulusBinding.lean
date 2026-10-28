import ImbalancedChen.Part3OriginalCompleteS123Ledger
import ImbalancedChen.Part3FactorFiberDivisor
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The still-unpaid LINEAR smooth-factor discard is grouped by its complete
physical modulus. The coefficients are actual filtered original factor
fibres, with their true tau_3 multiplicity and primitive residue support.
No squared mixed-tail model is identified with this original source.
-/

namespace ImbalancedChen.Part3.OriginalLinearDiscardModulusBinding20261028
noncomputable section
open Classical Finset
open scoped BigOperators
open MediumGlobalDyadicOwnership20261028 MediumActualPreliminaryCauchy20261028
open MediumActualPostSquareDeletion20261028
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def discardedFactorGamma (atom : MediumAtom) (receiver y : ℝ) (ell : ℕ) : ℂ :=
  ∑ r ∈ atom.physicalFactorFiber ell,
    if ¬Retained receiver y (r.2.1, r.2.2) then atom.complexFactorGamma r else 0

/-- A representative of the SAME complete modulus, used only to expose
the existing deleted count and unchanged primitive mean as one function. -/
def deletedModulusDiscrepancy (atom : MediumAtom) (ell : ℕ) : ℂ :=
  ∑ n ∈ atom.alphaCarrier, ∑ m ∈ atom.betaCarrier,
    atom.alpha n * atom.beta m * physicalDeletedKernel atom n ((ell, 1, 1), m)

theorem physicalDeletedKernel_eq_complete_modulus (atom : MediumAtom)
    (r : ℕ × ℕ × ℕ) (n m : ℕ) :
    physicalDeletedKernel atom n (r, m) =
      physicalDeletedKernel atom n ((complexFactorModulus r, 1, 1), m) := by
  simp only [physicalDeletedKernel, physicalMeanKernel, deletedCongruence,
    fullCongruence, complexFactorModulus, mul_one]

/-- The original row filter is independent of n and m. Exact finite
Fubini groups its original complex coefficient before taking any norm. -/
theorem discardedSource_eq_original_factor_sum (atom : MediumAtom) (receiver y : ℝ) :
    discardedSource atom receiver y = ∑ r ∈ atom.complexFactorLabels,
      (if ¬Retained receiver y (r.2.1, r.2.2) then atom.complexFactorGamma r else 0) *
        deletedModulusDiscrepancy atom (complexFactorModulus r) := by
  unfold discardedSource discardedRows
  simp only [MediumAtom.complexRowLabels, sum_filter, sum_product, rowModuli]
  apply sum_congr rfl
  intro r hr
  by_cases hb : ¬Retained receiver y (r.2.1, r.2.2)
  · simp only [if_pos hb]
    unfold deletedLinearTerm deletedModulusDiscrepancy
    rw [sum_comm]
    simp only [mul_sum]
    apply sum_congr rfl
    intro n hn
    apply sum_congr rfl
    intro m hm
    rw [physicalDeletedKernel_eq_complete_modulus atom r n m]
    ring
  · simp only [if_neg hb, zero_mul, sum_const_zero]

/-- Exact original LINEAR discard, with all physical modulus
multiplicities intact. This is independent of every S2/S3 tail model. -/
theorem discardedSource_eq_actual_modulus_fibres (atom : MediumAtom) (receiver y : ℝ) :
    discardedSource atom receiver y = ∑ ell ∈ atom.physicalFactorModuli,
      discardedFactorGamma atom receiver y ell * deletedModulusDiscrepancy atom ell := by
  rw [discardedSource_eq_original_factor_sum]
  have hf := sum_fiberwise_of_maps_to (s := atom.complexFactorLabels)
    (t := atom.physicalFactorModuli) (g := complexFactorModulus)
    (fun r hr => mem_image_of_mem _ hr)
    (fun r => (if ¬Retained receiver y (r.2.1, r.2.2) then atom.complexFactorGamma r else 0) *
      deletedModulusDiscrepancy atom (complexFactorModulus r))
  rw [← hf]
  apply sum_congr rfl
  intro ell hell
  rw [discardedFactorGamma, sum_mul]
  apply sum_congr rfl
  intro r hr
  rw [(mem_filter.mp hr).2]

private theorem factorGamma_norm_le_one {B : ℕ} {σ κ c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B σ κ c0 atom)
    {r : ℕ × ℕ × ℕ} (hr : r ∈ atom.complexFactorLabels) :
    ‖atom.complexFactorGamma r‖ ≤ 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3⟩ := hA
  obtain ⟨h1r, h23⟩ := mem_product.mp hr
  obtain ⟨h2r, h3r⟩ := mem_product.mp h23
  rw [MediumAtom.complexFactorGamma, norm_mul, norm_mul]
  calc
    _ ≤ 1 * 1 * 1 := mul_le_mul
      (mul_le_mul (h1 _ h1r).1 (h2 _ h2r).1 (norm_nonneg _) zero_le_one)
      (h3 _ h3r).1 (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num

/-- Actual filtered fibre multiplicity costs tau_3, not one. This
bound remains true with all complex signs and repeated factors. -/
theorem discardedFactorGamma_norm_le_tauThree {B : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (hA : MediumAdmissible B σ κ c0 atom)
    (receiver y : ℝ) (ell : ℕ) :
    ‖discardedFactorGamma atom receiver y ell‖ ≤ (fouvryTau 3 ell : ℝ) := by
  unfold discardedFactorGamma
  calc
    _ ≤ ∑ r ∈ atom.physicalFactorFiber ell,
        ‖if ¬Retained receiver y (r.2.1, r.2.2) then atom.complexFactorGamma r else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _r ∈ atom.physicalFactorFiber ell, (1 : ℝ) := by
      apply sum_le_sum
      intro r hr
      split_ifs
      · exact factorGamma_norm_le_one hA (mem_filter.mp hr).1
      · norm_num
    _ = ((atom.physicalFactorFiber ell).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast atom.card_physicalFactorFiber_le_tauThree hA ell

/-- Primitive Shiu is licensed by the actual gamma supports even for
the filtered complex fibre; primitivity is not assumed for every ell. -/
theorem discardedFactorGamma_support_primitive {B : ℕ} {σ κ c0 : ℝ}
    (atom : MediumAtom) (hA : MediumAdmissible B σ κ c0 atom)
    (receiver y : ℝ) (ell : ℕ) (hne : discardedFactorGamma atom receiver y ell ≠ 0) :
    ell.Coprime atom.residue.natAbs := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h1, h2, h3⟩ := hA
  by_contra hbad
  apply hne
  unfold discardedFactorGamma
  apply sum_eq_zero
  intro r hr
  by_cases hb : ¬Retained receiver y (r.2.1, r.2.2)
  · rw [if_pos hb]
    by_contra hg
    obtain ⟨h1r, h23⟩ := mem_product.mp (mem_filter.mp hr).1
    obtain ⟨h2r, h3r⟩ := mem_product.mp h23
    have hg' : atom.gamma1 r.1 * atom.gamma2 r.2.1 * atom.gamma3 r.2.2 ≠ 0 := hg
    have hn := mul_ne_zero_iff.mp hg'
    have hn12 := mul_ne_zero_iff.mp hn.1
    have hp := ((h1 _ h1r).2 hn12.1).mul_left ((h2 _ h2r).2 hn12.2)
    have hp3 := hp.mul_left ((h3 _ h3r).2 hn.2)
    apply hbad
    rw [← (mem_filter.mp hr).2]
    exact hp3
  · exact if_neg hb

end
end ImbalancedChen.Part3.OriginalLinearDiscardModulusBinding20261028
