import ImbalancedChen.Part3OriginalMediumS1SeparatedDivisorMean
import ImbalancedChen.Part3MediumCanonicalFixedBlock
import ImbalancedChen.Part3OriginalGevreyFinalPsi
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This binds the previous S1 ordinary-divisor budget to the literal
gamma2/gamma3 fixed block. The tau(d*w) bound is proved from a divisor
injection, not supplied as a field or a hypothesis. The q majorant is
the constructed paperPsi and its one-boundedness is proved upstream.

All geometric fields of the pre-existing physical FixedBlock are retained.
Its lambda and smooth fields are replaced by the actual canonical ones.
This is a coefficient/support instance, not a construction of the global
dyadic atlas or a statement that the previous commonMCount already uses
paperPsi: that count is still defined with CommonSmoothCutoff.
-/

namespace ImbalancedChen.Part3.OriginalMediumS1ActualCoefficientBinding

open Classical Finset
open scoped BigOperators FourierTransform
open OriginalMediumPhysicalE3Block OriginalMediumS1CommonMCount
open OriginalMediumS1WeightedRemainder OriginalMediumS1SeparatedDivisorMean
open OriginalMediumDoubleLambdaColorWindows20261028
open MediumInstalledFactorChoiceMap20261028 MediumInstalledSplitConverse20261028
open MediumCanonicalFixedBlock20261028 OriginalGevreyFinalPsi20261028

noncomputable section

theorem physical_product_of_choice (W : Block) (atom : MediumAtom)
    (z : ℝ) {w : ℕ} {p : Factor}
    (hp : p ∈ (W.factorData atom z).choices W.d w) :
    (physicalModuli p).1 * (physicalModuli p).2 = W.d * w := by
  obtain ⟨hd, hw, _⟩ := choice_products hp
  dsimp [physicalModuli]
  rw [← hd, ← hw]
  ring

/-- A fixed physical total d*w and its q2 divisor determine q3; the
canonical smooth/rough split then determines all four labelled factors. -/
theorem first_modulus_injective (W : Block) (atom : MediumAtom)
    (z : ℝ) (w : ℕ) :
    Set.InjOn (fun p : Factor => (physicalModuli p).1)
      ((W.factorData atom z).choices W.d w) := by
  intro p hp p' hp' heq
  have hsel := (Finset.mem_filter.mp (choice_mem_selected W atom z hp)).2
  have hq2 : (physicalModuli p).1 ≠ 0 := hsel.1
  have hprod := (physical_product_of_choice W atom z hp).trans
    (physical_product_of_choice W atom z hp').symm
  rw [← heq] at hprod
  have hq3 : (physicalModuli p).2 = (physicalModuli p').2 :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq2) hprod
  exact physicalModuli_injOn_choices W atom z w hp hp' (Prod.ext heq hq3)

theorem first_modulus_image_subset_divisors (W : Block) (atom : MediumAtom)
    (z : ℝ) (w : ℕ) :
    (((W.factorData atom z).choices W.d w).image
      (fun p : Factor => (physicalModuli p).1)) ⊆ (W.d * w).divisors := by
  intro q hq
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
  have hsel := (Finset.mem_filter.mp (choice_mem_selected W atom z hp)).2
  have hprod := physical_product_of_choice W atom z hp
  apply Nat.mem_divisors.mpr
  constructor
  · rw [← hprod]
    exact dvd_mul_right _ _
  · rw [← hprod]
    exact mul_ne_zero hsel.1 hsel.2.1

/-- Every labelled choice is charged to one actual divisor of d*w.
This retains prime powers and does not replace the source by a squarefree
or freely factorized surrogate. -/
theorem choices_card_le_divisors (W : Block) (atom : MediumAtom)
    (z : ℝ) (w : ℕ) :
    ((W.factorData atom z).choices W.d w).card ≤ (W.d * w).divisors.card := by
  calc
    _ = (((W.factorData atom z).choices W.d w).image
        (fun p : Factor => (physicalModuli p).1)).card :=
      (Finset.card_image_iff.mpr (first_modulus_injective W atom z w)).symm
    _ ≤ _ := Finset.card_le_card (first_modulus_image_subset_divisors W atom z w)

/-- The original gamma bounds pay each literal coefficient once. -/
theorem literal_lambda_norm_le_divisors (W : Block) (atom : MediumAtom)
    (z : ℝ) (w : ℕ)
    (hγ2 : ∀ q ∈ factorCarrier atom.Q2, ‖atom.gamma2 q‖ ≤ 1)
    (hγ3 : ∀ q ∈ factorCarrier atom.Q3, ‖atom.gamma3 q‖ ≤ 1) :
    ‖(W.factorData atom z).lambdaAt W.d w‖ ≤ tauR (W.d * w) := by
  unfold FactorData.lambdaAt
  calc
    _ ≤ ∑ p ∈ (W.factorData atom z).choices W.d w,
        ‖(W.factorData atom z).term p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ (W.factorData atom z).choices W.d w, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨_, _, ha⟩ := choice_products hp
      change p.u * p.s ∈ factorCarrier atom.Q2 ∧
        p.v * p.t ∈ factorCarrier atom.Q3 ∧ _ at ha
      change ‖atom.gamma2 (p.u * p.s) * atom.gamma3 (p.v * p.t)‖ ≤ 1
      rw [norm_mul]
      exact (mul_le_mul (hγ2 _ ha.1) (hγ3 _ ha.2.1)
        (norm_nonneg _) (by norm_num)).trans_eq (by ring)
    _ = (((W.factorData atom z).choices W.d w).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast choices_card_le_divisors W atom z w

/-- The tau-bound premise of the previous S1 budget is now supplied
from the actual original atom's admissibility. -/
theorem admissible_literal_lambda_norm_le {k : ℕ} {σ κ c0 : ℝ}
    (W : Block) (atom : MediumAtom) (z : ℝ)
    (hA : MediumAdmissible k σ κ c0 atom) (w : ℕ) :
    ‖(W.factorData atom z).lambdaAt W.d w‖ ≤ tauR (W.d * w) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hγ2, hγ3⟩ := hA
  exact literal_lambda_norm_le_divisors W atom z w
    (fun q hq => (hγ2 q hq).1) (fun q hq => (hγ3 q hq).1)

/-- The strict small/inclusive rough convention proves the coprimality
field needed by FixedBlock for every occupied literal Lambda fibre. -/
theorem choice_smooth_product_coprime_rough_product
    (W : Block) (atom : MediumAtom) (z : ℝ) {w : ℕ} {p : Factor}
    (hp : p ∈ (W.factorData atom z).choices W.d w) : W.d.Coprime w := by
  obtain ⟨hs, ht, hu, hv⟩ := choice_all_four_supports _ hp
  have hsS := (Finset.mem_filter.mp hs).2
  have htS := (Finset.mem_filter.mp ht).2
  have huR := (Finset.mem_filter.mp hu).2
  have hvR := (Finset.mem_filter.mp hv).2
  have hsu := smallPrimeSupportedAt_coprime_roughPrimeSupportedAt hsS huR
  have hsv := smallPrimeSupportedAt_coprime_roughPrimeSupportedAt hsS hvR
  have htu := smallPrimeSupportedAt_coprime_roughPrimeSupportedAt htS huR
  have htv := smallPrimeSupportedAt_coprime_roughPrimeSupportedAt htS hvR
  obtain ⟨hd, hw, _⟩ := choice_products hp
  rw [← hd, ← hw]
  exact Nat.coprime_mul_iff_left.mpr
    ⟨Nat.coprime_mul_iff_right.mpr ⟨hsu, hsv⟩,
      Nat.coprime_mul_iff_right.mpr ⟨htu, htv⟩⟩

theorem literal_lambda_support_coprime (W : Block) (atom : MediumAtom)
    (z : ℝ) (w : ℕ) (hn : (W.factorData atom z).lambdaAt W.d w ≠ 0) :
    W.d.Coprime w := by
  by_contra hc
  apply hn
  unfold FactorData.lambdaAt
  apply Finset.sum_eq_zero
  intro p hp
  exact False.elim (hc (choice_smooth_product_coprime_rough_product W atom z hp))

theorem paperPsi_complex_norm_le_one (x : ℝ) : ‖(paperPsi x : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (paperPsi_nonneg x)]
  exact paperPsi_le_one x

theorem paperPsi_complex_support (x : ℝ)
    (hx : x ∉ Set.Icc (1 / 2 : ℝ) (5 / 2)) : (paperPsi x : ℂ) = 0 := by
  have hout : x < 1 / 2 ∨ (5 / 2 : ℝ) < x := by
    by_cases hlo : (1 / 2 : ℝ) ≤ x
    · exact Or.inr (lt_of_not_ge fun hhi => hx ⟨hlo, hhi⟩)
    · exact Or.inl (lt_of_not_ge hlo)
  rw [paperPsi_zero_outside x hout]
  norm_num

/-- Install the literal fixed-window Lambda and actual paper cutoff in
the same physical block; all d, q, rough and alpha carriers are retained. -/
def bindBlock (B : FixedBlock) (W : Block) (z : ℝ) (hd : W.d = B.d) : FixedBlock :=
  { B with
    lambdaD := (W.factorData B.atom z).lambdaAt W.d
    lambdaD_support_coprime := by
      intro w hn
      rw [← hd]
      exact literal_lambda_support_coprime W B.atom z w hn
    psi0 := fun x => (paperPsi x : ℂ)
    psi0_support := paperPsi_complex_support
    psiHat0 := fun ξ => 𝓕 (fun x : ℝ => (paperPsi x : ℂ)) ξ }

@[simp] theorem bindBlock_lambda_physical_slice
    (B : FixedBlock) (W : Block) (z : ℝ) (hd : W.d = B.d) (w : ℕ) :
    (bindBlock B W z hd).lambdaD w =
      ∑ q ∈ W.selectedModuli B.atom z w, B.atom.gamma2 q.1 * B.atom.gamma3 q.2 :=
  lambdaAt_eq_original_physical_slice W B.atom z w

theorem bindBlock_lambda_bound {k : ℕ} {σ κ c0 : ℝ}
    (B : FixedBlock) (W : Block) (z : ℝ) (hd : W.d = B.d)
    (hA : MediumAdmissible k σ κ c0 B.atom) (w : ℕ) :
    ‖(bindBlock B W z hd).lambdaD w‖ ≤ tauR ((bindBlock B W z hd).d * w) := by
  change ‖(W.factorData B.atom z).lambdaAt W.d w‖ ≤ tauR (B.d * w)
  rw [← hd]
  exact admissible_literal_lambda_norm_le W B.atom z hA w

theorem bindBlock_q_majorant_bound
    (B : FixedBlock) (W : Block) (z : ℝ) (hd : W.d = B.d) (q : ℕ) :
    ‖actualQWeight (bindBlock B W z hd) q‖ ≤ 1 :=
  paperPsi_complex_norm_le_one _

def qCap (B : FixedBlock) : ℕ := max 1 B.qHi
def roughCap (B : FixedBlock) : ℕ := max 1 (Nat.floor (2 * B.roughLength))
def physicalCap (B : FixedBlock) : ℕ := B.qHi * B.d * Nat.floor (2 * B.roughLength)

theorem actual_qCarrier_cap (B : FixedBlock) :
    B.qCarrier ⊆ Finset.Ioc 0 (Nat.floor (qCap B : ℝ)) := by
  intro q hq
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hq
  have hposR : 0 < (B.qLo : ℝ) := lt_of_lt_of_le B.q0_pos B.qLo_block
  have hpos : 0 < B.qLo := by exact_mod_cast hposR
  simp only [Nat.floor_natCast]
  exact Finset.mem_Ioc.mpr ⟨by omega, hhi.trans (le_max_right _ _)⟩

theorem actual_wCarrier_cap (B : FixedBlock) :
    B.wCarrier ⊆ Finset.Ioc 0 (Nat.floor (roughCap B : ℝ)) := by
  intro r hr
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hr
  have hposR : 0 < (Nat.ceil B.roughLength : ℝ) :=
    lt_of_lt_of_le B.rough_pos (Nat.le_ceil B.roughLength)
  have hpos : 0 < Nat.ceil B.roughLength := by exact_mod_cast hposR
  simp only [Nat.floor_natCast]
  exact Finset.mem_Ioc.mpr ⟨by omega, hhi.trans (le_max_right _ _)⟩

theorem actual_physical_modulus_cap (B : FixedBlock)
    {q r : ℕ} (hq : q ∈ B.qCarrier) (hr : r ∈ B.wCarrier) :
    q * B.d * r ≤ physicalCap B := by
  have hqhi := (Finset.mem_Icc.mp hq).2
  have hrhi := (Finset.mem_Icc.mp hr).2
  unfold physicalCap
  exact Nat.mul_le_mul (Nat.mul_le_mul_right B.d hqhi) hrhi

/-- All coefficient and finite support premises of the earlier fixed-d
kernel budget are discharged for this actual binding. Only the geometric
FixedBlock and its original atom admissibility are supplied. -/
theorem bound_actual_boundBlock_kernel {k : ℕ} {σ κ c0 : ℝ}
    (B : FixedBlock) (W : Block) (z : ℝ) (hd : W.d = B.d)
    (hA : MediumAdmissible k σ κ c0 B.atom) :
    S1DivisorKernel (bindBlock B W z hd) ≤
      4 * (2 * B.atom.U) ^ 2 *
        P5Z.RoughSquareWeightedBudget.logBudget (physicalCap B) ^ 2 *
        (tauR B.d ^ 3 / (B.d : ℝ) ^ 2) *
        ((1 + Real.log (qCap B : ℝ)) ^ 4 / B.q0) *
        (1 + Real.log (roughCap B : ℝ)) ^ 16 := by
  apply S1DivisorKernel_le_log (bindBlock B W z hd) (physicalCap B)
    (2 * B.atom.U) (qCap B : ℝ) (roughCap B : ℝ)
  · exact mul_nonneg (by norm_num) B.U_pos.le
  · exact_mod_cast (le_max_left 1 B.qHi)
  · exact_mod_cast (le_max_left 1 (Nat.floor (2 * B.roughLength)))
  · exact actual_qCarrier_cap B
  · exact actual_wCarrier_cap B
  · intro q _
    exact bindBlock_q_majorant_bound B W z hd q
  · intro r _
    exact bindBlock_lambda_bound B W z hd hA r
  · intro q _ r _
    exact actual_alpha_mean_bound B hA q r
  · intro q hq r hr
    exact actual_physical_modulus_cap B hq hr

end

end ImbalancedChen.Part3.OriginalMediumS1ActualCoefficientBinding
