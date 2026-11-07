import ImbalancedChen.P5ActualHBMediumBranchPartition

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- PP section 2: a chart bank is fixed BEFORE n and its factor tuples.
-- The smooth psi(n/R) is retained literally. Its support proves the HB
-- cube condition; no sharp original-group indicator is inserted.
-- PP section 4: sum the retained medium AND Type I pieces with their
-- actual signed 3,-3,1 scalars against the SAME arbitrary functional.
namespace ImbalancedChen.P5Z.SmoothChartHBDyadicPartition
noncomputable section
open Classical
open scoped BigOperators
open LiteralHeathBrownOccurrenceWords ActualRoughHeathBrownWords
open HBRightClosedDyadicRoles ActualHBDyadicOccurrenceFamily
open ActualHBMediumBranchPartition
open ImbalancedChen.Part3

-- Unlike the predecessor's n-dependent bank, N is a fixed chart cap.
theorem fixed_bank_term (N : ℕ) (z y : ℝ) (j n : ℕ) (hn : n ≤ N) :
    (∑ ps ∈ factorTuples (2*(j+1)) n, roughTupleWeight z y (roles j) ps) =
      ∑ bs ∈ blockWords N (2*(j+1)), blockCoefficient z y j n bs := by
  calc
    _ = ∑ ps ∈ factorTuples (2*(j+1)) n,
        ∑ bs ∈ blockWords N (2*(j+1)), assignedWeight z y (roles j) bs ps := by
      apply Finset.sum_congr rfl
      intro ps hps
      have hbound : ∀ p ∈ ps, 0 < p ∧ p ≤ N := by
        intro p hp
        have h := actual_factor_bound hps hp
        exact ⟨h.1,h.2.trans hn⟩
      simpa only [roles_length] using
        (occurrence_reconstruct N z y (roles j) ps hbound).symm
    _ = _ := Finset.sum_comm

def scalar (j : ℕ) : ℂ := (((-1 : ℝ)^j * (Nat.choose 3 (j+1) : ℝ) : ℝ) : ℂ)

theorem fixed_bank_HB {z y : ℝ} (hz : 0 ≤ z) (hy : 0 ≤ y)
    (N : ℕ) {n : ℕ} (hn : n ≤ N) (hcube : (n : ℝ) ≤ y^3) :
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * roughOneSlot z n =
      ∑ j ∈ Finset.range 3, scalar j *
        ∑ bs ∈ blockWords N (2*(j+1)), blockCoefficient z y j n bs := by
  rw [actual_rough_order_three_identity hz hy hcube]
  apply Finset.sum_congr rfl
  intro j hj
  rw [fixed_bank_term N z y j n hn]
  rfl

-- psi is the manuscript smooth dyadic bump. Only its upper support
-- property is needed for the exact algebra; derivatives belong to F.
def chartWeight (psi : ℝ → ℂ) (R : ℝ) (w : ℕ → ℂ) (n : ℕ) : ℂ :=
  psi ((n : ℝ)/R) * w n

theorem chart_support {psi : ℝ → ℂ} {R : ℝ} (hR : 0 < R)
    (hpsi : ∀ t : ℝ, 2 < t → psi t = 0) (w : ℕ → ℂ) {n : ℕ}
    (hn : chartWeight psi R w n ≠ 0) : (n : ℝ) ≤ 2*R := by
  have hp : psi ((n : ℝ)/R) ≠ 0 := by
    intro h
    exact hn (by simp [chartWeight,h])
  have hquot : (n : ℝ)/R ≤ 2 := le_of_not_gt (fun h => hp (hpsi _ h))
  exact (div_le_iff₀ hR).mp hquot

-- This identity holds for EVERY n, including off-chart n. Off-chart
-- terms vanish by the smooth weight, rather than a new sharp wall.
theorem smooth_fixed_bank_HB {psi : ℝ → ℂ} {R z y : ℝ}
    (hR : 0 < R) (hpsi : ∀ t : ℝ, 2 < t → psi t = 0)
    (hz : 0 ≤ z) (hy : 0 ≤ y) (N : ℕ)
    (hcap : 2*R ≤ (N : ℝ)) (hcube : 2*R ≤ y^3)
    (w : ℕ → ℂ) (n : ℕ) :
    chartWeight psi R w n *
      (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * roughOneSlot z n) =
      ∑ j ∈ Finset.range 3, scalar j *
        ∑ bs ∈ blockWords N (2*(j+1)),
          chartWeight psi R w n * blockCoefficient z y j n bs := by
  by_cases hw : chartWeight psi R w n = 0
  · simp [hw]
  have hs := chart_support hR hpsi w hw
  have hn : n ≤ N := by exact_mod_cast hs.trans hcap
  rw [fixed_bank_HB hz hy N hn (hs.trans hcube),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← mul_assoc,mul_comm (chartWeight psi R w n) (scalar j),mul_assoc,
    Finset.mul_sum]

-- A rectangle is retained exactly when it contributes to this finite
-- arithmetic sum. Membership is fixed by the whole chart, before any
-- sign of its discrepancy is inspected. No product-wall is added.
def retained (S : Finset ℕ) (N : ℕ) (psi : ℝ → ℂ) (R z y : ℝ)
    (w : ℕ → ℂ) (j : ℕ) : Finset (List Block) :=
  (blockWords N (2*(j+1))).filter
    (fun bs => ∃ n ∈ S, chartWeight psi R w n * blockCoefficient z y j n bs ≠ 0)

theorem off_retained_zero (S : Finset ℕ) (N : ℕ) (psi : ℝ → ℂ)
    (R z y : ℝ) (w : ℕ → ℂ) (j : ℕ) (bs : List Block)
    (hb : bs ∈ blockWords N (2*(j+1)))
    (hret : bs ∉ retained S N psi R z y w j) {n : ℕ} (hn : n ∈ S) :
    chartWeight psi R w n * blockCoefficient z y j n bs = 0 := by
  by_contra h
  apply hret
  exact Finset.mem_filter.mpr ⟨hb,n,hn,h⟩

-- Select FIRST medium from the entire fixed block word as in Oct27.
-- This is the finite assembly glue, not a second proof of its dichotomy.
theorem smooth_retained_partition {psi : ℝ → ℂ} {R z y : ℝ}
    (hR : 0 < R) (hpsi : ∀ t : ℝ, 2 < t → psi t = 0)
    (hz : 0 ≤ z) (hy : 0 ≤ y) (S : Finset ℕ) (N : ℕ)
    (hcap : 2*R ≤ (N : ℝ)) (hcube : 2*R ≤ y^3)
    (A B : ℝ) (w F : ℕ → ℂ) :
    (∑ n ∈ S, chartWeight psi R w n *
      (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * roughOneSlot z n) * F n) =
      ∑ j ∈ Finset.range 3, scalar j *
        ∑ bs ∈ retained S N psi R z y w j,
          ((∑ n ∈ S, chartWeight psi R w n * mediumPart A B z y j n bs * F n) +
            (∑ n ∈ S, chartWeight psi R w n * typeIPart A B z y j n bs * F n)) := by
  calc
    _ = ∑ n ∈ S, ∑ j ∈ Finset.range 3, scalar j *
        ∑ bs ∈ blockWords N (2*(j+1)),
          chartWeight psi R w n * blockCoefficient z y j n bs * F n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [smooth_fixed_bank_HB hR hpsi hz hy N hcap hcube w n,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_assoc,Finset.sum_mul]
    _ = ∑ j ∈ Finset.range 3, scalar j *
        ∑ bs ∈ blockWords N (2*(j+1)),
          ∑ n ∈ S, chartWeight psi R w n * blockCoefficient z y j n bs * F n := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.mul_sum,Finset.sum_comm]
    _ = ∑ j ∈ Finset.range 3, scalar j *
        ∑ bs ∈ retained S N psi R z y w j,
          ∑ n ∈ S, chartWeight psi R w n * blockCoefficient z y j n bs * F n := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro bs hb hret
      apply Finset.sum_eq_zero
      intro n hn
      rw [off_retained_zero S N psi R z y w j bs hb hret hn,zero_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      apply Finset.sum_congr rfl
      intro bs hb
      simp_rw [exact_block_partition A B z y j, mul_add,add_mul]
      exact Finset.sum_add_distrib

-- The exact coprime mean and residue count use the identical expansion.
-- q=1, nonunits, n=T, and arithmetic endpoints remain literal values.
def discrepancyKernel (q a n : ℕ) : ℂ :=
  (if n % q = a % q then 1 else 0) -
    (if Nat.Coprime n q then ((Nat.totient q : ℂ)⁻¹) else 0)

end
end ImbalancedChen.P5Z.SmoothChartHBDyadicPartition
