import ImbalancedChen.Part3ActualCommonHeightKFactorizationFullGram
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED. 2026-10-24.
Actual PacketData restriction by ONE common natural m interval. The same
interval is used in every row and at every packet level. The signed n
coefficient, all n carriers, physical kernel, scales and region are retained.
No spectral estimate, Parseval theorem or Gram estimate is asserted here.
-/

namespace ImbalancedChen.Part3.ActualCommonMaskSourceOnly
noncomputable section

open Classical
open scoped BigOperators
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)
open ImbalancedChen.Part3.ActualCommonHeightKGramSourceOnly

variable {ι : Type*}

/-- Intersect the actual frozen interval with a single common interval [a,b).
Empty intersections need no additional endpoint hypothesis. -/
def restrictM (P : PacketData ι) (a b : ℕ) : PacketData ι :=
  { P with
    lo := max P.lo a
    hi := min P.hi b
    m_normalized := by
      intro m hm
      rcases Finset.mem_Ico.mp hm with ⟨hl, hu⟩
      apply P.m_normalized m
      exact Finset.mem_Ico.mpr
        ⟨le_trans (le_max_left P.lo a) hl,
          lt_of_lt_of_le hu (min_le_left P.hi b)⟩ }

theorem restrictM_lo (P : PacketData ι) (a b : ℕ) :
    (restrictM P a b).lo = max P.lo a := by rfl

theorem restrictM_hi (P : PacketData ι) (a b : ℕ) :
    (restrictM P a b).hi = min P.hi b := by rfl

theorem restrictM_mCarrier (P : PacketData ι) (a b : ℕ) :
    (restrictM P a b).mCarrier = Finset.Ico a b ∩ P.mCarrier := by
  ext m
  simp only [PacketData.mCarrier, restrictM, Finset.mem_inter, Finset.mem_Ico]
  omega

theorem restrictM_mCarrier_filter (P : PacketData ι) (a b : ℕ) :
    (restrictM P a b).mCarrier =
      P.mCarrier.filter (fun m => m ∈ Finset.Ico a b) := by
  rw [restrictM_mCarrier]
  ext m
  simp only [Finset.mem_inter, Finset.mem_filter, and_comm]

theorem restrictM_mCarrier_subset (P : PacketData ι) (a b : ℕ) :
    (restrictM P a b).mCarrier ⊆ P.mCarrier := by
  rw [restrictM_mCarrier]
  exact Finset.inter_subset_right

/-- All original row labels, n carriers, packets and physical kernels survive. -/
theorem restrictM_rows (P : PacketData ι) (a b : ℕ) :
    (restrictM P a b).rows = P.rows := by rfl

theorem restrictM_nCarrier (P : PacketData ι) (a b : ℕ) :
    (restrictM P a b).nCarrier = P.nCarrier := by rfl

theorem restrictM_packet (P : PacketData ι) (a b : ℕ) :
    (restrictM P a b).packet = P.packet := by rfl

theorem restrictM_kernel (P : PacketData ι) (a b : ℕ) :
    (restrictM P a b).kernel = P.kernel := by rfl

theorem restrictM_region (P : PacketData ι) (a b : ℕ) :
    (restrictM P a b).region = P.region := by rfl

theorem restrictM_parameters (P : PacketData ι) (a b : ℕ) :
    (restrictM P a b).V = P.V ∧ (restrictM P a b).U = P.U ∧
    (restrictM P a b).Z = P.Z ∧ (restrictM P a b).Y0 = P.Y0 ∧
    (restrictM P a b).rho = P.rho ∧ (restrictM P a b).sigma = P.sigma ∧
    (restrictM P a b).negativeCusp = P.negativeCusp := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The physical phase k_1/(64 V) remains a single phase at every level. -/
theorem restrictM_common_phase (P : PacketData ι) (a b : ℕ) (k : D4 → ℤ) :
    ((restrictM P a b).completed k).additivePhase =
      (P.completed k).additivePhase := by rfl

theorem restrictM_signed_mode_coefficient (P : PacketData ι)
    (a b : ℕ) (k : D4 → ℤ) (j : ι) (n : ℕ) :
    signedCoefficient (restrictM P a b).negativeCusp
      (modePacket ((restrictM P a b).packet j) k
        (restrictM P a b).U (restrictM P a b).Z) n =
      signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n := by
  rfl

/-- The exact indicator multiplied into the original completed weight. -/
def commonMaskWeight (P : PacketData ι) (a b : ℕ) (k : D4 → ℤ) (m : ℕ) : ℂ :=
  if m ∈ Finset.Ico a b then (P.completed k).weight m else 0

theorem restrictM_completed_weight (P : PacketData ι)
    (a b : ℕ) (k : D4 → ℤ) (m : ℕ) :
    ((restrictM P a b).completed k).weight m = commonMaskWeight P a b k m := by
  have hmem : m ∈ Finset.Ico (max P.lo a) (min P.hi b) ↔
      m ∈ Finset.Ico a b ∧ m ∈ Finset.Ico P.lo P.hi := by
    simp only [Finset.mem_Ico]
    omega
  change (if m ∈ Finset.Ico (max P.lo a) (min P.hi b) then
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        (((k 1 : ℝ) / (64 * P.V)) : ℂ) * (m : ℂ)) else 0) =
    (if m ∈ Finset.Ico a b then
      (if m ∈ Finset.Ico P.lo P.hi then
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (((k 1 : ℝ) / (64 * P.V)) : ℂ) * (m : ℂ)) else 0) else 0)
  rw [hmem]
  by_cases hI : m ∈ Finset.Ico a b <;>
    by_cases hP : m ∈ Finset.Ico P.lo P.hi <;> simp only [hI, hP, and_self,
      and_false, false_and, if_true, if_false]

theorem restrictM_completed_weight_indicator (P : PacketData ι)
    (a b : ℕ) (k : D4 → ℤ) (m : ℕ) :
    ((restrictM P a b).completed k).weight m =
      (if m ∈ Finset.Ico a b then (1 : ℂ) else 0) * (P.completed k).weight m := by
  rw [restrictM_completed_weight]
  by_cases hI : m ∈ Finset.Ico a b <;> simp [commonMaskWeight, hI]

/-- Apply the common mask to every level, retaining the original carriers. -/
def maskedCompletedPacketSum (P : PacketData ι) (a b : ℕ) (k : D4 → ℤ) : ℂ :=
  ∑ j ∈ P.rows, ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
    commonMaskWeight P a b k m *
      signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n

/-- The real restricted PacketData sum is exactly the same common mask in
every row. Neither the n variable nor the packet is restricted anew. -/
theorem completedPacketSum_restrictM (P : PacketData ι)
    (a b : ℕ) (k : D4 → ℤ) :
    completedPacketSum (restrictM P a b) k = maskedCompletedPacketSum P a b k := by
  unfold completedPacketSum maskedCompletedPacketSum
  change (∑ j ∈ P.rows, ∑ m ∈ (restrictM P a b).mCarrier, ∑ n ∈ P.nCarrier j,
      ((restrictM P a b).completed k).weight m *
        signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n) = _
  apply Finset.sum_congr rfl
  intro j _hj
  rw [restrictM_mCarrier_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _hm
  by_cases hI : m ∈ Finset.Ico a b
  · simp only [if_pos hI, restrictM_completed_weight]
  · simp only [if_neg hI, commonMaskWeight, zero_mul, Finset.sum_const_zero]

/-- A pointwise row version, with exactly the same a,b in each level. -/
theorem completed_row_restrictM (P : PacketData ι)
    (a b : ℕ) (k : D4 → ℤ) (j : ι) :
    (∑ m ∈ (restrictM P a b).mCarrier, ∑ n ∈ P.nCarrier j,
      ((restrictM P a b).completed k).weight m *
        signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n) =
    ∑ m ∈ P.mCarrier, ∑ n ∈ P.nCarrier j,
      commonMaskWeight P a b k m *
        signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n := by
  rw [restrictM_mCarrier_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _hm
  by_cases hI : m ∈ Finset.Ico a b
  · simp only [if_pos hI, restrictM_completed_weight]
  · simp only [if_neg hI, commonMaskWeight, zero_mul, Finset.sum_const_zero]

/-- The same completed mask factors across all levels simultaneously. -/
theorem maskedCompletedPacketSum_common_interval (P : PacketData ι)
    (a b : ℕ) (k : D4 → ℤ) :
    maskedCompletedPacketSum P a b k =
      (∑ m ∈ P.mCarrier, commonMaskWeight P a b k m) *
        (∑ j ∈ P.rows, ∑ n ∈ P.nCarrier j,
          signedCoefficient P.negativeCusp (modePacket (P.packet j) k P.U P.Z) n) := by
  unfold maskedCompletedPacketSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  exact (Finset.sum_mul_sum P.mCarrier (P.nCarrier j)
    (fun m => commonMaskWeight P a b k m)
    (fun n => signedCoefficient P.negativeCusp
      (modePacket (P.packet j) k P.U P.Z) n)).symm

theorem restrictM_kTestTransform (P : PacketData ι)
    (a b : ℕ) (k : D4 → ℤ) (t : ℝ) :
    kTestTransform (restrictM P a b) k t = kTestTransform P k t := by rfl

/-- Ordered adjacent half-open masks form an exact disjoint partition. -/
theorem commonMaskWeight_split (P : PacketData ι) (a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) (k : D4 → ℤ) (m : ℕ) :
    commonMaskWeight P a c k m =
      commonMaskWeight P a b k m + commonMaskWeight P b c k m := by
  have hmem : m ∈ Finset.Ico a c ↔
      m ∈ Finset.Ico a b ∨ m ∈ Finset.Ico b c := by
    simp only [Finset.mem_Ico]
    omega
  have hdis : ¬ (m ∈ Finset.Ico a b ∧ m ∈ Finset.Ico b c) := by
    simp only [Finset.mem_Ico]
    omega
  by_cases hl : m ∈ Finset.Ico a b
  · have hr : m ∉ Finset.Ico b c := fun hr => hdis ⟨hl, hr⟩
    have hac := hmem.mpr (Or.inl hl)
    simp only [commonMaskWeight, if_pos hl, if_neg hr, if_pos hac, add_zero]
  · by_cases hr : m ∈ Finset.Ico b c
    · have hac := hmem.mpr (Or.inr hr)
      simp only [commonMaskWeight, if_neg hl, if_pos hr, if_pos hac, zero_add]
    · have hac : m ∉ Finset.Ico a c := by
        intro hm
        rcases hmem.mp hm with hm | hm
        · exact hl hm
        · exact hr hm
      simp only [commonMaskWeight, if_neg hl, if_neg hr, if_neg hac, add_zero]

theorem maskedCompletedPacketSum_split (P : PacketData ι) (a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) (k : D4 → ℤ) :
    maskedCompletedPacketSum P a c k =
      maskedCompletedPacketSum P a b k + maskedCompletedPacketSum P b c k := by
  unfold maskedCompletedPacketSum
  simp only [commonMaskWeight_split P a b c hab hbc, add_mul,
    Finset.sum_add_distrib]

/-- Exact splitting of the ACTUAL completedPacketSum, retaining all levels
and their off-diagonal information before any subsequent energy estimate. -/
theorem completedPacketSum_restrictM_split (P : PacketData ι) (a b c : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) (k : D4 → ℤ) :
    completedPacketSum (restrictM P a c) k =
      completedPacketSum (restrictM P a b) k + completedPacketSum (restrictM P b c) k := by
  simp only [completedPacketSum_restrictM]
  exact maskedCompletedPacketSum_split P a b c hab hbc k

end
end ImbalancedChen.Part3.ActualCommonMaskSourceOnly
