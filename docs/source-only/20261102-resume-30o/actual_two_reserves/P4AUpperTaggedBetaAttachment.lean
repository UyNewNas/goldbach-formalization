import ImbalancedChen.P4AUpperTaggedParityCompiler
import Mathlib.Data.Nat.GCD.BigOperators

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

One literal physical coefficient for the preceding upper tagged compiler.
The beta pair is the actual Rosser pair. The majorant, absolute bound,
squarefree/coprime carrier, and coefficient error identity have no raw-majorant,
coefficient-domination, beta-sandwich, or compiler-norm hypotheses.

The final theorem removes the arbitrary coefficient-error expression from
the actual compiler slope estimate. Its right side is the explicit changed
tagged-cell mass, which is not asserted small. It is not the two-reserve
endpoint and does not instantiate an unimplemented full87 coarse policy.
-/

namespace ImbalancedChen.P4AUpperTaggedBetaAttachment

noncomputable section
open scoped Classical BigOperators
open P4AUpperTaggedParityCompiler

def support (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  smallRoughModuli (actualSmallRosserSupport N cap w) (universe N cap w z)

def rho (retainOdd : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ) : ℕ → ℝ :=
  smallRoughRho (actualSmallRosserSupport N cap w) (universe N cap w z)
    (coefficient retainOdd tag N cap w z tau)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)

theorem raw_divisorSum_on_universe (retainOdd : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) (n : ℕ) :
    supportedDivisorSum (universe N cap w z) (raw retainOdd N cap w z) n =
      supportedDivisorSum (rawSupport retainOdd N cap w z) (raw retainOdd N cap w z) n := by
  unfold supportedDivisorSum
  symm
  apply Finset.sum_subset
  · intro d hd
    obtain ⟨hd, hdn⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨rawSupport_subset_universe retainOdd N cap w z hd, hdn⟩
  · intro d hd hnot
    have hr : d ∉ rawSupport retainOdd N cap w z := by
      intro hr
      exact hnot (Finset.mem_filter.mpr ⟨hr, (Finset.mem_filter.mp hd).2⟩)
    rw [raw_value, if_neg hr]

/-- The actual raw first-exit theorem supplies the majorant on the enlarged carrier. -/
theorem raw_rough_majorant (retainOdd : List ℕ → Bool) (N cap : ℕ)
    (w z : ℝ) (hzcap : z ≤ (cap : ℝ)) (n : ℤ) :
    actualIntervalRoughIndicator N w z n ≤
      supportedDivisorSum (universe N cap w z) (raw retainOdd N cap w z) n.natAbs := by
  rw [raw_divisorSum_on_universe]
  exact roughIndicator_le_fixedRoughDivisorSum retainOdd N cap w z hzcap n

theorem raw_attachment_eq_actual (retainOdd : List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) :
    smallRoughRho (actualSmallRosserSupport N cap w) (universe N cap w z)
      (raw retainOdd N cap w z) (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L) = actualSmallRoughRho retainOdd N cap w z L := by
  apply smallRoughRho_eq_of_rough_enlargement (actualSmallRosserSupport N cap w)
    (rawSupport_subset_universe retainOdd N cap w z)
    (raw retainOdd N cap w z) (actualSmallRosserMinus N cap w L)
    (actualSmallRosserPlus N cap w L)
  intro d _ hnot
  rw [raw_value, if_neg hnot]

theorem raw_physical_density_on_universe (retainOdd : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) :
    physicalDensitySum (support N cap w z)
      (smallRoughRho (actualSmallRosserSupport N cap w) (universe N cap w z)
        (raw retainOdd N cap w z) (actualSmallRosserMinus N cap w L)
        (actualSmallRosserPlus N cap w L)) =
      physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) := by
  simpa only [support, actualSmallRoughModuli, actualSmallRoughRho,
    physicalDensitySum, div_eq_mul_inv] using
    sum_smallRoughRho_mul_eq_of_rough_enlargement (actualSmallRosserSupport N cap w)
      (rawSupport_subset_universe retainOdd N cap w z)
      (raw retainOdd N cap w z) (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L)
      (fun d _ hnot => by rw [raw_value, if_neg hnot])
      (fun q => (Nat.totient q : ℝ)⁻¹)

/-- Positive c takes beta-plus; negative c takes beta-minus, including at n=0. -/
theorem rho_majorant (retainOdd : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z)
    (hzcap : z ≤ (cap : ℝ)) (n : ℤ) :
    actualSmallRoughIndicator N z n ≤
      physicalDivisorSum (support N cap w z) (rho retainOdd tag N cap w z tau L) n.natAbs := by
  exact actualAttachedRho_majorant_of_rough_domination N cap w z L (universe N cap w z)
    (raw retainOdd N cap w z) (coefficient retainOdd tag N cap w z tau)
    (fun _ hd => P2LowerFiniteCellRounding.universe_rough N cap w z hd)
    (raw_rough_majorant retainOdd N cap w z hzcap)
    (fun d _ => raw_le_coefficient retainOdd tag N cap w z tau d)
    hL hwL hwz hzcap n

theorem rho_divisorSum_nonneg (retainOdd : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z)
    (hzcap : z ≤ (cap : ℝ)) (n : ℤ) :
    0 ≤ physicalDivisorSum (support N cap w z) (rho retainOdd tag N cap w z tau L) n.natAbs :=
  (actualSmallRoughIndicator_nonneg N z n).trans
    (rho_majorant retainOdd tag N cap w z tau L hL hwL hwz hzcap n)

theorem rho_at_product (retainOdd : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ) {a d : ℕ}
    (ha : a ∈ actualSmallRosserSupport N cap w) (hd : d ∈ universe N cap w z) :
    rho retainOdd tag N cap w z tau L (a * d) = coefficient retainOdd tag N cap w z tau d *
      (if 0 ≤ coefficient retainOdd tag N cap w z tau d then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a) :=
  smallRoughRho_mul
    (fun _ hm => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hm)
    (fun _ hm => P2LowerFiniteCellRounding.universe_rough N cap w z hm)
    (coefficient retainOdd tag N cap w z tau)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) ha hd

theorem product_unique (N cap : ℕ) (w z : ℝ) {a d a' d' : ℕ}
    (ha : a ∈ actualSmallRosserSupport N cap w) (hd : d ∈ universe N cap w z)
    (ha' : a' ∈ actualSmallRosserSupport N cap w) (hd' : d' ∈ universe N cap w z)
    (h : a * d = a' * d') : a = a' ∧ d = d' := by
  have hp := smallRough_factorization_unique
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
    (P2LowerFiniteCellRounding.universe_rough N cap w z hd)
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha')
    (P2LowerFiniteCellRounding.universe_rough N cap w z hd') h
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

theorem rho_abs_le_one (retainOdd : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau L : ℝ) (q : ℕ) : |rho retainOdd tag N cap w z tau L q| ≤ 1 := by
  by_cases hq : q ∈ support N cap w z
  · obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨ha, hd⟩ := Finset.mem_product.mp had
    exact abs_smallRoughRho_mul_le_one
      (fun _ hm => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hm)
      (fun _ hm => P2LowerFiniteCellRounding.universe_rough N cap w z hm)
      (coefficient retainOdd tag N cap w z tau)
      (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)
      (fun d _ => coefficient_abs_le_one retainOdd tag N cap w z tau d)
      (fun d _ => actualSmallRosserMinus_abs_le_one N cap w L d)
      (fun d _ => actualSmallRosserPlus_abs_le_one N cap w L d) ha hd
  · change |smallRoughRho _ _ _ _ _ q| ≤ 1
    rw [smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hq]
    norm_num

theorem universe_coprime_target (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ universe N cap w z) : d.Coprime N := by
  have hprod : (roughPrimeUniverse N cap w z).prod.Coprime N := by
    apply Nat.coprime_list_prod_left_iff.mpr
    intro p hp
    exact (mem_roughPrimeUniverse_prime hp).coprime_iff_not_dvd.mpr
      (mem_roughPrimeUniverse_not_dvd hp)
  exact hprod.of_dvd_left (Nat.mem_divisors.mp hd).1

theorem support_squarefree (N cap : ℕ) (w z : ℝ) {q : ℕ}
    (hq : q ∈ support N cap w z) : Squarefree q := by
  obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨ha, hd⟩ := Finset.mem_product.mp had
  exact (Nat.squarefree_mul (smallPrimeSupportedAt_coprime_roughPrimeSupportedAt
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
    (P2LowerFiniteCellRounding.universe_rough N cap w z hd))).mpr
    ⟨actualSmallRosserSupport_squarefree N cap w ha,
      P2LowerFiniteCellRounding.universe_squarefree N cap w z hd⟩

theorem support_coprime_target (N cap : ℕ) (w z : ℝ) {q : ℕ}
    (hq : q ∈ support N cap w z) : q.Coprime N := by
  obtain ⟨⟨a, d⟩, had, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨ha, hd⟩ := Finset.mem_product.mp had
  exact (actualSmallRosserSupport_coprime_target N cap w ha).mul_left
    (universe_coprime_target N cap w z hd)

/-- The supplied B precedes every tag, coefficient, fine width, target and atom count.
The error is for this very rho, and its norm is the literal changed-cell sum. -/
theorem exists_density_difference_le_changedMass :
    ∃ B : ℝ, 0 < B ∧ ∀ nu : ℝ, 0 < nu →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
        ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          ∀ cap : ℕ, (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (cap : ℝ) →
            ∀ (retainOdd : List ℕ → Bool) (tag : ℕ → List Bool) (z tau : ℝ),
              let w := (N : ℝ) ^ (nu * epsilon ^ 2)
              let L := (N : ℝ) ^ (nu * epsilon)
              |physicalDensitySum (support N cap w z) (rho retainOdd tag N cap w z tau L) -
                physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
                  (actualSmallRoughRho retainOdd N cap w z L)| ≤
                ((B / (nu * epsilon ^ 2)) * changedMass retainOdd tag N cap w z tau) *
                  (singularSeries N / Real.log (N : ℝ)) := by
  obtain ⟨B, hB, hsupply⟩ := exists_actualCompiledRho_target_density_difference_bound
  refine ⟨B, hB, ?_⟩
  intro nu hnu epsilon hepsilon hepsilon8
  obtain ⟨N₀, hN₀, hsupply⟩ := hsupply nu hnu epsilon hepsilon hepsilon8
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap retainOdd tag z tau
  let w := (N : ℝ) ^ (nu * epsilon ^ 2)
  let L := (N : ℝ) ^ (nu * epsilon)
  have h := hsupply N hN hEven cap hcap (universe N cap w z)
    (fun _ hd => P2LowerFiniteCellRounding.universe_rough N cap w z hd)
    (coefficient retainOdd tag N cap w z tau) (raw retainOdd N cap w z)
  dsimp only at h ⊢
  change |physicalDensitySum (support N cap w z) (rho retainOdd tag N cap w z tau L) -
    physicalDensitySum (support N cap w z)
      (smallRoughRho (actualSmallRosserSupport N cap w) (universe N cap w z)
        (raw retainOdd N cap w z) (actualSmallRosserMinus N cap w L)
        (actualSmallRosserPlus N cap w L))| ≤ _ at h
  rw [raw_physical_density_on_universe, coefficient_error_eq_changedMass] at h
  exact h

end
end ImbalancedChen.P4AUpperTaggedBetaAttachment
