import ImbalancedChen.ActualCompilerDensityReserve
import ImbalancedChen.RealPhysicalUpperWeightBridge

/-!
# The raw upper coefficient on the compiler's common finite carrier

The raw retained-tree coefficient is zero outside its own finite support.
Enlarging that support to include a compiler carrier therefore leaves the
raw physical coefficient itself, and every signed weighted sum of it,
unchanged. This is an exact carrier identification, not a density or
distribution assumption. The final estimate applies the existing proved
small-weight reserve to the literal actual raw density on its original
carrier. A compiler still owes its actual coefficient-error bound.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Enlarging the displayed rough support enlarges its product carrier. -/
theorem smallRoughModuli_subset_of_rough_subset
    (small : Finset ℕ) {raw rough : Finset ℕ} (hsub : raw ⊆ rough) :
    smallRoughModuli small raw ⊆ smallRoughModuli small rough := by
  intro q hq
  rcases Finset.mem_image.mp hq with ⟨x, hx, rfl⟩
  exact Finset.mem_image.mpr ⟨x,
    Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp hx).1, hsub (Finset.mem_product.mp hx).2⟩, rfl⟩

/-- Zero extension preserves the whole physical function, not only its
density. Cutoff separation is not needed for this finite fibre identity. -/
theorem smallRoughRho_eq_of_rough_enlargement
    (small : Finset ℕ) {raw rough : Finset ℕ} (hsub : raw ⊆ rough)
    (c betaMinus betaPlus : ℕ → ℝ)
    (hzero : ∀ d ∈ rough, d ∉ raw → c d = 0) :
    smallRoughRho small rough c betaMinus betaPlus =
      smallRoughRho small raw c betaMinus betaPlus := by
  classical
  funext q
  unfold smallRoughRho
  symm
  apply Finset.sum_subset
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hx, hprod⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp hx).1, hsub (Finset.mem_product.mp hx).2⟩, hprod⟩
  · intro x hx hnot
    rcases Finset.mem_filter.mp hx with ⟨hx, hprod⟩
    have hraw : x.2 ∉ raw := by
      intro hd
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp hx).1, hd⟩, hprod⟩)
    simp only [smallRoughPairCoefficient, signAttachedCoefficient,
      hzero x.2 (Finset.mem_product.mp hx).2 hraw, zero_mul]

/-- Every signed linear functional has exactly the same raw value after
carrier enlargement. In particular, no absolute discrepancy is introduced. -/
theorem sum_smallRoughRho_mul_eq_of_rough_enlargement
    (small : Finset ℕ) {raw rough : Finset ℕ} (hsub : raw ⊆ rough)
    (c betaMinus betaPlus : ℕ → ℝ)
    (hzero : ∀ d ∈ rough, d ∉ raw → c d = 0) (F : ℕ → ℝ) :
    (∑ q ∈ smallRoughModuli small rough,
      smallRoughRho small rough c betaMinus betaPlus q * F q) =
        ∑ q ∈ smallRoughModuli small raw,
          smallRoughRho small raw c betaMinus betaPlus q * F q := by
  rw [smallRoughRho_eq_of_rough_enlargement small hsub c betaMinus betaPlus hzero]
  symm
  apply Finset.sum_subset (smallRoughModuli_subset_of_rough_subset small hsub)
  intro q _hq hnot
  rw [smallRoughRho_eq_zero_of_not_mem small raw c betaMinus betaPlus hnot, zero_mul]

/-- The actual retained coefficient has its stated finite support. -/
theorem fixedRoughCoefficient_eq_zero_of_not_mem
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∉ fixedRoughSupport retainOdd N cap w z) :
    fixedRoughCoefficient retainOdd N cap w z d = 0 := by
  rw [fixedRoughCoefficient,
    oddFirstExitRetainedCoefficient_eq_zero_of_not_mem
      retainOdd (fun _ => 1) (roughPrimeUniverse N cap w z) d hd,
    Int.cast_zero]

/-- One explicit common carrier contains the raw and compiler supports.
The raw policy, target-prime deletions and real cutoffs are unchanged. -/
def actualUpperCommonRoughSupport
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (compilerSupport : Finset ℕ) : Finset ℕ :=
  fixedRoughSupport retainOdd N cap w z ∪ compilerSupport

theorem actualUpperCommonRoughSupport_roughPrimeSupportedAt
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (compilerSupport : Finset ℕ)
    (hcompiler : ∀ d ∈ compilerSupport, RoughPrimeSupportedAt w d)
    {d : ℕ} (hd : d ∈ actualUpperCommonRoughSupport
      retainOdd N cap w z compilerSupport) : RoughPrimeSupportedAt w d := by
  rcases Finset.mem_union.mp hd with hraw | hcompiled
  · exact fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hraw
  · exact hcompiler d hcompiled

/-- The raw physical coefficient on any covering rough carrier is
literally the actual retained-tree attachment, at every natural modulus. -/
theorem actualSmallRoughRho_eq_on_common_carrier
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (rough : Finset ℕ) (hcover : fixedRoughSupport retainOdd N cap w z ⊆ rough) :
    smallRoughRho (actualSmallRosserSupport N cap w) rough
        (fixedRoughCoefficient retainOdd N cap w z)
        (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) =
      actualSmallRoughRho retainOdd N cap w z L := by
  exact smallRoughRho_eq_of_rough_enlargement _ hcover _ _ _
    (fun _ _ hd => fixedRoughCoefficient_eq_zero_of_not_mem retainOdd N cap w z hd)

/-- All raw arithmetic uses transfer together to a common finite carrier.
This identity is uniform in the signed test function. -/
theorem sum_actualSmallRoughRho_mul_eq_on_common_carrier
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (rough : Finset ℕ) (hcover : fixedRoughSupport retainOdd N cap w z ⊆ rough)
    (F : ℕ → ℝ) :
    (∑ q ∈ smallRoughModuli (actualSmallRosserSupport N cap w) rough,
      smallRoughRho (actualSmallRosserSupport N cap w) rough
        (fixedRoughCoefficient retainOdd N cap w z)
        (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) q * F q) =
      ∑ q ∈ actualSmallRoughModuli retainOdd N cap w z,
        actualSmallRoughRho retainOdd N cap w z L q * F q := by
  exact sum_smallRoughRho_mul_eq_of_rough_enlargement _ hcover _ _ _
    (fun _ _ hd => fixedRoughCoefficient_eq_zero_of_not_mem retainOdd N cap w z hd) F

/-- The pointwise raw majorant is unchanged, including at test integer zero. -/
theorem actualSmallRoughRho_divisorSum_eq_on_common_carrier
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (rough : Finset ℕ) (hcover : fixedRoughSupport retainOdd N cap w z ⊆ rough)
    (n : ℕ) :
    physicalDivisorSum (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
        (smallRoughRho (actualSmallRosserSupport N cap w) rough
          (fixedRoughCoefficient retainOdd N cap w z)
          (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)) n =
      physicalDivisorSum (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) n := by
  simpa only [physicalDivisorSum, mul_ite, mul_one, mul_zero] using
    sum_actualSmallRoughRho_mul_eq_on_common_carrier retainOdd N cap w z L rough hcover
      (fun q => if q ∣ n then 1 else 0)

/-- The actual raw density can be used on the compiler's common carrier
without changing its value or adding a new density premise. -/
theorem actualSmallRoughRho_density_eq_on_common_carrier
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (rough : Finset ℕ) (hcover : fixedRoughSupport retainOdd N cap w z ⊆ rough) :
    physicalDensitySum (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
        (smallRoughRho (actualSmallRosserSupport N cap w) rough
          (fixedRoughCoefficient retainOdd N cap w z)
          (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)) =
      physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) := by
  simpa only [physicalDensitySum, div_eq_mul_inv] using
    sum_actualSmallRoughRho_mul_eq_on_common_carrier retainOdd N cap w z L rough hcover
      (fun q => (Nat.totient q : ℝ)⁻¹)

/-- The real-source coprime correction uses the identical extended raw rho. -/
theorem actualSmallRoughRho_coprimeCorrection_eq_on_common_carrier
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L b T : ℝ)
    (rough : Finset ℕ) (hcover : fixedRoughSupport retainOdd N cap w z ⊆ rough) :
    realPhysicalCoprimeCorrection b N T
        (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
        (smallRoughRho (actualSmallRosserSupport N cap w) rough
          (fixedRoughCoefficient retainOdd N cap w z)
          (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)) =
      realPhysicalCoprimeCorrection b N T (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) := by
  exact sum_actualSmallRoughRho_mul_eq_on_common_carrier retainOdd N cap w z L rough
    hcover (fun q => (realHalfProductCoprimeMass b N T q -
      ((realHalfProductSource b N T).card : ℝ)) / (Nat.totient q : ℝ))

/-- The full signed real-source discrepancy, rather than an absolute sum,
is preserved under the same raw carrier enlargement. -/
theorem actualSmallRoughRho_distribution_eq_on_common_carrier
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L b T : ℝ)
    (rough : Finset ℕ) (hcover : fixedRoughSupport retainOdd N cap w z ⊆ rough) :
    realPhysicalDistributionError b N T
        (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
        (smallRoughRho (actualSmallRosserSupport N cap w) rough
          (fixedRoughCoefficient retainOdd N cap w z)
          (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)) =
      realPhysicalDistributionError b N T (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) := by
  exact sum_actualSmallRoughRho_mul_eq_on_common_carrier retainOdd N cap w z L rough
    hcover (fun q => realHalfProductCongruenceMass b N T q -
      realHalfProductCoprimeMass b N T q / (Nat.totient q : ℝ))

/-- The proved compiler reserve now compares the compiled density on a
common carrier with the literal raw density on its own retained support.
The coefficient-error mass is still charged on the whole common carrier,
including compiler-only moduli. No sharp error estimate is assumed or
asserted here, and the scale retains its exact factor `1 / nu`. -/
theorem exists_actualUpperCommonCarrier_target_density_difference_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ nu : ℝ, 0 < nu →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
        ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
          ∀ cap : ℕ, (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (cap : ℝ) →
            ∀ (retainOdd : List ℕ → Bool) (z : ℝ) (rough : Finset ℕ),
              fixedRoughSupport retainOdd N cap ((N : ℝ) ^ (nu * epsilon ^ 2)) z ⊆ rough →
              (∀ d ∈ rough, RoughPrimeSupportedAt ((N : ℝ) ^ (nu * epsilon ^ 2)) d) →
                ∀ compiled : ℕ → ℝ,
                  let w := (N : ℝ) ^ (nu * epsilon ^ 2)
                  let L := (N : ℝ) ^ (nu * epsilon)
                  let raw := fixedRoughCoefficient retainOdd N cap w z
                  |physicalDensitySum (smallRoughModuli (actualSmallRosserSupport N cap w) rough)
                      (smallRoughRho (actualSmallRosserSupport N cap w) rough compiled
                        (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)) -
                    physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
                      (actualSmallRoughRho retainOdd N cap w z L)| ≤
                    ((B / (nu * epsilon ^ 2)) *
                      reciprocalTotientDensity rough (fun d => |compiled d - raw d|)) *
                        (singularSeries N / Real.log (N : ℝ)) := by
  obtain ⟨B, hB, hsupply⟩ := exists_actualCompiledRho_target_density_difference_bound
  refine ⟨B, hB, ?_⟩
  intro nu hnu epsilon hepsilon hepsilon8
  obtain ⟨N₀, hN₀, hsupply⟩ := hsupply nu hnu epsilon hepsilon hepsilon8
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap retainOdd z rough hcover hrough compiled
  have h := hsupply N hN hEven cap hcap rough hrough compiled
    (fixedRoughCoefficient retainOdd N cap ((N : ℝ) ^ (nu * epsilon ^ 2)) z)
  dsimp only at h ⊢
  rw [actualSmallRoughRho_density_eq_on_common_carrier retainOdd N cap
    ((N : ℝ) ^ (nu * epsilon ^ 2)) z ((N : ℝ) ^ (nu * epsilon)) rough hcover] at h
  exact h

end

end ImbalancedChen
