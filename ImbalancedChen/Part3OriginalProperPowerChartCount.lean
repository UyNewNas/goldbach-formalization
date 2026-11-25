import ImbalancedChen.P5ActualLabelledPrimeSmoothCharts
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Log

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / INCOMPLETE PP TRANSFER.
-- Proper powers in ONE original dyadic slot are counted as prime-base,
-- exponent pairs. This preserves every other slot's position. The finite
-- chart count gives the square-root saving before the signed q-sum.
-- The current source does not attach the smooth eta/psi/W weight, the
-- complete-product trim, or the same-rho congruence/mean functional.

namespace ImbalancedChen.Part3.OriginalProperPowerChartCount

noncomputable section
open scoped BigOperators Classical

def properPowers (U : ℕ) : Finset ℕ :=
  (Finset.Icc 1 U).filter
    (fun n => ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ n = p ^ k)

def baseExponentPairs (U : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 2 (Nat.sqrt U)).product (Finset.Icc 2 (Nat.log2 U))

-- The possible base is at most sqrt(U) and the exponent is at most log2(U).
-- Repeated representations of one natural power only enlarge this cover.
theorem properPowers_subset_pair_image {U : ℕ} (hU : 1 ≤ U) :
    properPowers U ⊆
      (baseExponentPairs U).image (fun pk => pk.1 ^ pk.2) := by
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hnrange, p, k, hp, hk, heq⟩
  subst n
  have hpU : p * p ≤ U := by
    calc
      p * p = p ^ 2 := by ring
      _ ≤ p ^ k := pow_le_pow_right₀ (by omega : 1 ≤ p) hk
      _ ≤ U := (Finset.mem_Icc.mp hnrange).2
  have hroot : p ≤ Nat.sqrt U := Nat.le_sqrt.mpr hpU
  have htwo : 2 ^ k ≤ U := by
    calc
      2 ^ k ≤ p ^ k := pow_le_pow_left₀ (by omega : 0 ≤ (2 : ℕ)) hp.two_le k
      _ ≤ U := (Finset.mem_Icc.mp hnrange).2
  have hlog : k ≤ Nat.log2 U := (Nat.le_log2 (by omega : U ≠ 0)).mpr htwo
  apply Finset.mem_image.mpr
  refine ⟨(p,k),?_,rfl⟩
  exact Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨hp.two_le,hroot⟩,
      Finset.mem_Icc.mpr ⟨hk,hlog⟩⟩

-- A chart-local proper-power alphabet costs sqrt(U) times one logarithm.
-- No primality count or unordered-permutation estimate is substituted.
theorem properPowers_card_le {U : ℕ} (hU : 1 ≤ U) :
    (properPowers U).card ≤ (Nat.sqrt U + 1) * (Nat.log2 U + 1) := by
  have hsub := Finset.card_le_card (properPowers_subset_pair_image hU)
  have himage : ((baseExponentPairs U).image
      (fun pk => pk.1 ^ pk.2)).card ≤ (baseExponentPairs U).card :=
    Finset.card_image_le
  have hbase : (Finset.Icc 2 (Nat.sqrt U)).card ≤ Nat.sqrt U + 1 := by
    simp only [Nat.card_Icc]
    omega
  have hexp : (Finset.Icc 2 (Nat.log2 U)).card ≤ Nat.log2 U + 1 := by
    simp only [Nat.card_Icc]
    omega
  calc
    (properPowers U).card ≤ ((baseExponentPairs U).image
        (fun pk => pk.1 ^ pk.2)).card := hsub
    _ ≤ (baseExponentPairs U).card := himage
    _ = (Finset.Icc 2 (Nat.sqrt U)).card *
          (Finset.Icc 2 (Nat.log2 U)).card := by
            simp [baseExponentPairs]
    _ ≤ (Nat.sqrt U + 1) * (Nat.log2 U + 1) := Nat.mul_le_mul hbase hexp

-- For a fixed rank and one labelled bad slot, all remaining integer slots
-- stay separate in the Cartesian chart. This carrier is an overcount of
-- the smooth original prime tuple support, not its unordered quotient.
def oneBadSlotBox {r : ℕ} (U : Fin r → ℕ) (bad : Fin r) :
    Finset (Fin r → ℕ) :=
  Fintype.piFinset (fun i =>
    if i = bad then properPowers (U i) else Finset.Icc 1 (U i))

theorem oneBadSlotBox_card_le {r : ℕ} (U : Fin r → ℕ)
    (bad : Fin r) (hU : ∀ i, 1 ≤ U i) :
    (oneBadSlotBox U bad).card ≤
      ∏ i : Fin r,
        if i = bad then
          (Nat.sqrt (U i) + 1) * (Nat.log2 (U i) + 1)
        else U i + 1 := by
  classical
  rw [oneBadSlotBox, Fintype.card_piFinset]
  apply Finset.prod_le_prod
  · intro i hi
    positivity
  · intro i hi
    by_cases hib : i = bad
    · simpa only [if_pos hib] using properPowers_card_le (hU i)
    · simp only [if_neg hib, Nat.card_Icc]
      omega

-- A nonnegative pointwise smooth-weight envelope pays the actual finite
-- bad chart by the labelled cardinal bound. The envelope is deliberately
-- kept separate from its eta/psi/W derivation and q/divisor payment.
theorem oneBadSlotBox_absolute_mass {r : ℕ} (U : Fin r → ℕ)
    (bad : Fin r) (hU : ∀ i, 1 ≤ U i)
    (weight : (Fin r → ℕ) → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hweight : ∀ ps ∈ oneBadSlotBox U bad, ‖weight ps‖ ≤ M) :
    (∑ ps ∈ oneBadSlotBox U bad, ‖weight ps‖) ≤
      M * (∏ i : Fin r,
        if i = bad then
          ((Nat.sqrt (U i) + 1) * (Nat.log2 (U i) + 1) : ℕ)
        else U i + 1) := by
  calc
    (∑ ps ∈ oneBadSlotBox U bad, ‖weight ps‖) ≤
        ∑ _ps ∈ oneBadSlotBox U bad, M :=
          Finset.sum_le_sum (fun ps hps => hweight ps hps)
    _ = M * ((oneBadSlotBox U bad).card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ M * (∏ i : Fin r,
        if i = bad then
          ((Nat.sqrt (U i) + 1) * (Nat.log2 (U i) + 1) : ℕ)
        else U i + 1) := by
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast oneBadSlotBox_card_le U bad hU) hM

-- The chart product is the COMPLETE original product upper bound (with
-- harmless +1 endpoint padding), and A is the lower scale of this original
-- slot. Thus the factor 1/sqrt(A) is an explicit power reserve when
-- A is a fixed positive multiple of T^a_star. No signed modulus sum is
-- included in this combinatorial statement.
theorem oneBadSlotBox_absolute_mass_scale {r : ℕ} (U : Fin r → ℕ)
    (bad : Fin r) (hU : ∀ i, 1 ≤ U i)
    (weight : (Fin r → ℕ) → ℂ) (M C T A L : ℝ)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hT : 0 ≤ T) (hA : 0 < A)
    (hL : 0 ≤ L)
    (hweight : ∀ ps ∈ oneBadSlotBox U bad, ‖weight ps‖ ≤ M)
    (hcomplete : (∏ i : Fin r, ((U i + 1 : ℕ) : ℝ)) ≤ C * T)
    (hfloor : A ≤ (U bad : ℝ))
    (hlog : ((Nat.log2 (U bad) + 1 : ℕ) : ℝ) ≤ L) :
    (∑ ps ∈ oneBadSlotBox U bad, ‖weight ps‖) ≤
      2 * M * C * T * L / Real.sqrt A := by
  let B : ℝ := (Nat.sqrt (U bad) + 1 : ℕ)
  let H : ℝ := (Nat.log2 (U bad) + 1 : ℕ)
  let V : Fin r → ℝ := fun i => (U i + 1 : ℕ)
  let O : ℝ := ∏ i ∈ (Finset.univ : Finset (Fin r)).erase bad, V i
  have hBpos : 0 ≤ B := Nat.cast_nonneg _
  have hHpos : 0 ≤ H := Nat.cast_nonneg _
  have hOpos : 0 ≤ O := by
    apply Finset.prod_nonneg
    intro i hi
    exact Nat.cast_nonneg _
  have hrootpos : 0 < Real.sqrt A := Real.sqrt_pos.2 hA
  have hUroot : 0 < Real.sqrt (U bad : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hU bad)
  have hrootSquare : (Real.sqrt (U bad : ℝ)) ^ 2 = (U bad : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hNatSq : (Nat.sqrt (U bad) : ℝ) ^ 2 ≤ (U bad : ℝ) := by
    exact_mod_cast Nat.le_sqrt.mp (le_refl (Nat.sqrt (U bad)))
  have hNatRoot : (Nat.sqrt (U bad) : ℝ) ≤ Real.sqrt (U bad : ℝ) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hrootOne : 1 ≤ Real.sqrt (U bad : ℝ) := by
    nlinarith [hrootSquare, (by exact_mod_cast hU bad : (1 : ℝ) ≤ U bad)]
  have hB : B ≤ 2 * Real.sqrt (U bad : ℝ) := by
    dsimp [B]
    push_cast
    linarith
  have hAroot : Real.sqrt A ≤ Real.sqrt (U bad : ℝ) :=
    Real.sqrt_le_sqrt hfloor
  have hproduct : O * V bad ≤ C * T := by
    have hh := Finset.prod_erase_mul Finset.univ V (Finset.mem_univ bad)
    dsimp [O]
    rw [hh]
    exact hcomplete
  have hboxSplit :
      (∏ i : Fin r,
        if i = bad then
          ((Nat.sqrt (U i) + 1) * (Nat.log2 (U i) + 1) : ℕ)
        else U i + 1) =
      ((Nat.sqrt (U bad) + 1) * (Nat.log2 (U bad) + 1)) *
        (∏ i ∈ (Finset.univ : Finset (Fin r)).erase bad, U i + 1) := by
    let f : Fin r → ℕ := fun i =>
      if i = bad then
        (Nat.sqrt (U i) + 1) * (Nat.log2 (U i) + 1)
      else U i + 1
    have he : (∏ i ∈ (Finset.univ : Finset (Fin r)).erase bad, f i) =
        ∏ i ∈ (Finset.univ : Finset (Fin r)).erase bad, U i + 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      have hne : i ≠ bad := (Finset.mem_erase.mp hi).1
      simp [f, hne]
    have hh := Finset.prod_erase_mul Finset.univ f (Finset.mem_univ bad)
    rw [he] at hh
    simpa only [f, if_pos rfl, mul_comm] using hh.symm
  have hmass := oneBadSlotBox_absolute_mass U bad hU weight M hM hweight
  rw [hboxSplit] at hmass
  have hmass' : (∑ ps ∈ oneBadSlotBox U bad, ‖weight ps‖) ≤ M * B * H * O := by
    simpa only [B,H,O,V,Nat.cast_mul,Nat.cast_prod,mul_assoc] using hmass
  have hV : V bad = (U bad : ℝ) + 1 := by simp [V]
  have hMO : 0 ≤ M * O := mul_nonneg hM hOpos
  have hBH : B * H * Real.sqrt A ≤ 2 * L * V bad := by
    calc
      B * H * Real.sqrt A ≤
          (2 * Real.sqrt (U bad : ℝ)) * H * Real.sqrt A := by
            gcongr
      _ ≤ (2 * Real.sqrt (U bad : ℝ)) * L * Real.sqrt A := by
            gcongr
      _ ≤ (2 * Real.sqrt (U bad : ℝ)) * L *
          Real.sqrt (U bad : ℝ) := by
            gcongr
      _ = 2 * L * (U bad : ℝ) := by rw [← hrootSquare]; ring
      _ ≤ 2 * L * V bad := by rw [hV]; nlinarith
  have hbound :
      (∑ ps ∈ oneBadSlotBox U bad, ‖weight ps‖) * Real.sqrt A ≤
        2 * M * C * T * L := by
    have h1 := mul_le_mul_of_nonneg_right hmass' hrootpos.le
    have h2 := mul_le_mul_of_nonneg_left hBH hMO
    have h3 := mul_le_mul_of_nonneg_left hproduct
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hM hL))
    nlinarith [h1,h2,h3]
  exact (le_div_iff₀ hrootpos).mpr hbound

end
end ImbalancedChen.Part3.OriginalProperPowerChartCount
