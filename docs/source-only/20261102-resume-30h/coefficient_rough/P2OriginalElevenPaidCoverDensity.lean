import ImbalancedChen.P2OriginalElevenLocalizedFullQDifference

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Pay the signed density of the ACTUAL G compact-gate difference.  A fixed
owner partitions overlapping omitted divisor covers; no monotonicity of a
signed density is used.  The original beta signs and all residual moduli
are retained.  This module does not assert any AP estimate.
-/
namespace ImbalancedChen.P2OriginalElevenPaidCoverDensity
noncomputable section
open Classical Filter
open scoped BigOperators Topology
open Certificates.P2OriginalSixthElevenLogSemantics
open P5OriginalCommonRefinedConstructor P2OriginalElevenCompactGatedPolicy
open P2OriginalElevenActualDifferenceLocalization
open P2OriginalElevenLocalizedFullQDifference
open P2OriginalElevenFullModulusOmittedCover P2OriginalElevenAttachedOmittedDensity

/-- Ownership uses only the original omitted prefix, never an AP test. -/
def owner (n N b : ℕ) : Cell :=
  if h : PaidDivisorCover n N b then h.choose else .singleton33_1355

def ownedRough (n N : ℕ) (S : Finset ℕ) (c : Cell) : Finset ℕ :=
  S.filter (fun b => owner n N b = c)

theorem ownedRough_subset_cover (ret : List ℕ → Bool) (n N cap : ℕ)
    (w z : ℝ) (S : Finset ℕ)
    (hS : S ⊆ fixedRoughSupport ret N cap w z)
    (hcover : ∀ b ∈ S, PaidDivisorCover n N b) (c : Cell) :
    ownedRough n N S c ⊆ omittedRough ret c n N cap w z := by
  intro b hb
  obtain ⟨hbS,howner⟩ := Finset.mem_filter.mp hb
  have hc := hcover b hbS
  have hw := hc.choose_spec
  have heq : owner n N b = hc.choose := by simp only [owner,dif_pos hc]
  rw [← heq,howner] at hw
  obtain ⟨p,hp,hdiv⟩ := hw
  exact actual_omitted_prefix_covered ret c n N cap w z (hS hbS) hp hdiv

/-- Finite ownership is exact, even when a modulus has several omitted
prefixes or belongs to several original cells. -/
theorem sum_eq_sum_owned (n N : ℕ) (S : Finset ℕ) (f : ℕ → ℝ) :
    (∑ b ∈ S, f b) = ∑ c ∈ allCells.toFinset, ∑ b ∈ ownedRough n N S c, f b := by
  simp only [ownedRough,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  symm
  rw [Finset.sum_eq_single (owner n N b)]
  · simp only [if_pos rfl]
  · intro c hc hne
    exact if_neg (Ne.symm hne)
  · intro hnot
    exact (hnot (List.mem_toFinset.mpr (allCells_complete (owner n N b)))).elim

theorem restrictedDensity_eq_roughSum (ret : List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) (S : Finset ℕ) (hS : ∀ b ∈ S, RoughPrimeSupportedAt w b) :
    restrictedDensity ret N cap w z L S =
      signSensitiveReciprocalTotientDensity S (fixedRoughCoefficient ret N cap w z)
        (actualSmallRosserMinusDensity N cap w L) (actualSmallRosserPlusDensity N cap w L) :=
  physicalDensitySum_smallRoughRho_eq_signSensitive
    (fun _ he => actualSmallRosserSupport_smallPrimeSupportedAt N cap w he) hS _ _ _

theorem restrictedDensity_eq_sum_owned (ret : List ℕ → Bool) (n N cap : ℕ)
    (w z L : ℝ) (S : Finset ℕ) (hS : S ⊆ fixedRoughSupport ret N cap w z) :
    restrictedDensity ret N cap w z L S =
      ∑ c ∈ allCells.toFinset, restrictedDensity ret N cap w z L (ownedRough n N S c) := by
  have hrough : ∀ b ∈ S, RoughPrimeSupportedAt w b := fun b hb =>
    fixedRoughSupport_roughPrimeSupportedAt ret N cap w z (hS hb)
  rw [restrictedDensity_eq_roughSum ret N cap w z L S hrough]
  unfold signSensitiveReciprocalTotientDensity
  rw [sum_eq_sum_owned n N S]
  apply Finset.sum_congr rfl
  intro c hc
  symm
  exact restrictedDensity_eq_roughSum ret N cap w z L _
    (fun b hb => hrough b (Finset.mem_filter.mp hb).1)

/-- Uniform payment for ANY actual subcarrier of the union cover.  The
finite partition proves the needed signed estimate; an estimate of the
desired union density is not a hypothesis. -/
theorem exists_paid_cover_density_payment (epsilon r eta : ℝ)
    (he : 0 < epsilon) (he8 : epsilon < 1/8) (her : epsilon^2 ≤ r) (heta : 0 < eta) :
    ∃ n₀ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n, n₀ ≤ n → ∀ N, N₀ ≤ N → Even N →
      ∀ cap, (N : ℝ)^r ≤ (cap : ℝ) → ∀ (ret : List ℕ → Bool) (S : Finset ℕ),
        S ⊆ fixedRoughSupport ret N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) →
        (∀ b ∈ S, PaidDivisorCover n N b) →
        |restrictedDensity ret N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) ((N : ℝ)^epsilon) S| <
          eta * (singularSeries N / Real.log (N : ℝ)) := by
  let k : ℝ := allCells.toFinset.card
  have hk : 0 < k+1 := by dsimp [k]; positivity
  obtain ⟨n₀,N₀,hN₀,h⟩ := exists_full_attached_density_payment epsilon r (eta/(k+1))
    he he8 her (div_pos heta hk)
  refine ⟨n₀,N₀,hN₀,?_⟩
  intro n hn N hN hEven cap hcap ret S hS hcover
  have hN2 := hN₀.trans hN
  have hnorm : 0 < singularSeries N / Real.log (N : ℝ) :=
    div_pos (singularSeries_pos N)
      (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
  rw [restrictedDensity_eq_sum_owned ret n N cap _ _ _ S hS]
  calc
    _ ≤ ∑ c ∈ allCells.toFinset,
        |restrictedDensity ret N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r)
          ((N : ℝ)^epsilon) (ownedRough n N S c)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ allCells.toFinset, (eta/(k+1))*(singularSeries N/Real.log (N : ℝ)) := by
      apply Finset.sum_le_sum
      intro c hc
      simpa only [div_eq_mul_inv,mul_assoc] using
        (h n hn N hN hEven cap hcap ret c _
          (ownedRough_subset_cover ret n N cap _ _ S hS hcover c)).le
    _ = k*((eta/(k+1))*(singularSeries N/Real.log (N : ℝ))) := by simp [k]
    _ < eta*(singularSeries N/Real.log (N : ℝ)) := by
      have hs : k*(eta/(k+1)) < eta := by
        rw [← mul_div_assoc]
        apply (div_lt_iff₀ hk).2
        nlinarith
      simpa only [mul_assoc] using mul_lt_mul_of_pos_right hs hnorm

def paidSide (ret : List ℕ → Bool) (n N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  (fixedRoughSupport ret N cap w z).filter (PaidDivisorCover n N)

private theorem restrictedDensity_on_union_eq_side
    (d : OriginalData) (n N cap : ℕ) (w z L : ℝ) (ret : List ℕ → Bool)
    (hsub : fixedRoughSupport ret N cap w z ⊆ commonRough d n N cap w z) :
    restrictedDensity ret N cap w z L (paidRough d n N cap w z) =
      restrictedDensity ret N cap w z L (paidSide ret n N cap w z) := by
  have hs : paidSide ret n N cap w z ⊆ paidRough d n N cap w z := by
    intro b hb
    obtain ⟨hb,hcover⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨hsub hb,hcover⟩
  have hz : ∀ b ∈ paidRough d n N cap w z, b ∉ paidSide ret n N cap w z →
      fixedRoughCoefficient ret N cap w z b = 0 := by
    intro b hb hnot
    apply fixedRoughCoefficient_eq_zero_of_not_mem
    intro hmem
    exact hnot (Finset.mem_filter.mpr ⟨hmem,(Finset.mem_filter.mp hb).2⟩)
  simpa only [restrictedDensity,physicalDensitySum,div_eq_mul_inv,one_mul] using
    sum_smallRoughRho_mul_eq_of_rough_enlargement (actualSmallRosserSupport N cap w) hs
      (fixedRoughCoefficient ret N cap w z) (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L) hz (fun q => (Nat.totient q : ℝ)⁻¹)

/-- Exact connection from G's independently defined deltaRho to the two
actual policy restrictions.  The small sign choice is made separately on
each side before subtraction. -/
theorem actual_delta_density_eq_paid_sides (d : OriginalData) (n N cap : ℕ)
    (hN : 1 < N) (w z L : ℝ) :
    physicalDensitySum (commonQ d n N cap w z) (deltaRho d n N cap w z L) =
      restrictedDensity ((compactPolicy8 d n (N : ℝ)) false) N cap w z L
        (paidSide ((compactPolicy8 d n (N : ℝ)) false) n N cap w z) -
      restrictedDensity ((policy8 d (N : ℝ)) false) N cap w z L
        (paidSide ((policy8 d (N : ℝ)) false) n N cap w z) := by
  have hrough : ∀ b ∈ paidRough d n N cap w z, RoughPrimeSupportedAt w b :=
    fun b hb => commonRough_rough d n N cap w z (Finset.mem_filter.mp hb).1
  have hnew := physicalDensitySum_smallRoughRho_eq_pairSum
    (fun _ he => actualSmallRosserSupport_smallPrimeSupportedAt N cap w he) hrough
    (fixedRoughCoefficient ((compactPolicy8 d n (N : ℝ)) false) N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)
  have hold := physicalDensitySum_smallRoughRho_eq_pairSum
    (fun _ he => actualSmallRosserSupport_smallPrimeSupportedAt N cap w he) hrough
    (fixedRoughCoefficient ((policy8 d (N : ℝ)) false) N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L)
  have hid := actual_delta_test_localized d n N cap hN w z L
    (fun q => (Nat.totient q : ℝ)⁻¹)
  have hmid : physicalDensitySum (commonQ d n N cap w z) (deltaRho d n N cap w z L) =
      restrictedDensity ((compactPolicy8 d n (N : ℝ)) false) N cap w z L
        (paidRough d n N cap w z) -
      restrictedDensity ((policy8 d (N : ℝ)) false) N cap w z L
        (paidRough d n N cap w z) := by
    change _ = _ - _
    rw [show restrictedDensity ((compactPolicy8 d n (N : ℝ)) false) N cap w z L
        (paidRough d n N cap w z) = _ from hnew,
      show restrictedDensity ((policy8 d (N : ℝ)) false) N cap w z L
        (paidRough d n N cap w z) = _ from hold]
    simpa only [physicalDensitySum,deltaPair,div_eq_mul_inv,sub_mul,Finset.sum_sub_distrib]
      using hid
  rw [hmid,
    restrictedDensity_on_union_eq_side d n N cap w z L _ Finset.subset_union_left,
    restrictedDensity_on_union_eq_side d n N cap w z L _ Finset.subset_union_right]

/-- A uniform arbitrary reserve for the literal compactPolicy8-minus-
policy8 physical density, with both original full-q sources unchanged. -/
theorem exists_actual_delta_density_payment (epsilon r eta : ℝ)
    (he : 0 < epsilon) (he8 : epsilon < 1/8) (her : epsilon^2 ≤ r) (heta : 0 < eta) :
    ∃ n₀ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n, n₀ ≤ n → ∀ N, N₀ ≤ N → Even N →
      ∀ cap, (N : ℝ)^r ≤ (cap : ℝ) → ∀ d : OriginalData,
        |physicalDensitySum (commonQ d n N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r))
          (deltaRho d n N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) ((N : ℝ)^epsilon))| <
          eta * (singularSeries N / Real.log (N : ℝ)) := by
  obtain ⟨n₀,N₀,hN₀,h⟩ := exists_paid_cover_density_payment epsilon r (eta/2)
    he he8 her (by positivity)
  refine ⟨n₀,N₀,hN₀,?_⟩
  intro n hn N hN hEven cap hcap d
  have hN2 := hN₀.trans hN
  rw [actual_delta_density_eq_paid_sides d n N cap (by omega)]
  have hs (ret : List ℕ → Bool) := h n hn N hN hEven cap hcap ret
    (paidSide ret n N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r))
    (Finset.filter_subset _ _) (fun b hb => (Finset.mem_filter.mp hb).2)
  exact (abs_sub _ _).trans_lt (by linarith [
    hs ((compactPolicy8 d n (N : ℝ)) false), hs ((policy8 d (N : ℝ)) false)])

end
end ImbalancedChen.P2OriginalElevenPaidCoverDensity
