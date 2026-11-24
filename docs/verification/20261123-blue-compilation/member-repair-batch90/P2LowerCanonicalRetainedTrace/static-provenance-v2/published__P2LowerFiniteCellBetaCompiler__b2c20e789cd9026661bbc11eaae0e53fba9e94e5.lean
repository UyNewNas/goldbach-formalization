import ImbalancedChen.P2LowerFiniteCellRounding
import ImbalancedChen.ActualLowerSmallRoughAttachment
import ImbalancedChen.FiniteUpperCarrierCore

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual finite-cell rounded rough coefficient receives the actual
small Rosser pair. Positive c uses beta-minus and negative c uses beta-plus.
The small/rough product determines its factors uniquely and defines one
physical output rho. Its pointwise minorant is derived from the output's
proved coefficient comparison and the actual raw lower tree.

No identity with a newly invented retained policy is asserted. The full
raw policy, the rounded coefficient and the two physical rho functions
remain distinct. No nonnegativity of beta-minus is required.
-/

namespace ImbalancedChen.P2LowerFiniteCellBetaCompiler

noncomputable section
open scoped Classical BigOperators
open P2LowerFiniteCellRounding

theorem raw_divisorSum_on_universe (retainEven : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) (n : ℕ) :
    supportedDivisorSum (universe N cap w z) (raw retainEven N cap w z) n=
      supportedDivisorSum (rawSupport retainEven N cap w z) (raw retainEven N cap w z) n := by
  unfold supportedDivisorSum
  symm
  apply Finset.sum_subset
  · intro d hd
    obtain ⟨hd,hdn⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨rawSupport_subset_universe retainEven N cap w z hd,hdn⟩
  · intro d hd hnot
    have hraw : d∉rawSupport retainEven N cap w z := by
      intro hr
      exact hnot (Finset.mem_filter.mpr ⟨hr,(Finset.mem_filter.mp hd).2⟩)
    rw [raw_value,if_neg hraw]

theorem raw_density_on_universe (retainEven : List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) :
    reciprocalTotientDensity (universe N cap w z) (raw retainEven N cap w z)=
      reciprocalTotientDensity (rawSupport retainEven N cap w z) (raw retainEven N cap w z) := by
  unfold reciprocalTotientDensity
  symm
  apply Finset.sum_subset (rawSupport_subset_universe retainEven N cap w z)
  intro d hd hnot
  rw [raw_value,if_neg hnot,zero_div]

theorem compiled_rough_minorant (retainEven : List ℕ → Bool) (N cap : ℕ)
    (w z tau : ℝ) (hzcap : z≤(cap:ℝ)) (n : ℤ) :
    supportedDivisorSum (universe N cap w z) (coefficient retainEven N cap w z tau) n.natAbs≤
      actualIntervalRoughIndicator N w z n := by
  have hcoeff := supportedDivisorSum_le_of_coefficient_le (universe N cap w z)
    (coefficient retainEven N cap w z tau) (raw retainEven N cap w z)
    (fun d _=>coefficient_le_raw retainEven N cap w z tau d) n.natAbs
  rw [raw_divisorSum_on_universe] at hcoeff
  exact hcoeff.trans (fixedEvenRoughDivisorSum_le_roughIndicator retainEven N cap w z hzcap n)

def support (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  smallRoughModuli (actualSmallRosserSupport N cap w) (universe N cap w z)

def rho (retainEven : List ℕ → Bool) (N cap : ℕ) (w z tau L : ℝ) : ℕ → ℝ :=
  smallRoughRho (actualSmallRosserSupport N cap w) (universe N cap w z)
    (coefficient retainEven N cap w z tau)
    (actualSmallRosserPlus N cap w L) (actualSmallRosserMinus N cap w L)

/-- Zero extension of the RAW coefficient to the complete common carrier
is exactly the already-installed raw lower rho, as a physical function. -/
theorem raw_attachment_eq_actual (retainEven : List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) :
    smallRoughRho (actualSmallRosserSupport N cap w) (universe N cap w z)
      (raw retainEven N cap w z) (actualSmallRosserPlus N cap w L)
      (actualSmallRosserMinus N cap w L)=actualLowerSmallRoughRho retainEven N cap w z L := by
  apply smallRoughRho_eq_of_rough_enlargement (actualSmallRosserSupport N cap w)
    (rawSupport_subset_universe retainEven N cap w z)
    (raw retainEven N cap w z) (actualSmallRosserPlus N cap w L)
    (actualSmallRosserMinus N cap w L)
  intro d hd hnot
  rw [raw_value,if_neg hnot]

/-- The actual physical coefficient at a displayed small/rough pair.
Zero c contributes zero, so its choice of beta at equality is immaterial. -/
theorem rho_at_product (retainEven : List ℕ → Bool) (N cap : ℕ)
    (w z tau L : ℝ) {e d : ℕ} (he : e∈actualSmallRosserSupport N cap w)
    (hd : d∈universe N cap w z) :
    rho retainEven N cap w z tau L (e*d)=coefficient retainEven N cap w z tau d*
      (if 0≤coefficient retainEven N cap w z tau d then actualSmallRosserMinus N cap w L e
       else actualSmallRosserPlus N cap w L e) := by
  exact smallRoughRho_mul
    (fun _ hm=>actualSmallRosserSupport_smallPrimeSupportedAt N cap w hm)
    (fun _ hm=>universe_rough N cap w z hm)
    (coefficient retainEven N cap w z tau)
    (actualSmallRosserPlus N cap w L) (actualSmallRosserMinus N cap w L) he hd

theorem product_unique (N cap : ℕ) (w z : ℝ) {e d e' d' : ℕ}
    (he : e∈actualSmallRosserSupport N cap w) (hd : d∈universe N cap w z)
    (he' : e'∈actualSmallRosserSupport N cap w) (hd' : d'∈universe N cap w z)
    (h : e*d=e'*d') : e=e' ∧ d=d' := by
  have hp := smallRough_factorization_unique
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w he) (universe_rough N cap w z hd)
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w he') (universe_rough N cap w z hd') h
  exact ⟨congrArg Prod.fst hp,congrArg Prod.snd hp⟩

theorem rho_abs_le_one (retainEven : List ℕ → Bool) (N cap : ℕ)
    (w z tau L : ℝ) (q : ℕ) : |rho retainEven N cap w z tau L q|≤1 := by
  by_cases hq : q∈support N cap w z
  · obtain ⟨⟨e,d⟩,hed,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨he,hd⟩ := Finset.mem_product.mp hed
    exact abs_smallRoughRho_mul_le_one
      (fun _ hm=>actualSmallRosserSupport_smallPrimeSupportedAt N cap w hm)
      (fun _ hm=>universe_rough N cap w z hm)
      (coefficient retainEven N cap w z tau)
      (actualSmallRosserPlus N cap w L) (actualSmallRosserMinus N cap w L)
      (fun d _=>coefficient_abs_le_one retainEven N cap w z tau d)
      (fun d _=>actualSmallRosserPlus_abs_le_one N cap w L d)
      (fun d _=>actualSmallRosserMinus_abs_le_one N cap w L d) he hd
  · change |smallRoughRho _ _ _ _ _ q|≤1
    rw [smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hq]
    norm_num

/-- The output's actual lower polynomial, derived without a raw count,
compiled-comparison, or beta nonnegativity premise. -/
theorem rho_minorant (retainEven : List ℕ → Bool) (N cap : ℕ)
    (w z tau L : ℝ) (hL : 1<L) (hwL : w≤L) (hwz : w≤z)
    (hzcap : z≤(cap:ℝ)) (n : ℤ) :
    physicalDivisorSum (support N cap w z) (rho retainEven N cap w z tau L) n.natAbs≤
      actualSmallRoughIndicator N z n := by
  have hs := actualSmallRosser_sandwich N cap w L hL hwL (hwz.trans hzcap) n
  have h := physicalDivisorSum_smallRoughRho_lower
    (fun _ hm=>actualSmallRosserSupport_smallPrimeSupportedAt N cap w hm)
    (fun _ hm=>universe_rough N cap w z hm)
    (coefficient retainEven N cap w z tau)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) n.natAbs
    (actualSmallRoughIndicator_nonneg N w n)
    (compiled_rough_minorant retainEven N cap w z tau hzcap n) hs.1 hs.2
  change _≤actualSmallRoughIndicator N w n*actualIntervalRoughIndicator N w z n at h
  rw [actualSmallRoughIndicator_mul_interval N w z hwz n] at h
  exact h

end
end ImbalancedChen.P2LowerFiniteCellBetaCompiler
