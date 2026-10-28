import ImbalancedChen.P5All16PhysicalOwnerDiscrepancy
import ImbalancedChen.P5OriginalGatedSlotsRetainedSupport
import ImbalancedChen.P5OriginalPresievedRoughRank

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Reverse coverage and rank exhaustion for the ORIGINAL unrestricted rough
Cartesian convolution.  Squarefree product fibres have one possible rank,
namely primeFactors.card.  If their actual raw upper gate passes, they lie
in the genuine retained first-exit support.  Conversely every retained d
has its canonical raw Cartesian representative at precisely that rank.

The fixed rank bound is derived for the ACTUAL all16 ordinary mark family,
including W, from the genuine near-cap full-modulus bound.  No equality of
supports, no raw-projection identity, and no per-mark rank bound are premises
of the final theorem.  Only the physical rough cutoff licence w<=Z remains.

The resulting finite equality identifies squarefreeAll16Sigma pointwise
with jointPresievedSigma.  Count and exact coprime mean therefore share the
same projected coefficient.  Repeated rough primes remain a separate signed
kernel; no absolute collision saving or PP estimate is inferred here.
-/

namespace ImbalancedChen.P5Z.All16SquarefreeRawProjection
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen
open OriginalOrdinaryCommonBetaModel OriginalOrdinaryPresievedSigma
open OriginalOrdinaryResidualArithmeticFactor OriginalPresievedRoughPrimeSlots
open OriginalPresievedRoughSlotCoefficient OriginalPresievedRoughRank
open OriginalGatedSlotsRetainedSupport OriginalJointPresievedCompiler
open ActualAll16UnrestrictedResidualConvolution All16PhysicalOwnerDiscrepancy
open U1011OriginalSixteenArithmeticProducts

/-- Squarefreeness fixes the rank of ANY raw Cartesian representative.
No descending representative or first-exit support assumption is supplied. -/
theorem raw_squarefree_product_rank_and_divisor {N cap k d : ℕ} {w Z : ℝ}
    (hd : d ∈ residualProducts N cap k w Z) (hsf : Squarefree d) :
    d.primeFactors.card = k ∧
      d ∈ (roughPrimeUniverse N cap w Z).prod.divisors := by
  obtain ⟨ps, hps, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hlen, hmem⟩ := (mem_actualPrimeSlotBox_replicate _ k ps).mp hps
  have hprime : ∀ p ∈ ps, Nat.Prime p :=
    fun p hp => (mem_roughPrimeFinset.mp (hmem p hp)).2.1
  have hnd : ps.Nodup := actualPrimeVector_nodup_of_squarefree ps hprime hsf
  have hpsprod : (∏ p ∈ ps.toFinset, p) = ps.prod := by
    simpa using List.prod_toFinset (fun p : ℕ => p) hnd
  have hpf : ps.prod.primeFactors = ps.toFinset := by
    rw [← hpsprod]
    exact Nat.primeFactors_prod (fun p hp => hprime p (List.mem_toFinset.mp hp))
  have hfullprod : (∏ p ∈ (roughPrimeUniverse N cap w Z).toFinset, p) =
      (roughPrimeUniverse N cap w Z).prod := by
    simpa using List.prod_toFinset (fun p : ℕ => p)
      (roughPrimeUniverse_nodup N cap w Z)
  have hsub : ps.toFinset ⊆ (roughPrimeUniverse N cap w Z).toFinset := by
    intro p hp
    rw [roughPrimeUniverse_toFinset]
    exact hmem p (List.mem_toFinset.mp hp)
  have hdvd : ps.prod ∣ (roughPrimeUniverse N cap w Z).prod := by
    rw [← hpsprod, ← hfullprod]
    exact Finset.prod_dvd_prod_of_subset _ _ id hsub
  have hfull0 : (roughPrimeUniverse N cap w Z).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro hp0
    exact (mem_roughPrimeUniverse_prime hp0).ne_zero rfl
  refine ⟨?_, Nat.mem_divisors.mpr ⟨hdvd, hfull0⟩⟩
  rw [hpf, List.toFinset_card_of_nodup hnd, hlen]

/-- Actual raw gates and squarefreeness construct the retained support;
the reverse support inclusion is proved, not assumed as a licence. -/
theorem raw_squarefree_gated_product_retained {N cap k d : ℕ} {w Z L : ℝ}
    (hL : 1 < L) (hd : d ∈ residualProducts N cap k w Z)
    (hsf : Squarefree d) (hg : rawUpperGate L d) :
    d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z ∧
      k = d.primeFactors.card := by
  have hr := raw_squarefree_product_rank_and_divisor hd hsf
  exact ⟨(retained_rough_iff_divisor_upper hL).mpr ⟨hr.2, hg.1, hg.2⟩,
    hr.1.symm⟩

/-- Every true retained modulus occurs in the raw Cartesian product image
at its canonical prime-factor rank, including the nil word d=1. -/
theorem retained_in_raw_products {N cap d : ℕ} {w Z L : ℝ}
    (hd : d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z) :
    d ∈ residualProducts N cap d.primeFactors.card w Z := by
  apply Finset.mem_image.mpr
  refine ⟨canonicalSlots N cap w Z d, ?_, canonicalSlots_prod hd⟩
  apply (mem_actualPrimeSlotBox_replicate _ _ _).mpr
  refine ⟨canonicalSlots_length hd, ?_⟩
  intro p hp
  have hu := (List.mem_filter.mp hp).1
  simpa only [← roughPrimeUniverse_toFinset N cap w Z, List.mem_toFinset] using hu

/-- Exact rank-by-rank equivalence on the unrestricted Cartesian box.
Different ranks cannot represent the same squarefree physical modulus. -/
theorem raw_squarefree_gated_iff_retained_rank {N cap k d : ℕ} {w Z L : ℝ}
    (hL : 1 < L) :
    (d ∈ residualProducts N cap k w Z ∧ Squarefree d ∧ rawUpperGate L d) ↔
      d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z ∧
        k = d.primeFactors.card := by
  constructor
  · rintro ⟨hd, hsf, hg⟩
    exact raw_squarefree_gated_product_retained hL hd hsf hg
  · rintro ⟨hd, rfl⟩
    have hg := canonicalSlots_original_upper_gates hL hd
    change ((canonicalSlots N cap w Z d).reverse.prod : ℝ) < L ∧
      MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet L
        (canonicalSlots N cap w Z d).reverse.toFinset at hg
    rw [List.prod_reverse, List.toFinset_reverse, canonicalSlots_prod hd,
      canonicalSlots_toFinset hd] at hg
    exact ⟨retained_in_raw_products hd,
      fixedRoughSupport_squarefree _ _ _ _ _ hd, hg⟩

/-- Nonzero signed raw weight on a squarefree fibre has a unique rank
and a genuine physical retained modulus; beta is allowed to vanish. -/
theorem raw_squarefree_nonzero_rank {N cap k e d : ℕ} {w Z L B : ℝ}
    (hL : 1 < L) (hd : d ∈ residualProducts N cap k w Z)
    (hsf : Squarefree d)
    (hnz : rawResidualRowWeight N cap k w Z L B e d ≠ 0) :
    d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z ∧
      k = d.primeFactors.card := by
  have hg : rawUpperGate L d := by
    by_contra hg
    exact hnz (by simp [rawResidualRowWeight, rawResidualWeight, hg])
  exact raw_squarefree_gated_product_retained hL hd hsf hg

/-- One unrestricted squarefree rank contributes exactly the retained
slice of that rank.  Off-gate products have weight zero, not missing terms. -/
theorem squarefree_raw_rank_sum {N cap k e : ℕ} {w Z L B : ℝ}
    (hL : 1 < L) (he : e ∈ actualSmallRosserSupport N cap w)
    (H : ℕ → ℝ) :
    (∑ d ∈ (residualProducts N cap k w Z).filter Squarefree,
      rawResidualRowWeight N cap k w Z L B e d * H d) =
      ∑ d ∈ fixedRoughSupport (ordinaryRetainOdd L) N cap w Z,
        if k = d.primeFactors.card then presievedCoefficient N cap w Z L B (e * d) * H d
        else 0 := by
  let A := (residualProducts N cap k w Z).filter
    (fun d => Squarefree d ∧ rawUpperGate L d)
  have hcut :
      (∑ d ∈ (residualProducts N cap k w Z).filter Squarefree,
        rawResidualRowWeight N cap k w Z L B e d * H d) =
      ∑ d ∈ A, rawResidualRowWeight N cap k w Z L B e d * H d := by
    simp only [A, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hsf : Squarefree d <;> by_cases hg : rawUpperGate L d <;>
      simp [hsf, hg, rawResidualRowWeight, rawResidualWeight]
  have hA : A = (fixedRoughSupport (ordinaryRetainOdd L) N cap w Z).filter
      (fun d => k = d.primeFactors.card) := by
    ext d
    simp only [A, Finset.mem_filter]
    exact raw_squarefree_gated_iff_retained_rank hL
  rw [hcut, hA, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hk : k = d.primeFactors.card
  · rw [if_pos hk, if_pos hk, hk, physical_residual_raw_row hL he hd]
  · rw [if_neg hk, if_neg hk]

/-- Exact all-k exhaustion.  No overlap factor is left: a squarefree d
is present in precisely its single rank. -/
theorem squarefree_raw_all_ranks {N cap R e : ℕ} {w Z L B : ℝ}
    (hL : 1 < L) (he : e ∈ actualSmallRosserSupport N cap w)
    (H : ℕ → ℝ) :
    (∑ k ∈ Finset.range (R + 1),
      ∑ d ∈ (residualProducts N cap k w Z).filter Squarefree,
        rawResidualRowWeight N cap k w Z L B e d * H d) =
      ∑ d ∈ (fixedRoughSupport (ordinaryRetainOdd L) N cap w Z).filter
        (fun d => d.primeFactors.card ≤ R),
          presievedCoefficient N cap w Z L B (e * d) * H d := by
  simp_rw [squarefree_raw_rank_sum hL he H]
  rw [Finset.sum_comm, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  simp [Finset.mem_range, Nat.lt_succ_iff]

/-- The genuine all16 compiler bounds every retained rough d, including
W.  This extends the old helper which was restricted to policy.val<15. -/
theorem actual_all16_rough_modulus_bound {n N d : ℕ} {eta : ℚ}
    {E : ℕ × ℕ → Prop} (hN : 1 < N) (heta : 0 < eta) {t : Four}
    (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    {w : ℝ} (hw : w ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (hd : d ∈ rowRough n N eta w t) :
    (d : ℝ) < (N : ℝ) ^ (153 / 256 : ℝ) := by
  have hj := (Finset.mem_filter.mp ht).1
  have hlegal := U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht
  have hdNative := ordinary_rough_supported_native_active hlegal.2.1 hw hd
  have hdSupport := (actualSmallRosserPlus_active hdNative).1
  have hm : (⟨t, d⟩ : U1011OriginalSixteenJointNearCapModulusConvolution.Mark) ∈
      U1011OriginalSixteenJointNearCapModulusConvolution.marks n N eta E := by
    apply Finset.mem_sigma.mpr
    exact ⟨ht, Finset.mem_filter.mpr ⟨hdSupport, hdNative⟩⟩
  have hcap := U1011OriginalSixteenJointNearCapModulusConvolution.mark_modulus_cap hN heta hm
  have hpref : 0 < fullPrefix t := by
    rw [fullPrefix_eq_multiplier]
    exact P5U1011JointOverlap.joint_multiplier_pos hj
  have hnat : d ≤ fullPrefix t * d := by nlinarith
  have hreal : (d : ℝ) ≤ ((fullPrefix t * d : ℕ) : ℝ) := by exact_mod_cast hnat
  exact hreal.trans_lt hcap

/-- A rank bound depending only on the fixed rough exponent rho, chosen
before N and t.  It is derived from actual physical support, not assumed
for the new raw family. -/
theorem actual_all16_rough_rank_bound {n N d : ℕ} {eta : ℚ}
    {E : ℕ × ℕ → Prop} (hN : 1 < N) (heta : 0 < eta)
    (rho : ℝ) (hrho : 0 < rho) {t : Four}
    (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E)
    (hw : (N : ℝ) ^ rho ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (hd : d ∈ rowRough n N eta ((N : ℝ) ^ rho) t) :
    d.primeFactors.card ≤ actualRoughVectorRankBound rho := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < N := zero_lt_one.trans hn
  have hlo := P4ASpliceDifferenceLowerModulus.retained_pow_primeFactors_card_le
    (ordinaryRetainOdd (U1011OriginalSixteenJointNearCapCompiler.D n N eta t)) N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
    (Real.rpow_nonneg hnpos.le _) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) hd
  have hhi := actual_all16_rough_modulus_bound hN heta ht hw hd
  have hpow : (N : ℝ) ^ (rho * (d.primeFactors.card : ℝ)) ≤
      (N : ℝ) ^ (5 / 8 : ℝ) := by
    rw [Real.rpow_mul hnpos.le, Real.rpow_natCast]
    exact hlo.trans (hhi.le.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by norm_num)))
  have hcard := (Real.rpow_le_rpow_left_iff hn).mp hpow
  unfold actualRoughVectorRankBound
  apply (Nat.le_floor_iff (div_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 8) hrho.le)).mpr
  apply (le_div_iff₀ hrho).mpr
  simpa only [mul_comm] using hcard

/-- Projection of the ENTIRE all16 squarefree raw family to its original
physical coefficient, with a fixed rank chosen only from rho.  E, the mark
set, beta and the signed test F are all unchanged. -/
theorem squarefree_all16_linear_eq_physical {n N : ℕ} {eta : ℚ} {B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (rho : ℝ) (hrho : 0 < rho)
    (E : ℕ × ℕ → Prop)
    (hw : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      (N : ℝ) ^ rho ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (F : ℕ → ℝ) :
    squarefreeAll16Linear (actualRoughVectorRankBound rho) n N eta ((N : ℝ) ^ rho) B E F =
      ∑ q ∈ jointSupport n N eta ((N : ℝ) ^ rho) E,
        jointPresievedSigma n N eta ((N : ℝ) ^ rho) B E q * F q := by
  rw [← joint_exact_pushforward n N eta ((N : ℝ) ^ rho) B E F]
  unfold squarefreeAll16Linear
  apply Finset.sum_congr rfl
  intro t ht
  rw [physical_row_pullback]
  apply Finset.sum_congr rfl
  intro e he
  have hL := (U1011OriginalSixteenJointNearCapCompiler.compiled_legality hN heta ht).2.1
  change (∑ k ∈ Finset.range (actualRoughVectorRankBound rho + 1),
    ∑ d ∈ (residualProducts N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) k ((N : ℝ) ^ rho)
      (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)).filter Squarefree,
      rawResidualRowWeight N
        (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)) k ((N : ℝ) ^ rho)
        (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
        (U1011OriginalSixteenJointNearCapCompiler.D n N eta t) B e d *
          F (fullPrefix t * (e * d))) = _
  rw [squarefree_raw_all_ranks hL he]
  have hfilter : (rowRough n N eta ((N : ℝ) ^ rho) t).filter
      (fun d => d.primeFactors.card ≤ actualRoughVectorRankBound rho) =
      rowRough n N eta ((N : ℝ) ^ rho) t := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    exact actual_all16_rough_rank_bound hN heta rho hrho ht (hw t ht) hd
  change (∑ d ∈ (rowRough n N eta ((N : ℝ) ^ rho) t).filter
    (fun d => d.primeFactors.card ≤ actualRoughVectorRankBound rho),
      rowCoefficient n N eta ((N : ℝ) ^ rho) B t (e * d) * F (fullPrefix t * (e * d))) = _
  rw [hfilter]

/-- In particular the all-k squarefree raw family and the first-batch
retained owner family are the same signed functional on every F. -/
theorem squarefree_all16_linear_eq_owner {n N : ℕ} {eta : ℚ} {B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (rho : ℝ) (hrho : 0 < rho)
    (E : ℕ × ℕ → Prop)
    (hw : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      (N : ℝ) ^ rho ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (F : ℕ → ℝ) :
    squarefreeAll16Linear (actualRoughVectorRankBound rho) n N eta ((N : ℝ) ^ rho) B E F =
      physicalOwnerLinear n N eta ((N : ℝ) ^ rho) B E F := by
  rw [squarefree_all16_linear_eq_physical hN heta rho hrho E hw]
  exact joint_linear_eq_owner_linear hN heta E F

/-- Pointwise equality of the projected all-k raw coefficient and the
same physical jointPresievedSigma, including off-support and zero cases. -/
theorem squarefree_all16_sigma_eq_joint {n N : ℕ} {eta : ℚ} {B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (rho : ℝ) (hrho : 0 < rho)
    (E : ℕ × ℕ → Prop)
    (hw : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      (N : ℝ) ^ rho ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (q : ℕ) :
    squarefreeAll16Sigma (actualRoughVectorRankBound rho) n N eta ((N : ℝ) ^ rho) B E q =
      jointPresievedSigma n N eta ((N : ℝ) ^ rho) B E q := by
  unfold squarefreeAll16Sigma
  rw [squarefree_all16_linear_eq_owner hN heta rho hrho E hw]
  exact physical_owner_sigma_eq_joint hN heta E q

/-- The remaining unrestricted-to-physical difference is EXACTLY the
signed repeated-rough kernel.  Count and coprime mean use the same F;
absolute collision-envelope estimates are not part of this identity. -/
theorem raw_all16_eq_physical_add_collision {n N : ℕ} {eta : ℚ} {B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (rho : ℝ) (hrho : 0 < rho)
    (E : ℕ × ℕ → Prop)
    (hw : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      (N : ℝ) ^ rho ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    (F : ℕ → ℝ) :
    rawAll16Linear (actualRoughVectorRankBound rho) n N eta ((N : ℝ) ^ rho) B E F =
      (∑ q ∈ jointSupport n N eta ((N : ℝ) ^ rho) E,
        jointPresievedSigma n N eta ((N : ℝ) ^ rho) B E q * F q) +
      repeatedRoughAll16Linear (actualRoughVectorRankBound rho) n N eta ((N : ℝ) ^ rho) B E F := by
  rw [raw_all16_split, squarefree_all16_linear_eq_physical hN heta rho hrho E hw]

end
end ImbalancedChen.P5Z.All16SquarefreeRawProjection
