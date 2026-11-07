import ImbalancedChen.P5OriginalIndependentFrozenSlotRealization

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Reverse arithmetic dictionary for the actual ordinary rough tree: every
finite descending prime word satisfying the ORIGINAL upper gates is an
actual retained tree modulus. Consequently the finite ranked slot
coefficient has an exact all-integer formula, including every zero and
off-support case. No factorability, distribution, or boundary deletion
is inferred from this identity.
-/

namespace ImbalancedChen.P5Z.OriginalGatedSlotsRetainedSupport
noncomputable section
open Classical
open scoped BigOperators
open OriginalOrdinaryCommonBetaModel OriginalOrdinaryResidualArithmeticFactor
open OriginalPresievedRoughPrimeSlots OriginalPresievedRoughSlotCoefficient

theorem retained_rough_iff_divisor_upper {N cap d:ℕ} {w Z L:ℝ} (hL:1<L) :
    d∈fixedRoughSupport (ordinaryRetainOdd L) N cap w Z ↔
      d∈(roughPrimeUniverse N cap w Z).prod.divisors ∧ (d:ℝ)<L ∧
        MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet L d.primeFactors := by
  change d∈fixedRoughSupport (ordinaryParityRosserPolicy false L false) N cap w Z ↔ _
  rw [UpperPolicyFiniteBridge.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    (ordinaryParityRosserPolicy false L) (ordinaryParityRosserPolicy_upper_even L),
    ordinaryParityRosserRetainedModuli_eq false L hL _ (roughPrimeUniverse_pairwise_gt N cap w Z)
      (fun p hp=>mem_roughPrimeUniverse_prime hp) (by simp)]
  simpa only [Bool.false_eq_true,if_false] using
    mem_ordinaryRosserRetainedModuli_iff false L hL _ (roughPrimeUniverse_pairwise_gt N cap w Z)
      (fun p hp=>mem_roughPrimeUniverse_prime hp) d

theorem ranked_word_product_retained {R N cap:ℕ} {w Z L:ℝ} (hL:1<L)
    {ps:List ℕ} (hps:ps∈rankedOrderedSlots R N cap w Z L) :
    ps.prod∈fixedRoughSupport (ordinaryRetainOdd L) N cap w Z := by
  obtain ⟨k,hk,hcell⟩:=Finset.mem_biUnion.mp hps
  obtain ⟨hbox,hdesc,hgate⟩:=Finset.mem_filter.mp hcell
  obtain ⟨hlen,hmem⟩:=(mem_actualPrimeSlotBox_replicate _ _ _).mp hbox
  have hprime:∀p∈ps,Nat.Prime p:=fun p hp=>(mem_roughPrimeFinset.mp (hmem p hp)).2.1
  have hnd:=hdesc.nodup
  have hpsprod:(∏p∈ps.toFinset,p)=ps.prod:=by
    simpa using List.prod_toFinset (fun p:ℕ=>p) hnd
  have hfullprod:(∏p∈(roughPrimeUniverse N cap w Z).toFinset,p)=
      (roughPrimeUniverse N cap w Z).prod:=by
    simpa using List.prod_toFinset (fun p:ℕ=>p) (roughPrimeUniverse_nodup N cap w Z)
  have hsubset:ps.toFinset⊆(roughPrimeUniverse N cap w Z).toFinset:=by
    intro p hp
    rw [roughPrimeUniverse_toFinset]
    exact hmem p (List.mem_toFinset.mp hp)
  have hdvd:ps.prod∣(roughPrimeUniverse N cap w Z).prod:=by
    rw [←hpsprod,←hfullprod]
    exact Finset.prod_dvd_prod_of_subset _ _ id hsubset
  have hfull0:(roughPrimeUniverse N cap w Z).prod≠0:=by
    apply List.prod_ne_zero
    intro hzero
    exact (mem_roughPrimeUniverse_prime hzero).ne_zero rfl
  have hpf:ps.prod.primeFactors=ps.toFinset:=by
    rw [←hpsprod]
    exact Nat.primeFactors_prod (fun p hp=>hprime p (List.mem_toFinset.mp hp))
  apply (retained_rough_iff_divisor_upper hL).mpr
  refine ⟨Nat.mem_divisors.mpr ⟨hdvd,hfull0⟩,?_,?_⟩
  · simpa only [ordinaryRosserPrefixAdmissible,List.prod_reverse] using hgate.1
  · change MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet L _
    rw [hpf]
    simpa only [List.toFinset_reverse] using hgate.2

/-- Exact all-argument slot arithmetic function. In particular a gated
word can never add a modulus outside the original retained rough tree. -/
theorem signedSlotCoefficient_all_arguments (R N cap:ℕ) (w Z L:ℝ) (hL:1<L) (d:ℕ) :
    signedSlotCoefficient R N cap w Z L d =
      if d∈fixedRoughSupport (ordinaryRetainOdd L) N cap w Z ∧ d.primeFactors.card≤R
      then roughWeight N cap w Z L d else 0 := by
  by_cases h:d∈fixedRoughSupport (ordinaryRetainOdd L) N cap w Z ∧ d.primeFactors.card≤R
  · rw [if_pos h]
    exact (roughWeight_eq_signedSlotCoefficient hL h.1 h.2).symm
  · rw [if_neg h]
    unfold signedSlotCoefficient
    apply Finset.sum_eq_zero
    intro ps hps
    apply if_neg
    intro hprod
    have hd:d∈fixedRoughSupport (ordinaryRetainOdd L) N cap w Z:=by
      rw [←hprod]
      exact ranked_word_product_retained hL hps
    have heq:=ranked_product_unique hd hps hprod
    obtain ⟨k,hk,hcell⟩:=Finset.mem_biUnion.mp hps
    have hbox:=(Finset.mem_filter.mp hcell).1
    have hlen:=((mem_actualPrimeSlotBox_replicate _ _ _).mp hbox).1
    have hcard:ps.length=d.primeFactors.card:=by
      rw [heq,canonicalSlots_length hd]
    have hrank:d.primeFactors.card≤R:=by
      have hkR:=Finset.mem_range.mp hk
      simp only [List.length_replicate] at hlen
      omega
    exact h ⟨hd,hrank⟩

end
end ImbalancedChen.P5Z.OriginalGatedSlotsRetainedSupport
