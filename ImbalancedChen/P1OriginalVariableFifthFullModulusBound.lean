import ImbalancedChen.P1OriginalFifthAttainedRowBinding
import ImbalancedChen.P1ActualCoarseLevelCeiling
import ImbalancedChen.ActualSmallRoughAttachment

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Complete ORIGINAL variable-fifth rough-modulus bound, including ranks zero
through four and the empty d=1 branch. The initial firstStop/rawQ3 policy
is literal. Every fourth/fifth candidate is globally below Lambda-2e,
while inactive/unselected rawQ3 keeps Theta-2e. Hence the correct global
ceiling is Theta-2e, not Lambda-2e. The physical nonzero-coefficient bound
also records its actual small-factor level. No all22/stored-policy claim.
-/

namespace ImbalancedChen.P1OriginalVariableFifthFullModulusBound
noncomputable section
open scoped Classical BigOperators
open HistoricalThirdCoarse VariableEnvelope
open P2OriginalFourthCapProducerInterface
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFourthDescendantLevel
open P1OriginalVariableFifthContinuation

/-- The buffered fifth envelope has the same global Lambda bound as the
fourth producer; no endpoint gate or winning-row hypothesis is needed. -/
theorem fifth_candidate_le_initial (e : ℚ) (I : Finset (Fin 5)) (t : Fin 5 → ℝ) :
    candidate (e : ℝ) I t ≤ initial (e : ℝ) := by
  have hc : VariableEnvelope.cap ≤ extendedDistributionCap := by
    norm_num [VariableEnvelope.cap, extendedDistributionCap]
  calc
    candidate (e : ℝ) I t = v (∑ i ∈ I, t i) - 2 * (e : ℝ) := by
      rw [candidate, envelope_eq_v]
    _ ≤ VariableEnvelope.cap - 2 * (e : ℝ) :=
      sub_le_sub_right (v_le_cap _) _
    _ ≤ initial (e : ℝ) := sub_le_sub_right hc _

/-- This seed is the actual original fourth max on the same ancestor.
Its rawQ3 inactive and unselected branches keep the larger Theta ceiling. -/
theorem inherited4_le_initial (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ)
    (omega N : ℝ) (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (pre : List ℕ) :
    inherited4 e chi m omega N rows4 licensed4 pre ≤ initial (e : ℝ) := by
  have heR : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  exact producer_exponent4_le_initial (e : ℝ) chi heR m omega N rows4 licensed4 _

/-- Every history has the bound, including histories outside rank five.
The maximum is bounded from its genuine seed and each literal row value. -/
theorem exponent5_le_initial (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ)
    (omega N : ℝ) (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m))
    (rows5 : Finset (FifthRow m)) (pre : List ℕ) :
    exponent5 e chi m omega N rows4 licensed4 J5 rows5 pre ≤ initial (e : ℝ) := by
  unfold exponent5
  split_ifs
  · exact finiteMax_le rows5 _ _ _ _
      (inherited4_le_initial e he chi m omega N rows4 licensed4 pre)
      (fun r _hr _he => fifth_candidate_le_initial e r.selected _)
  · exact inherited4_le_initial e he chi m omega N rows4 licensed4 pre

/-- Rank five can equivalently use the constructed seed-or-attained-row
resolution. Overlaps and a losing row do not change the global ceiling. -/
theorem level5_le_initial (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ)
    (omega N : ℝ) (hN : 1 ≤ N)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m))
    (rows5 : Finset (FifthRow m)) (pre : List ℕ) :
    level5 e chi m omega N rows4 licensed4 J5 rows5 pre ≤ N ^ initial (e : ℝ) := by
  by_cases hlen : pre.length = 5
  · rcases P1OriginalFifthAttainedRowBinding.level5_seed_or_attained_row
        e chi m omega N rows4 licensed4 J5 rows5 pre hlen with hs | hr
    · rw [hs]
      change N ^ _ ≤ N ^ initial (e : ℝ)
      exact Real.rpow_le_rpow_of_exponent_le hN
        (inherited4_le_initial e he chi m omega N rows4 licensed4 pre)
    · obtain ⟨r, _hr, _he, hcap, _hliteral, _hhalf, _hfull, _hselected⟩ := hr
      rw [hcap]
      exact Real.rpow_le_rpow_of_exponent_le hN (fifth_candidate_le_initial e r.selected _)
  · change N ^ _ ≤ N ^ initial (e : ℝ)
    exact Real.rpow_le_rpow_of_exponent_le hN
      (exponent5_le_initial e he chi m omega N rows4 licensed4 J5 rows5 pre)

/-- The ALL-rank current level has the same global ceiling. Short ranks
use the actual original frozen rawQ3; rank five and later use Q5. -/
theorem currentLevel_le_initial (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ)
    (omega N : ℝ) (hN : 1 ≤ N)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m))
    (rows5 : Finset (FifthRow m)) (pre : List ℕ) :
    P1OriginalHistoricalRetainedModulusLevel.currentLevel (e : ℝ) chi m omega N
      (level5 e chi m omega N rows4 licensed4 J5 rows5) pre ≤ N ^ initial (e : ℝ) := by
  unfold P1OriginalHistoricalRetainedModulusLevel.currentLevel
  split_ifs
  · have heR : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
    exact P1ActualCoarseLevelCeiling.frozenLevel_le_initial
      (e : ℝ) chi heR m omega N hN pre
  · exact level5_le_initial e he chi m omega N hN rows4 licensed4 J5 rows5 _

/-- The genuine original retained-leaf validity theorem covers every
rank, including d=1. No rank>=5 restriction or cap target is supplied. -/
theorem retained_leaf_modulus_lt_initial (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m))
    (rows5 : Finset (FifthRow m)) (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (weight : ℕ → ℝ) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5)
      weight [] true 1 (roughPrimeUniverse N cap w z)) :
    (leaf.selected.prod : ℝ) < (N : ℝ) ^ initial (e : ℝ) := by
  have hv := P1OriginalHistoricalRetainedModulusLevel.actual_original_fifth_retained_leaf_prod_lt_current
    (e : ℝ) chi m omega N cap w z
    (level5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5)
    heupper hN weight leaf hleaf
  exact hv.trans_le (currentLevel_le_initial e he chi m omega (N : ℝ) hN.le
    rows4 licensed4 J5 rows5 leaf.selected)

/-- Full support bound for the literal variable-fifth rough coefficient. -/
theorem retained_modulus_lt_initial (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m))
    (rows5 : Finset (FifthRow m)) (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ)) (d : ℕ)
    (hd : d ∈ firstExitRetainedModuli
      (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5)
      (roughPrimeUniverse N cap w z)) :
    (d : ℝ) < (N : ℝ) ^ initial (e : ℝ) := by
  obtain ⟨leaf, hleaf, hprod⟩ := (mem_firstExitRetainedModuli _ _ d).mp hd
  simpa only [hprod] using retained_leaf_modulus_lt_initial e he chi m omega
    rows4 licensed4 J5 rows5 N cap w z heupper hN (fun _ => 1) leaf hleaf

/-- A convenient fixed exponent strictly below one, on the complete rough
support. The sharper buffered Theta exponent is retained in the prior API. -/
theorem retained_modulus_lt_599 (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ)
    (omega : ℝ) (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m))
    (rows5 : Finset (FifthRow m)) (N cap : ℕ) (w z : ℝ)
    (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ)) (d : ℕ)
    (hd : d ∈ firstExitRetainedModuli
      (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5)
      (roughPrimeUniverse N cap w z)) :
    (d : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := by
  have heR : (0 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
  have htheta : initial (e : ℝ) ≤ (599 / 1000 : ℝ) := by
    dsimp [initial, extendedDistributionCap]
    linarith
  exact (retained_modulus_lt_initial e he chi m omega rows4 licensed4 J5 rows5
    N cap w z heupper hN d hd).trans_le
      (Real.rpow_le_rpow_of_exponent_le hN.le htheta)

/-- The physical tree retains every even sign, so its fixed rough carrier
is exactly the full original retained-modulus carrier bounded above. -/
theorem variable5_even_retained (e : ℚ) (chi : ℝ) (m : ℕ) (omega N : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m))
    (rows5 : Finset (FifthRow m)) (pre : List ℕ) :
    policy5 e chi m omega N rows4 licensed4 J5 rows5 true pre = true := by
  apply fifthCappedUpperPolicy_even_retained
  intro history
  simp [HistoricalThirdCoarse.initialPolicy, oddFirstExitPolicy]

/-- Only nonzero physical coefficients matter for support: the displayed
small divisor carrier itself can contain zero coefficients above L. -/
theorem physical_nonzero_modulus_lt_smallLevel_mul_initial
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m))
    (rows5 : Finset (FifthRow m)) (N cap : ℕ) (w z L : ℝ)
    (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ)) (q : ℕ)
    (hq : actualSmallRoughRho
      (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 false)
      N cap w z L q ≠ 0) :
    (q : ℝ) < L * (N : ℝ) ^ initial (e : ℝ) := by
  obtain ⟨a, _ha, b, hb, hqprod, haL, _hbc⟩ := actualSmallRoughRho_ne_zero_factors
    (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 false)
    N cap w z L hq
  rw [UpperPolicyFiniteBridge.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5)
    (variable5_even_retained e chi m omega (N : ℝ) rows4 licensed4 J5 rows5)
    N cap w z] at hb
  have hbBound := retained_modulus_lt_initial e he chi m omega rows4 licensed4 J5 rows5
    N cap w z heupper hN b hb
  have hLpos : 0 < L := lt_of_le_of_lt (Nat.cast_nonneg a) haL
  rw [hqprod, Nat.cast_mul]
  exact (mul_le_mul_of_nonneg_right haL.le (Nat.cast_nonneg b)).trans_lt
    (mul_lt_mul_of_pos_left hbBound hLpos)

/-- A small-prime level exponent is a primitive physical parameter.
The result follows from the two actual factors, rather than an assumed
per-history modulus ceiling. -/
theorem physical_nonzero_modulus_lt_power
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m))
    (rows5 : Finset (FifthRow m)) (N cap : ℕ) (w z L lambda theta : ℝ)
    (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (hL : L ≤ (N : ℝ) ^ lambda) (hexp : lambda + initial (e : ℝ) ≤ theta)
    (q : ℕ) (hq : actualSmallRoughRho
      (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 false)
      N cap w z L q ≠ 0) :
    (q : ℝ) < (N : ℝ) ^ theta := by
  calc
    (q : ℝ) < L * (N : ℝ) ^ initial (e : ℝ) :=
      physical_nonzero_modulus_lt_smallLevel_mul_initial e he chi m omega
        rows4 licensed4 J5 rows5 N cap w z L heupper hN q hq
    _ ≤ (N : ℝ) ^ lambda * (N : ℝ) ^ initial (e : ℝ) :=
      mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (zero_lt_one.trans hN).le _)
    _ = (N : ℝ) ^ (lambda + initial (e : ℝ)) :=
      (Real.rpow_add (zero_lt_one.trans hN) _ _).symm
    _ ≤ (N : ℝ) ^ theta := Real.rpow_le_rpow_of_exponent_le hN.le hexp

/-- Physical theta=599/1000, provided the actual small level uses at most
the available 2e buffer plus 1/1000. This restriction is explicit data. -/
theorem physical_nonzero_modulus_lt_599
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m))
    (rows5 : Finset (FifthRow m)) (N cap : ℕ) (w z L : ℝ)
    (heupper : 2 * (e : ℝ) < (299 / 500 : ℝ)) (hN : 1 < (N : ℝ))
    (hL : L ≤ (N : ℝ) ^ (2 * (e : ℝ) + 1 / 1000))
    (q : ℕ) (hq : actualSmallRoughRho
      (policy5 e chi m omega (N : ℝ) rows4 licensed4 J5 rows5 false)
      N cap w z L q ≠ 0) :
    (q : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ) := by
  exact physical_nonzero_modulus_lt_power e he chi m omega rows4 licensed4 J5 rows5
    N cap w z L (2 * (e : ℝ) + 1 / 1000) (599 / 1000) heupper hN hL (by
      dsimp [initial, extendedDistributionCap]
      linarith) q hq

end
end ImbalancedChen.P1OriginalVariableFifthFullModulusBound