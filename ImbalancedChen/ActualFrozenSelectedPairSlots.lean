import ImbalancedChen.ActualRoughVectorEndpointBudget

/-!
# One selected-pair slot partition for a whole original prime box

The capacity case and both greedy lists are computed from the original
upper endpoints once. Every actual tuple then maps these same three lists
of original slot labels. The concatenated lists permute the original full
vector, including the full-vector repair when the selected capacity is
below one. No individual tuple decision fibre is treated as a rectangle.

The endpoint targets below use the original policy support, its paid
uniform rank and width budget, and the selected pair's actual whole-cell
gate. They do not take a remainder-square predicate or an assignment as
an input. Grouped arithmetic means and small-factor attachment remain
separate obligations.
-/

namespace ImbalancedChen

noncomputable section

open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation
open scoped Classical

/-- The literal greedy run always partitions occurrences, independently
of the numerical hypotheses used to prove its capacities. -/
theorem actualTwoCapacityGreedy_partition {α : Type*} (weight : α → ℝ)
    (A : ℝ) (input : List α) :
    BoxPartition (actualTwoCapacityGreedy weight A input).1
      (actualTwoCapacityGreedy weight A input).2 input := by
  induction input using List.reverseRecOn with
  | nil => exact BoxPartition.nil
  | append_singleton input p ih =>
      rw [actualTwoCapacityGreedy_append]
      unfold actualTwoCapacityStep
      split_ifs
      · exact ih.left p
      · exact ih.right p

/-- Both the capacity test and all slot decisions use upper endpoints. -/
def actualFrozenSelectedPairSlots {α : Type*} (D A : ℝ) (yz : Bool)
    (upper : α → ℕ) (p : Fin 3 → α) (tail : List α) : List α × List α × List α :=
  if 1 ≤ D / (A * (actualSelectedPairProduct yz (fun i => upper (p i)) : ℝ)) then
    let ac := actualTwoCapacityGreedy (fun i => (upper i : ℝ)) A
      ((if yz then p 0 else p 1) :: tail)
    (ac.1, if yz then [p 1, p 2] else [p 0, p 2], ac.2)
  else
    let ab := actualTwoCapacityGreedy (fun i => (upper i : ℝ)) A
      (p 0 :: p 1 :: p 2 :: tail)
    (ab.1, ab.2, [])

def actualFrozenSelectedPairFactors {α : Type*} (D A : ℝ) (yz : Bool)
    (upper actual : α → ℕ) (p : Fin 3 → α) (tail : List α) : ℕ × ℕ × ℕ :=
  let slots := actualFrozenSelectedPairSlots D A yz upper p tail
  ((slots.1.map actual).prod, (slots.2.1.map actual).prod, (slots.2.2.map actual).prod)

/-- This is a partition of the original labelled slots, including equal
values in different slots. No capacity assumption is needed for this fact. -/
theorem actualFrozenSelectedPairSlots_perm {α : Type*} (D A : ℝ) (yz : Bool)
    (upper : α → ℕ) (p : Fin 3 → α) (tail : List α) :
    let slots := actualFrozenSelectedPairSlots D A yz upper p tail
    (slots.1 ++ slots.2.1 ++ slots.2.2).Perm (p 0 :: p 1 :: p 2 :: tail) := by
  unfold actualFrozenSelectedPairSlots
  split_ifs
  · let ac := actualTwoCapacityGreedy (fun i => (upper i : ℝ)) A
      ((if yz then p 0 else p 1) :: tail)
    let selected := if yz then [p 1, p 2] else [p 0, p 2]
    have hpart := actualTwoCapacityGreedy_partition (fun i => (upper i : ℝ)) A
      ((if yz then p 0 else p 1) :: tail)
    have hmove : (ac.1 ++ selected ++ ac.2).Perm (selected ++ (ac.1 ++ ac.2)) := by
      simpa only [List.append_assoc] using
        (List.perm_append_comm (l₁ := ac.1) (l₂ := selected)).append_right ac.2
    apply hmove.trans ((hpart.perm.append_left selected).trans ?_)
    cases yz
    · exact (List.Perm.swap (p 1) (p 2) tail).cons (p 0)
    · exact ((List.Perm.swap (p 0) (p 2) tail).cons (p 1)).trans
        (List.Perm.swap (p 0) (p 1) (p 2 :: tail))
  · simpa only [List.append_nil] using
      (actualTwoCapacityGreedy_partition (fun i => (upper i : ℝ)) A
        (p 0 :: p 1 :: p 2 :: tail)).perm

/-- Every actual tuple uses the very same slot lists and retains its exact
original product. This does not identify its own tuplewise greedy action. -/
theorem actualFrozenSelectedPairFactors_prod {α : Type*} (D A : ℝ) (yz : Bool)
    (upper actual : α → ℕ) (p : Fin 3 → α) (tail : List α) :
    let abc := actualFrozenSelectedPairFactors D A yz upper actual p tail
    abc.1 * abc.2.1 * abc.2.2 = ((p 0 :: p 1 :: p 2 :: tail).map actual).prod := by
  have h := ((actualFrozenSelectedPairSlots_perm D A yz upper p tail).map actual).prod_eq
  simpa only [actualFrozenSelectedPairFactors, List.map_append, List.prod_append,
    mul_assoc] using h

/-- The common groups have their actual endpoint bounds for every tuple
in the original coordinate box, without imposing an assignment fibre. -/
theorem actualFrozenSelectedPairFactors_le_upper {α : Type*} (D A : ℝ) (yz : Bool)
    (upper actual : α → ℕ) (p : Fin 3 → α) (tail : List α)
    (hsize : ∀ i ∈ p 0 :: p 1 :: p 2 :: tail, actual i ≤ upper i) :
    let abc := actualFrozenSelectedPairFactors D A yz upper actual p tail
    let ABC := actualFrozenSelectedPairFactors D A yz upper upper p tail
    abc.1 ≤ ABC.1 ∧ abc.2.1 ≤ ABC.2.1 ∧ abc.2.2 ≤ ABC.2.2 := by
  let slots := actualFrozenSelectedPairSlots D A yz upper p tail
  have hperm := actualFrozenSelectedPairSlots_perm D A yz upper p tail
  have hbound (l : List α) (hmem : ∀ i ∈ l, i ∈ p 0 :: p 1 :: p 2 :: tail) :
      (l.map actual).prod ≤ (l.map upper).prod :=
    List.prod_map_le_prod_map₀ actual upper (fun i _ => Nat.zero_le _)
      (fun i hi => hsize i (hmem i hi))
  exact ⟨hbound slots.1 (fun i hi => hperm.mem_iff.mp (List.mem_append.mpr (Or.inl hi))),
    hbound slots.2.1 (fun i hi => hperm.mem_iff.mp
      (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hi))))),
    hbound slots.2.2 (fun i hi => hperm.mem_iff.mp
      (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hi)))))⟩

/-- At the upper vector this is exactly the already defined numerical pair
action. Only the action at upper endpoints is used for every tuple's slots. -/
theorem actualFrozenSelectedPairFactors_at_upper {α : Type*} (D A : ℝ) (yz : Bool)
    (upper : α → ℕ) (p : Fin 3 → α) (tail : List α) :
    actualFrozenSelectedPairFactors D A yz upper upper p tail =
      actualSelectedPairFactors D A yz (fun i => upper (p i)) (tail.map upper) := by
  have hmap (input : List α) : actualTwoCapacityFactors A (input.map upper) =
      (((actualTwoCapacityGreedy (fun i => (upper i : ℝ)) A input).1.map upper).prod,
        ((actualTwoCapacityGreedy (fun i => (upper i : ℝ)) A input).2.map upper).prod) := by
    unfold actualTwoCapacityFactors
    rw [actualTwoCapacityGreedy_map]
  have hrest : actualTwoCapacityFactors A
      (actualSelectedPairRemainingPrime yz (fun i => upper (p i)) :: tail.map upper) =
      (((actualTwoCapacityGreedy (fun i => (upper i : ℝ)) A
        ((if yz then p 0 else p 1) :: tail)).1.map upper).prod,
       ((actualTwoCapacityGreedy (fun i => (upper i : ℝ)) A
        ((if yz then p 0 else p 1) :: tail)).2.map upper).prod) := by
    cases yz
    · simpa only [actualSelectedPairRemainingPrime, Bool.false_eq_true, if_false,
        List.map_cons] using hmap (p 1 :: tail)
    · simpa only [actualSelectedPairRemainingPrime, if_true, List.map_cons] using hmap (p 0 :: tail)
  have hfull := hmap (p 0 :: p 1 :: p 2 :: tail)
  simp only [List.map_cons] at hfull
  have hb : ((if yz then [p 1, p 2] else [p 0, p 2]).map upper).prod =
      actualSelectedPairProduct yz (fun i => upper (p i)) := by
    cases yz <;> simp [actualSelectedPairProduct]
  unfold actualFrozenSelectedPairFactors actualFrozenSelectedPairSlots actualSelectedPairFactors
  split_ifs
  · dsimp only
    rw [hrest, hb]
  · exact congrArg (fun ab : ℕ × ℕ => (ab.1, ab.2, 1)) hfull.symm

/-- Original prime distinctness pays all three coprimality conditions for
the same fixed slot partition. -/
theorem actualFrozenSelectedPairFactors_coprime {α : Type*} (D A : ℝ) (yz : Bool)
    (upper actual : α → ℕ) (p : Fin 3 → α) (tail : List α)
    (hprime : ∀ q ∈ (p 0 :: p 1 :: p 2 :: tail).map actual, Nat.Prime q)
    (hnodup : ((p 0 :: p 1 :: p 2 :: tail).map actual).Nodup) :
    let abc := actualFrozenSelectedPairFactors D A yz upper actual p tail
    Nat.Coprime abc.1 abc.2.1 ∧ Nat.Coprime abc.1 abc.2.2 ∧
      Nat.Coprime abc.2.1 abc.2.2 := by
  exact actualPrimeVector_threeFactors_coprime _ hprime hnodup _ _ _
    (actualFrozenSelectedPairFactors_prod D A yz upper actual p tail)

/-- A support-level adapter for the existing numerical action. All three
monomial proofs are reused; the new premise is the original full support
at the already inflated level, not support for a caller-chosen remainder. -/
theorem actualSelectedPairFactors_targets_of_fullSupport {x δ θ α A : ℝ} {yz : Bool}
    (hx : 1 < x) (hδ0 : 0 < δ) (hδ : δ < 1 / 100000)
    (hθlo : 1 / 2 ≤ θ) (hθhi : θ ≤ 5 / 8)
    (hAlower : x ^ δ ≤ A) (hAupper : A ≤ x ^ (1 / 3 - δ / 2))
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (hpositive : ∀ q ∈ p 0 :: p 1 :: p 2 :: tail, 0 < q)
    (hfull : actualDwellSupport (x ^ (θ - 2 * δ)) (p 0 :: p 1 :: p 2 :: tail))
    (hgate : (actualSelectedPairProduct yz p : ℝ) *
      (actualSelectedPairRemainingPrime yz p : ℝ) ^ 2 ≤ x ^ (θ - 2 * δ))
    (hblower : x ^ (2 * θ - 1) ≤ (actualSelectedPairProduct yz p : ℝ))
    (hbupper : (actualSelectedPairProduct yz p : ℝ) ≤ x ^ actualSelectedSubproductUpper α θ) :
    let abc := actualSelectedPairFactors (x ^ (θ - 2 * δ)) A yz p tail
    (abc.1 : ℝ) ≤ A ∧
      A ^ 2 * (abc.2.1 : ℝ) * (abc.2.2 : ℝ) ^ 2 ≤ x ^ (1 - 3 * δ) ∧
      x ^ (7 * α / 32) * A * (abc.1 : ℝ) * (abc.2.1 : ℝ) ^ 5 *
        (abc.2.2 : ℝ) ^ 2 ≤ x ^ (2 - 3 * δ) ∧
      (A * (abc.2.2 : ℝ) / (abc.2.1 : ℝ)) ^ (7 / 16 : ℝ) * A * (abc.1 : ℝ) *
        (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤ x ^ (2 - 2 * δ) := by
  have hp : ∀ i, 0 < p i := by
    intro i
    fin_cases i <;> exact hpositive _ (by simp)
  have hbpos : (0 : ℝ) < actualSelectedPairProduct yz p := by
    cases yz <;> simp only [actualSelectedPairProduct, Bool.false_eq_true, if_false, if_true]
    · exact_mod_cast Nat.mul_pos (hp 0) (hp 2)
    · exact_mod_cast Nat.mul_pos (hp 1) (hp 2)
  have hA : 1 ≤ A := (show (1 : ℝ) ≤ x ^ δ by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hx.le hδ0.le).trans hAlower
  have hApos : 0 < A := zero_lt_one.trans_le hA
  by_cases hC : 1 ≤ x ^ (θ - 2 * δ) / (A * (actualSelectedPairProduct yz p : ℝ))
  · have halloc :
        let ac := actualTwoCapacityFactors A (actualSelectedPairRemainingPrime yz p :: tail)
        ac.1 * actualSelectedPairProduct yz p * ac.2 = (p 0 :: p 1 :: p 2 :: tail).prod ∧
          (ac.1 : ℝ) ≤ A ∧
          (ac.2 : ℝ) ≤ x ^ (θ - 2 * δ) / (A * (actualSelectedPairProduct yz p : ℝ)) := by
      cases yz
      · apply actualDwell_selected_p1p3_allocate hA (p 0) (p 1) (p 2) tail
          (hp 0) (hp 2) hfull ?_ hC
        simpa only [actualSelectedPairProduct, actualSelectedPairRemainingPrime,
          Bool.false_eq_true, if_false, Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using hgate
      · apply actualDwell_selected_p2p3_allocate hA (p 0) (p 1) (p 2) tail
          (hp 1) (hp 2) hfull ?_ hC
        simpa only [actualSelectedPairProduct, actualSelectedPairRemainingPrime,
          if_true, Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using hgate
    obtain ⟨hprod, ha, hc⟩ := halloc
    let ac := actualTwoCapacityFactors A (actualSelectedPairRemainingPrime yz p :: tail)
    have hprodpos : 0 < ac.1 * actualSelectedPairProduct yz p * ac.2 := by
      rw [hprod]
      exact List.prod_pos hpositive
    have hapos : (0 : ℝ) < ac.1 := by
      exact_mod_cast Nat.pos_of_mul_pos_right (Nat.pos_of_mul_pos_right hprodpos)
    have hcpos : (0 : ℝ) < ac.2 := by
      exact_mod_cast Nat.pos_of_mul_pos_left hprodpos
    have hcap : A * (actualSelectedPairProduct yz p : ℝ) * (ac.2 : ℝ) ≤ x ^ (θ - 2 * δ) := by
      calc
        _ = (ac.2 : ℝ) * (A * (actualSelectedPairProduct yz p : ℝ)) := by ring
        _ ≤ _ := (le_div_iff₀ (mul_pos hApos hbpos)).mp hc
    obtain ⟨hfirst, hsecond, hthird⟩ := selectedPair_monomials hx hApos hapos hbpos hcpos
      hcap hblower hbupper ha
    dsimp only
    rw [actualSelectedPairFactors, if_pos hC]
    exact ⟨ha,
      hfirst.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)),
      hsecond.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)),
      hthird.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))⟩
  · have hbNat : 0 < actualSelectedPairProduct yz p := by exact_mod_cast hbpos
    obtain ⟨_, ha, hfirst, hsecond, hthird⟩ := actualDwell_full_vector_repair_targets
      hx hδ0 hδ hθlo hθhi hAlower hAupper _ hpositive hfull
      (actualSelectedPairProduct yz p) hbNat hbupper (lt_of_not_ge hC)
    dsimp only
    rw [actualSelectedPairFactors, if_neg hC]
    simpa only [Nat.cast_one, one_pow, mul_one] using And.intro ha ⟨hfirst, hsecond, hthird⟩

/-- Endpoint gates use the literal logarithms of the three upper integers
in the same original cell. This step does not assume support for their
remaining vector or at the old policy level. -/
theorem actualExtendedThirdSelectedPair_endpointBounds {e κ δ x : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (he0 : 0 < e) (he : e ≤ 1 / 384)
    (hκ : κ ≤ e / 4) (hδ : δ ≤ e / 32)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ VariableEnvelope.mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (yz : Bool) (hk : actualExtendedThirdLeastWinningIndex e m j = if yz then 7 else 6)
    (hx : 1 < x) (p : Fin 3 → ℕ) (hp : ∀ i, 0 < p i)
    (hs : actualSelectedPrimeCoordinates x p ∈ actualExtendedThirdPhysicalCell m j) :
    let θ := actualExtendedThirdPairParameter e m j t yz
    (actualSelectedPairProduct yz p : ℝ) *
        (actualSelectedPairRemainingPrime yz p : ℝ) ^ 2 < x ^ (θ - 2 * δ) ∧
      x ^ (2 * θ - 1) ≤ (actualSelectedPairProduct yz p : ℝ) ∧
      (actualSelectedPairProduct yz p : ℝ) ≤
        x ^ actualSelectedSubproductUpper (1 + 3 * κ) θ := by
  obtain ⟨_, _, _, hcell⟩ := actualExtendedThirdSelectedPair_wholeCell
    he0 he hmesh hfull ht yz hk
  obtain ⟨hgate, hend⟩ := hcell _ hs
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hpow := rpow_actualSelectedPrimeCoordinates x hx p hp
  have hselected :
      x ^ (if yz then actualSelectedPrimeCoordinates x p 1 + actualSelectedPrimeCoordinates x p 2
        else actualSelectedPrimeCoordinates x p 0 + actualSelectedPrimeCoordinates x p 2) =
        (actualSelectedPairProduct yz p : ℝ) := by
    cases yz <;> simp [actualSelectedPairProduct, Real.rpow_add hxpos, hpow]
  have hstart : (actualSelectedPairProduct yz p : ℝ) *
      (actualSelectedPairRemainingPrime yz p : ℝ) ^ 2 =
      x ^ (if yz then 2 * actualSelectedPrimeCoordinates x p 0 +
          actualSelectedPrimeCoordinates x p 1 + actualSelectedPrimeCoordinates x p 2
        else actualSelectedPrimeCoordinates x p 0 +
          2 * actualSelectedPrimeCoordinates x p 1 + actualSelectedPrimeCoordinates x p 2) := by
    cases yz
    · change ((p 0 * p 2 : ℕ) : ℝ) * (p 1 : ℝ) ^ 2 = _
      rw [Nat.cast_mul, ← hpow 0, ← hpow 1, ← hpow 2,
        ← Real.rpow_mul_natCast hxpos.le, ← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
      congr 1
      ring
    · change ((p 1 * p 2 : ℕ) : ℝ) * (p 0 : ℝ) ^ 2 = _
      rw [Nat.cast_mul, ← hpow 0, ← hpow 1, ← hpow 2,
        ← Real.rpow_mul_natCast hxpos.le, ← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
      congr 1
      ring
  have hpert := actualSelectedSubproductV_residue_margin he0.le hκ hend
  have hcrit := (actualSelectedSubproduct_critical_iff _ _ _).mp
    (show actualExtendedThirdPairParameter e m j t yz ≤
      actualSelectedSubproductV (1 + 3 * κ)
        (if yz then actualSelectedPrimeCoordinates x p 1 + actualSelectedPrimeCoordinates x p 2
          else actualSelectedPrimeCoordinates x p 0 + actualSelectedPrimeCoordinates x p 2) by
      linarith)
  refine ⟨?_, ?_, ?_⟩
  · rw [hstart]
    apply Real.rpow_lt_rpow_of_exponent_lt hx
    linarith
  · rw [← hselected]
    exact Real.rpow_le_rpow_of_exponent_le hx.le hcrit.1
  · rw [← hselected]
    exact Real.rpow_le_rpow_of_exponent_le hx.le hcrit.2

/-- The three upper targets for one computed whole-box partition. Original
lambda support and the universal (R+1)*tau budget pay full upper support;
the actual whole-cell pair action pays its extra square gate and critical
interval. The caller never supplies a slot assignment or remainder budget. -/
theorem actualExtendedThirdSelectedPair_frozenUpperTargets
    {α : Type*} {e κ δ ρ τ x A : ℝ} {m : ℕ} {j : ActualExtendedThirdDyadicLabel m}
    (he0 : 0 < e) (he : e ≤ 1 / 384) (hκ : κ ≤ e / 4)
    (hδ0 : 0 < δ) (hδ : δ < 1 / 100000) (hδfine : δ ≤ e / 32)
    (hρ : 0 < ρ) (hτ : 0 ≤ τ)
    (hwidth : τ * (actualRoughVectorRankBound ρ + 1) ≤ e / 2)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ VariableEnvelope.mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (yz : Bool) (hk : actualExtendedThirdLeastWinningIndex e m j = if yz then 7 else 6)
    (hx : 1 < x) (actual upper : α → ℕ) (p : Fin 3 → α) (tail : List α)
    (hpositive : ∀ i ∈ p 0 :: p 1 :: p 2 :: tail, 0 < actual i)
    (hrough : ∀ i ∈ p 0 :: p 1 :: p 2 :: tail, x ^ ρ ≤ (actual i : ℝ))
    (hbelow : ∀ i ∈ p 0 :: p 1 :: p 2 :: tail, actual i ≤ upper i)
    (hinflate : ∀ i ∈ p 0 :: p 1 :: p 2 :: tail, (upper i : ℝ) ≤ x ^ τ * (actual i : ℝ))
    (hs : actualSelectedPrimeCoordinates x (fun i => upper (p i)) ∈
      actualExtendedThirdPhysicalCell m j)
    (hsupport : actualDwellSupport (x ^ actualExtendedThirdPhysicalLevel e m j)
      ((p 0 :: p 1 :: p 2 :: tail).map actual))
    (hAlower : x ^ δ ≤ A) (hAupper : A ≤ x ^ (1 / 3 - δ / 2)) :
    let θ := actualExtendedThirdPairParameter e m j t yz
    let abc := actualFrozenSelectedPairFactors (x ^ (θ - 2 * δ)) A yz upper upper p tail
    (abc.1 : ℝ) ≤ A ∧
      A ^ 2 * (abc.2.1 : ℝ) * (abc.2.2 : ℝ) ^ 2 ≤ x ^ (1 - 3 * δ) ∧
      x ^ (7 * (1 + 3 * κ) / 32) * A * (abc.1 : ℝ) * (abc.2.1 : ℝ) ^ 5 *
        (abc.2.2 : ℝ) ^ 2 ≤ x ^ (2 - 3 * δ) ∧
      (A * (abc.2.2 : ℝ) / (abc.2.1 : ℝ)) ^ (7 / 16 : ℝ) * A * (abc.1 : ℝ) *
        (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤ x ^ (2 - 2 * δ) := by
  have huppositive : ∀ i ∈ p 0 :: p 1 :: p 2 :: tail, 0 < upper i :=
    fun i hi => (hpositive i hi).trans_le (hbelow i hi)
  have hp : ∀ i, 0 < upper (p i) := by
    intro i
    fin_cases i <;> exact huppositive _ (by simp)
  have huppersupport := actualExtendedThirdSelectedPair_upperSupport
    he0 he hδfine hρ hτ hwidth hmesh hfull ht yz hk hx actual upper
      (p 0 :: p 1 :: p 2 :: tail) (by simp) hpositive hrough hinflate hsupport
  obtain ⟨hθlo, hθhi, _, _⟩ := actualExtendedThirdSelectedPair_wholeCell
    he0 he hmesh hfull ht yz hk
  obtain ⟨hgate, hblower, hbupper⟩ := actualExtendedThirdSelectedPair_endpointBounds
    he0 he hκ hδfine hmesh hfull ht yz hk hx (fun i => upper (p i)) hp hs
  dsimp only
  rw [actualFrozenSelectedPairFactors_at_upper]
  apply actualSelectedPairFactors_targets_of_fullSupport hx hδ0 hδ hθlo hθhi.le
    hAlower hAupper (fun i => upper (p i)) (tail.map upper)
  · change ∀ q ∈ (p 0 :: p 1 :: p 2 :: tail).map upper, 0 < q
    simpa only [List.forall_mem_map] using huppositive
  · simpa only [List.map_cons] using huppersupport
  · exact hgate.le
  · exact hblower
  · exact hbupper

end

end ImbalancedChen
