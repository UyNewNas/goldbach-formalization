import ImbalancedChen.ActualFrozenCapacitySlots

/-!
# Original rough-vector length and upper-endpoint support budgets

The positive rough exponent is fixed before the scale x.  The original
full D-well support bounds its total product, hence the original number of
prime slots independently of x.  Enlarging each slot by at most x^tau
costs at most (R+1)*tau in every original prefix-square test.

For the actual chosen pair, the previously paid lambda+e<=theta margin
absorbs this entire endpoint cost and 2*delta.  No support predicate for
a replacement remainder, assignment, or distribution estimate is an input.
The resulting original upper vector is suitable for one auxiliary frozen
endpoint allocation; it is not identified with the tuplewise greedy run.
-/

namespace ImbalancedChen

noncomputable section

open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

/-- This bound depends on the fixed rough exponent, not on the scale. -/
def actualRoughVectorRankBound (ρ : ℝ) : ℕ := ⌊(5 / 8 : ℝ) / ρ⌋₊

theorem actualDwellSupport_prod_le {D : ℝ} (input : List ℕ) (hne : input ≠ [])
    (hpositive : ∀ p ∈ input, 0 < p) (hfull : actualDwellSupport D input) :
    (input.prod : ℝ) ≤ D := by
  induction input using List.reverseRecOn with
  | nil => exact (hne rfl).elim
  | append_singleton input p _ih =>
      have hlast := (prefixSquareBound_append_singleton_iff
        (fun p : ℕ => (p : ℝ)) D input p).mp hfull |>.2
      have hp : (1 : ℝ) ≤ p := by
        have hpNat : 1 ≤ p := hpositive p (by simp)
        exact_mod_cast hpNat
      have hp2 : (p : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
      have hpre : (0 : ℝ) ≤ (input.map (fun p : ℕ => (p : ℝ))).prod := by
        rw [actualNatList_cast_prod]
        exact Nat.cast_nonneg _
      have h := (mul_le_mul_of_nonneg_left hp2 hpre).trans hlast
      simpa only [List.prod_append, List.prod_cons, List.prod_nil, mul_one,
        Nat.cast_mul, actualNatList_cast_prod] using h

/-- Every original rough slot is counted, including repeated slots. Prime
distinctness is needed later for squarefreeness, not for this length bound. -/
theorem actualRoughPrimeVector_length_le {x ρ lam0 : ℝ}
    (hx : 1 < x) (hρ : 0 < ρ) (hlevel : lam0 ≤ 5 / 8)
    (input : List ℕ) (hne : input ≠ [])
    (hpositive : ∀ p ∈ input, 0 < p)
    (hrough : ∀ p ∈ input, x ^ ρ ≤ (p : ℝ))
    (hfull : actualDwellSupport (x ^ lam0) input) :
    input.length ≤ actualRoughVectorRankBound ρ := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hprod := actualDwellSupport_prod_le input hne hpositive hfull
  have hlower := List.prod_map_le_prod_map₀ (fun _ : ℕ => x ^ ρ)
    (fun p : ℕ => (p : ℝ))
    (fun _ _ => Real.rpow_nonneg hxpos.le ρ) hrough
  have hpow : x ^ (ρ * (input.length : ℝ)) ≤ x ^ (5 / 8 : ℝ) := by
    rw [Real.rpow_mul hxpos.le, Real.rpow_natCast]
    apply le_trans ?_ (hprod.trans (Real.rpow_le_rpow_of_exponent_le hx.le hlevel))
    simpa only [List.map_const', List.prod_replicate, actualNatList_cast_prod] using hlower
  have hlen : ρ * (input.length : ℝ) ≤ 5 / 8 := (Real.rpow_le_rpow_left_iff hx).mp hpow
  unfold actualRoughVectorRankBound
  apply (Nat.le_floor_iff (div_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 8) hρ.le)).mpr
  apply (le_div_iff₀ hρ).mpr
  simpa only [mul_comm] using hlen

private theorem mapped_upper_prod_le_inflation {α : Type*} (x τ : ℝ) (hx : 0 < x)
    (actual upper : α → ℕ) (input : List α)
    (hsize : ∀ i ∈ input, (upper i : ℝ) ≤ x ^ τ * (actual i : ℝ)) :
    (input.map (fun i => (upper i : ℝ))).prod ≤
      (x ^ τ) ^ input.length * (input.map (fun i => (actual i : ℝ))).prod := by
  revert hsize
  induction input with
  | nil => intro _; simp
  | cons i input ih =>
      intro hsize
      have hi := hsize i (by simp)
      have ht := ih (fun j hj => hsize j (List.mem_cons_of_mem i hj))
      have hprod0 : 0 ≤ (input.map (fun j => (upper j : ℝ))).prod := by
        simpa only [← actualNatList_cast_prod (input.map upper), List.map_map, Function.comp_def]
          using (Nat.cast_nonneg (α := ℝ) (input.map upper).prod)
      have h := mul_le_mul hi ht hprod0
        (mul_nonneg (Real.rpow_nonneg hx.le τ) (Nat.cast_nonneg _))
      simpa only [List.map_cons, List.prod_cons, List.length_cons, pow_succ,
        mul_assoc, mul_comm, mul_left_comm] using h

/-- The complete original upper vector pays every square test. At index i
the cost is (i+2)*tau, bounded by (R+1)*tau for all original slots. -/
theorem actualDwellSupport_upper_inflation {α : Type*} {x τ lam0 lam1 : ℝ} {R : ℕ}
    (hx : 1 < x) (hτ : 0 ≤ τ) (actual upper : α → ℕ) (input : List α)
    (hlen : input.length ≤ R)
    (hsize : ∀ i ∈ input, (upper i : ℝ) ≤ x ^ τ * (actual i : ℝ))
    (hfull : actualDwellSupport (x ^ lam0) (input.map actual))
    (hbudget : lam0 + τ * (R + 1) ≤ lam1) :
    actualDwellSupport (x ^ lam1) (input.map upper) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  intro i hi
  have hi' : i < input.length := by simpa only [List.length_map] using hi
  have hs := hfull i (by simpa only [List.length_map] using hi')
  simp only [← List.map_take, List.map_map, List.getElem_map, Function.comp_def] at hs ⊢
  have hpre := mapped_upper_prod_le_inflation x τ hxpos actual upper (input.take i)
    (fun j hj => hsize j (List.mem_of_mem_take hj))
  rw [List.length_take, Nat.min_eq_left hi'.le] at hpre
  have hq := hsize input[i] (List.getElem_mem hi')
  have hq2 := pow_le_pow_left₀ (Nat.cast_nonneg (upper input[i])) hq 2
  have hactual0 : 0 ≤ ((input.take i).map (fun j => (actual j : ℝ))).prod := by
    simpa only [← actualNatList_cast_prod ((input.take i).map actual), List.map_map, Function.comp_def]
      using (Nat.cast_nonneg (α := ℝ) ((input.take i).map actual).prod)
  calc
    _ ≤ ((x ^ τ) ^ i * ((input.take i).map (fun j => (actual j : ℝ))).prod) *
        (x ^ τ * (actual input[i] : ℝ)) ^ 2 :=
      mul_le_mul hpre hq2 (sq_nonneg _) (mul_nonneg (pow_nonneg (Real.rpow_nonneg hxpos.le _) _) hactual0)
    _ = (x ^ τ) ^ (i + 2) *
        (((input.take i).map (fun j => (actual j : ℝ))).prod * (actual input[i] : ℝ) ^ 2) := by
      rw [pow_add]
      ring
    _ ≤ (x ^ τ) ^ (i + 2) * x ^ lam0 :=
      mul_le_mul_of_nonneg_left hs (pow_nonneg (Real.rpow_nonneg hxpos.le _) _)
    _ = x ^ (τ * (i + 2 : ℕ) + lam0) := by
      rw [Real.rpow_add hxpos, Real.rpow_mul_natCast hxpos.le]
    _ ≤ x ^ lam1 := by
      apply Real.rpow_le_rpow_of_exponent_le hx.le
      have hiR : ((i + 2 : ℕ) : ℝ) ≤ (R : ℝ) + 1 := by
        exact_mod_cast (show i + 2 ≤ R + 1 by omega)
      nlinarith

/-- The actual pair's pre-existing surplus pays the original full endpoint
vector, with rank and width fixed before the scale varies. -/
theorem actualExtendedThirdSelectedPair_upperSupport
    {α : Type*} {e δ ρ τ x : ℝ} {m : ℕ} {j : ActualExtendedThirdDyadicLabel m}
    (he0 : 0 < e) (he : e ≤ 1 / 384) (hδ : δ ≤ e / 32)
    (hρ : 0 < ρ) (hτ : 0 ≤ τ)
    (hwidth : τ * (actualRoughVectorRankBound ρ + 1) ≤ e / 2)
    (hmesh : actualExtendedThirdDyadicStep m ≤ e / 32)
    (hfull : actualExtendedThirdDyadicHi m j 0 ≤ VariableEnvelope.mu - 4 * e)
    {t : Fin 3 → ℝ} (ht : t ∈ actualExtendedThirdPhysicalCell m j)
    (yz : Bool) (hk : actualExtendedThirdLeastWinningIndex e m j = if yz then 7 else 6)
    (hx : 1 < x) (actual upper : α → ℕ) (input : List α) (hne : input ≠ [])
    (hpositive : ∀ i ∈ input, 0 < actual i)
    (hrough : ∀ i ∈ input, x ^ ρ ≤ (actual i : ℝ))
    (hsize : ∀ i ∈ input, (upper i : ℝ) ≤ x ^ τ * (actual i : ℝ))
    (hsupport : actualDwellSupport (x ^ actualExtendedThirdPhysicalLevel e m j)
      (input.map actual)) :
    actualDwellSupport (x ^ (actualExtendedThirdPairParameter e m j t yz - 2 * δ))
      (input.map upper) := by
  obtain ⟨_, hθhi, hlevel, _⟩ := actualExtendedThirdSelectedPair_wholeCell
    he0 he hmesh hfull ht yz hk
  have hlen : input.length ≤ actualRoughVectorRankBound ρ := by
    have h := actualRoughPrimeVector_length_le hx hρ
      (show actualExtendedThirdPhysicalLevel e m j ≤ 5 / 8 by linarith)
      (input.map actual) (by intro heq; exact hne (List.map_eq_nil_iff.mp heq))
      (by simpa only [List.forall_mem_map] using hpositive)
      (by simpa only [List.forall_mem_map] using hrough) hsupport
    simpa only [List.length_map] using h
  exact actualDwellSupport_upper_inflation hx hτ actual upper input hlen hsize hsupport (by linarith)

end

end ImbalancedChen
