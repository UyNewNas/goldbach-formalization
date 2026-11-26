import ImbalancedChen.P2FiniteMarkedGamma5UnitTailProduct
import ImbalancedChen.P2FiniteMarkedGamma5IntegerSupport
import ImbalancedChen.P2FiniteMarkedGamma5FrozenConstants
import ImbalancedChen.P2MarkedPrimeProductFibreCore
import ImbalancedChen.PowerErrorBudget
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Interval.Finset.Nat

/-! Count the nonzero, scale-admitted part of the original physical
Gamma5 profile for a unit rough cofactor. Its two fresh coordinates
remain ordered positions, and all old coordinates are retained.
The two scale restrictions are tests on individual tuples. -/
namespace ImbalancedChen.P2FiniteMarkedGamma5UnitTailCount

noncomputable section
open Filter Finset Real
open Part5OriginalH430FrozenRootRefinement (frozenLeafCutoffFloor frozenResidualFloor)
open P2FiniteMarkedGamma5ActualRank (frozenSourceRankBound)
open P2FiniteMarkedGamma5PhysicalExtension (PhysicalPoint physicalProduct physicalProfile
  physicalProfile_nonzero_lower)
open P2FiniteMarkedGamma5EulerWordBudget (finToPhysical)
open P2FiniteMarkedGamma5IntegerSupport (physicalProduct_finToPhysical)
open P2FiniteMarkedGamma5UnitTailProduct (unit_tail_product_le)
open scoped Classical BigOperators Topology

abbrev Tuple (N k : ℕ) := Fin (k + (2 + 0)) → Fin (2*N + 1)

def point {N k : ℕ} (t : Tuple N k) : PhysicalPoint k 0 :=
  finToPhysical k 0 (fun i => ((t i).val : ℝ))

def oldProduct {N k : ℕ} (t : Tuple N k) : ℝ :=
  ∏ i : Fin k, point t (.inl i)

def saving : ℝ := frozenResidualFloor * (38 / 29 : ℝ)

private theorem saving_pos : 0 < saving := by
  unfold saving frozenResidualFloor
  positivity

def cap (N : ℕ) : ℝ := exp 2 * (N : ℝ) / (N : ℝ) ^ saving

theorem cap_eq_power {N : ℕ} (hN : 0 < N) :
    cap N = exp 2 * (N : ℝ) ^ (1 - saving) := by
  rw [rpow_sub (Nat.cast_pos.mpr hN), rpow_one]
  unfold cap
  ring

def unitTuples (N k : ℕ) (Q width : ℝ) : Finset (Tuple N k) :=
  (Part3.labelledPrimeTuples (k + (2 + 0)) (2*N)).filter fun t =>
    physicalProfile (log Q) (N : ℝ) width ((N : ℝ) ^ frozenLeafCutoffFloor) (point t) ≠ 0 ∧
      (N : ℝ) ^ frozenResidualFloor ≤ Q / oldProduct t ∧
      (Q / oldProduct t) ^ (2 : ℕ) ≤ (N : ℝ) / oldProduct t

/-- The original physical support estimate applied only at the selected
tuple. Positivity of its prefix product, including the empty old word,
and positivity of Q follow from the original floor and the scale test. -/
theorem unit_product_le_cap {N k : ℕ} {Q width : ℝ} (hN : 0 < N)
    (hw : 0 < width) (hw1 : width ≤ 1) {t : Tuple N k}
    (ht : t ∈ unitTuples N k Q width) : (Part3.labelledProduct t : ℝ) ≤ cap N := by
  obtain ⟨_, hne, hR, hscale⟩ := mem_filter.mp ht
  have h0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hb : 0 < (N : ℝ) ^ frozenLeafCutoffFloor := rpow_pos_of_pos h0 _
  have hd : 0 < oldProduct t :=
    prod_pos (fun i _ => (half_pos hb).trans (physicalProfile_nonzero_lower hb hne (.inl i)))
  have hR0 : 0 < Q / oldProduct t := (rpow_pos_of_pos h0 _).trans_le hR
  have hQ : 0 < Q := by simpa only [zero_mul] using (lt_div_iff₀ hd).mp hR0
  have hg : 0 ≤ (38 / 29 : ℝ) := by norm_num
  have hpow : (N : ℝ) ^ saving ≤ (Q / oldProduct t) ^ (38 / 29 : ℝ) := by
    unfold saving
    rw [rpow_mul h0.le]
    exact rpow_le_rpow (rpow_nonneg h0.le _) hR hg
  have hexp : exp (2 * width) ≤ exp 2 := exp_le_exp.mpr (by linarith)
  have hprod : physicalProduct (point t) = (Part3.labelledProduct t : ℝ) := by
    simp only [point, physicalProduct_finToPhysical, Part3.labelledProduct, Nat.cast_prod]
  rw [← hprod]
  calc
    _ ≤ exp (2 * width) * (N : ℝ) / (Q / oldProduct t) ^ (38 / 29 : ℝ) :=
      unit_tail_product_le hQ hb hw hne hscale
    _ ≤ exp 2 * (N : ℝ) / (Q / oldProduct t) ^ (38 / 29 : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hexp h0.le)
        (rpow_nonneg hR0.le _)
    _ ≤ cap N := div_le_div_of_nonneg_left (mul_nonneg (exp_pos _).le h0.le)
      (rpow_pos_of_pos h0 _) hpow

/-- Full tuple multiplicities are charged to the original prime-product
fibre theorem, even when a given product has several orderings. The
range of positive integer products has at most cap N elements. -/
theorem unit_card_le {N k : ℕ} {Q width : ℝ} (hN : 0 < N)
    (hw : 0 < width) (hw1 : width ≤ 1) :
    ((unitTuples N k Q width).card : ℝ) ≤
      (((k+2)^(k+2) : ℕ) : ℝ) * cap N := by
  let S := unitTuples N k Q width
  let I := Ioc 0 ⌊cap N⌋₊
  have hs : S ⊆ Part3.labelledPrimeTuples (k + (2 + 0)) (2*N) := filter_subset _ _
  have hm {t} (ht : t ∈ S) : Part3.labelledProduct t ∈ I := by
    have hprime := (mem_filter.mp (hs ht)).2
    exact mem_Ioc.mpr ⟨prod_pos (fun i _ => (hprime i).pos),
      Nat.le_floor (unit_product_le_cap hN hw hw1 ht)⟩
  have hc : S.card = ∑ m ∈ I, (S.filter (fun t => Part3.labelledProduct t = m)).card :=
    card_eq_sum_card_fiberwise (fun _ ht => hm ht)
  have hcap : 0 ≤ cap N := div_nonneg
    (mul_nonneg (exp_pos _).le (Nat.cast_nonneg N)) (rpow_nonneg (Nat.cast_nonneg N) _)
  change (S.card : ℝ) ≤ _
  rw [hc, Nat.cast_sum]
  calc
    _ ≤ ∑ _m ∈ I, (((k+2)^(k+2) : ℕ) : ℝ) := sum_le_sum (fun m _ => by
      exact_mod_cast p5z_marked_prime_product_fibre_card_le S hs m)
    _ = (((k+2)^(k+2) : ℕ) : ℝ) * (⌊cap N⌋₊ : ℝ) := by
      simp [I, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.floor_le hcap) (Nat.cast_nonneg _)

private theorem fixed_rank_payment (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (Q width : ℝ), 0 < width → width ≤ 1 →
      (log (N : ℝ) / (N : ℝ)) * ((unitTuples N k Q width).card : ℝ) ≤ ε := by
  let A : ℝ := (((k+2)^(k+2) : ℕ) : ℝ) * exp 2
  have H : Tendsto (fun N : ℕ => A * (log (N : ℝ) / (N : ℝ) ^ saving)) atTop (𝓝 0) := by
    simpa only [pow_one, mul_zero] using (tendsto_nat_log_pow_div_rpow 1 saving_pos).const_mul A
  filter_upwards [H.eventually (gt_mem_nhds hε), eventually_gt_atTop (1 : ℕ)] with N hp hN
  intro Q width hw hw1
  have hR : (1 : ℝ) < N := by exact_mod_cast hN
  have h0 := zero_lt_one.trans hR
  have hn : 0 ≤ (log (N : ℝ) / (N : ℝ)) := div_nonneg (log_pos hR).le h0.le
  calc
    _ ≤ (log (N : ℝ) / (N : ℝ)) * ((((k+2)^(k+2) : ℕ) : ℝ) * cap N) :=
      mul_le_mul_of_nonneg_left (unit_card_le (by omega : 0 < N) hw hw1) hn
    _ = A * (log (N : ℝ) / (N : ℝ) ^ saving) := by
      unfold cap
      dsimp only [A]
      field_simp [h0.ne', (rpow_pos_of_pos h0 saving).ne'] <;> ring
    _ ≤ ε := hp.le

/-- The scale threshold is uniform in all old ranks with k+2 ≤ K, as
well as all targets and widths satisfying the original inequalities. -/
theorem eventually_unitTuples_payment {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (Q width : ℝ) (k : ℕ), 0 < width → width ≤ 1 →
      k + 2 ≤ frozenSourceRankBound →
      (log (N : ℝ) / (N : ℝ)) * ((unitTuples N k Q width).card : ℝ) ≤ ε := by
  have H : ∀ᶠ N : ℕ in atTop, ∀ j : Fin (frozenSourceRankBound + 1),
      ∀ (Q width : ℝ), 0 < width → width ≤ 1 →
        (log (N : ℝ) / (N : ℝ)) * ((unitTuples N j.val Q width).card : ℝ) ≤ ε :=
    eventually_all.mpr (fun j => fixed_rank_payment j.val hε)
  filter_upwards [H] with N hNN
  intro Q width k hw hw1 hkr
  exact hNN ⟨k, by omega⟩ Q width hw hw1

end
end ImbalancedChen.P2FiniteMarkedGamma5UnitTailCount
