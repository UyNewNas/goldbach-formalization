import ImbalancedChen.P5OriginalU5UnitMark
import ImbalancedChen.P5PrimeFixedWidthMass
import ImbalancedChen.P2GammaU5PlateauMass

/-! Positive arithmetic weights at the actual unit quotient. The small
mark ranges over a fixed exponent interval. The large mark can range
over a prescribed multiplicative window after deleting primes dividing N. -/
namespace ImbalancedChen.P5OriginalU5MarkedMass

noncomputable section
open Classical Filter Topology
open scoped BigOperators
open P5OriginalU5CausalFinite
open P5OriginalU5PlateauPrimeBV (Policy integerRho fullModulus)
open P2GammaSelectedPhysicalTheta (reciprocalMass)

def powerBand (N : ℕ) (a b : ℝ) : Finset ℕ :=
  roughPrimeFinset N ⌈(N : ℝ)^b⌉₊ ((N : ℝ)^a) ((N : ℝ)^b)

theorem mem_powerBand {N p : ℕ} {a b : ℝ} : p ∈ powerBand N a b ↔
    p.Prime ∧ ¬p ∣ N ∧ (N : ℝ)^a ≤ p ∧ (p : ℝ) < (N : ℝ)^b :=
  mem_roughPrimeFinset_iff_of_cutoff_le_cap (Nat.le_ceil _)

def multiplicativeBand (N : ℕ) (x : ℝ) : Finset ℕ :=
  (P5PrimeFixedWidthMass.window x).filter (fun p => ¬p ∣ N)

def unitWeight (N : ℕ) (e : ℝ) (P : Policy) (t : ℕ × ℕ) : ℝ :=
  (integerRho N e P (fullModulus t 1) : ℝ)

def activeUnits (N : ℕ) (e : ℝ) (P : Policy) (S : Finset (ℕ × ℕ)) :=
  S.filter (fun t => integerRho N e P (fullModulus t 1) ≠ 0)

theorem active_units_data {N : ℕ} (hN : 2 ≤ N) {e : ℝ} (he : 0 < e) (he8 : e < 1/8)
    (P : Policy) (S : Finset (ℕ × ℕ)) (hS : S ⊆ pairSupport N) :
    activeUnits N e P S = S ∧ ∀ t ∈ S, unitWeight N e P t = 1 := by
  have hunit (t : ℕ × ℕ) (ht : t ∈ S) :=
    (P5OriginalU5UnitMark.original_integer_unit hN he he8 P (hS ht)).2
  refine ⟨Finset.filter_true_of_mem (fun t ht => by rw [hunit t ht]; norm_num), ?_⟩
  intro t ht
  simp only [unitWeight, hunit t ht, Int.cast_one]

theorem reciprocal_product (S T : Finset ℕ) :
    reciprocalMass (S.product T) (fun _ => 1) =
      (∑ p ∈ S, 1/(p : ℝ)) * (∑ q ∈ T, 1/(q : ℝ)) := by
  rw [reciprocalMass, Finset.sum_product, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simp [Nat.cast_mul, one_div, mul_inv_rev, mul_comm]

theorem active_product_mass {N : ℕ} (hN : 2 ≤ N) {e : ℝ}
    (he : 0 < e) (he8 : e < 1/8) (P : Policy) (S T : Finset ℕ)
    (hST : S.product T ⊆ pairSupport N) :
    reciprocalMass (activeUnits N e P (S.product T)) (unitWeight N e P) =
      (∑ p ∈ S, 1/(p : ℝ)) * (∑ q ∈ T, 1/(q : ℝ)) := by
  obtain ⟨hset,hw⟩ := active_units_data hN he he8 P _ hST
  rw [hset, ← reciprocal_product]
  exact Finset.sum_congr rfl (fun t ht => by rw [hw t ht])

theorem eventually_powerBand_mass {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ᶠ N : ℕ in atTop, Real.log (b/a)/4 ≤ ∑ p ∈ powerBand N a b, 1/(p : ℝ) := by
  have hlog := Real.log_pos ((one_lt_div ha).mpr hab)
  have h := (tendsto_actualPrimeReciprocalMass ha hab).eventually
    (gt_mem_nhds (show Real.log (b/a)/2 < Real.log (b/a) by linarith))
  filter_upwards [h] with N hN
  change Real.log (b/a)/2 < ∑ p ∈ powerBand N a b, 1/((p : ℝ)-1) at hN
  have hshift : (∑ p ∈ powerBand N a b, 1/((p : ℝ)-1)) ≤
      2*(∑ p ∈ powerBand N a b, 1/(p : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_powerBand.mp hp).1.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hp1 : 0 < (p : ℝ)-1 := by linarith
    rw [mul_one_div]
    exact (div_le_div_iff₀ hp1 hp0).mpr (by linarith)
  linarith

theorem eventually_multiplicativeBand_mass (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ∀ᶠ N : ℕ in atTop, 1/(128*Real.log (N : ℝ)) ≤
      ∑ p ∈ multiplicativeBand N ((N : ℝ)^a), 1/(p : ℝ) := by
  have hg : Tendsto (fun N : ℕ => (N : ℝ)^a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have herr := (tendsto_nat_log_pow_div_rpow 2 ha).eventually
    (lt_mem_nhds (show (0 : ℝ) < Real.log 2/128 by positivity))
  filter_upwards [hg.eventually P5PrimeFixedWidthMass.eventually_window_mass,
    herr, eventually_ge_atTop (2 : ℕ)] with N hwhole herr hN
  let x := (N : ℝ)^a
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hx : 0 < x := Real.rpow_pos_of_pos (zero_lt_one.trans hn) _
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hn
  have hlogx : Real.log x = a*Real.log (N : ℝ) := Real.log_rpow (zero_lt_one.trans hn) _
  have hpay := chen_prime_centre_removal_bound (show 0 < N by omega)
    (P5PrimeFixedWidthMass.window x) (fun p => 1/(p : ℝ)) (E := 1/x)
    (by positivity) (fun p hp => ((P5PrimeFixedWidthMass.mem_window hx.le).mp hp).1)
    (fun p hp _ => by
      rw [abs_of_nonneg (by positivity : 0 ≤ 1/(p : ℝ))]
      exact one_div_le_one_div_of_le hx ((P5PrimeFixedWidthMass.mem_window hx.le).mp hp).2.1.le)
  have he : (1/x)*(Real.log (N : ℝ)/Real.log 2) ≤ 1/(128*Real.log (N : ℝ)) := by
    change (Real.log (N : ℝ))^2 / x < Real.log 2/128 at herr
    have hh := (div_lt_div_iff₀ hx (by norm_num : (0 : ℝ)<128)).mp herr
    rw [show (1/x)*(Real.log (N : ℝ)/Real.log 2) = Real.log (N : ℝ)/(x*Real.log 2) by
      field_simp [hx.ne', hlog2.ne'] <;> ring]
    apply (div_le_div_iff₀ (mul_pos hx hlog2) (by positivity)).mpr
    nlinarith only [hh]
  have hstart : 1/(64*Real.log (N : ℝ)) ≤ ∑ p ∈ P5PrimeFixedWidthMass.window x, 1/(p : ℝ) := by
    refine le_trans ?_ hwhole
    rw [hlogx]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right ha1 hlogN.le]
  have hbudget : 1/(64*Real.log (N : ℝ)) = 2*(1/(128*Real.log (N : ℝ))) := by
    field_simp [hlogN.ne'] <;> ring
  change _ ≤ ∑ p ∈ (P5PrimeFixedWidthMass.window x).filter (fun p => ¬p ∣ N), 1/(p : ℝ)
  linarith [(abs_le.mp hpay).1]

end
end ImbalancedChen.P5OriginalU5MarkedMass
