import ImbalancedChen.P5OriginalPrimeEndpointLogPayment
import ImbalancedChen.OrderedBad
import ImbalancedChen.P5zPositiveFamilyBudget

/-!
# Sharp endpoint transfer for an arbitrary original prime-pair source

Finite stepped domains and keep masks are the literal source. Product
fibers have at most two labels (one when sorted), including prime squares.
No label is silently dropped when products are pushed forward. The same
physical rho occurs in the sharp test, smooth test and coprime mean.
Zero distance is excluded only from odd-product / even-centre data.
SOURCE_WRITTEN / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.P5PrimePairEndpoint

noncomputable section
open scoped BigOperators
open Classical Filter Topology
open P5OriginalPrimeEndpoint

def product (t : ℕ × ℕ) : ℕ := t.1 * t.2

def productImage (S : Finset (ℕ × ℕ)) : Finset ℕ := S.image product

def productWeight (S : Finset (ℕ × ℕ)) (W : (ℕ × ℕ) → ℝ) (m : ℕ) : ℝ :=
  ∑ t ∈ S with product t = m, W t

/-- Reuse the existing proved prime.dvd_mul/cancellation uniqueness.
Both orientations survive and a square has only its literal single label. -/
theorem product_fiber_card_le_two (S : Finset (ℕ × ℕ))
    (hprime : ∀ t ∈ S, Nat.Prime t.1 ∧ Nat.Prime t.2) (m : ℕ) :
    ((S.filter (fun t => product t = m)).card : ℝ) ≤ 2 := by
  by_cases hempty : S.filter (fun t => product t = m) = ∅
  · simp [hempty]
  obtain ⟨t,ht⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have htp := hprime t (Finset.mem_filter.mp ht).1
  have hsub : S.filter (fun u => product u = m) ⊆ {t,(t.2,t.1)} := by
    intro u hu
    have hup := hprime u (Finset.mem_filter.mp hu).1
    have heq : u.1*u.2 = t.1*t.2 :=
      (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp ht).2.symm
    rcases (prime_mul_eq_prime_mul_iff hup.1 hup.2 htp.1 htp.2).mp heq with
      hsame | hswap
    · have hu : u = t := Prod.ext hsame.1 hsame.2
      simp [hu]
    · have hu : u = (t.2,t.1) := Prod.ext hswap.1 hswap.2
      simp [hu]
  have hcard : (S.filter (fun u => product u = m)).card ≤ 2 := by
    calc
      _ ≤ ({t,(t.2,t.1)} : Finset (ℕ × ℕ)).card := Finset.card_le_card hsub
      _ ≤ 2 := by by_cases h : t = (t.2,t.1) <;> simp [h]
  exact_mod_cast hcard

/-- Weak sorting already removes the swap ambiguity; squares are retained. -/
theorem product_fiber_card_le_one_of_sorted (S : Finset (ℕ × ℕ))
    (hprime : ∀ t ∈ S, Nat.Prime t.1 ∧ Nat.Prime t.2)
    (hsorted : ∀ t ∈ S, t.1 ≤ t.2) (m : ℕ) :
    ((S.filter (fun t => product t = m)).card : ℝ) ≤ 1 := by
  have hcard : (S.filter (fun t => product t = m)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro t ht u hu
    have htS := (Finset.mem_filter.mp ht).1
    have huS := (Finset.mem_filter.mp hu).1
    have heq : t.1*t.2 = u.1*u.2 :=
      (Finset.mem_filter.mp ht).2.trans (Finset.mem_filter.mp hu).2.symm
    have h := ordered_prime_factors_unique (hprime t htS).1 (hprime t htS).2
      (hprime u huS).1 (hprime u huS).2 (hsorted t htS) (hsorted u huS) heq
    exact Prod.ext h.1 h.2
  exact_mod_cast hcard

/-- Exact weighted pushforward; it keeps both labels of a swapped product. -/
theorem productWeight_sum (S : Finset (ℕ × ℕ)) (W : (ℕ × ℕ) → ℝ) (F : ℕ → ℝ) :
    (∑ m ∈ productImage S, productWeight S W m * F m) =
      ∑ t ∈ S, W t * F (product t) := by
  have hf := Finset.sum_fiberwise_of_maps_to (s := S) (t := productImage S) (g := product)
    (fun t ht => Finset.mem_image_of_mem product ht) (fun t => W t * F (product t))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro m hm
  unfold productWeight
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [(Finset.mem_filter.mp ht).2]

theorem abs_productWeight_le_fiber_card (S : Finset (ℕ × ℕ)) (W : (ℕ × ℕ) → ℝ)
    (hW : ∀ t ∈ S, |W t| ≤ 1) (m : ℕ) :
    |productWeight S W m| ≤ ((S.filter (fun t => product t = m)).card : ℝ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ t ∈ S with product t = m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact hW t (Finset.mem_filter.mp ht).1
    _ = _ := by simp

/-- The literal pair-source discrepancy equals its multiplicity-weighted
natural product discrepancy, before any absolute value. -/
theorem distribution_eq_productWeight (S : Finset (ℕ × ℕ)) (W : (ℕ × ℕ) → ℝ)
    (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError S product W N Q rho =
      ∑ q ∈ Q, rho q * finitePrimitiveDiscrepancy (productImage S) (productWeight S W) N q := by
  have hAP (q : ℕ) : finiteCongruenceMass (productImage S) (productWeight S W) N q =
      p5z_labelledCongruenceMass S product W N q := by
    simpa only [finiteCongruenceMass,Finset.sum_filter,p5z_labelledCongruenceMass,
      mul_ite,mul_one,mul_zero] using
      productWeight_sum S W (fun m => if Nat.ModEq q m N then 1 else 0)
  have hcop (q : ℕ) : finiteCoprimeMass (productImage S) (productWeight S W) q =
      p5z_labelledCoprimeMass S product W q := by
    simpa only [finiteCoprimeMass,Finset.sum_filter,p5z_labelledCoprimeMass,
      mul_ite,mul_one,mul_zero] using
      productWeight_sum S W (fun m => if Nat.Coprime m q then 1 else 0)
  simp only [finitePrimitiveDiscrepancy,hAP,hcop,p5z_labelledDistributionError]

private theorem discrepancy_half (S : Finset ℕ) (W : ℕ → ℝ) (N q : ℕ) :
    finitePrimitiveDiscrepancy S (fun m => W m / 2) N q =
      finitePrimitiveDiscrepancy S W N q / 2 := by
  simp only [finitePrimitiveDiscrepancy,finiteCongruenceMass,finiteCoprimeMass,Finset.sum_div]
  ring

/-- Twice the generic scalar endpoint bound, proved from actual prime
product fibers rather than a supplied multiplicity or final PP estimate. -/
theorem abs_pair_distribution_endpoint_le (S : Finset (ℕ × ℕ)) (W : (ℕ × ℕ) → ℝ)
    (N D : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hprime : ∀ t ∈ S, Nat.Prime t.1 ∧ Nat.Prime t.2)
    (hendpoint : ∀ t ∈ S, product t ≠ N ∧ distance N (product t) ≤ D)
    (hW : ∀ t ∈ S, |W t| ≤ 1) (hrho : ∀ q ∈ Q, |rho q| ≤ 1) :
    |p5z_labelledDistributionError S product W N Q rho| ≤
      4 * ∑ n ∈ Finset.Icc 1 D, (n.divisors.card : ℝ) +
        4 * (D : ℝ) * ∑ q ∈ Q, |rho q| / (Nat.totient q : ℝ) := by
  have hI : ∀ m ∈ productImage S, m ≠ N ∧ distance N m ≤ D := by
    intro m hm
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hm
    exact hendpoint t ht
  have hhalf : ∀ m ∈ productImage S, |productWeight S W m / 2| ≤ 1 := by
    intro m hm
    have hh := (abs_productWeight_le_fiber_card S W hW m).trans (product_fiber_card_le_two S hprime m)
    rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hbase := abs_signed_primitive_endpoint_le (productImage S) Q rho
    (fun m => productWeight S W m / 2) N D hI hrho hhalf
  have hcard := endpoint_card_le (productImage S) N D hI
  have hsum0 : 0 ≤ ∑ q ∈ Q, |rho q| / (Nat.totient q : ℝ) :=
    Finset.sum_nonneg (fun _ _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  have hmean := mul_le_mul_of_nonneg_right hcard hsum0
  have heq : (∑ q ∈ Q, rho q * finitePrimitiveDiscrepancy (productImage S)
      (fun m => productWeight S W m / 2) N q) =
      p5z_labelledDistributionError S product W N Q rho / 2 := by
    simp_rw [discrepancy_half,mul_div_assoc]
    rw [← Finset.sum_div,← distribution_eq_productWeight]
  rw [heq,abs_div] at hbase
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hbase
  nlinarith

/-- For sorted pairs (including squares), the exact scalar endpoint
constant suffices. No triangular or rectangular source-shape premise. -/
theorem abs_sorted_pair_distribution_endpoint_le (S : Finset (ℕ × ℕ)) (W : (ℕ × ℕ) → ℝ)
    (N D : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hprime : ∀ t ∈ S, Nat.Prime t.1 ∧ Nat.Prime t.2)
    (hsorted : ∀ t ∈ S, t.1 ≤ t.2)
    (hendpoint : ∀ t ∈ S, product t ≠ N ∧ distance N (product t) ≤ D)
    (hW : ∀ t ∈ S, |W t| ≤ 1) (hrho : ∀ q ∈ Q, |rho q| ≤ 1) :
    |p5z_labelledDistributionError S product W N Q rho| ≤
      2 * ∑ n ∈ Finset.Icc 1 D, (n.divisors.card : ℝ) +
        2 * (D : ℝ) * ∑ q ∈ Q, |rho q| / (Nat.totient q : ℝ) := by
  have hI : ∀ m ∈ productImage S, m ≠ N ∧ distance N m ≤ D := by
    intro m hm
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hm
    exact hendpoint t ht
  have hweight : ∀ m ∈ productImage S, |productWeight S W m| ≤ 1 := by
    intro m hm
    exact (abs_productWeight_le_fiber_card S W hW m).trans
      (product_fiber_card_le_one_of_sorted S hprime hsorted m)
  rw [distribution_eq_productWeight]
  refine (abs_signed_primitive_endpoint_le (productImage S) Q rho _ N D hI hrho hweight).trans ?_
  apply add_le_add_left
  exact mul_le_mul_of_nonneg_right (endpoint_card_le (productImage S) N D hI)
    (Finset.sum_nonneg (fun _ _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)))

/-- The even-centre zero product difference really is absent for two odd
primes. The assumption p,q>2 is essential and is never inferred from
primality alone. -/
theorem product_ne_even_of_two_lt {N : ℕ} (hEven : Even N) {t : ℕ × ℕ}
    (hp : Nat.Prime t.1 ∧ Nat.Prime t.2) (hgt : 2 < t.1 ∧ 2 < t.2) :
    product t ≠ N := by
  have ho : Odd (product t) := (hp.1.odd_of_ne_two (by omega)).mul
    (hp.2.odd_of_ne_two (by omega))
  intro heq
  apply (Nat.not_even_iff_odd.mpr ho)
  rw [heq]
  exact hEven

def kernel (N q m : ℕ) : ℝ :=
  (if Nat.ModEq q m N then 1 else 0) -
    (if Nat.Coprime m q then 1 else 0) / (Nat.totient q : ℝ)

theorem distribution_eq_source_sum (S : Finset (ℕ × ℕ)) (W : (ℕ × ℕ) → ℝ)
    (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError S product W N Q rho =
      ∑ q ∈ Q, rho q * ∑ t ∈ S, W t * kernel N q (product t) := by
  unfold p5z_labelledDistributionError p5z_labelledCongruenceMass p5z_labelledCoprimeMass kernel
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  simp_rw [mul_sub,← mul_div_assoc,mul_ite,mul_one,mul_zero,
    Finset.sum_sub_distrib,Finset.sum_div]

/-- Exact sharp-minus-smooth identity with the original source and its
arbitrary stepped domain and keep mask unchanged. Only their difference
is restricted to the literal endpoint subcarrier E. -/
theorem distribution_test_difference_eq_endpoint
    (S E : Finset (ℕ × ℕ)) (sharp smooth : (ℕ × ℕ) → ℝ)
    (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) (hES : E ⊆ S)
    (hagree : ∀ t ∈ S, t ∉ E → sharp t = smooth t) :
    p5z_labelledDistributionError S product sharp N Q rho -
      p5z_labelledDistributionError S product smooth N Q rho =
        p5z_labelledDistributionError E product (fun t => sharp t-smooth t) N Q rho := by
  rw [distribution_eq_source_sum,distribution_eq_source_sum,distribution_eq_source_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← mul_sub]
  apply congrArg (fun x : ℝ => rho q*x)
  calc
    _ = ∑ t ∈ S, (sharp t-smooth t)*kernel N q (product t) := by
      simp only [sub_mul,Finset.sum_sub_distrib]
    _ = _ := by
      symm
      apply Finset.sum_subset hES
      intro t ht hn
      rw [hagree t ht hn,sub_self,zero_mul]

/-- Full finite logarithmic payment for the actual pair-source error.
The constant twenty is exactly twice the scalar constant ten. -/
theorem abs_pair_distribution_endpoint_logN_le
    (S : Finset (ℕ × ℕ)) (W : (ℕ × ℕ) → ℝ) (N D M : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (hN : 1 ≤ N)
    (hQ : Q ⊆ Finset.Icc 1 M) (hMN : M ≤ N) (hDN : D ≤ N)
    (hprime : ∀ t ∈ S, Nat.Prime t.1 ∧ Nat.Prime t.2)
    (hendpoint : ∀ t ∈ S, product t ≠ N ∧ distance N (product t) ≤ D)
    (hW : ∀ t ∈ S, |W t| ≤ 1) (hrho : ∀ q ∈ Q, |rho q| ≤ 1) :
    |p5z_labelledDistributionError S product W N Q rho| ≤
      20 * (D : ℝ) * (1 + Real.log (N : ℝ)) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogD : Real.log (D : ℝ) ≤ Real.log (N : ℝ) := by
    by_cases hD : D = 0
    · simpa only [hD,Nat.cast_zero,Real.log_zero] using Real.log_nonneg hNr
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hD)
        (by exact_mod_cast hDN)
  have hlogM : Real.log (max 1 (M : ℝ)) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (max_le hNr (by exact_mod_cast hMN))
  have ht : (∑ n ∈ Finset.Icc 1 D, (n.divisors.card : ℝ)) ≤
      (D : ℝ)*(1+Real.log (N : ℝ)) :=
    (sum_divisors_card_le_log D).trans
      (mul_le_mul_of_nonneg_left (add_le_add_left hlogD 1) (Nat.cast_nonneg _))
  have hm : (∑ q ∈ Q, |rho q| / (Nat.totient q : ℝ)) ≤
      4 * (1 + Real.log (N : ℝ)) := by
    refine le_trans ?_ ((sum_reciprocal_totient_subset_le_log Q M hQ).trans ?_)
    · apply Finset.sum_le_sum
      intro q hq
      exact div_le_div_of_nonneg_right (hrho q hq) (Nat.cast_nonneg _)
    · exact mul_le_mul_of_nonneg_left (add_le_add_left hlogM 1) (by norm_num)
  refine (abs_pair_distribution_endpoint_le S W N D Q rho hprime hendpoint hW hrho).trans ?_
  have ht4 := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 4)
  have hm4 := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 4*(D : ℝ))
  calc
    _ ≤ 4 * ((D : ℝ)*(1+Real.log (N : ℝ))) +
        (4*(D : ℝ))*(4*(1+Real.log (N : ℝ))) := add_le_add ht4 hm4
    _ = _ := by ring

/-- One threshold precedes every finite stepped source and keep mask.
The actual positive lower exponent makes both primes odd, which excludes
product=N at an even centre. No sharp distribution conclusion is assumed. -/
theorem eventually_actual_causal_pair_endpoint_log_saving (a : ℝ) (ha : 0 < a) (A : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (retainEven : List ℕ → Bool) (cap D M : ℕ)
      (w z L : ℝ) (S E : Finset (ℕ × ℕ)) (Q : Finset ℕ)
      (sharp smooth : (ℕ × ℕ) → ℝ),
      Even N → E ⊆ S → Q ⊆ Finset.Icc 1 M → M ≤ N →
      D ≤ Nat.ceil ((N : ℝ) / Real.log (N : ℝ) ^ (A + 3)) →
      (∀ t ∈ E, Nat.Prime t.1 ∧ Nat.Prime t.2) →
      (∀ t ∈ E, (N : ℝ)^a ≤ (t.1 : ℝ) ∧ (N : ℝ)^a ≤ (t.2 : ℝ)) →
      (∀ t ∈ E, distance N (product t) ≤ D) →
      (∀ t ∈ S, t ∉ E → sharp t = smooth t) →
      (∀ t ∈ E, |sharp t-smooth t| ≤ 1) →
      |p5z_labelledDistributionError S product sharp N Q
          (actualLowerSmallRoughRho retainEven N cap w z L) -
        p5z_labelledDistributionError S product smooth N Q
          (actualLowerSmallRoughRho retainEven N cap w z L)| ≤
        80 * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  have hpow : ∀ᶠ N : ℕ in atTop, (2 : ℝ) < (N : ℝ)^a :=
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (2 : ℝ))
  filter_upwards [hpow,eventually_log_window_cost_le A,eventually_ge_atTop (1 : ℕ)]
    with N hpowN hcost hN
  intro retainEven cap D M w z L S E Q sharp smooth hEven hES hQ hMN hD hprime hrough
    hwindow hagree hdelta
  have hendpoint : ∀ t ∈ E, product t ≠ N ∧ distance N (product t) ≤ D := by
    intro t ht
    have hgt : 2 < t.1 ∧ 2 < t.2 := by
      constructor
      · exact_mod_cast hpowN.trans_le (hrough t ht).1
      · exact_mod_cast hpowN.trans_le (hrough t ht).2
    exact ⟨product_ne_even_of_two_lt hEven (hprime t ht) hgt,hwindow t ht⟩
  rw [distribution_test_difference_eq_endpoint S E sharp smooth N Q _ hES hagree]
  have hfinite := abs_pair_distribution_endpoint_logN_le E (fun t => sharp t-smooth t)
    N D M Q (actualLowerSmallRoughRho retainEven N cap w z L) hN hQ hMN
    (hcost D hD).1 hprime hendpoint hdelta
    (fun q _ => actualLowerSmallRoughRho_abs_le_one retainEven N cap w z L q)
  have hpaid := mul_le_mul_of_nonneg_left (hcost D hD).2 (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ 20*(D : ℝ)*(1+Real.log (N : ℝ)) := hfinite
    _ = 2*(10*(D : ℝ)*(1+Real.log (N : ℝ))) := by ring
    _ ≤ 2*(40*(N : ℝ)/Real.log (N : ℝ)^A) := hpaid
    _ = _ := by ring

/-- Concrete original pair lower exponent, with the entire endpoint
payment absorbed in the unchanged eleven-term normalization. -/
theorem eventually_original_pair_endpoint_normalized (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ (retainEven : List ℕ → Bool) (cap D M : ℕ)
      (w z L : ℝ) (S E : Finset (ℕ × ℕ)) (Q : Finset ℕ)
      (sharp smooth : (ℕ × ℕ) → ℝ),
      Even N → E ⊆ S → Q ⊆ Finset.Icc 1 M → M ≤ N →
      D ≤ Nat.ceil ((N : ℝ) / Real.log (N : ℝ) ^ 6) →
      (∀ t ∈ E, Nat.Prime t.1 ∧ Nat.Prime t.2) →
      (∀ t ∈ E, (N : ℝ)^(417/5000 : ℝ) ≤ (t.1 : ℝ) ∧
        (N : ℝ)^(417/5000 : ℝ) ≤ (t.2 : ℝ)) →
      (∀ t ∈ E, distance N (product t) ≤ D) →
      (∀ t ∈ S, t ∉ E → sharp t = smooth t) →
      (∀ t ∈ E, |sharp t-smooth t| ≤ 1) →
      |p5z_labelledDistributionError S product sharp N Q
          (actualLowerSmallRoughRho retainEven N cap w z L) -
        p5z_labelledDistributionError S product smooth N Q
          (actualLowerSmallRoughRho retainEven N cap w z L)| ≤
        epsilon * singularNormalization N := by
  filter_upwards [eventually_actual_causal_pair_endpoint_log_saving (417/5000)
    (by norm_num) 3,p5z_eventually_logCube_le_singularNormalization 80 epsilon hepsilon]
    with N hendpoint hpaid
  intro retainEven cap D M w z L S E Q sharp smooth hEven hES hQ hMN hD hprime hrough
    hwindow hagree hdelta
  exact (hendpoint retainEven cap D M w z L S E Q sharp smooth hEven hES hQ hMN hD
    hprime hrough hwindow hagree hdelta).trans hpaid

/-- Natural pair read from a native rank-two Part3 physical label. -/
def physicalPair {P : ℕ} (u : Fin 2 → Fin (P+1)) : ℕ × ℕ := ((u 0).val,(u 1).val)

def physicalWeight {P : ℕ} (S : Finset (ℕ × ℕ)) (W : (ℕ × ℕ) → ℝ)
    (u : Fin 2 → Fin (P+1)) : ℝ := if physicalPair u ∈ S then W (physicalPair u) else 0

theorem physicalPair_product {P : ℕ} (u : Fin 2 → Fin (P+1)) :
    product (physicalPair u) = Part3.labelledProduct u := by
  simp [product,physicalPair,Part3.labelledProduct,Fin.prod_univ_two]

/-- Exact finite rank-two dictionary. The original stepped and keep-mask
source is the physical coefficient, independent of every future modulus. -/
theorem physicalWeight_sum (S : Finset (ℕ × ℕ)) (W : (ℕ × ℕ) → ℝ) (P : ℕ)
    (hprime : ∀ t ∈ S, Nat.Prime t.1 ∧ Nat.Prime t.2)
    (hcap : ∀ t ∈ S, t.1 ≤ P ∧ t.2 ≤ P) (F : ℕ → ℝ) :
    (∑ t ∈ S, W t * F (product t)) =
      ∑ u ∈ Part3.labelledPrimeTuples 2 P, physicalWeight S W u * F (Part3.labelledProduct u) := by
  let encode : (t : ℕ × ℕ) → t ∈ S → (Fin 2 → Fin (P+1)) := fun t ht =>
    ![⟨t.1,Nat.lt_succ_of_le (hcap t ht).1⟩,⟨t.2,Nat.lt_succ_of_le (hcap t ht).2⟩]
  have hinverse (t : ℕ × ℕ) (ht : t ∈ S) : physicalPair (encode t ht) = t := by
    simp [physicalPair,encode]
  let T := (Part3.labelledPrimeTuples 2 P).filter (fun u => physicalPair u ∈ S)
  have hbij : (∑ t ∈ S, W t * F (product t)) =
      ∑ u ∈ T, W (physicalPair u) * F (Part3.labelledProduct u) := by
    refine Finset.sum_bij encode ?_ ?_ ?_ ?_
    · intro t ht
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        intro i
        fin_cases i
        · simpa [encode] using (hprime t ht).1
        · simpa [encode] using (hprime t ht).2
      · rw [hinverse t ht]
        exact ht
    · intro t ht s hs heq
      have h := congrArg physicalPair heq
      simpa only [hinverse] using h
    · intro u hu
      have hi := (Finset.mem_filter.mp hu).2
      refine ⟨physicalPair u,hi,?_⟩
      funext i
      fin_cases i <;> apply Fin.ext <;> rfl
    · intro t ht
      rw [← physicalPair_product,hinverse t ht]
  calc
    _ = ∑ u ∈ T, W (physicalPair u)*F (Part3.labelledProduct u) := hbij
    _ = _ := by
      dsimp only [T]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u hu
      by_cases h : physicalPair u ∈ S <;>
        simp only [physicalWeight,h,if_true,if_false,zero_mul]

/-- Exact Part3 PP error at the same rho, including all source labels,
square pairs and the exact primitive-coprime mean. No analytic licence. -/
theorem distribution_eq_physicalPP (S : Finset (ℕ × ℕ)) (W : (ℕ × ℕ) → ℝ)
    (P N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hprime : ∀ t ∈ S, Nat.Prime t.1 ∧ Nat.Prime t.2)
    (hcap : ∀ t ∈ S, t.1 ≤ P ∧ t.2 ≤ P) :
    p5z_labelledDistributionError S product W N Q rho =
      Part3.primeProductSignedError 2 P N Q rho (physicalWeight S W) := by
  rw [distribution_eq_source_sum]
  unfold Part3.primeProductSignedError
  apply Finset.sum_congr rfl
  intro q hq
  apply congrArg (fun x : ℝ => rho q*x)
  simpa only [kernel] using physicalWeight_sum S W P hprime hcap (kernel N q)

end
end ImbalancedChen.P5PrimePairEndpoint
