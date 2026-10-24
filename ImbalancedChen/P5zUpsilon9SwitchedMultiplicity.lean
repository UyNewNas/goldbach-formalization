import ImbalancedChen.CurrentChenUpsilon9ProductCoefficient
import ImbalancedChen.P5zPositiveFamilyBudget

/-!
# Actual U9 triple-multiplicity switched family

SOURCE ONLY / UNCOMPILED. The intended preceding candidate is
P5zPositiveFamilyBudget.lean.txt, staged as ImbalancedChen.P5zPositiveFamilyBudget.

The source below has no primality condition on N-product. The original
pair ranges, moving square-root cutoff and centre-coprimality are retained.
The fibre cardinal weight records EVERY original triple label. No ordinary
factor-eight density is relabelled as a currentK density estimate.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Classical

abbrev P5zU9Triple := Σ _ : ℕ × ℕ, ℕ

def p5z_u9_product (t : P5zU9Triple) : ℕ := t.1.1 * t.1.2 * t.2

/-- Literal ninth source before the additive-prime filter. The modulus
q of any future PP sum is not an argument of this finite source. -/
def p5z_u9_switchedLabels (N : ℕ) : Finset P5zU9Triple :=
  (chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
    ((N : ℝ) ^ (59 / 250 : ℝ))).sigma fun p =>
      (Finset.range (N + 1)).filter fun q => Nat.Prime q ∧
        p.1 * p.2 * q < N ∧
        Real.sqrt ((N : ℝ) / ((p.1 : ℝ) * (p.2 : ℝ))) ≤ (q : ℝ) ∧
        Nat.Coprime (N - p.1 * p.2 * q) N

/-- Membership exposes every original band, cutoff and arithmetic gate. -/
theorem mem_p5z_u9_switchedLabels_iff {N p₁ p₂ q : ℕ} :
    (⟨(p₁, p₂), q⟩ : P5zU9Triple) ∈ p5z_u9_switchedLabels N ↔
      (p₁, p₂) ∈ chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
        ((N : ℝ) ^ (59 / 250 : ℝ)) ∧
      q < N + 1 ∧ Nat.Prime q ∧ p₁ * p₂ * q < N ∧
      Real.sqrt ((N : ℝ) / ((p₁ : ℝ) * (p₂ : ℝ))) ≤ (q : ℝ) ∧
      Nat.Coprime (N - p₁ * p₂ * q) N := by
  simp only [p5z_u9_switchedLabels, Finset.mem_sigma, Finset.mem_filter, Finset.mem_range]
/-- Triple multiplicity at the PRODUCT. This is a fibre cardinal, not an
unweighted product image, even if several labels share that product. -/
def p5z_u9_switchedWeight (N m : ℕ) : ℝ :=
  (((p5z_u9_switchedLabels N).filter (fun t => p5z_u9_product t = m)).card : ℝ)

theorem p5z_u9_switchedWeight_nonneg (N m : ℕ) :
    0 ≤ p5z_u9_switchedWeight N m := Nat.cast_nonneg _

theorem p5z_u9_switchedLabels_product_lt {N : ℕ} {t : P5zU9Triple}
    (ht : t ∈ p5z_u9_switchedLabels N) : p5z_u9_product t < N := by
  obtain ⟨_, hq⟩ := Finset.mem_sigma.mp ht
  exact (Finset.mem_filter.mp hq).2.2.1

private theorem p5z_u9_pair_product_pos {N : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
      ((N : ℝ) ^ (59 / 250 : ℝ))) : 0 < p.1 * p.2 := by
  obtain ⟨h₁, h₂, _⟩ := chenY9PrimeSelector_ordered_prime_data hp
  exact mul_pos h₁.pos h₂.pos

/-- A source prime filter restores exactly the actual prime triples. -/
theorem p5z_u9_switchedLabels_filter_eq_primeTriples (N : ℕ) :
    (p5z_u9_switchedLabels N).filter
        (fun t => p5z_u9_product t < N ∧ Nat.Prime (N - p5z_u9_product t)) =
      currentChenUpsilon9PrimeTriples N := by
  ext t
  rcases t with ⟨⟨p₁, p₂⟩, q⟩
  simp only [Finset.mem_filter, p5z_u9_switchedLabels, Finset.mem_sigma,
    Finset.mem_filter, Finset.mem_range, p5z_u9_product,
    currentChenUpsilon9PrimeTriples, Finset.mem_sigma, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hp, hqN, hq, hlt, hcut, hcop⟩, _, hprime⟩
    have hP : N - p₁ * p₂ * q ∈ chenAdditivePrimeCarrier N := by
      apply mem_chenAdditivePrimeCarrier.mpr
      refine ⟨?_, hprime, hcop⟩
      have hb := p5z_u9_pair_product_pos hp
      have hqpos := hq.pos
      have hmpos : 0 < p₁ * p₂ * q := mul_pos hb hqpos
      omega
    exact ⟨hp,
      (currentChenUpsilon9_prime_mem_iff (p5z_u9_pair_product_pos hp) hq _).mpr
        ⟨hlt, hP, hcut⟩, hq⟩
  · rintro ⟨hp, hqsource, hq⟩
    obtain ⟨hlt, hP, hcut⟩ :=
      (currentChenUpsilon9_prime_mem_iff (p5z_u9_pair_product_pos hp) hq _).mp hqsource
    obtain ⟨hPN, hprime, hcop⟩ := mem_chenAdditivePrimeCarrier.mp hP
    have hqle : q ≤ p₁ * p₂ * q :=
      Nat.le_mul_of_pos_left q (p5z_u9_pair_product_pos hp)
    exact ⟨⟨hp, by omega, hq, hlt, hcut, hcop⟩, hlt, hprime⟩

/-- Exact finite pushforward with multiplicity. It works for an arbitrary
real-valued test function, so applies before any signed PP norm. -/
theorem p5z_u9_switchedWeight_sum (N : ℕ) (G : ℕ → ℝ) :
    (∑ m ∈ Finset.range N, p5z_u9_switchedWeight N m * G m) =
      ∑ t ∈ p5z_u9_switchedLabels N, G (p5z_u9_product t) := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := p5z_u9_switchedLabels N) (t := Finset.range N)
    (g := p5z_u9_product)
    (fun t ht => Finset.mem_range.mpr (p5z_u9_switchedLabels_product_lt ht))
    (fun t => G (p5z_u9_product t))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro m hm
  change (((p5z_u9_switchedLabels N).filter
    (fun t => p5z_u9_product t = m)).card : ℝ) * G m = _
  calc
    _ = ∑ _t ∈ (p5z_u9_switchedLabels N).filter
        (fun t => p5z_u9_product t = m), G m := by simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [(Finset.mem_filter.mp ht).2]

/-- The total source mass is the literal number of labels. -/
theorem p5z_u9_switchedMass_eq_card (N : ℕ) :
    p5z_labelledMass (Finset.range N) (p5z_u9_switchedWeight N) =
      ((p5z_u9_switchedLabels N).card : ℝ) := by
  simpa only [p5z_labelledMass, mul_one, Finset.sum_const, nsmul_eq_mul] using
    p5z_u9_switchedWeight_sum N (fun _ => 1)

/-- The original ninth count is exactly the positive switched weight
prime-receiver sum and its actual unit fibres, including all multiplicities. -/
theorem p5z_u9_eq_switchedWeight_primeMass_add_units (N : ℕ) :
    currentChenUpsilon9 N =
      p5z_labelledPrimeMass (Finset.range N) id (p5z_u9_switchedWeight N) N +
        ((currentChenUpsilon9UnitFibres N).card : ℝ) := by
  have hprime : p5z_labelledPrimeMass (Finset.range N) id
      (p5z_u9_switchedWeight N) N = ((currentChenUpsilon9PrimeTriples N).card : ℝ) := by
    have h := p5z_u9_switchedWeight_sum N
      (fun m => if m < N ∧ Nat.Prime (N - m) then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero] at h
    have hcount : (∑ t ∈ p5z_u9_switchedLabels N,
        if p5z_u9_product t < N ∧ Nat.Prime (N - p5z_u9_product t)
        then (1 : ℝ) else 0) = ((currentChenUpsilon9PrimeTriples N).card : ℝ) := by
      rw [← Finset.sum_filter, p5z_u9_switchedLabels_filter_eq_primeTriples]
      simp
    simpa only [p5z_labelledPrimeMass, id_eq] using h.trans hcount
  rw [currentChenUpsilon9_eq_primeTriples_add_unitFibres, hprime]

/-- The congruence source retains every product fibre before summing q. -/
theorem p5z_u9_switched_congruenceMass_eq_labels (N q : ℕ) :
    p5z_labelledCongruenceMass (Finset.range N) id
      (p5z_u9_switchedWeight N) N q =
    p5z_labelledCongruenceMass (p5z_u9_switchedLabels N) p5z_u9_product
      (fun _ => 1) N q := by
  simpa only [p5z_labelledCongruenceMass, id_eq, mul_ite, mul_one, mul_zero] using
    p5z_u9_switchedWeight_sum N (fun m => if Nat.ModEq q m N then 1 else 0)

theorem p5z_u9_switched_coprimeMass_eq_labels (N q : ℕ) :
    p5z_labelledCoprimeMass (Finset.range N) id (p5z_u9_switchedWeight N) q =
    p5z_labelledCoprimeMass (p5z_u9_switchedLabels N) p5z_u9_product
      (fun _ => 1) q := by
  simpa only [p5z_labelledCoprimeMass, id_eq, mul_ite, mul_one, mul_zero] using
    p5z_u9_switchedWeight_sum N (fun m => if Nat.Coprime m q then 1 else 0)

/-- Small prime receiver losses also preserve their original labels. -/
theorem p5z_u9_switched_smallPrimeMass_eq_labels (N z : ℕ) :
    p5z_labelledSmallPrimeMass (Finset.range N) id (p5z_u9_switchedWeight N) N z =
    p5z_labelledSmallPrimeMass (p5z_u9_switchedLabels N) p5z_u9_product
      (fun _ => 1) N z := by
  simpa only [p5z_labelledSmallPrimeMass, id_eq, mul_ite, mul_one, mul_zero] using
    p5z_u9_switchedWeight_sum N
      (fun m => if m < N ∧ Nat.Prime (N - m) ∧ N - m < z then 1 else 0)
/-- The complete signed distribution error equals the original labelled
triple expression, rather than an error for a deduplicated source. -/
theorem p5z_u9_switched_distribution_eq_labels (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (Finset.range N) id
      (p5z_u9_switchedWeight N) N Q rho =
    p5z_labelledDistributionError (p5z_u9_switchedLabels N) p5z_u9_product
      (fun _ => 1) N Q rho := by
  unfold p5z_labelledDistributionError
  simp_rw [p5z_u9_switched_congruenceMass_eq_labels,
    p5z_u9_switched_coprimeMass_eq_labels]

/-- Total product-weight mass and total original-label mass agree. -/
theorem p5z_u9_switched_mass_eq_labels (N : ℕ) :
    p5z_labelledMass (Finset.range N) (p5z_u9_switchedWeight N) =
      p5z_labelledMass (p5z_u9_switchedLabels N) (fun _ => 1) := by
  simpa only [p5z_labelledMass, mul_one] using
    p5z_u9_switchedWeight_sum N (fun _ => 1)

/-- Primitive recentering preserves the exact label multiplicity too. -/
theorem p5z_u9_switched_correction_eq_labels (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledCoprimeCorrection (Finset.range N) id
      (p5z_u9_switchedWeight N) Q rho =
    p5z_labelledCoprimeCorrection (p5z_u9_switchedLabels N) p5z_u9_product
      (fun _ => 1) Q rho := by
  unfold p5z_labelledCoprimeCorrection
  simp_rw [p5z_u9_switched_coprimeMass_eq_labels, p5z_u9_switched_mass_eq_labels]

/-- Exact finite physical Fubini at the actual switched multiplicity
weight, before any positivity estimate or absolute discrepancy bound. -/
theorem p5z_u9_same_rho_physical_sum_eq_main_errors (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ m ∈ Finset.range N, p5z_u9_switchedWeight N m *
        physicalDivisorSum Q rho (N - m)) =
      p5z_labelledMass (Finset.range N) (p5z_u9_switchedWeight N) * physicalDensitySum Q rho +
      p5z_labelledCoprimeCorrection (Finset.range N) id (p5z_u9_switchedWeight N) Q rho +
      p5z_labelledDistributionError (Finset.range N) id (p5z_u9_switchedWeight N) N Q rho := by
  exact p5z_labelled_physical_sum_eq_main_add_errors (Finset.range N) id
    (p5z_u9_switchedWeight N) N Q rho
    (fun m hm => (Finset.mem_range.mp hm).le)
/-- Actual U9 finite same-rho main and error bridge. The unit term is
retained exactly; no mean estimate at currentK is presumed. -/
theorem p5z_u9_le_same_rho_main_add_errors (N z : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    currentChenUpsilon9 N ≤
      p5z_labelledMass (Finset.range N) (p5z_u9_switchedWeight N) * physicalDensitySum Q rho +
      p5z_labelledCoprimeCorrection (Finset.range N) id (p5z_u9_switchedWeight N) Q rho +
      p5z_labelledDistributionError (Finset.range N) id (p5z_u9_switchedWeight N) N Q rho +
      p5z_labelledSmallPrimeMass (Finset.range N) id (p5z_u9_switchedWeight N) N z +
      ((currentChenUpsilon9UnitFibres N).card : ℝ) := by
  rw [p5z_u9_eq_switchedWeight_primeMass_add_units]
  exact add_le_add_right
    (p5z_labelledPrimeMass_le_main_add_errors (Finset.range N) id
      (p5z_u9_switchedWeight N) N z Q rho
      (fun m _ => p5z_u9_switchedWeight_nonneg N m)
      (fun m hm => (Finset.mem_range.mp hm).le) hmajor) _

/-- Instantiate the positive-family budget at the actual ninth switched
weight. The four explicit losses include the actual unit fibres. -/
theorem p5z_u9_currentK_upper_of_finite_inputs
    (N z : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) (J delta eta : ℝ)
    (hN : 2 ≤ N) (hJ : 0 ≤ J) (hdelta : 0 ≤ delta)
    (hbudget : (J + delta) * (currentK + delta) + 4 * delta ≤ currentK * J + eta)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤ physicalDivisorSum Q rho n)
    (hmass : p5z_labelledMass (Finset.range N) (p5z_u9_switchedWeight N) ≤
      (J + delta) * ((N : ℝ) / Real.log (N : ℝ)))
    (hdensity : physicalDensitySum Q rho ≤
      (currentK + delta) * (singularSeries N / Real.log (N : ℝ)))
    (hcop : |p5z_labelledCoprimeCorrection (Finset.range N) id
      (p5z_u9_switchedWeight N) Q rho| ≤ delta * singularNormalization N)
    (hPP : |p5z_labelledDistributionError (Finset.range N) id
      (p5z_u9_switchedWeight N) N Q rho| ≤ delta * singularNormalization N)
    (hsmall : p5z_labelledSmallPrimeMass (Finset.range N) id
      (p5z_u9_switchedWeight N) N z ≤ delta * singularNormalization N)
    (hunit : ((currentChenUpsilon9UnitFibres N).card : ℝ) ≤ delta * singularNormalization N) :
    currentChenUpsilon9 N ≤ (currentK * J + eta) * singularNormalization N := by
  have hprime := p5z_labelled_positive_family_currentK_upper
    (Finset.range N) id (p5z_u9_switchedWeight N) N z Q rho J delta (eta - delta)
    hN hJ hdelta (by linarith only [hbudget])
    (fun m _ => p5z_u9_switchedWeight_nonneg N m)
    (fun m hm => (Finset.mem_range.mp hm).le) hmajor hmass hdensity hcop hPP hsmall
  rw [p5z_u9_eq_switchedWeight_primeMass_add_units]
  nlinarith only [hprime, hunit]

end

end ImbalancedChen


