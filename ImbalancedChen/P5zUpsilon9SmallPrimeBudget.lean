import ImbalancedChen.P5zUpsilon9SwitchedMultiplicity
import ImbalancedChen.PowerErrorBudget

/-!
# Actual ninth multiplicity and small-prime receiver payment

SOURCE ONLY / UNCOMPILED. A product represented by three primes has at
most THREE distinct prime values. Its ordered pair label determines q.
Consequently the literal fibre weight is at most 9, without assuming that
all m are rough, squarefree, or even represented. Repeated q=p1 or q=p2
is retained. Products 0 and 1 are explicitly excluded by the proved lower
bound 8 on every represented product.
-/

namespace ImbalancedChen

noncomputable section

open Filter
open scoped BigOperators
open Classical

theorem p5z_u9_switchedLabels_prime_data {N : ℕ} {t : P5zU9Triple}
    (ht : t ∈ p5z_u9_switchedLabels N) :
    Nat.Prime t.1.1 ∧ Nat.Prime t.1.2 ∧ Nat.Prime t.2 ∧ t.1.1 < t.1.2 := by
  obtain ⟨hp, hq⟩ := Finset.mem_sigma.mp ht
  obtain ⟨h₁, h₂, horder⟩ := chenY9PrimeSelector_ordered_prime_data hp
  exact ⟨h₁, h₂, (Finset.mem_filter.mp hq).2.1, horder⟩

theorem p5z_u9_switchedLabels_product_ge_eight {N : ℕ} {t : P5zU9Triple}
    (ht : t ∈ p5z_u9_switchedLabels N) : 8 ≤ p5z_u9_product t := by
  obtain ⟨h₁, h₂, hq, _⟩ := p5z_u9_switchedLabels_prime_data ht
  have hpair : 4 ≤ t.1.1 * t.1.2 := Nat.mul_le_mul h₁.two_le h₂.two_le
  exact Nat.mul_le_mul hpair hq.two_le

/-- Includes the formerly delicate m=0 and m=1 cases, without a nonzero
premise on arbitrary test products. -/
theorem p5z_u9_switchedWeight_eq_zero_of_lt_eight (N m : ℕ) (hm : m < 8) :
    p5z_u9_switchedWeight N m = 0 := by
  have hempty : (p5z_u9_switchedLabels N).filter
      (fun t => p5z_u9_product t = m) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨htS, htm⟩ := Finset.mem_filter.mp ht
    have hmin := p5z_u9_switchedLabels_product_ge_eight htS
    omega
  simp only [p5z_u9_switchedWeight, hempty, Finset.card_empty, Nat.cast_zero]

private theorem p5z_prime_mem_three_of_dvd {p a b c : ℕ}
    (hp : Nat.Prime p) (ha : Nat.Prime a) (hb : Nat.Prime b) (hc : Nat.Prime c)
    (hd : p ∣ a * b * c) : p ∈ ({a, b, c} : Finset ℕ) := by
  rcases hp.dvd_mul.mp hd with hab | hpc
  · rcases hp.dvd_mul.mp hab with hpa | hpb
    · have heq := (Nat.prime_dvd_prime_iff_eq hp ha).mp hpa
      simp [heq]
    · have heq := (Nat.prime_dvd_prime_iff_eq hp hb).mp hpb
      simp [heq]
  · have heq := (Nat.prime_dvd_prime_iff_eq hp hc).mp hpc
    simp [heq]

/-- Every literal product fibre has at most nine labels. A witness gives
at most three possible prime values for each of the first two slots, and
the quotient is uniquely determined by their positive product. -/
theorem p5z_u9_switched_fibre_card_le_nine (N m : ℕ) :
    ((p5z_u9_switchedLabels N).filter (fun t => p5z_u9_product t = m)).card ≤ 9 := by
  let F := (p5z_u9_switchedLabels N).filter (fun t => p5z_u9_product t = m)
  change F.card ≤ 9
  by_cases hF : F = ∅
  · simpa only [hF, Finset.card_empty] using (Nat.zero_le 9)
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hF
  obtain ⟨huS, hum⟩ := Finset.mem_filter.mp hu
  obtain ⟨hu₁, hu₂, huq, _⟩ := p5z_u9_switchedLabels_prime_data huS
  let T : Finset ℕ := {u.1.1, u.1.2, u.2}
  have hT : T.card ≤ 3 := Finset.card_le_three
  have hcard : F.card ≤ (T ×ˢ T).card := by
    apply Finset.card_le_card_of_injOn (fun t : P5zU9Triple => t.1)
    · intro t ht
      obtain ⟨htS, htm⟩ := Finset.mem_filter.mp ht
      obtain ⟨ht₁, ht₂, htq, _⟩ := p5z_u9_switchedLabels_prime_data htS
      have hprod : p5z_u9_product t = p5z_u9_product u := htm.trans hum.symm
      apply Finset.mem_product.mpr
      constructor
      · apply p5z_prime_mem_three_of_dvd ht₁ hu₁ hu₂ huq
        change t.1.1 ∣ p5z_u9_product u
        rw [← hprod]
        exact (dvd_mul_right t.1.1 t.1.2).trans
          (dvd_mul_right (t.1.1 * t.1.2) t.2)
      · apply p5z_prime_mem_three_of_dvd ht₂ hu₁ hu₂ huq
        change t.1.2 ∣ p5z_u9_product u
        rw [← hprod]
        exact (dvd_mul_left t.1.2 t.1.1).trans
          (dvd_mul_right (t.1.1 * t.1.2) t.2)
    · intro t ht v hv hpair
      rcases t with ⟨p, q⟩
      rcases v with ⟨r, s⟩
      change p = r at hpair
      subst r
      obtain ⟨htS, htm⟩ := Finset.mem_filter.mp ht
      obtain ⟨hvS, hvm⟩ := Finset.mem_filter.mp hv
      obtain ⟨hp₁, hp₂, _, _⟩ := p5z_u9_switchedLabels_prime_data htS
      have hb : 0 < p.1 * p.2 := mul_pos hp₁.pos hp₂.pos
      have hmul : p.1 * p.2 * q = p.1 * p.2 * s := htm.trans hvm.symm
      have hqs := Nat.eq_of_mul_eq_mul_left hb hmul
      subst s
      rfl
  change F.card ≤ 9
  calc
    F.card ≤ (T ×ˢ T).card := hcard
    _ = T.card * T.card := Finset.card_product _ _
    _ ≤ 3 * 3 := Nat.mul_le_mul hT hT
    _ = 9 := by norm_num

theorem p5z_u9_switchedWeight_le_nine (N m : ℕ) : p5z_u9_switchedWeight N m ≤ 9 := by
  change ((((p5z_u9_switchedLabels N).filter (fun t => p5z_u9_product t = m)).card : ℝ) ≤ 9)
  exact_mod_cast p5z_u9_switched_fibre_card_le_nine N m

/-- The receiver map m -> N-m is injective below N. The literal prime
and centre-coprime gates are retained in the counted family; the upper
bound is nine times the number of possible small receiver integers. -/
theorem p5z_u9_smallPrimeMass_le_nine_mul_cutoff (N z : ℕ) :
    p5z_labelledSmallPrimeMass (Finset.range N) id (p5z_u9_switchedWeight N) N z ≤
      9 * (z : ℝ) := by
  let F := (Finset.range N).filter
    (fun m => m < N ∧ Nat.Prime (N - m) ∧ N - m < z)
  have hcard : F.card ≤ z := by
    calc
      F.card ≤ (Finset.range z).card := by
        apply Finset.card_le_card_of_injOn (fun m : ℕ => N - m)
        · intro m hm
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hm).2.2.2
        · intro m hm r hr heq
          have hmN := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
          have hrN := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
          omega
      _ = z := Finset.card_range z
  have hcardR : (F.card : ℝ) ≤ (z : ℝ) := by exact_mod_cast hcard
  change (∑ m ∈ Finset.range N,
    if m < N ∧ Nat.Prime (N - m) ∧ N - m < z then p5z_u9_switchedWeight N m else 0) ≤ _
  rw [← Finset.sum_filter]
  change (∑ m ∈ F, p5z_u9_switchedWeight N m) ≤ _
  calc
    _ ≤ ∑ _m ∈ F, (9 : ℝ) := Finset.sum_le_sum (fun m _ => p5z_u9_switchedWeight_le_nine N m)
    _ = (F.card : ℝ) * 9 := by simp
    _ ≤ (z : ℝ) * 9 := mul_le_mul_of_nonneg_right hcardR (by norm_num)
    _ = 9 * (z : ℝ) := by ring

/-- Any fixed sublinear-power cutoff pays the actual weighted small-prime
loss. Only a cutoff-size bound is supplied, not a smallPrimeMass bound. -/
theorem p5z_eventually_u9_smallPrimeMass_le_of_sublinear_cutoff
    (z : ℕ → ℕ) (theta : ℝ) (htheta : theta < 1)
    (hcap : ∀ᶠ N : ℕ in atTop, (z N : ℝ) ≤ (N : ℝ) ^ theta)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      p5z_labelledSmallPrimeMass (Finset.range N) id (p5z_u9_switchedWeight N) N (z N) ≤
        eta * singularNormalization N := by
  filter_upwards [hcap,
    eventually_powerLog_le_singularNormalization 9 theta 0 htheta eta heta]
    with N hcapN hpowerN
  calc
    _ ≤ 9 * (z N : ℝ) := p5z_u9_smallPrimeMass_le_nine_mul_cutoff N (z N)
    _ ≤ 9 * (N : ℝ) ^ theta := mul_le_mul_of_nonneg_left hcapN (by norm_num)
    _ ≤ eta * singularNormalization N := by simpa only [pow_zero, mul_one] using hpowerN

/-- The usual NATURAL CEILING of a real-power cap is paid too, with its
rounding loss retained by the already proved ceiling budget. -/
theorem p5z_eventually_u9_smallPrimeMass_le_ceil_rpow
    (theta : ℝ) (htheta : theta < 1) (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      p5z_labelledSmallPrimeMass (Finset.range N) id (p5z_u9_switchedWeight N) N
        (Nat.ceil ((N : ℝ) ^ theta)) ≤ eta * singularNormalization N := by
  have hpaid := eventually_ceil_powerLog_le_singularNormalization
    1 theta 0 (by norm_num) htheta (eta / 9) (by linarith only [heta])
  filter_upwards [hpaid] with N hN
  have hsmall := p5z_u9_smallPrimeMass_le_nine_mul_cutoff N (Nat.ceil ((N : ℝ) ^ theta))
  simp only [one_mul, pow_zero, mul_one] at hN
  nlinarith only [hsmall, hN]

/-- The exact labelled-source small-prime supplier required by the
same-rho eventual U* specialization is now derived from a GEOMETRIC
cutoff bound. No smallPrimeMass estimate is assumed. The local licence
and delta are identical to the downstream PP/density instance. -/
theorem p5z_u9_labelledSmallPrime_supplier_of_cutoff_bound
    (z : ℝ → ℕ → ℕ) (Licensed : ℝ → ℕ → Prop)
    (theta : ℝ) (htheta : theta < 1)
    (hcap : ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Licensed delta N → (z delta N : ℝ) ≤ (N : ℝ) ^ theta) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      Even N → Licensed delta N →
        p5z_labelledSmallPrimeMass (p5z_u9_switchedLabels N) p5z_u9_product
          (fun _ => 1) N (z delta N) ≤ delta * singularNormalization N := by
  intro delta hdelta
  filter_upwards [hcap delta hdelta,
    eventually_powerLog_le_singularNormalization 9 theta 0 htheta delta hdelta]
    with N hcapN hpowerN
  intro hEven hL
  rw [← p5z_u9_switched_smallPrimeMass_eq_labels]
  calc
    _ ≤ 9 * (z delta N : ℝ) := p5z_u9_smallPrimeMass_le_nine_mul_cutoff N (z delta N)
    _ ≤ 9 * (N : ℝ) ^ theta :=
      mul_le_mul_of_nonneg_left (hcapN hEven hL) (by norm_num)
    _ ≤ delta * singularNormalization N := by simpa only [pow_zero, mul_one] using hpowerN
end

end ImbalancedChen

