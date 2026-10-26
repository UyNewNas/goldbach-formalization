import ImbalancedChen.CurrentChenP5U9OrderedBranches
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
# The original ninth labels regrouped into a semiprime and a switched prime

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The existing full-product pushforward does not supply this regrouping:
the switched prime is the ORIGINAL second prime p₂, and its complementary
semiprime is p₁*q. Both ordered original factor labels remain in the fibre
cardinality. In particular no squarefreeness or injectivity of (p₁,q) ↦ p₁*q
is asserted. The source is exactly the existing original switched labels,
with their half-open bands, product-dependent square-root cutoff, strict
product endpoint, and centre-coprimality.

The arbitrary real lower product parameter X can be (1-κ)*N, for every
κ and every N, with precisely the original strict endpoint; there is no
change of the near-cap quantifier order. The AP
conversion works for every positive modulus coprime to N, including prime
powers, and retains the full totient of that modulus. No analytical AP
estimate, final lower bound, or sharp currentK density is assumed or proved.
-/

namespace ImbalancedChen.U9SemiprimeSwitch

noncomputable section

open scoped BigOperators
open Classical

/-- An arbitrary lower product cut on the unchanged original labels. -/
def labels (N : ℕ) (X : ℝ) : Finset P5zU9Triple :=
  (p5z_u9_switchedLabels N).filter fun t => X < (p5z_u9_product t : ℝ)

/-- The original first and terminal slots form the semiprime; the original
second slot is the switched prime. This is not a sorted-factor quotient. -/
def key (t : P5zU9Triple) : ℕ × ℕ := (t.1.1 * t.2, t.1.2)

theorem key_product (t : P5zU9Triple) :
    (key t).1 * (key t).2 = p5z_u9_product t := by
  simp only [key, p5z_u9_product]
  ring

/-- Every original factorisation label is counted, even for repeated
primes or several original factorizations with the same semiprime. -/
def weight (N : ℕ) (X : ℝ) (m r : ℕ) : ℝ :=
  (((labels N X).filter fun t => key t = (m, r)).card : ℝ)

theorem weight_nonneg (N : ℕ) (X : ℝ) (m r : ℕ) :
    0 ≤ weight N X m r := Nat.cast_nonneg _

theorem labels_zero (N : ℕ) : labels N 0 = p5z_u9_switchedLabels N := by
  ext t
  simp only [labels, Finset.mem_filter]
  constructor
  · exact And.left
  · intro ht
    have hd := p5z_u9_order_source_data ht
    obtain ⟨hp₁, hp₂, _⟩ := chenY9PrimeSelector_ordered_prime_data hd.1
    refine ⟨ht, ?_⟩
    have hpos : 0 < p5z_u9_product t :=
      mul_pos (mul_pos hp₁.pos hp₂.pos) hd.2.2.1.pos
    exact_mod_cast hpos

/-- This concrete fibre description preserves the original ordered pair,
moving cutoff, strict upper product endpoint, and all equality owners. -/
theorem mem_weight_fibre_iff {N m r : ℕ} {X : ℝ} {t : P5zU9Triple} :
    t ∈ (labels N X).filter (fun t => key t = (m, r)) ↔
      t.1 ∈ chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
        ((N : ℝ) ^ (59 / 250 : ℝ)) ∧
      t.2 < N + 1 ∧ Nat.Prime t.2 ∧ p5z_u9_product t < N ∧
      Real.sqrt ((N : ℝ) / ((t.1.1 : ℝ) * (t.1.2 : ℝ))) ≤ (t.2 : ℝ) ∧
      Nat.Coprime (N - p5z_u9_product t) N ∧
      X < (p5z_u9_product t : ℝ) ∧ t.1.1 * t.2 = m ∧ t.1.2 = r := by
  rcases t with ⟨⟨p₁, p₂⟩, q⟩
  simp only [labels, Finset.mem_filter, key, Prod.mk.injEq]
  rw [mem_p5z_u9_switchedLabels_iff]
  simp only [p5z_u9_product]
  tauto

private theorem key_mem_carrier {N : ℕ} {X : ℝ} {t : P5zU9Triple}
    (ht : t ∈ labels N X) :
    key t ∈ Finset.range N ×ˢ chenAdditivePrimeCarrier N := by
  have hs := (Finset.mem_filter.mp ht).1
  have hd := p5z_u9_order_source_data hs
  obtain ⟨_, hr⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hd.1).1
  have hrpos := (mem_chenAdditivePrimeCarrier.mp hr).2.1.pos
  have hmle : (key t).1 ≤ (key t).1 * (key t).2 :=
    Nat.le_mul_of_pos_right _ hrpos
  have hprod := p5z_u9_switchedLabels_product_lt hs
  rw [← key_product t] at hprod
  exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (hmle.trans_lt hprod), hr⟩

/-- A genuine two-coordinate pushforward, for every real test function.
The fibre weight is not replaced by the cardinality of a product image. -/
theorem pushforward (N : ℕ) (X : ℝ) (G : ℕ → ℕ → ℝ) :
    (∑ m ∈ Finset.range N, ∑ r ∈ chenAdditivePrimeCarrier N,
      weight N X m r * G m r) =
      ∑ t ∈ labels N X, G (t.1.1 * t.2) t.1.2 := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := labels N X) (t := Finset.range N ×ˢ chenAdditivePrimeCarrier N)
    (g := key) (fun t ht => key_mem_carrier ht)
    (fun t => G (key t).1 (key t).2)
  rw [← hf]
  rw [← Finset.sum_product]
  apply Finset.sum_congr rfl
  rintro ⟨m, r⟩ _
  change (((labels N X).filter (fun t => key t = (m, r))).card : ℝ) * G m r = _
  calc
    _ = ∑ _t ∈ (labels N X).filter (fun t => key t = (m, r)), G m r := by simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [(Finset.mem_filter.mp ht).2]

/-- The original ninth count itself, with no source thinning, is the
semiprime/switched-prime receiver count plus every original unit fibre.
The strict product endpoint stays inside the same prime test. -/
theorem originalCount_eq_semiprimePrimeReceiver (N : ℕ) :
    currentChenUpsilon9 N =
      (∑ m ∈ Finset.range N, ∑ r ∈ chenAdditivePrimeCarrier N,
        weight N 0 m r *
          (if m * r < N ∧ Nat.Prime (N - m * r) then 1 else 0)) +
        ((currentChenUpsilon9UnitFibres N).card : ℝ) := by
  have hf := pushforward N 0
    (fun m r => if m * r < N ∧ Nat.Prime (N - m * r) then 1 else 0)
  have hcount : (∑ t ∈ labels N 0,
      if p5z_u9_product t < N ∧ Nat.Prime (N - p5z_u9_product t)
        then (1 : ℝ) else 0) =
      ((currentChenUpsilon9PrimeTriples N).card : ℝ) := by
    rw [labels_zero, ← Finset.sum_filter,
      p5z_u9_switchedLabels_filter_eq_primeTriples]
    simp
  have hprod (t : P5zU9Triple) : t.1.1 * t.2 * t.1.2 = p5z_u9_product t :=
    key_product t
  simp_rw [hprod] at hf
  rw [hcount] at hf
  rw [currentChenUpsilon9_eq_primeTriples_add_unitFibres, hf]

/-- A constructed canonical residue; Bezout's coefficient is attached to
the complete semiprime m and the complete modulus d. -/
def residue (N m d : ℕ) : ℕ :=
  (((N : ℤ) * Nat.gcdA m d) % (d : ℤ)).toNat

theorem residue_lt (N m : ℕ) {d : ℕ} (hd : 0 < d) : residue N m d < d := by
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  have hnonneg := Int.emod_nonneg ((N : ℤ) * Nat.gcdA m d) hdZ.ne'
  have hlt := Int.emod_lt_of_pos ((N : ℤ) * Nat.gcdA m d) hdZ
  have hcast : (residue N m d : ℤ) = ((N : ℤ) * Nat.gcdA m d) % (d : ℤ) :=
    Int.toNat_of_nonneg hnonneg
  exact_mod_cast (show (residue N m d : ℤ) < d by rw [hcast]; exact hlt)

theorem residue_spec (N : ℕ) {m d : ℕ} (hd : 0 < d) (hm : Nat.Coprime m d) :
    Nat.ModEq d (m * residue N m d) N := by
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  have hcast : (residue N m d : ℤ) = ((N : ℤ) * Nat.gcdA m d) % (d : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hdZ.ne')
  have hinv : Int.ModEq d ((m : ℤ) * Nat.gcdA m d) 1 := by
    calc
      (m : ℤ) * Nat.gcdA m d ≡
          (m : ℤ) * Nat.gcdA m d + (d : ℤ) * Nat.gcdB m d [ZMOD (d : ℤ)] := by simp
      _ ≡ 1 [ZMOD (d : ℤ)] := by rw [← Nat.gcd_eq_gcd_ab, hm.gcd_eq_one]; rfl
  have hred : Int.ModEq d (residue N m d : ℤ) ((N : ℤ) * Nat.gcdA m d) := by
    rw [hcast]
    simp only [Int.ModEq, Int.emod_emod]
  apply Int.natCast_modEq_iff.mp
  have h := (hred.mul_left (m : ℤ)).trans
    (by simpa only [mul_assoc, mul_comm, mul_left_comm, mul_one] using hinv.mul_left (N : ℤ))
  simpa only [Nat.cast_mul] using h

/-- The constructed AP residue is primitive whenever the actual target N
is primitive. This does not require d or the semiprime to be squarefree. -/
theorem residue_coprime (N : ℕ) {m d : ℕ} (hd : 0 < d)
    (hm : Nat.Coprime m d) (hN : Nat.Coprime N d) :
    Nat.Coprime (residue N m d) d := by
  have hprod : Nat.Coprime (m * residue N m d) d := by
    change Nat.gcd (m * residue N m d) d = 1
    rw [(residue_spec N hd hm).gcd_eq, hN.gcd_eq_one]
  exact (Nat.coprime_mul_iff_left.mp hprod).2

/-- Exact AP switching at every positive modulus, including prime powers.
The nonprimitive semiprime rows vanish arithmetically. -/
theorem product_AP_iff {N m r d : ℕ} (hd : 0 < d) (hN : Nat.Coprime N d) :
    Nat.ModEq d (m * r) N ↔
      Nat.Coprime m d ∧ Nat.ModEq d r (residue N m d) := by
  constructor
  · intro h
    have hprod : Nat.Coprime (m * r) d := by
      change Nat.gcd (m * r) d = 1
      rw [h.gcd_eq, hN.gcd_eq_one]
    have hm := (Nat.coprime_mul_iff_left.mp hprod).1
    exact ⟨hm, Nat.ModEq.cancel_left_of_coprime hm.symm.gcd_eq_one
      (h.trans (residue_spec N hd hm).symm)⟩
  · rintro ⟨hm, hr⟩
    exact (hr.mul_left m).trans (residue_spec N hd hm)

/-- The switched prime AP sum still uses the literal original prime
carrier; the weight retains the other two original factor labels. -/
def APCount (N : ℕ) (X : ℝ) (d : ℕ) : ℝ :=
  ∑ m ∈ Finset.range N, if Nat.Coprime m d then
    ∑ r ∈ (chenAdditivePrimeCarrier N).filter
      (fun r => Nat.ModEq d r (residue N m d)), weight N X m r
    else 0

theorem congruenceMass_eq_APCount (N : ℕ) (X : ℝ) {d : ℕ}
    (hd : 0 < d) (hN : Nat.Coprime N d) :
    p5z_labelledCongruenceMass (labels N X) p5z_u9_product (fun _ => 1) N d =
      APCount N X d := by
  have hf := pushforward N X
    (fun m r => if Nat.ModEq d (m * r) N then 1 else 0)
  have hleft :
      (∑ m ∈ Finset.range N, ∑ r ∈ chenAdditivePrimeCarrier N,
        weight N X m r * (if Nat.ModEq d (m * r) N then 1 else 0)) =
      APCount N X d := by
    unfold APCount
    apply Finset.sum_congr rfl
    intro m _
    by_cases hm : Nat.Coprime m d
    · simp only [hm, if_true, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r _
      rw [product_AP_iff hd hN]
      simp only [hm, true_and, mul_ite, mul_one, mul_zero]
    · simp only [hm, if_false]
      apply Finset.sum_eq_zero
      intro r _
      rw [product_AP_iff hd hN]
      simp only [hm, false_and, if_false, mul_zero]
  rw [hleft] at hf
  rw [hf]
  unfold p5z_labelledCongruenceMass
  apply Finset.sum_congr rfl
  intro t _
  have hp := key_product t
  change t.1.1 * t.2 * t.1.2 = p5z_u9_product t at hp
  rw [hp]
  simp only [one_mul]

/-- Exact primitive mean with the full totient of d. The denominator is
never replaced by a radical or by a product of distinct prime factors. -/
def coprimeMass (N : ℕ) (X : ℝ) (d : ℕ) : ℝ :=
  ∑ m ∈ Finset.range N, ∑ r ∈ chenAdditivePrimeCarrier N,
    weight N X m r * (if Nat.Coprime (m * r) d then 1 else 0)

theorem coprimeMass_eq_labels (N : ℕ) (X : ℝ) (d : ℕ) :
    coprimeMass N X d =
      p5z_labelledCoprimeMass (labels N X) p5z_u9_product (fun _ => 1) d := by
  have hf := pushforward N X
    (fun m r => if Nat.Coprime (m * r) d then 1 else 0)
  rw [coprimeMass, hf]
  unfold p5z_labelledCoprimeMass
  apply Finset.sum_congr rfl
  intro t _
  have hp := key_product t
  change t.1.1 * t.2 * t.1.2 = p5z_u9_product t at hp
  rw [hp]
  simp only [one_mul]

/-- One original signed modulus sum, before absolute values. Every
near-cap precision X and the same rho occur on both sides. -/
theorem signedError_eq_switchedPrimeAP (N : ℕ) (X : ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hQ : ∀ d ∈ Q, 0 < d ∧ Nat.Coprime N d) :
    p5z_labelledDistributionError (labels N X) p5z_u9_product
        (fun _ => 1) N Q rho =
      ∑ d ∈ Q, rho d *
        (APCount N X d - coprimeMass N X d / (Nat.totient d : ℝ)) := by
  unfold p5z_labelledDistributionError
  apply Finset.sum_congr rfl
  intro d hd
  rw [congruenceMass_eq_APCount N X (hQ d hd).1 (hQ d hd).2,
    ← coprimeMass_eq_labels]

end

end ImbalancedChen.U9SemiprimeSwitch
