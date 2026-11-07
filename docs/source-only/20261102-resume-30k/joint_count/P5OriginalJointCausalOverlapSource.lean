import ImbalancedChen.CurrentChenUpsilon1011JointOverlapFiniteMean
import ImbalancedChen.CurrentChenPairRosser
import ImbalancedChen.RealPhysicalUpperWeightBridge
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original joint source is sifted at its second smallest prime. Its
first prime overlaps the four-prime multiplier. This file attaches the
actual sign-sensitive odd-first-exit small/rough rho, including BOTH small
Rosser signs, to that literal quotient source and computes its true mean.
No ordinary Rosser initialization is substituted for this causal rho.

The policy is fixed before the quotient receiver is tested. The theorem
is uniform in that policy; selecting the complete manuscript history and
proving its enhanced density/licences remain separate obligations.
-/

namespace ImbalancedChen.P5OriginalJointCausalOverlapSource

noncomputable section
open Classical
open scoped BigOperators
open P5U10OriginalMean P5U1011JointOverlap

abbrev Policy := List ℕ → Bool

def causalSupport (R : Policy) (N : ℕ) (t : Label) (w : ℝ) : Finset ℕ :=
  actualSmallRoughModuli R N t.1.2 w (t.1.2 : ℝ)

def causalRho (R : Policy) (N : ℕ) (t : Label) (w L : ℝ) : ℕ → ℝ :=
  actualSmallRoughRho R N t.1.2 w (t.1.2 : ℝ) L

def rawDensity (R : Policy) (N : ℕ) (t : Label) (w L : ℝ) : ℝ :=
  physicalDensitySum (causalSupport R N t w) (causalRho R N t w L)

def fullDensity (R : Policy) (N : ℕ) (t : Label) (w L : ℝ) : ℝ :=
  ∑ d ∈ causalSupport R N t w,
    causalRho R N t w L d / (Nat.totient (multiplier t * d) : ℝ)

def effectiveDensity (R : Policy) (N : ℕ) (t : Label) (w L : ℝ) : ℝ :=
  ∑ e ∈ (residualProduct N t).divisors,
    (causalRho R N t w L e + causalRho R N t w L (t.1.1 * e) / (t.1.1 : ℝ)) /
      (Nat.totient e : ℝ)

/-- Signed mass of the branch which really repeats p1 in b*d. -/
def overlapCorrection (R : Policy) (N : ℕ) (t : Label) (w L : ℝ) : ℝ :=
  ∑ e ∈ (residualProduct N t).divisors,
    causalRho R N t w L (t.1.1 * e) / (Nat.totient (t.1.1 * e) : ℝ)

theorem causalRho_zero_off_support (R : Policy) (N : ℕ) (t : Label)
    (w L : ℝ) {d : ℕ} (hd : d ∉ causalSupport R N t w) :
    causalRho R N t w L d = 0 :=
  smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hd

theorem causalSupport_subset_divisors (R : Policy) (N : ℕ) (t : Label)
    (w : ℝ) (hw : w ≤ (t.1.2 : ℝ)) :
    causalSupport R N t w ⊆ (sieveProduct N t.1.2).divisors := by
  intro d hd
  apply Nat.mem_divisors.mpr
  refine ⟨?_, (sieveProduct_squarefree N t.1.2).ne_zero⟩
  simpa only [Nat.ceil_natCast] using
    actualSmallRoughModuli_dvd_sieveProduct_ceil R N t.1.2 w (t.1.2 : ℝ) hw hd

/-- Zero extension is an exact signed identity; no discarded absolute mass. -/
theorem causal_sum_eq_divisors (R : Policy) (N : ℕ) (t : Label)
    (w L : ℝ) (hw : w ≤ (t.1.2 : ℝ)) (F : ℕ → ℝ) :
    (∑ d ∈ causalSupport R N t w, causalRho R N t w L d * F d) =
      ∑ d ∈ (sieveProduct N t.1.2).divisors, causalRho R N t w L d * F d := by
  apply Finset.sum_subset (causalSupport_subset_divisors R N t w hw)
  intro d _ hd
  rw [causalRho_zero_off_support R N t w L hd, zero_mul]

/-- The actual upper causal tree majorizes the literal quotient indicator.
The quotient remains coprime to N; no coprimality of b with the p2 sieve
is asserted or needed. Quotient one and repeated residual factors remain. -/
theorem quotient_pointwise_majorant (R : Policy) (N : ℕ) (t : Label)
    (w L : ℝ) (hL : 1 < L) (hwL : w ≤ L) (hw : w ≤ (t.1.2 : ℝ))
    {q : ℕ} (hq : q ∈ chenQuotientPrimeSource N (multiplier t)) :
    (if ChenPrimeRough (t.1.2 : ℝ) q then (1 : ℝ) else 0) ≤
      physicalDivisorSum (causalSupport R N t w) (causalRho R N t w L) q := by
  have h := actualSmallRoughRho_sieveProduct_majorant R N t.1.2
    w (t.1.2 : ℝ) L hL hwL hw le_rfl q
  have hr := chenPrimeRough_iff_coprime_sieveProduct (t.1.2 : ℝ)
    (chenQuotientPrimeSource_data hq).2.2
  simpa only [← hr] using h

theorem row_count_upper (R : Policy) (N : ℕ) (t : Label)
    (w L : ℝ) (hL : 1 < L) (hwL : w ≤ L) (hw : w ≤ (t.1.2 : ℝ)) :
    ((chenSiftedQuotientPrimeSource N (multiplier t) (t.1.2 : ℝ)).card : ℝ) ≤
      ∑ d ∈ causalSupport R N t w, causalRho R N t w L d *
        (chenPrimeAPCount N N (multiplier t * d) -
          chenCentrePrimeAPCount N N (multiplier t * d)) := by
  have hsum := currentChen_quotient_sum_supportedDivisorSum N (multiplier t)
    (causalSupport R N t w) (causalRho R N t w L)
  have hid : (∑ q ∈ chenQuotientPrimeSource N (multiplier t),
      physicalDivisorSum (causalSupport R N t w) (causalRho R N t w L) q) =
      ∑ d ∈ causalSupport R N t w, causalRho R N t w L d *
        (chenPrimeAPCount N N (multiplier t * d) -
          chenCentrePrimeAPCount N N (multiplier t * d)) := by
    simpa only [physicalDivisorSum, supportedDivisorSum, Finset.sum_filter] using hsum
  rw [← hid]
  calc
    _ = ∑ q ∈ chenQuotientPrimeSource N (multiplier t),
        if ChenPrimeRough (t.1.2 : ℝ) q then (1 : ℝ) else 0 := by
      rw [← Finset.sum_filter]
      simp only [chenSiftedQuotientPrimeSource, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ _ := Finset.sum_le_sum (fun q hq =>
      quotient_pointwise_majorant R N t w L hL hwL hw hq)

theorem fullDensity_eq_effective {N : ℕ} {E : ℕ × ℕ → Prop} {t : Label}
    (ht : t ∈ jointSelector N E) (R : Policy) (w L : ℝ) (hw : w ≤ (t.1.2 : ℝ)) :
    fullDensity R N t w L = effectiveDensity R N t w L / (Nat.totient (multiplier t) : ℝ) := by
  have hext := causal_sum_eq_divisors R N t w L hw
    (fun d => 1 / (Nat.totient (multiplier t * d) : ℝ))
  simp only [mul_one_div] at hext
  rw [fullDensity, hext]
  have h := joint_signed_overlap_divisor_sum ht (causalRho R N t w L)
  simpa only [effectiveDensity, one_div_mul_eq_div] using h

/-- Exact comparison with the density of the SAME physical causal rho.
The correction is signed and the p1 branch is not deleted. -/
theorem effectiveDensity_eq_raw_sub_overlap {N : ℕ} {E : ℕ × ℕ → Prop} {t : Label}
    (ht : t ∈ jointSelector N E) (R : Policy) (w L : ℝ) (hw : w ≤ (t.1.2 : ℝ)) :
    effectiveDensity R N t w L =
      rawDensity R N t w L - overlapCorrection R N t w L / (t.1.1 : ℝ) := by
  have hp := (mem_sievePrimes.mp (joint_first_mem_sievePrimes ht)).2.1
  have hpb : t.1.1 ∣ multiplier t :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  have hcop := (joint_multiplier_coprime_residualProduct ht).of_dvd_left hpb
  have hext := causal_sum_eq_divisors R N t w L hw (fun d => 1 / (Nat.totient d : ℝ))
  simp only [mul_one_div] at hext
  have hraw : rawDensity R N t w L =
      (∑ e ∈ (residualProduct N t).divisors,
        causalRho R N t w L e / (Nat.totient e : ℝ)) + overlapCorrection R N t w L := by
    rw [rawDensity, physicalDensitySum, hext, ← joint_first_mul_residualProduct ht]
    exact sum_divisors_prime_mul_split hp (joint_residualProduct_ne_zero ht) hcop
      (fun d => causalRho R N t w L d / (Nat.totient d : ℝ))
  simp only [hraw, effectiveDensity, overlapCorrection]
  rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have hpe := hcop.of_dvd_right (Nat.mem_divisors.mp he).1
  have hpR : (0 : ℝ) < t.1.1 := Nat.cast_pos.mpr hp.pos
  have hp1 : (0 : ℝ) < (t.1.1 : ℝ) - 1 := by
    have hp2 : (2 : ℝ) ≤ t.1.1 := by exact_mod_cast hp.two_le
    linarith
  simp only [Nat.totient_mul hpe, Nat.totient_prime hp, Nat.cast_mul,
    Nat.cast_sub hp.one_le, Nat.cast_one]
  have hcoeff : causalRho R N t w L (t.1.1 * e) / (t.1.1 : ℝ) =
      causalRho R N t w L (t.1.1 * e) / ((t.1.1 : ℝ) - 1) -
        (causalRho R N t w L (t.1.1 * e) / ((t.1.1 : ℝ) - 1)) / (t.1.1 : ℝ) := by
    field_simp [hpR.ne', hp1.ne']
    <;> ring
  calc
    _ = causalRho R N t w L e / (Nat.totient e : ℝ) +
        (causalRho R N t w L (t.1.1 * e) / (t.1.1 : ℝ)) / (Nat.totient e : ℝ) := by ring
    _ = causalRho R N t w L e / (Nat.totient e : ℝ) +
        (causalRho R N t w L (t.1.1 * e) / ((t.1.1 : ℝ) - 1) -
          (causalRho R N t w L (t.1.1 * e) / ((t.1.1 : ℝ) - 1)) / (t.1.1 : ℝ)) /
            (Nat.totient e : ℝ) := by rw [hcoeff]
    _ = _ := by ring

def jointRawDensity (N : ℕ) (E : ℕ × ℕ → Prop)
    (R : Label → Policy) (w L : Label → ℝ) : ℝ :=
  ∑ t ∈ jointSelector N E, rawDensity (R t) N t (w t) (L t) /
    (Nat.totient (multiplier t) : ℝ)

def jointEffectiveDensity (N : ℕ) (E : ℕ × ℕ → Prop)
    (R : Label → Policy) (w L : Label → ℝ) : ℝ :=
  ∑ t ∈ jointSelector N E, effectiveDensity (R t) N t (w t) (L t) /
    (Nat.totient (multiplier t) : ℝ)

def jointAP (N : ℕ) (E : ℕ × ℕ → Prop)
    (R : Label → Policy) (w L : Label → ℝ) (M : ℝ) : ℝ :=
  ∑ t ∈ jointSelector N E, ∑ d ∈ causalSupport (R t) N t (w t),
    causalRho (R t) N t (w t) (L t) d * chenQuotientPrimeAPError N M (multiplier t * d)

def jointCentre (N : ℕ) (E : ℕ × ℕ → Prop)
    (R : Label → Policy) (w L : Label → ℝ) : ℝ :=
  ∑ t ∈ jointSelector N E, ∑ d ∈ causalSupport (R t) N t (w t),
    causalRho (R t) N t (w t) (L t) d * chenCentrePrimeAPCount N N (multiplier t * d)

abbrev Mark := Σ _ : Label, ℕ

def marks (N : ℕ) (E : ℕ × ℕ → Prop) (R : Label → Policy) (w : Label → ℝ) : Finset Mark :=
  (jointSelector N E).sigma (fun t => causalSupport (R t) N t (w t))

def modulus (m : Mark) : ℕ := multiplier m.1 * m.2

def modulusSupport (N : ℕ) (E : ℕ × ℕ → Prop) (R : Label → Policy) (w : Label → ℝ) : Finset ℕ :=
  (marks N E R w).image modulus

/-- The aggregate signed physical coefficient retains every original
mark. No injectivity, squarefree-q restriction or aggregate unit bound. -/
def fibreRho (N : ℕ) (E : ℕ × ℕ → Prop) (R : Label → Policy) (w L : Label → ℝ) (q : ℕ) : ℝ :=
  ∑ m ∈ (marks N E R w).filter (fun m => modulus m = q),
    causalRho (R m.1) N m.1 (w m.1) (L m.1) m.2

theorem exact_signed_pushforward (N : ℕ) (E : ℕ × ℕ → Prop)
    (R : Label → Policy) (w L : Label → ℝ) (F : ℕ → ℝ) :
    (∑ t ∈ jointSelector N E, ∑ d ∈ causalSupport (R t) N t (w t),
      causalRho (R t) N t (w t) (L t) d * F (multiplier t * d)) =
      ∑ q ∈ modulusSupport N E R w, fibreRho N E R w L q * F q := by
  have hm : (∑ t ∈ jointSelector N E, ∑ d ∈ causalSupport (R t) N t (w t),
      causalRho (R t) N t (w t) (L t) d * F (multiplier t * d)) =
      ∑ m ∈ marks N E R w, causalRho (R m.1) N m.1 (w m.1) (L m.1) m.2 * F (modulus m) := by
    simp only [marks, Finset.sum_sigma, modulus]
  rw [hm]
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := marks N E R w) (t := modulusSupport N E R w) (g := modulus)
    (fun m hm => Finset.mem_image_of_mem modulus hm)
    (fun m => causalRho (R m.1) N m.1 (w m.1) (L m.1) m.2 * F (modulus m))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro q hq
  rw [fibreRho, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [(Finset.mem_filter.mp hm).2]

theorem jointAP_eq_modulus_fibre (N : ℕ) (E : ℕ × ℕ → Prop)
    (R : Label → Policy) (w L : Label → ℝ) (M : ℝ) :
    jointAP N E R w L M = ∑ q ∈ modulusSupport N E R w,
      fibreRho N E R w L q * chenQuotientPrimeAPError N M q :=
  exact_signed_pushforward N E R w L _

theorem jointCentre_eq_modulus_fibre (N : ℕ) (E : ℕ × ℕ → Prop)
    (R : Label → Policy) (w L : Label → ℝ) :
    jointCentre N E R w L = ∑ q ∈ modulusSupport N E R w,
      fibreRho N E R w L q * chenCentrePrimeAPCount N N q :=
  exact_signed_pushforward N E R w L _

/-- Exactly the SAME fibre coefficient as the AP and centre terms. The
overlapping p1 branch retains its full denominator phi(b*p1*e). -/
theorem jointEffectiveDensity_eq_physical_fibre (N : ℕ) (E : ℕ × ℕ → Prop)
    (R : Label → Policy) (w L : Label → ℝ)
    (hw : ∀ t ∈ jointSelector N E, w t ≤ (t.1.2 : ℝ)) :
    jointEffectiveDensity N E R w L =
      physicalDensitySum (modulusSupport N E R w) (fibreRho N E R w L) := by
  have h := exact_signed_pushforward N E R w L (fun q => 1 / (Nat.totient q : ℝ))
  simp only [mul_one_div] at h
  have hrows : (∑ t ∈ jointSelector N E, ∑ d ∈ causalSupport (R t) N t (w t),
      causalRho (R t) N t (w t) (L t) d / (Nat.totient (multiplier t * d) : ℝ)) =
      jointEffectiveDensity N E R w L := by
    apply Finset.sum_congr rfl
    intro t ht
    exact fullDensity_eq_effective ht (R t) (w t) (L t) (hw t ht)
  rw [hrows] at h
  exact h

/-- Changing the reference prime mass keeps its full signed correction.
In particular the later N/log(N) normalization does not identify that mass
with li(N), pi(N), or the primitive prime mass. -/
theorem jointAP_change_center (N : ℕ) (E : ℕ × ℕ → Prop)
    (R : Label → Policy) (w L : Label → ℝ) (M M' : ℝ)
    (hw : ∀ t ∈ jointSelector N E, w t ≤ (t.1.2 : ℝ)) :
    jointAP N E R w L M = jointAP N E R w L M' +
      (M' - M) * jointEffectiveDensity N E R w L := by
  simp only [jointAP_eq_modulus_fibre]
  rw [jointEffectiveDensity_eq_physical_fibre N E R w L hw,
    physicalDensitySum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  unfold chenQuotientPrimeAPError
  ring

/-- Genuine causal count-to-density entrance for the COMPLETE joint
source. Low-band U10 is unmasked; high-band U11 keeps the original E
complement. Main, AP and centre all use the same causal function rho. -/
theorem joint_count_upper_actual_causal {N : ℕ} (hN : 1 ≤ (N : ℝ))
    (E : ℕ × ℕ → Prop) (R : Label → Policy) (w L : Label → ℝ) (M : ℝ)
    (hgates : ∀ t ∈ jointSelector N E, 1 < L t ∧ w t ≤ L t ∧ w t ≤ (t.1.2 : ℝ)) :
    currentChenUpsilon10 N + currentChenUpsilon11 N E ≤
      M * jointEffectiveDensity N E R w L + jointAP N E R w L M - jointCentre N E R w L := by
  rw [currentChenUpsilon10_add_11_eq_joint_source N E hN]
  change (∑ t ∈ jointSelector N E,
    ((chenSiftedQuotientPrimeSource N (multiplier t) (t.1.2 : ℝ)).card : ℝ)) ≤ _
  unfold jointEffectiveDensity jointAP jointCentre
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro t ht
  have hg := hgates t ht
  have hu := row_count_upper (R t) N t (w t) (L t) hg.1 hg.2.1 hg.2.2
  rw [← fullDensity_eq_effective ht (R t) (w t) (L t) hg.2.2, fullDensity,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  convert hu using 1
  apply Finset.sum_congr rfl
  intro d hd
  unfold chenQuotientPrimeAPError
  ring

end
end ImbalancedChen.P5OriginalJointCausalOverlapSource
