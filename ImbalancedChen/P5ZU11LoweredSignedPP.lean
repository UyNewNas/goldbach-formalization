import ImbalancedChen.P5ZU11SelectedOrdinaryCentrePaid
import ImbalancedChen.SingletonPrimeProductTransportP5
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
Signed physical-modulus pushforward for the ACTUAL lowered ordinary sieve.
The divisor carrier and every weight below use Z(t), never the original p2
cutoff. Fibre coefficients are signed sums, bounded by fibre cardinality;
no unit bound or squarefree-modulus claim is inferred.

The singleton PP weight is independent of the modulus. Its primitive mean
is converted to the actual li(N)-centred AP error with both exact remaining
normalization corrections. Centre payment uses the preceding original
selected-parent theorem. Remaining CP: the genuine averaged signed-PP
estimate, H248 averaged count semantics, and the endpoint limit.
Status: source_written / uncompiled; older source files unchanged.
-/

namespace ImbalancedChen.P5Z.U11LoweredSignedPP

open Filter Topology
open scoped BigOperators
open Classical
open U11Adaptive U11LoweredRosser U11SelectedCentre
open Part3 P5S1SingletonPP
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

noncomputable section

abbrev Mark := Σ _ : Four, ℕ

def active (N : ℕ) (Z R : Four → ℝ) (t : Four) : Finset ℕ :=
  (actualSmallRosserSupport N (Nat.ceil (Z t)) (Z t)).filter
    (fun d => actualSmallRosserPlus N (Nat.ceil (Z t)) (Z t) (R t) d ≠ 0)

def marks (N : ℕ) (T : Finset Four) (Z R : Four → ℝ) : Finset Mark := T.sigma (active N Z R)

def modulus (x : Mark) : ℕ := multiplier x.1 * x.2

def markWeight (N : ℕ) (Z R : Four → ℝ) (x : Mark) : ℝ :=
  actualSmallRosserPlus N (Nat.ceil (Z x.1)) (Z x.1) (R x.1) x.2

def moduli (N : ℕ) (T : Finset Four) (Z R : Four → ℝ) : Finset ℕ :=
  (marks N T Z R).image modulus

def fibre (N : ℕ) (T : Finset Four) (Z R : Four → ℝ) (q : ℕ) : Finset Mark :=
  (marks N T Z R).filter (fun x => modulus x = q)

def A (N : ℕ) (T : Finset Four) (Z R : Four → ℝ) (q : ℕ) : ℝ :=
  ∑ x ∈ fibre N T Z R q, markWeight N Z R x

theorem signedAP_eq_marks (N : ℕ) (T : Finset Four) (Z R : Four → ℝ) :
    (∑ t ∈ T, signedAP N t (Z t) (R t)) =
      ∑ x ∈ marks N T Z R, markWeight N Z R x *
        chenQuotientPrimeAPError N (trueLogarithmicIntegral N) (modulus x) := by
  rw [marks, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro t _
  unfold signedAP active
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : actualSmallRosserPlus N (Nat.ceil (Z t)) (Z t) (R t) d = 0 <;>
    simp [markWeight, modulus, hd]

/-- Exact signed Fubini against an arbitrary test, before any norm. -/
theorem signed_pushforward (N : ℕ) (T : Finset Four) (Z R : Four → ℝ) (F : ℕ → ℝ) :
    (∑ x ∈ marks N T Z R, markWeight N Z R x * F (modulus x)) =
      ∑ q ∈ moduli N T Z R, A N T Z R q * F q := by
  have hh := Finset.sum_fiberwise_of_maps_to
    (s := marks N T Z R) (t := moduli N T Z R) (g := modulus)
    (fun x hx => Finset.mem_image_of_mem modulus hx)
    (fun x => markWeight N Z R x * F (modulus x))
  rw [← hh]
  apply Finset.sum_congr rfl
  intro q _
  unfold A fibre
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [(Finset.mem_filter.mp hx).2]

theorem signedAP_eq_modulus_sum (N : ℕ) (T : Finset Four) (Z R : Four → ℝ) :
    (∑ t ∈ T, signedAP N t (Z t) (R t)) =
      ∑ q ∈ moduli N T Z R, A N T Z R q *
        chenQuotientPrimeAPError N (trueLogarithmicIntegral N) q := by
  rw [signedAP_eq_marks]
  exact signed_pushforward N T Z R _

theorem A_eq_zero_off_support {N q : ℕ} {T : Finset Four} {Z R : Four → ℝ}
    (hq : q ∉ moduli N T Z R) : A N T Z R q = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  obtain ⟨hxm, hxq⟩ := Finset.mem_filter.mp hx
  exact (hq (Finset.mem_image.mpr ⟨x, hxm, hxq⟩)).elim

theorem abs_A_le_fibre_card (N : ℕ) (T : Finset Four) (Z R : Four → ℝ) (q : ℕ) :
    |A N T Z R q| ≤ ((fibre N T Z R q).card : ℝ) := by
  unfold A
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ x ∈ fibre N T Z R q, |markWeight N Z R x|) ≤
        ∑ _x ∈ fibre N T Z R q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      exact actualSmallRosserPlus_abs_le_one N _ _ _ _
    _ = _ := by simp

theorem mark_physical_data {N : ℕ} {E : ℕ × ℕ → Prop} {T : Finset Four}
    {Z R : Four → ℝ} (hN : 1 ≤ (N : ℝ)) (hT : T ⊆ source N E)
    (hcap : ∀ t ∈ T, R t ≤ (N : ℝ) ^ (153 / 256 : ℝ) / (multiplier t : ℝ))
    {x : Mark} (hx : x ∈ marks N T Z R) :
    0 < modulus x ∧ Nat.Coprime N (modulus x) ∧ (modulus x : ℝ) < (N : ℝ) ^ (153 / 256 : ℝ) := by
  obtain ⟨ht, hd⟩ := Finset.mem_sigma.mp hx
  have hs := (Finset.mem_filter.mp hd).1
  have ha := actualSmallRosserPlus_active (Finset.mem_filter.mp hd).2
  obtain ⟨h1, h2, h3, h4, _⟩ := original_carrier_order hN (hT ht)
  have hbN : Nat.Coprime (multiplier x.1) N :=
    (((mem_chenAdditivePrimeCarrier.mp h1).2.2.mul_left
      (mem_chenAdditivePrimeCarrier.mp h2).2.2).mul_left
        (mem_chenAdditivePrimeCarrier.mp h3).2.2).mul_left
          (mem_chenAdditivePrimeCarrier.mp h4).2.2
  have hdN := actualSmallRosserSupport_coprime_target N (Nat.ceil (Z x.1)) (Z x.1) hs
  have hj := P5U1011JointOverlap.originalU11_mem_joint hN (hT ht)
  have hb := P5U1011JointOverlap.joint_multiplier_pos hj
  have hbr : (0 : ℝ) < (multiplier x.1 : ℝ) := Nat.cast_pos.mpr hb
  have hlt := (lt_div_iff₀ hbr).mp (ha.2.1.trans_le (hcap x.1 ht))
  refine ⟨mul_pos hb (Nat.pos_of_mem_divisors ha.1), (hbN.mul_left hdN).symm, ?_⟩
  simpa only [modulus, Nat.cast_mul, mul_comm] using hlt

theorem moduli_physical_data {N q : ℕ} {E : ℕ × ℕ → Prop} {T : Finset Four}
    {Z R : Four → ℝ} (hN : 1 ≤ (N : ℝ)) (hT : T ⊆ source N E)
    (hcap : ∀ t ∈ T, R t ≤ (N : ℝ) ^ (153 / 256 : ℝ) / (multiplier t : ℝ))
    (hq : q ∈ moduli N T Z R) :
    0 < q ∧ Nat.Coprime N q ∧ (q : ℝ) ≤ (N : ℝ) ^ (153 / 256 : ℝ) := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hp, hc, hb⟩ := mark_physical_data hN hT hcap hx
  exact ⟨hp, hc, hb.le⟩

theorem A_nonzero_physical_data {N q : ℕ} {E : ℕ × ℕ → Prop} {T : Finset Four}
    {Z R : Four → ℝ} (hN : 1 ≤ (N : ℝ)) (hT : T ⊆ source N E)
    (hcap : ∀ t ∈ T, R t ≤ (N : ℝ) ^ (153 / 256 : ℝ) / (multiplier t : ℝ))
    (hA : A N T Z R q ≠ 0) :
    0 < q ∧ Nat.Coprime N q ∧ (q : ℝ) ≤ (N : ℝ) ^ (153 / 256 : ℝ) := by
  have hq : q ∈ moduli N T Z R := by
    by_contra hnot
    exact hA (A_eq_zero_off_support hnot)
  exact moduli_physical_data hN hT hcap hq

/-- Original selected-parent slots imply the actual modulus support cap;
this supplies the structural PP gate without assuming a distribution law. -/
theorem parent_moduli_physical_data (N : ℕ) (hN : 1 < (N : ℝ))
    (E : ℕ × ℕ → Prop) (T : Finset Four) (hT : T ⊆ source N E)
    (lower upper : U11Integral.LogFour) (nu delta : ℝ)
    (hg : U11SelectedLargest.parentGate lower upper nu) (hlu : lower ≤ upper)
    (hdelta : 0 ≤ delta) (Z : Four → ℝ)
    (hupper : ∀ t ∈ T, (t.2.2 : ℝ) ≤ (N : ℝ) ^ upper 0 ∧
      (t.2.1 : ℝ) ≤ (N : ℝ) ^ upper 1 ∧
      (t.1.2 : ℝ) ≤ (N : ℝ) ^ upper 2 ∧ (t.1.1 : ℝ) ≤ (N : ℝ) ^ upper 3)
    (q : ℕ) (hq : q ∈ moduli N T Z
      (fun _ => (N : ℝ) ^ (nu - U11SelectedLargest.prefixSum upper - 20 * delta))) :
    0 < q ∧ Nat.Coprime N q ∧ (q : ℝ) ≤ (N : ℝ) ^ (153 / 256 : ℝ) := by
  apply moduli_physical_data hN.le hT ?_ hq
  intro t ht
  have hnu : nu ≤ (153 / 256 : ℝ) :=
    (U11SelectedLargest.parentGate_point hg hlu le_rfl).2.2.2.le.trans
      (U11SelectedLargest.cap_le_Lambda upper)
  have hj := P5U1011JointOverlap.originalU11_mem_joint hN.le (hT ht)
  exact reduced_level_cap N hN _ (P5U1011JointOverlap.joint_multiplier_pos hj)
    _ nu delta hnu hdelta (prefix_product_le_power N (zero_lt_one.trans hN) t upper (hupper t ht))

def physicalDensity (N : ℕ) (T : Finset Four) (Z R : Four → ℝ) : ℝ :=
  ∑ q ∈ moduli N T Z R, A N T Z R q / (Nat.totient q : ℝ)

def primeMassCorrection (N : ℕ) (T : Finset Four) (Z R : Four → ℝ) : ℝ :=
  (((chenPrimePrefix N).card : ℝ) - trueLogarithmicIntegral N) * physicalDensity N T Z R

def modulusPrimeCorrection (N : ℕ) (T : Finset Four) (Z R : Four → ℝ) : ℝ :=
  ∑ q ∈ moduli N T Z R, A N T Z R q *
    (chenPrimeDivisorCount N q / (Nat.totient q : ℝ))

def actualSignedPP (N : ℕ) (T : Finset Four) (Z R : Four → ℝ) : ℝ :=
  primeProductSignedError 1 N N (moduli N T Z R) (A N T Z R)
    (singletonWeight N (fun _ => 1))

/-- Both remaining corrections occur with their actual signs. The prime
mass centre is li(N), not an assumed replacement by the total prime mass. -/
theorem signedAP_eq_actualPP_and_corrections (N : ℕ) (T : Finset Four) (Z R : Four → ℝ) :
    (∑ t ∈ T, signedAP N t (Z t) (R t)) =
      actualSignedPP N T Z R + primeMassCorrection N T Z R - modulusPrimeCorrection N T Z R := by
  have hPP := primeProductSignedError_singleton_unit_eq_AP N (moduli N T Z R) (A N T Z R)
  have hmodel : (∑ t ∈ T, signedAP N t (Z t) (R t)) =
      (∑ q ∈ moduli N T Z R, A N T Z R q *
        (chenPrimeAPCount N N q - ((chenPrimePrefix N).card : ℝ) / (Nat.totient q : ℝ))) +
        primeMassCorrection N T Z R := by
    rw [signedAP_eq_modulus_sum]
    unfold primeMassCorrection physicalDensity
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    unfold chenQuotientPrimeAPError
    ring
  unfold actualSignedPP modulusPrimeCorrection
  linarith only [hPP, hmodel]

/-- Original selected ordinary winner families, with the centre already
paid, now expose the actual signed PP target and both exact recenterings. -/
theorem eventually_reduced_parent_upper_actualPP (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ E : ℕ × ℕ → Prop, ∀ T : Finset Four,
      T ⊆ source N E → ∀ lower upper : U11Integral.LogFour, ∀ nu delta xi rho : ℝ,
      U11SelectedLargest.parentGate lower upper nu → lower ≤ upper →
      0 ≤ delta → 0 ≤ xi → 0 < lower 3 - xi →
      20 * delta < nu - U11SelectedLargest.prefixSum upper → 0 < rho →
      (∀ t ∈ T, (N : ℝ) ^ lower 3 ≤ (t.1.1 : ℝ)) →
      (∀ t ∈ T, (t.2.2 : ℝ) ≤ (N : ℝ) ^ upper 0 ∧
        (t.2.1 : ℝ) ≤ (N : ℝ) ^ upper 1 ∧
        (t.1.2 : ℝ) ≤ (N : ℝ) ^ upper 2 ∧ (t.1.1 : ℝ) ≤ (N : ℝ) ^ upper 3) →
      let Z := fun _ : Four => (N : ℝ) ^ U11SelectedLargest.reducedCutoff lower upper nu delta xi rho
      let R := fun _ : Four => (N : ℝ) ^ (nu - U11SelectedLargest.prefixSum upper - 20 * delta)
      (∑ t ∈ T, weight N t) ≤ (∑ t ∈ T, mainTerm N t (Z t) (R t)) +
        actualSignedPP N T Z R + primeMassCorrection N T Z R - modulusPrimeCorrection N T Z R +
          epsilon * singularNormalization N := by
  filter_upwards [eventually_reduced_parent_upper_centre_paid epsilon hepsilon] with N hfinite
  intro E T hT lower upper nu delta xi rho hg hlu hdelta hxi hsmall hmargin hrho hfirst hupper
  have hh := hfinite E T hT lower upper nu delta xi rho hg hlu hdelta hxi hsmall hmargin hrho hfirst hupper
  rw [signedAP_eq_actualPP_and_corrections] at hh
  dsimp only at hh ⊢
  linarith only [hh]

end

end ImbalancedChen.P5Z.U11LoweredSignedPP
