import ImbalancedChen.P1ActualHighWWholeBoxNativeRegroup
import ImbalancedChen.SmallRoughMainTerm

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Independent arithmetic interface for the actual W4 fixed whole-box slots:
three normalized Mobius tuple coefficients, with the actual fixed small
Rosser beta attached only to group3. Unique small/rough multiplication
proves a one-bound on EVERY integer without a small-support cardinality.
The signed finite identity keeps the complete q=e*(a*b*d) exactly.

This module does NOT assume or prove that native rho is uniform on a
whole box. The original causal gate is absent from the separated object
constructed here, and no identity to native rho is asserted. Actual gate-
uniform subdivision and its wall/collision accounting remain necessary
before this object can replace the original coefficient in medium/Brun.
-/

namespace ImbalancedChen.P1ActualWGammaThirdBeta
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.Part3.ActualWFineWordAdapter
open ImbalancedChen.Part3.ActualWSmallThirdAttachment
open ImbalancedChen.Part3.ActualWThreeCapacityRun

def groupBox (N : ℕ) (sigma : ℝ) (word : List ℕ) : Finset (List ℕ) :=
  actualPrimeSlotBox (actualPrimeFineLabelFinset N sigma) word

def groupSupport (N : ℕ) (sigma : ℝ) (word : List ℕ) : Finset ℕ :=
  (groupBox N sigma word).image List.prod

/-- The original normalized prime tuple coefficient with its own Mobius
factor. Internal repeated-prime collisions vanish here, before estimates. -/
def gamma (N : ℕ) (sigma : ℝ) (word : List ℕ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℝ) *
    actualNormalizedPrimeTupleCoefficient (groupBox N sigma word) word.length n

theorem gamma_abs_le_one (N : ℕ) (sigma : ℝ) (word : List ℕ) (n : ℕ) :
    |gamma N sigma word n| ≤ 1 := by
  have hm : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  have hg := actualPrimeFineWord_normalized_abs_le_one N sigma word n
  rw [gamma, abs_mul]
  calc
    _ ≤ (1 : ℝ) * 1 := mul_le_mul hm hg (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem gamma_zero_off_support (N : ℕ) (sigma : ℝ) (word : List ℕ) {n : ℕ}
    (hn : n ∉ groupSupport N sigma word) : gamma N sigma word n = 0 := by
  have hf : (groupBox N sigma word).filter (fun ps => ps.prod = n) = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro ps hps
    obtain ⟨hps, heq⟩ := Finset.mem_filter.mp hps
    exact hn (Finset.mem_image.mpr ⟨ps, hps, heq⟩)
  simp only [gamma, actualNormalizedPrimeTupleCoefficient,
    actualPrimeTupleCoefficient, hf, Finset.card_empty, Nat.cast_zero, zero_div, mul_zero]

/-- Fine-label lower endpoints, not a factorability premise, give actual
rough support. Repeated labels/prime factors are allowed. -/
theorem groupSupport_rough {N : ℕ} (hN : 1 ≤ N) (sigma omega : ℝ)
    (word : List ℕ) (hword : ∀ label ∈ word, omega ≤ sigma * (label : ℝ))
    {d : ℕ} (hd : d ∈ groupSupport N sigma word) :
    RoughPrimeSupportedAt ((N : ℝ) ^ omega) d := by
  obtain ⟨ps, hps, rfl⟩ := Finset.mem_image.mp hd
  have hp : ∀ p ∈ ps, Nat.Prime p := actualPrimeSlotBox_prime
    (actualPrimeFineLabelFinset N sigma) word
    (fun _ _ p hp => (mem_actualPrimeFineLabelFinset.mp hp).1) ps hps
  have hpos : 0 < ps.prod := List.prod_pos (fun p h => (hp p h).pos)
  refine ⟨hpos.ne', ?_⟩
  intro p hfactor
  have hlist : p ∈ ps.prod.primeFactorsList := by
    apply List.mem_toFinset.mp
    simpa only [Nat.toFinset_factors] using hfactor
  have hperm := Nat.primeFactorsList_unique (rfl : ps.prod = ps.prod) hp
  have hpmem : p ∈ ps := hperm.mem_iff.mpr hlist
  obtain ⟨paired, hlabels, hvalues, hpair⟩ := atom_pairing
    (actualPrimeFineLabelFinset N sigma) word ps hps
  have hmap : p ∈ paired.map Prod.snd := by rwa [hvalues]
  obtain ⟨iq, hiq, hiqp⟩ := List.mem_map.mp hmap
  have hilabel : iq.1 ∈ word := by
    rw [← hlabels]
    exact List.mem_map.mpr ⟨iq, hiq, rfl⟩
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlo := (mem_actualPrimeFineLabelFinset.mp (hpair iq hiq)).2.2.1
  have hpow := Real.rpow_le_rpow_of_exponent_le hn (hword iq.1 hilabel)
  exact hpow.trans (by simpa only [hiqp] using hlo)

/-- The fixed sign-selected ORIGINAL small Rosser function. The caller
chooses lower/upper once on its source atom, before q or arithmetic tests. -/
def beta (lower : Bool) (N cap : ℕ) (w L : ℝ) : ℕ → ℝ :=
  if lower then actualSmallRosserMinus N cap w L else actualSmallRosserPlus N cap w L

theorem beta_abs_le_one (lower : Bool) (N cap : ℕ) (w L : ℝ) (e : ℕ) :
    |beta lower N cap w L e| ≤ 1 := by
  cases lower
  · exact actualSmallRosserPlus_abs_le_one N cap w L e
  · exact actualSmallRosserMinus_abs_le_one N cap w L e

/-- The actual third group and the fixed actual beta, as a single physical
coefficient on the exact product support. This definition does not use rho. -/
def attachedGamma3 (lower : Bool) (N cap : ℕ) (sigma omega L : ℝ)
    (word : List ℕ) : ℕ → ℝ :=
  smallRoughRho (actualSmallRosserSupport N cap ((N : ℝ) ^ omega))
    (groupSupport N sigma word) (gamma N sigma word)
    (beta lower N cap ((N : ℝ) ^ omega) L)
    (beta lower N cap ((N : ℝ) ^ omega) L)

def attachedSupport3 (N cap : ℕ) (sigma omega : ℝ) (word : List ℕ) : Finset ℕ :=
  smallRoughModuli (actualSmallRosserSupport N cap ((N : ℝ) ^ omega))
    (groupSupport N sigma word)

/-- Exactly ONE actual pair supplies every occupied full third modulus. -/
theorem attachedGamma3_at_product {N cap e d : ℕ} (hN : 1 ≤ N)
    (lower : Bool) (sigma omega L : ℝ) (word : List ℕ)
    (hword : ∀ label ∈ word, omega ≤ sigma * (label : ℝ))
    (he : e ∈ actualSmallRosserSupport N cap ((N : ℝ) ^ omega))
    (hd : d ∈ groupSupport N sigma word) :
    attachedGamma3 lower N cap sigma omega L word (e * d) =
      gamma N sigma word d * beta lower N cap ((N : ℝ) ^ omega) L e := by
  rw [attachedGamma3, smallRoughRho_mul
    (fun a ha => actualSmallRosserSupport_smallPrimeSupportedAt N cap _ ha)
    (fun b hb => groupSupport_rough hN sigma omega word hword hb) _ _ _ he hd]
  simp only [smallRoughPairCoefficient, signAttachedCoefficient, ite_self]

/-- Full-integer one-bound after beta, including values off support.
There is NO factor card(actualSmallRosserSupport). -/
theorem attachedGamma3_abs_le_one {N cap : ℕ} (hN : 1 ≤ N)
    (lower : Bool) (sigma omega L : ℝ) (word : List ℕ)
    (hword : ∀ label ∈ word, omega ≤ sigma * (label : ℝ)) (q : ℕ) :
    |attachedGamma3 lower N cap sigma omega L word q| ≤ 1 := by
  by_cases hq : q ∈ attachedSupport3 N cap sigma omega word
  · obtain ⟨⟨e, d⟩, hed, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨he, hd⟩ := Finset.mem_product.mp hed
    exact abs_smallRoughRho_mul_le_one
      (fun a ha => actualSmallRosserSupport_smallPrimeSupportedAt N cap _ ha)
      (fun b hb => groupSupport_rough hN sigma omega word hword hb)
      (gamma N sigma word) _ _ (fun d _ => gamma_abs_le_one N sigma word d)
      (fun e _ => beta_abs_le_one lower N cap _ L e)
      (fun e _ => beta_abs_le_one lower N cap _ L e) he hd
  · rw [attachedGamma3, smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hq]
    norm_num

/-- Exact signed beta push-forward with the original scalar and every
complete physical third modulus. No absolute values or size loss occur. -/
theorem attachedGamma3_fullq_sum {N cap : ℕ} (hN : 1 ≤ N)
    (lower : Bool) (sigma omega L : ℝ) (word : List ℕ)
    (hword : ∀ label ∈ word, omega ≤ sigma * (label : ℝ)) (F : ℕ → ℝ) :
    (∑ q ∈ attachedSupport3 N cap sigma omega word,
      attachedGamma3 lower N cap sigma omega L word q * F q) =
    ∑ e ∈ actualSmallRosserSupport N cap ((N : ℝ) ^ omega),
      ∑ d ∈ groupSupport N sigma word,
        gamma N sigma word d * beta lower N cap ((N : ℝ) ^ omega) L e * F (e * d) := by
  rw [attachedSupport3, attachedGamma3, sum_smallRoughRho_mul
    (fun a ha => actualSmallRosserSupport_smallPrimeSupportedAt N cap _ ha)
    (fun b hb => groupSupport_rough hN sigma omega word hword hb)]
  rw [smallRoughPairs, Finset.sum_product]
  simp only [smallRoughPairCoefficient, signAttachedCoefficient, ite_self]

/-- The all-three separated full-q arithmetic interface for independently
frozen original slot words. The original scalar is consumed literally. -/
theorem separated_three_group_beta_identity {N cap : ℕ} (hN : 1 ≤ N)
    (lower : Bool) (sigma omega L c : ℝ) (word1 word2 word3 : List ℕ)
    (hword3 : ∀ label ∈ word3, omega ≤ sigma * (label : ℝ)) (F : ℕ → ℝ) :
    (∑ a ∈ groupSupport N sigma word1, ∑ b ∈ groupSupport N sigma word2,
      ∑ q ∈ attachedSupport3 N cap sigma omega word3,
        c * gamma N sigma word1 a * gamma N sigma word2 b *
          attachedGamma3 lower N cap sigma omega L word3 q * F (a * b * q)) =
    ∑ a ∈ groupSupport N sigma word1, ∑ b ∈ groupSupport N sigma word2,
      ∑ e ∈ actualSmallRosserSupport N cap ((N : ℝ) ^ omega),
        ∑ d ∈ groupSupport N sigma word3,
          c * beta lower N cap ((N : ℝ) ^ omega) L e * gamma N sigma word1 a *
            gamma N sigma word2 b * gamma N sigma word3 d * F (e * (a * b * d)) := by
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have h := attachedGamma3_fullq_sum hN lower sigma omega L word3 hword3
    (fun q => c * gamma N sigma word1 a * gamma N sigma word2 b * F (a * b * q))
  calc
    _ = ∑ q ∈ attachedSupport3 N cap sigma omega word3,
        attachedGamma3 lower N cap sigma omega L word3 q *
          (c * gamma N sigma word1 a * gamma N sigma word2 b * F (a * b * q)) := by
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = _ := by
      rw [h]
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro d hd
      rw [show a * b * (e * d) = e * (a * b * d) by ring]
      ring

/-- The actual W4 right word inherits rough lower endpoints from the
original whole word by its proved occurrence permutation. -/
theorem row4_right_rough_endpoints (N : ℕ) (e sigma omega : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) (t : Fin 3 → ℝ) (A : ℝ)
    (labels : Fin 3 → ℕ) (tail : List ℕ)
    (hword : ∀ label ∈ labels 0 :: labels 1 :: labels 2 :: tail,
      omega ≤ sigma * (label : ℝ)) :
    ∀ label ∈ (row4Slots N e sigma m j t A labels tail).right,
      omega ≤ sigma * (label : ℝ) := by
  intro label hlabel
  have hperm := P1ActualHighWWholeBoxNativeRegroup.row4_slots_perm
    N e sigma m j t A labels tail
  apply hword label
  apply hperm.mem_iff.mp
  exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hlabel)))

end
end ImbalancedChen.P1ActualWGammaThirdBeta
