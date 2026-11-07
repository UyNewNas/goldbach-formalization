import ImbalancedChen.P5U7OriginalArithmeticFamily
import ImbalancedChen.P5U7OriginalOmegaIntegral
import ImbalancedChen.CurrentChenTrueLiNormalization
import ImbalancedChen.CurrentChenUpsilon9HarmonicIntegral
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabBands

/-!
Original U7 source-mass prerequisites, source only / uncompiled.
The first two imports are preceding exclusive drafts' proposed installed paths.

The actual prime and semiprime arithmetic sources are bounded by the actual
rough mother, with no multiplicity loss. The pinned proved Buchstab band
estimate then gives a finite original main term and its explicit boundary
error. Independently, uniform leading-one PNT bounds transport both terminal
prime counts to genuine li masses. No desired source-mass limit is a premise.
The final double-prime integral limit and boundary-error summation remain open.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology MeasureTheory Set LiLiuPrereqBuchstab
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

def p5U7MassPrimeFibre (N a ell : ℕ) : Finset ℕ :=
  (chenAdditivePrimeCarrier N).filter fun q => ell ≤ q ∧ a * q < N

def p5U7MassSemiprimePairs (N : ℕ) (t : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (chenAdditivePrimeCarrier N ×ˢ chenAdditivePrimeCarrier N).filter fun u =>
    t.2 ≤ u.1 ∧ u.1 ≤ u.2 ∧ t.1 * t.2 * (u.1 * u.2) < N

def p5U7MassSemiprimePrefixes (N : ℕ) (t : ℕ × ℕ) : Finset ℕ :=
  (chenAdditivePrimeCarrier N).filter fun r =>
    t.2 ≤ r ∧ (t.1 * t.2 * r) * r < N

theorem p5U7Mass_outer_geometry {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))) :
    0 < t.1 * t.2 ∧ (N : ℝ) ^ (59 / 250 : ℝ) ≤ (t.2 : ℝ) ∧
      (t.2 : ℝ) < (N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ) ∧
      (N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ) ≤ (t.2 : ℝ) ^ 3 := by
  obtain ⟨hc, hD, ho, hcap⟩ := Finset.mem_filter.mp ht
  obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hc
  have hp₁ := (mem_chenAdditivePrimeCarrier.mp h₁).2.1
  have hp₂ := (mem_chenAdditivePrimeCarrier.mp h₂).2.1
  have hb := mul_pos hp₁.pos hp₂.pos
  have hbR : (0 : ℝ) < ((t.1 * t.2 : ℕ) : ℝ) := by exact_mod_cast hb
  have hp₁R : (0 : ℝ) < t.1 := by exact_mod_cast hp₁.pos
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hcapsq : (t.2 : ℝ) ^ 2 < (N : ℝ) / (t.1 : ℝ) := by
    have h := (sq_lt_sq₀ (Nat.cast_nonneg t.2) (Real.sqrt_nonneg _)).mpr hcap
    rwa [Real.sq_sqrt (div_nonneg hN0 hp₁R.le)] at h
  have hmul : (t.1 : ℝ) * (t.2 : ℝ) ^ 2 < (N : ℝ) := by
    have h := (lt_div_iff₀ hp₁R).mp hcapsq
    nlinarith only [h]
  refine ⟨hb, hD.trans (by exact_mod_cast ho.le), ?_, ?_⟩
  · apply (lt_div_iff₀ hbR).mpr
    simpa only [Nat.cast_mul, pow_two, mul_assoc, mul_comm, mul_left_comm] using hmul
  · by_contra hn
    have hltR : ((t.1 * t.2 : ℕ) : ℝ) * (t.2 : ℝ) ^ 3 < (N : ℝ) := by
      have h := (lt_div_iff₀ hbR).mp (lt_of_not_ge hn)
      simpa only [mul_comm] using h
    have hlt : t.1 * t.2 * t.2 ^ 3 < N := by exact_mod_cast hltR
    exact (Nat.lt_irrefl (t.2 ^ 3)) (p5U7Arithmetic_rough_cofactor_lt_cube ht hlt)

/-- Actual finite prime-fibre count enlarged only to the prime prefix. -/
theorem p5U7Mass_primeFibre_card_le_primePi (N a ell : ℕ) (ha : 0 < a) :
    ((p5U7MassPrimeFibre N a ell).card : ℝ) ≤ primePi ((N : ℝ) / (a : ℝ)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hx0 : 0 ≤ (N : ℝ) / (a : ℝ) := div_nonneg (Nat.cast_nonneg N) haR.le
  have hsub : p5U7MassPrimeFibre N a ell ⊆ Nat.primesLE (Nat.floor ((N : ℝ) / (a : ℝ))) := by
    intro q hq
    obtain ⟨hqc, _hwall, hlt⟩ := Finset.mem_filter.mp hq
    have hltR : (a : ℝ) * (q : ℝ) < (N : ℝ) := by exact_mod_cast hlt
    have hqx : (q : ℝ) ≤ (N : ℝ) / (a : ℝ) :=
      ((lt_div_iff₀ haR).mpr (by simpa only [mul_comm] using hltR)).le
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hx0).mpr hqx,
      (mem_chenAdditivePrimeCarrier.mp hqc).2.1⟩
  have hc := (Finset.card_le_card hsub).trans_eq (Nat.primesLE_card_eq_primeCounting _)
  change ((p5U7MassPrimeFibre N a ell).card : ℝ) ≤
    (Nat.primeCounting (Nat.floor ((N : ℝ) / (a : ℝ))) : ℝ)
  exact_mod_cast hc

/-- The actual pinned PNT supplies the real tail; no PNT witness is an input. -/
theorem p5U7Mass_eventually_primePi_le_trueLi (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ x : ℝ in atTop, primePi x ≤ (1 + eta) * trueLogarithmicIntegral x := by
  have hsmall := tendsto_primeErrorEnvelope.eventually (gt_mem_nhds heta)
  filter_upwards [hsmall, eventually_ge_atTop (max 4 primeErrorStart)] with x he hx
  have hx4 : 4 ≤ x := (le_max_left _ _).trans hx
  have hxstart : primeErrorStart ≤ x := (le_max_right _ _).trans hx
  have hxpos : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hmain : 0 ≤ x / Real.log x := (div_pos hxpos hlog).le
  have herr := (le_abs_self (primePi x - x / Real.log x)).trans (primePi_error_le hxstart le_rfl)
  have herror := mul_le_mul_of_nonneg_right he.le hmain
  have hpi : primePi x ≤ (1 + eta) * (x / Real.log x) := by linarith only [herr, herror]
  have hli : x / Real.log x ≤ trueLogarithmicIntegral x := by
    apply (div_le_iff₀ hlog).mpr
    have hn := (currentChen_trueLi_normalized_bounds hx4).1
    simpa only [one_mul] using (le_div_iff₀ hxpos).mp hn
  exact hpi.trans (mul_le_mul_of_nonneg_left hli (by linarith))

/-- One threshold precedes all physical multipliers and ordered walls. -/
theorem p5U7Mass_eventually_all_primeFibres_le_trueLi (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ a ell : ℕ, 0 < a →
      (N : ℝ) ^ (59 / 250 : ℝ) ≤ (N : ℝ) / (a : ℝ) →
      ((p5U7MassPrimeFibre N a ell).card : ℝ) ≤
        (1 + eta) * trueLogarithmicIntegral ((N : ℝ) / (a : ℝ)) := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp (p5U7Mass_eventually_primePi_le_trueLi eta heta)
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ) ^ (59 / 250 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hgrowth.eventually (eventually_ge_atTop X)] with N hN
  intro a ell ha harg
  exact (p5U7Mass_primeFibre_card_le_primePi N a ell ha).trans (hX _ (hN.trans harg))

def p5U7MassPrimeLi (N : ℕ) : ℝ :=
  ∑ t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)),
    trueLogarithmicIntegral ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ))

theorem p5U7Mass_three_card_eq_primeFibres (N : ℕ) :
    ((p5U7ArithmeticThree N).card : ℝ) =
      ∑ t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)),
        ((p5U7MassPrimeFibre N (t.1 * t.2) t.2).card : ℝ) := by
  simp only [p5U7ArithmeticThree, p5U7MassPrimeFibre, Finset.card_sigma, Nat.cast_sum]

theorem p5U7Mass_eventually_three_le_primeLi (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ((p5U7ArithmeticThree N).card : ℝ) ≤ (1 + eta) * p5U7MassPrimeLi N := by
  filter_upwards [p5U7Mass_eventually_all_primeFibres_le_trueLi eta heta] with N hN
  rw [p5U7Mass_three_card_eq_primeFibres, p5U7MassPrimeLi, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  have hg := p5U7Mass_outer_geometry ht
  exact hN _ _ hg.1 (hg.2.1.trans hg.2.2.1.le)

/-- Exact ordered semiprime Fubini, before any PNT enlargement. -/
theorem p5U7Mass_pairs_card_eq_nested (N : ℕ) (t : ℕ × ℕ) :
    (p5U7MassSemiprimePairs N t).card =
      ∑ r ∈ p5U7MassSemiprimePrefixes N t,
        (p5U7MassPrimeFibre N (t.1 * t.2 * r) r).card := by
  have hc : (p5U7MassSemiprimePairs N t).card =
      ((p5U7MassSemiprimePrefixes N t).sigma
        (fun r => p5U7MassPrimeFibre N (t.1 * t.2 * r) r)).card := by
    refine Finset.card_bij' (fun u _ => ⟨u.1,u.2⟩) (fun v _ => (v.1,v.2)) ?_ ?_ ?_ ?_
    · rintro ⟨r,s⟩ hu
      obtain ⟨hrs, hwall, horder, hlt⟩ := Finset.mem_filter.mp hu
      obtain ⟨hrc,hsc⟩ := Finset.mem_product.mp hrs
      have hlt' : (t.1 * t.2 * r) * s < N := by simpa only [Nat.mul_assoc] using hlt
      have hrr : (t.1 * t.2 * r) * r < N :=
        (Nat.mul_le_mul_left _ horder).trans_lt hlt'
      exact Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨hrc,hwall,hrr⟩,
        Finset.mem_filter.mpr ⟨hsc,horder,hlt'⟩⟩
    · rintro ⟨r,s⟩ hv
      obtain ⟨hr,hs⟩ := Finset.mem_sigma.mp hv
      obtain ⟨hrc,hwall,_hrr⟩ := Finset.mem_filter.mp hr
      obtain ⟨hsc,horder,hlt⟩ := Finset.mem_filter.mp hs
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hrc,hsc⟩,hwall,horder,
        by simpa only [Nat.mul_assoc] using hlt⟩
    · intro u hu
      rfl
    · intro v hv
      rfl
  simpa only [Finset.card_sigma] using hc

theorem p5U7Mass_four_card_eq_nested (N : ℕ) :
    ((p5U7ArithmeticFour N).card : ℝ) =
      ∑ t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)),
        ∑ r ∈ p5U7MassSemiprimePrefixes N t,
          ((p5U7MassPrimeFibre N (t.1 * t.2 * r) r).card : ℝ) := by
  change (((chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))).sigma
    (p5U7MassSemiprimePairs N)).card : ℝ) = _
  simp only [Finset.card_sigma, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro t ht
  exact_mod_cast p5U7Mass_pairs_card_eq_nested N t

theorem p5U7Mass_prefix_argument_lower {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)))
    {r : ℕ} (hr : r ∈ p5U7MassSemiprimePrefixes N t) :
    0 < t.1 * t.2 * r ∧
      (N : ℝ) ^ (59 / 250 : ℝ) ≤ (N : ℝ) / ((t.1 * t.2 * r : ℕ) : ℝ) := by
  obtain ⟨hrc,hwall,hrr⟩ := Finset.mem_filter.mp hr
  have hpr := (mem_chenAdditivePrimeCarrier.mp hrc).2.1
  have hg := p5U7Mass_outer_geometry ht
  have ha := mul_pos hg.1 hpr.pos
  have haR : (0 : ℝ) < ((t.1 * t.2 * r : ℕ) : ℝ) := by exact_mod_cast ha
  have hrrR : ((t.1 * t.2 * r : ℕ) : ℝ) * (r : ℝ) < (N : ℝ) := by exact_mod_cast hrr
  have hrx : (r : ℝ) < (N : ℝ) / ((t.1 * t.2 * r : ℕ) : ℝ) :=
    (lt_div_iff₀ haR).mpr (by simpa only [mul_comm] using hrrR)
  exact ⟨ha, hg.2.1.trans ((by exact_mod_cast hwall : (t.2 : ℝ) ≤ r).trans hrx.le)⟩

def p5U7MassSemiprimeLi (N : ℕ) : ℝ :=
  ∑ t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)),
    ∑ r ∈ p5U7MassSemiprimePrefixes N t,
      trueLogarithmicIntegral ((N : ℝ) / ((t.1 * t.2 * r : ℕ) : ℝ))

theorem p5U7Mass_eventually_four_le_semiprimeLi (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ((p5U7ArithmeticFour N).card : ℝ) ≤ (1 + eta) * p5U7MassSemiprimeLi N := by
  filter_upwards [p5U7Mass_eventually_all_primeFibres_le_trueLi eta heta] with N hN
  rw [p5U7Mass_four_card_eq_nested, p5U7MassSemiprimeLi, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hg := p5U7Mass_prefix_argument_lower ht hr
  exact hN _ _ hg.1 hg.2

theorem p5U7Mass_eventually_total_le_liMasses (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      ((p5U7ArithmeticThree N).card : ℝ) + ((p5U7ArithmeticFour N).card : ℝ) ≤
        (1 + eta) * (p5U7MassPrimeLi N + p5U7MassSemiprimeLi N) := by
  filter_upwards [p5U7Mass_eventually_three_le_primeLi eta heta,
    p5U7Mass_eventually_four_le_semiprimeLi eta heta] with N hthree hfour
  exact (add_le_add hthree hfour).trans_eq (mul_add _ _ _).symm

private theorem p5U7Mass_rough_prime {p : ℕ} {z : ℝ} (hp : Nat.Prime p) (hz : z ≤ (p : ℝ)) :
    Rough z p := by
  intro r hr hd
  have heq : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp hd
  simpa only [heq] using hz

private theorem p5U7Mass_rough_pair {r s : ℕ} {z : ℝ}
    (hr : Nat.Prime r) (hs : Nat.Prime s) (hzr : z ≤ (r : ℝ)) (hrs : r ≤ s) : Rough z (r*s) := by
  intro p hp hd
  rcases hp.dvd_mul.mp hd with hdr | hds
  · have heq : p = r := (Nat.prime_dvd_prime_iff_eq hp hr).mp hdr
    simpa only [heq] using hzr
  · have heq : p = s := (Nat.prime_dvd_prime_iff_eq hp hs).mp hds
    subst p
    exact hzr.trans (by exact_mod_cast hrs)

/-- Both ungated branches enter one rough mother, with coefficient ONE. -/
theorem p5U7Mass_row_le_roughCount {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))) :
    ((p5U7MassPrimeFibre N (t.1*t.2) t.2).card : ℝ) +
      ((p5U7MassSemiprimePairs N t).card : ℝ) ≤
        (roughCount ((N : ℝ) / ((t.1*t.2 : ℕ) : ℝ)) (t.2 : ℝ) : ℝ) := by
  let P := p5U7MassPrimeFibre N (t.1*t.2) t.2
  let S := p5U7MassSemiprimePairs N t
  let Q := S.image (fun u => u.1*u.2)
  have hg := p5U7Mass_outer_geometry ht
  have hbR : (0 : ℝ) < ((t.1*t.2 : ℕ) : ℝ) := by exact_mod_cast hg.1
  have hP : P ⊆ roughNumbers ((N : ℝ) / ((t.1*t.2 : ℕ) : ℝ)) (t.2 : ℝ) := by
    intro q hq
    obtain ⟨hqc,hwall,hlt⟩ := Finset.mem_filter.mp hq
    have hp := (mem_chenAdditivePrimeCarrier.mp hqc).2.1
    have hltR : ((t.1*t.2 : ℕ) : ℝ)*(q : ℝ)<N := by exact_mod_cast hlt
    exact mem_roughNumbers.mpr ⟨hp.pos,
      ((lt_div_iff₀ hbR).mpr (by simpa only [mul_comm] using hltR)).le,
      p5U7Mass_rough_prime hp (by exact_mod_cast hwall)⟩
  have hQ : Q ⊆ roughNumbers ((N : ℝ) / ((t.1*t.2 : ℕ) : ℝ)) (t.2 : ℝ) := by
    intro q hq
    obtain ⟨⟨r,s⟩,hrs,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hc,hwall,horder,hlt⟩ := Finset.mem_filter.mp hrs
    obtain ⟨hrc,hsc⟩ := Finset.mem_product.mp hc
    have hr := (mem_chenAdditivePrimeCarrier.mp hrc).2.1
    have hs := (mem_chenAdditivePrimeCarrier.mp hsc).2.1
    have hltR : ((t.1*t.2 : ℕ) : ℝ)*((r*s : ℕ) : ℝ)<N := by exact_mod_cast hlt
    exact mem_roughNumbers.mpr ⟨mul_pos hr.pos hs.pos,
      ((lt_div_iff₀ hbR).mpr (by simpa only [mul_comm] using hltR)).le,
      p5U7Mass_rough_pair hr hs (by exact_mod_cast hwall) horder⟩
  have hinj : Set.InjOn (fun u : ℕ×ℕ => u.1*u.2) S := by
    intro a ha b hb heq
    obtain ⟨hac,_hwa,hoa,_hlta⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbc,_hwb,hob,_hltb⟩ := Finset.mem_filter.mp hb
    obtain ⟨ha1,ha2⟩ := Finset.mem_product.mp hac
    obtain ⟨hb1,hb2⟩ := Finset.mem_product.mp hbc
    obtain ⟨he1,he2⟩ := ordered_prime_factors_unique
      (mem_chenAdditivePrimeCarrier.mp ha1).2.1 (mem_chenAdditivePrimeCarrier.mp ha2).2.1
      (mem_chenAdditivePrimeCarrier.mp hb1).2.1 (mem_chenAdditivePrimeCarrier.mp hb2).2.1 hoa hob heq
    exact Prod.ext he1 he2
  have hd : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro q hqP hqQ
    have hprime := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hqP).1).2.1
    obtain ⟨⟨r,s⟩,hrs,rfl⟩ := Finset.mem_image.mp hqQ
    have hc := (Finset.mem_filter.mp hrs).1
    obtain ⟨hrc,hsc⟩ := Finset.mem_product.mp hc
    exact (Nat.not_prime_mul (mem_chenAdditivePrimeCarrier.mp hrc).2.1.ne_one
      (mem_chenAdditivePrimeCarrier.mp hsc).2.1.ne_one) hprime
  have hcardQ : Q.card = S.card := Finset.card_image_of_injOn hinj
  have hbound := Finset.card_le_card (Finset.union_subset hP hQ)
  rw [Finset.card_union_of_disjoint hd,hcardQ] at hbound
  change (P.card : ℝ) + (S.card : ℝ) ≤
    ((roughNumbers ((N : ℝ) / ((t.1*t.2 : ℕ) : ℝ)) (t.2 : ℝ)).card : ℝ)
  exact_mod_cast hbound

def p5U7MassBuchstabMain (N : ℕ) : ℝ :=
  ∑ t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)),
    let x := (N : ℝ) / ((t.1*t.2 : ℕ) : ℝ)
    x * buchstab (Real.log x / Real.log (t.2 : ℝ)) / Real.log (t.2 : ℝ)

def p5U7MassBuchstabBoundaryError (N : ℕ) : ℝ :=
  ∑ t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)),
    let x := (N : ℝ) / ((t.1*t.2 : ℕ) : ℝ)
    buchstabBandConstant 3 * (buchstabRemainder (t.2 : ℝ) * (x / Real.log (t.2 : ℝ)) +
      (t.2 : ℝ) / Real.log (t.2 : ℝ))

/-- The proved pinned rough-count supplier applies in the actual original
three-band geometry. The boundary term is retained, not declared negligible. -/
theorem p5U7Mass_eventually_total_le_Buchstab_with_boundary :
    ∀ᶠ N : ℕ in atTop,
      ((p5U7ArithmeticThree N).card : ℝ) + ((p5U7ArithmeticFour N).card : ℝ) ≤
        p5U7MassBuchstabMain N + p5U7MassBuchstabBoundaryError N := by
  have hgrowth : Tendsto (fun N : ℕ => (N : ℝ) ^ (59 / 250 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hgrowth.eventually (eventually_ge_atTop primeErrorStart)] with N hN
  rw [p5U7Mass_three_card_eq_primeFibres]
  have hfour : ((p5U7ArithmeticFour N).card : ℝ) =
      ∑ t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)),
        ((p5U7MassSemiprimePairs N t).card : ℝ) := by
    change (((chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))).sigma
      (p5U7MassSemiprimePairs N)).card : ℝ) = _
    simp only [Finset.card_sigma,Nat.cast_sum]
  rw [hfour,← Finset.sum_add_distrib]
  unfold p5U7MassBuchstabMain p5U7MassBuchstabBoundaryError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t ht
  have hg := p5U7Mass_outer_geometry ht
  have herr := roughCount_buchstab_band_error 3 (by norm_num)
    (hN.trans hg.2.1) hg.2.2.1.le hg.2.2.2
  have hu := (le_abs_self _).trans herr
  exact (p5U7Mass_row_le_roughCount ht).trans (by linarith only [hu])

theorem p5U7Mass_eventually_productWeight_le_Buchstab_with_boundary :
    ∀ᶠ N : ℕ in atTop,
      (∑ m ∈ Finset.range N, p5U7ArithmeticProductWeight N m) ≤
        p5U7MassBuchstabMain N + p5U7MassBuchstabBoundaryError N := by
  filter_upwards [p5U7Mass_eventually_total_le_Buchstab_with_boundary] with N hN
  rw [p5U7Arithmetic_product_weight_mass]
  exact hN

/-- The real three-prime harmonic candidate for the semiprime branch.
Its last-prime PNT has already been isolated above; this is a real integral,
not a definition of the missing arithmetic limit. -/
def p5U7MassSemiprimeIntegralSlice (t u : ℝ) : ℝ :=
  ∫ v in Set.Ico u ((1 - t - u) / 2),
    1 / (t * u * v * (1 - t - u - v))

/-- The exact semiprime inner integral supplies the log(s-1) term in
the actual second Buchstab piece. The s=2 wall gives a zero-width interval. -/
theorem p5U7Mass_semiprime_integral_slice_eq {t u : ℝ}
    (ht : 0 < t) (htu : t ≤ u) (hcut : u ≤ (1 - t) / 3) :
    p5U7MassSemiprimeIntegralSlice t u =
      Real.log ((1 - t - 2*u) / u) / (t * u * (1 - t - u)) := by
  have hu : 0 < u := ht.trans_le htu
  have hsum : 0 < t + u := add_pos ht hu
  have hsum1 : t + u < 1 := by linarith
  have hA : 0 < 1 - t - u := by linarith
  have hA' : 0 < 1 - (t+u) := by linarith
  have hcap : u ≤ (1 - (t+u)) / 2 := by linarith
  have hbase := currentChenUpsilon9Harmonic_inner_integral hsum hsum1 hu hcap
  have hend : (1 - t - u) / 2 = (1 - (t+u)) / 2 := by ring
  calc
    _ = ((t+u)/(t*u)) *
        (∫ v in Set.Ico u ((1-(t+u))/2), 1/((t+u)*v*(1-(t+u)-v))) := by
      unfold p5U7MassSemiprimeIntegralSlice
      rw [hend, ← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ico
      intro v hv
      have hvpos : 0 < v := hu.trans_le hv.1
      have hgap : 0 < 1 - (t+u) - v := by linarith [hv.2]
      have hgap' : 0 < 1 - t - u - v := by linarith
      field_simp [ht.ne', hu.ne', hsum.ne', hvpos.ne', hgap.ne', hgap'.ne']
      <;> ring
    _ = _ := by
      rw [hbase]
      have hlogarg : 1 - (t+u) - u = 1 - t - 2*u := by ring
      rw [hlogarg]
      field_simp [ht.ne', hu.ne', hsum.ne', hA.ne', hA'.ne']
      <;> ring

theorem p5U7Mass_semiprime_integral_slice_nonneg {t u : ℝ}
    (ht : 0 < t) (htu : t ≤ u) (hcut : u ≤ (1 - t) / 3) :
    0 ≤ p5U7MassSemiprimeIntegralSlice t u := by
  have hu : 0 < u := ht.trans_le htu
  have harg : 1 ≤ (1 - t - 2*u) / u := (le_div_iff₀ hu).mpr (by linarith)
  rw [p5U7Mass_semiprime_integral_slice_eq ht htu hcut]
  exact div_nonneg (Real.log_nonneg harg)
    (mul_nonneg (mul_nonneg ht.le hu.le) (by linarith))

/-- The real source-mass candidate consists of a terminal-prime density
and the ordered semiprime inner integral only where its interval exists. -/
def p5U7MassRealKernel (t u : ℝ) : ℝ :=
  1 / (t*u*(1-t-u)) +
    if u < (1-t)/3 then p5U7MassSemiprimeIntegralSlice t u else 0

theorem p5U7MassRealKernel_eq_originalOmega {t u : ℝ}
    (h : p5U7OmegaClosedSupport t u) :
    p5U7MassRealKernel t u = p5U7OmegaKernel 1 t u := by
  have ht := (p5U7Omega_closed_geometry h).1
  unfold p5U7MassRealKernel
  by_cases hcut : (1-t)/3 ≤ u
  · rw [if_neg (not_lt_of_ge hcut), p5U7Omega_kernel_first 1 h hcut]
    simp only [p5U7OmegaFirstKernel, add_zero]
  · have hu := lt_of_not_ge hcut
    rw [if_pos hu, (p5U7Omega_kernel_second 1 h hu).2,
      p5U7Mass_semiprime_integral_slice_eq ht h.2.1 hu.le]
    dsimp [p5U7OmegaSecondKernel]
    ring

/-- Exact identification of the real candidate with the original omega
functional at K=1. This is not a source-mass asymptotic hypothesis. -/
theorem p5U7Mass_real_candidate_integral_eq_originalOmega :
    (∫ t in (59/250 : ℝ)..(1/3 : ℝ),
      ∫ u in t..((1-t)/2), p5U7MassRealKernel t u) = p5U7OriginalOmegaIntegral 1 := by
  unfold p5U7OriginalOmegaIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (59/250 : ℝ) ≤ 1/3)] at ht
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le (by linarith [ht.2] : t ≤ (1-t)/2)] at hu
  exact p5U7MassRealKernel_eq_originalOmega ⟨ht.1,hu.1,hu.2⟩

end

end ImbalancedChen
