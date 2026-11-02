import ImbalancedChen.Part3TwoLongHBMellinBrunProfiles
import ImbalancedChen.DivisorMomentBudget
import ImbalancedChen.P5OriginalOneLongLiteralBrunDictionary
import ImbalancedChen.P5ActualLowerNormalizedPostModulusTail

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The proved elementary fourth-divisor moment is reused. Here Q and rho
are the literal full lower coefficient; no JOINT coefficient is substituted.
The Brun alphabet is exactly p <= Z and support is paid at REAL Z^r.
Only an active physical support gate remains; no P2, E4 or moment bound
is assumed. This pays expanded cores, not the unproved rough E1/E3 step.
-/
namespace ImbalancedChen.Part3.TwoLongActualLowerBrunMoment
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen.P5Z.ActualLowerNormalizedPostModulusTail (lowerQ lowerRho lowerRho_norm)
open ImbalancedChen.Part3.TwoLongActualThreeBrunP2Receiver (modulusBudget tau modulusBudget_nonneg)
open ImbalancedChen.Part3.TwoLongInternalP2Modes (CompositeWeilInput)
open ImbalancedChen.Part3.TwoLongHBMellinBrunProfiles
open ImbalancedChen.OriginalOneLongLiteralBrunDictionary
open ImbalancedChen.Part3.RoughSlotCharacterLift20261026b (smallPrimes smallPrimes_prime mem_smallPrimes)
open ImbalancedChen.Part3.TwoLongDivisorAxisClosure (chartDivisor)

def activeLowerQ (policy : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) : Finset ℕ :=
  (lowerQ policy N cap w z).filter (fun q => lowerRho policy N cap w z L q ≠ 0)

theorem lowerQ_geometry (policy : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    {q : ℕ} (hq : q ∈ lowerQ policy N cap w z) :
    0 < q ∧ Nat.Coprime N q ∧ Squarefree q := by
  have hsf := actualLowerSmallRoughModuli_squarefree policy N cap w z hq
  exact ⟨Nat.pos_of_ne_zero hsf.ne_zero,
    (actualLowerSmallRoughModuli_coprime_target policy N cap w z hq).symm, hsf⟩

theorem full_modulus_moment_eq_active (policy : List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) :
    (∑ q ∈ lowerQ policy N cap w z, ‖lowerRho policy N cap w z L q‖ * modulusBudget q) =
      ∑ q ∈ activeLowerQ policy N cap w z L,
        ‖lowerRho policy N cap w z L q‖ * modulusBudget q := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro q hq hnot
  have hz : lowerRho policy N cap w z L q = 0 := by
    by_contra hn
    exact hnot (Finset.mem_filter.mpr ⟨hq, hn⟩)
  simp [hz]

/-- No containment of inactive moduli is needed. The support gate is a
pointwise arithmetic size gate on the same coefficient, not a moment
estimate. Its adopted-policy supplier remains an internal obligation. -/
theorem actual_lower_p2_modulus_moment (policy : List ℕ → Bool) (N cap D : ℕ)
    (w z L : ℝ)
    (hlevel : ∀ q ∈ lowerQ policy N cap w z,
      lowerRho policy N cap w z L q ≠ 0 → q ≤ D) :
    (∑ q ∈ lowerQ policy N cap w z, ‖lowerRho policy N cap w z L q‖ * modulusBudget q) ≤
      ((D : ℝ) * Real.sqrt D + 1) * (4 * (1 + Real.log (max 1 (D : ℝ)))) ^ 16 := by
  rw [full_modulus_moment_eq_active]
  let S := activeLowerQ policy N cap w z L
  have hS : S ⊆ Finset.Icc 1 D := by
    intro q hq
    obtain ⟨hQ, hn⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Icc.mpr ⟨(lowerQ_geometry policy N cap w z hQ).1,
      hlevel q hQ hn⟩
  have hsf : ∀ q ∈ S, Squarefree q := by
    intro q hq
    exact (lowerQ_geometry policy N cap w z (Finset.mem_filter.mp hq).1).2.2
  have hpoint (q : ℕ) (hq : q ∈ S) :
      ‖lowerRho policy N cap w z L q‖ * modulusBudget q ≤
      ((D : ℝ) * Real.sqrt D + 1) *
        ((q.divisors.card : ℝ)^4 / (Nat.totient q : ℝ)) := by
    obtain ⟨hqpos, hqD⟩ := Finset.mem_Icc.mp (hS hq)
    have hphi : 0 < (Nat.totient q : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hqpos
    have hphiD : (Nat.totient q : ℝ) ≤ (D : ℝ) := by
      exact_mod_cast (Nat.totient_le q).trans hqD
    have htau : (1 : ℝ) ≤ (q.divisors.card : ℝ) := by
      have hm : 1 ∈ q.divisors := Nat.mem_divisors.mpr ⟨one_dvd _, Nat.ne_of_gt hqpos⟩
      exact_mod_cast Finset.card_pos.mpr ⟨1, hm⟩
    have htau1 : (q.divisors.card : ℝ) ≤ (q.divisors.card : ℝ)^4 := by
      simpa only [pow_one] using pow_le_pow_right₀ htau (by norm_num : (1 : ℕ) ≤ 4)
    have htau2 : (q.divisors.card : ℝ)^2 ≤ (q.divisors.card : ℝ)^4 :=
      pow_le_pow_right₀ htau (by norm_num)
    have hsqrt : Real.sqrt (q : ℝ) ≤ Real.sqrt (D : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hqD)
    have hfirst : Real.sqrt (q : ℝ) * (q.divisors.card : ℝ) ≤
        ((D : ℝ) * Real.sqrt D) * ((q.divisors.card : ℝ)^4 / (Nat.totient q : ℝ)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hphi).2
      calc
        _ ≤ Real.sqrt (D : ℝ) * (q.divisors.card : ℝ)^4 * (D : ℝ) := by gcongr
        _ = _ := by ring
    have hsecond : (q.divisors.card : ℝ)^2 / (Nat.totient q : ℝ) ≤
        (q.divisors.card : ℝ)^4 / (Nat.totient q : ℝ) :=
      div_le_div_of_nonneg_right htau2 hphi.le
    calc
      _ ≤ modulusBudget q := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (lowerRho_norm policy N cap w z L q) (modulusBudget_nonneg q)
      _ ≤ _ := by
        unfold modulusBudget tau
        nlinarith [hfirst, hsecond]
  calc
    _ ≤ ∑ q ∈ S, ((D : ℝ) * Real.sqrt D + 1) *
        ((q.divisors.card : ℝ)^4 / (Nat.totient q : ℝ)) := Finset.sum_le_sum hpoint
    _ = ((D : ℝ) * Real.sqrt D + 1) *
        ∑ q ∈ S, (q.divisors.card : ℝ)^4 / (Nat.totient q : ℝ) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_divisor_fourth_moment_le_log S D hS hsf) (by positivity)

def brunSupport (Z : ℝ) (r : ℕ) : Finset ℕ := divisorSupport (smallPrimes Z) r

theorem brunSupport_bounds {Z : ℝ} (hZ : 1 ≤ Z) (r : ℕ)
    {d : ℕ} (hd : d ∈ brunSupport Z r) : 0 < d ∧ (d : ℝ) ≤ Z^r := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hd
  have hAP := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
  have hAr := (Finset.mem_filter.mp hA).2
  refine ⟨chartDivisor_positive A (fun p hp => smallPrimes_prime (hAP hp)), ?_⟩
  calc
    (chartDivisor A : ℝ) = ∏ p ∈ A, (p : ℝ) := by simp [chartDivisor]
    _ ≤ ∏ _p ∈ A, Z := by
      apply Finset.prod_le_prod (fun p hp => Nat.cast_nonneg _)
      intro p hp
      exact ((mem_smallPrimes (by linarith)).mp (hAP hp)).2
    _ = Z^A.card := by simp
    _ ≤ Z^r := pow_le_pow_right₀ hZ hAr

/-- The actual image carrier has at most floor(Z^r) positive integers.
Thus the growing Brun order appears only in the power support, never
in a divisor-moment exponent or in a factorial restoring scalar. -/
theorem brunSupport_card {Z : ℝ} (hZ : 1 ≤ Z) (r : ℕ) :
    ((brunSupport Z r).card : ℝ) ≤ Z^r := by
  have hsub : brunSupport Z r ⊆ Finset.Icc 1 ⌊Z^r⌋₊ := by
    intro d hd
    obtain ⟨hpos, hbound⟩ := brunSupport_bounds hZ r hd
    exact Finset.mem_Icc.mpr ⟨hpos, Nat.le_floor hbound⟩
  have hc : (brunSupport Z r).card ≤ ⌊Z^r⌋₊ := by
    simpa using Finset.card_le_card hsub
  have hcR : ((brunSupport Z r).card : ℝ) ≤ (⌊Z^r⌋₊ : ℝ) := by exact_mod_cast hc
  exact hcR.trans (Nat.floor_le (pow_nonneg (by linarith) _))

def brunPairCoefficient (Z : ℝ) (j : ℕ) (b₁ b₂ : Bool) (d : ℕ × ℕ) : ℂ :=
  ((if b₁ then gapCoefficient (smallPrimes Z) (2*j+1) d.1
    else upperCoefficient (smallPrimes Z) (2*j) d.1) : ℂ) *
  ((if b₂ then gapCoefficient (smallPrimes Z) (2*j+1) d.2
    else upperCoefficient (smallPrimes Z) (2*j) d.2) : ℂ)

theorem brunPairCoefficient_norm (Z : ℝ) (j : ℕ) (b₁ b₂ : Bool) (d : ℕ × ℕ) :
    ‖brunPairCoefficient Z j b₁ b₂ d‖ ≤ 1 := by
  have hb (b : Bool) (e : ℕ) :
      ‖((if b then gapCoefficient (smallPrimes Z) (2*j+1) e
        else upperCoefficient (smallPrimes Z) (2*j) e) : ℂ)‖ ≤ 1 := by
    have h := coefficient_bounds (smallPrimes Z) (2*j) (2*j+1) e
    cases b
    · simpa only [Bool.false_eq_true, if_false, Complex.norm_real, Real.norm_eq_abs] using h.1
    · simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.2.1] using h.2.2
  rw [brunPairCoefficient, norm_mul]
  exact (mul_le_mul (hb b₁ d.1) (hb b₂ d.2) (norm_nonneg _) zero_le_one).trans_eq (by ring)

/-- The four Boolean coefficient pairs are bounded. E3 needs only the
upper/upper, gap/upper and upper/gap three. Transition-profile labels are
independent; confusing a smoothing strip with a Brun gap is avoided. -/
theorem brunPair_mass {Z : ℝ} (hZ : 1 ≤ Z) (j : ℕ) (b₁ b₂ : Bool) (alpha : ℂ) :
    (∑ d ∈ (brunSupport Z (2*j+1)) ×ˢ (brunSupport Z (2*j+1)),
      ‖brunPairCoefficient Z j b₁ b₂ d‖ * ‖alpha‖) ≤ (Z^(2*j+1))^2 * ‖alpha‖ := by
  calc
    _ ≤ ∑ _d ∈ (brunSupport Z (2*j+1)) ×ˢ (brunSupport Z (2*j+1)), ‖alpha‖ := by
      apply Finset.sum_le_sum
      intro d hd
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (brunPairCoefficient_norm Z j b₁ b₂ d) (norm_nonneg alpha)
    _ = ((brunSupport Z (2*j+1)).card : ℝ)^2 * ‖alpha‖ := by
      simp [Finset.card_product, Nat.cast_mul, pow_two]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (brunSupport_card hZ _) 2) (norm_nonneg alpha)

def lowerBrunCoreSum (policy : List ℕ → Bool) (N cap : ℕ) (w z L Z : ℝ)
    (j : ℕ) (b₁ b₂ : Bool) (delta U V t₁ t₂ : ℝ) (label : Fin 3)
    (log₁ log₂ : Bool) (alpha : ℂ) (m : ℕ) : ℂ :=
  ∑ q ∈ lowerQ policy N cap w z, lowerRho policy N cap w z L q *
    ∑ d ∈ (brunSupport Z (2*j+1)) ×ˢ (brunSupport Z (2*j+1)),
      brunPairCoefficient Z j b₁ b₂ d *
        mellinBrunCore delta U V t₁ t₂ label log₁ log₂ alpha m d.1 d.2 N q

/-- The local actual-lower-rho sum pays BOTH previously open finite
ports: the literal Brun coefficients/pairs and the physical P2 modulus
moment. H/I supply the internal profile/P2 body. No hP2 is a premise. -/
theorem actual_lower_Brun_P2 (hWeil : CompositeWeilInput)
    (policy : List ℕ → Bool) (N cap D : ℕ) (w z L : ℝ) {Z : ℝ} (hZ : 1 ≤ Z)
    (hlevel : ∀ q ∈ lowerQ policy N cap w z,
      lowerRho policy N cap w z L q ≠ 0 → q ≤ D)
    {delta U V H t₁ t₂ : ℝ} (hd : 0 < delta) (hs : delta ≤ 1/4)
    (hU : 0 < U) (hV : 0 < V) (hH : 0 ≤ H) (ht₁ : |t₁| ≤ H) (ht₂ : |t₂| ≤ H)
    (j : ℕ) (b₁ b₂ : Bool) (label : Fin 3) (log₁ log₂ : Bool) (alpha : ℂ) (m : ℕ) :
    ‖lowerBrunCoreSum policy N cap w z L Z j b₁ b₂ delta U V t₁ t₂ label log₁ log₂ alpha m‖ ≤
      pairCost delta U V H * ((Z^(2*j+1))^2 * ‖alpha‖) *
        (((D : ℝ) * Real.sqrt D + 1) * (4 * (1 + Real.log (max 1 (D : ℝ)))) ^ 16) := by
  have hp := finite_sameRho_mellinBrun hWeil hd hs hU hV hH ht₁ ht₂ label log₁ log₂ m N
    (lowerQ policy N cap w z) ((brunSupport Z (2*j+1)) ×ˢ (brunSupport Z (2*j+1)))
    (lowerRho policy N cap w z L) (fun _ => alpha) (brunPairCoefficient Z j b₁ b₂)
    (fun q hq => ⟨(lowerQ_geometry policy N cap w z hq).1,
      (lowerQ_geometry policy N cap w z hq).2.1⟩)
    (fun d hd => ⟨(brunSupport_bounds hZ _ (Finset.mem_product.mp hd).1).1,
      (brunSupport_bounds hZ _ (Finset.mem_product.mp hd).2).1⟩)
  exact hp.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (brunPair_mass hZ j b₁ b₂ alpha) (pairCost_nonneg _ _ _ _))
    (actual_lower_p2_modulus_moment policy N cap D w z L hlevel)
    (Finset.sum_nonneg (fun q hq => mul_nonneg (norm_nonneg _) (modulusBudget_nonneg _)))
    (mul_nonneg (pairCost_nonneg _ _ _ _) (mul_nonneg (sq_nonneg _) (norm_nonneg _))))

end
end ImbalancedChen.Part3.TwoLongActualLowerBrunMoment
