import ImbalancedChen.P1OriginalHistoricalTwoLongP2
import ImbalancedChen.P1HistoricalTwoLongFiniteRoughData

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

Finite historical P1 rough-to-upper comparison for the frozen 1106
coefficient appendix, rough-product-gap and two-rough-error. This module
reuses the preserved actual_pair_E3, polynomial_P2 and gapPairMean_point;
it does not reprove their finite Brun, E1 or P2 arguments.

The physical modulus carrier and signed coefficient are precisely
historicalModuli and historicalRho. The mean keeps one totient inverse,
both positive gap products, the nonunit-short zero branch and the factor
two on the exact means. The actual factorial Brun epsilon is supplied by
gap_density_B2. Its coefficient contains only the reciprocal moment R(D),
with no additional D or Y. The scalar gates epsilon <= 1 and Y <= x are
explicit; no gap-mean, P2 or target-bound premise is introduced.

The missing Part3TwoLongFixedMRectangularCore source still prevents a
complete import closure. No source is reconstructed here. Sharp strips,
singleton Fourier reconstruction, outer HB/selector attachment and final
asymptotic payment remain outside this finite comparison.
-/

namespace ImbalancedChen.P1OriginalHistoricalTwoLongRoughComparison
noncomputable section
open Classical Set
open scoped BigOperators SchwartzMap
open P1OriginalHistoricalTwoLongP2
open P4BOriginalRoughPairFinite
open P4BOriginalEnvelopePolynomialPayment (p2Price p2Price_nonneg polynomial_P2)
open P4BOriginalPositiveLongEnvelope
open P4BOriginalTwiceMeanPayment (gapPairMean gapPairMean_point)
open P4BOriginalPairMeanNorm (densityLog densityLog_one_le)
open P4BOriginalBrunCoprimeE1 (density gap_density_B2)
open OriginalOneLongE5FiniteBudget (brunEpsilon)
open Part3.RoughSlotCharacterLift20261026b (smallPrimes)
open Part3.TwoLongHBMellinBrunProfiles
open Part3.TwoLongLiteralMellinModes (wideWindow)
open Part3.TwoLongLiteralBrunSubstitution
  (smoothBrunTupleCore smoothBrunTupleCore_eq_expansion)
open Part3.TwoLongTransitionMellinN2
open Part3.TwoLongActualThreeBrunP2Receiver
  (modulusBudget modulusBudget_nonneg)
open Part3.TwoLongActualHBShortMass
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.ActualRoughHeathBrownWords (Role)

/-- The fixed logarithmic reciprocal budget; it has no power of D. -/
def reciprocalMoment (D : ℕ) : ℝ :=
  (4 * (1 + Real.log (max 1 (D : ℝ)))) ^ 16

theorem reciprocalMoment_nonneg (D : ℕ) : 0 ≤ reciprocalMoment D := by
  unfold reciprocalMoment
  positivity

/-- The original signed historical coefficient stays inside the rough sum. -/
def historicalRoughSum (B : ℝ) (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (F G : ℝ → ℂ) (U V Z : ℝ)
    (Mset : Finset ℕ) (alpha : ℕ → ℂ) : ℂ :=
  ∑ q ∈ historicalModuli B old fresh N cap w z,
    historicalRho old fresh N cap w z L q *
      ∑ short ∈ Mset, roughDelta F G U V Z short N q (alpha short)

def historicalPolynomialSum (B : ℝ) (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (F G : ℝ → ℂ) (U V Z : ℝ)
    (j : ℕ) (b₁ b₂ : Bool) (Mset : Finset ℕ) (alpha : ℕ → ℂ) : ℂ :=
  ∑ q ∈ historicalModuli B old fresh N cap w z,
    historicalRho old fresh N cap w z L q *
      ∑ short ∈ Mset, polyDelta F G U V Z j b₁ b₂ short N q (alpha short)

/-- Direct dictionary attachment to the original strict rough masks.
The complete short*u*v remains in the exact residue kernel. -/
theorem historicalRoughSum_original (B : ℝ) (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (F G : ℝ → ℂ) (U V : ℝ)
    {Z : ℝ} (hZ : 0 ≤ Z) (Mset : Finset ℕ) (alpha : ℕ → ℂ) :
    historicalRoughSum B old fresh N cap w z L F G U V Z Mset alpha =
      ∑ q ∈ historicalModuli B old fresh N cap w z,
        historicalRho old fresh N cap w z L q * ∑ short ∈ Mset,
          ∑ u ∈ wideWindow U, ∑ v ∈ wideWindow V,
            alpha short * F ((u : ℝ)/U) * G ((v : ℝ)/V) *
              Part3.roughOneSlot Z u * Part3.roughOneSlot Z v *
                MellinInsertion20261028.residueKernel q N (short*u*v) := by
  simp only [historicalRoughSum, roughDelta_original F G U V hZ]

private theorem divisor_card_one_le {q : ℕ} (hq : 0 < q) :
    (1 : ℝ) ≤ (q.divisors.card : ℝ) := by
  have hc : 0 < q.divisors.card := Finset.card_pos.mpr
    ⟨1, Nat.mem_divisors.mpr ⟨one_dvd _, hq.ne'⟩⟩
  exact_mod_cast Nat.succ_le_of_lt hc

/-- All needed reciprocal orders are paid on the actual historical set.
This invokes the existing fourth-divisor moment, not a P4 coefficient. -/
theorem historical_tau_moment (B : ℝ) (old fresh : List ℕ → Bool)
    (N cap D : ℕ) (w z L : ℝ)
    (hlevel : ∀ q ∈ historicalModuli B old fresh N cap w z, q ≤ D)
    (p : ℕ) (hp : p ≤ 4) :
    (∑ q ∈ historicalModuli B old fresh N cap w z,
      ‖historicalRho old fresh N cap w z L q‖ *
        (q.divisors.card : ℝ)^p / (q.totient : ℝ)) ≤ reciprocalMoment D := by
  let Q := historicalModuli B old fresh N cap w z
  have hQ : Q ⊆ Finset.Icc 1 D := by
    intro q hq
    exact Finset.mem_Icc.mpr
      ⟨(historical_modulus_class B old fresh N cap w z L hq).1, hlevel q hq⟩
  calc
    _ ≤ ∑ q ∈ Q, (q.divisors.card : ℝ)^4 / (q.totient : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      obtain ⟨hqpos, _, _, hrho⟩ :=
        historical_modulus_class B old fresh N cap w z L hq
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      calc
        _ ≤ (q.divisors.card : ℝ)^p := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hrho (by positivity)
        _ ≤ _ := pow_le_pow_right₀ (divisor_card_one_le hqpos) hp
    _ ≤ _ := sum_divisor_fourth_moment_le_log Q D hQ
      (fun q hq => (historical_modulus_class B old fresh N cap w z L hq).2.2.1)

/-- Absolute finite payment for one polynomial product. The existing
polynomial_P2 and historical_modulus_moment do all analytic/arithmetic work. -/
theorem historical_polynomial_norm_sum (B : ℝ) (old fresh : List ℕ → Bool)
    (N cap D : ℕ) (w z L : ℝ)
    (hlevel : ∀ q ∈ historicalModuli B old fresh N cap w z, q ≤ D)
    (F G : 𝓢(ℝ,ℂ))
    (hF : Function.support (F : ℝ → ℂ) ⊆ Icc (1/2 : ℝ) (5/2))
    (hG : Function.support (G : ℝ → ℂ) ⊆ Icc (1/2 : ℝ) (5/2))
    {U V Z : ℝ} (hU : 0 < U) (hV : 0 < V) (hZ : 1 ≤ Z)
    (j : ℕ) (b₁ b₂ : Bool) (Mset : Finset ℕ) (alpha : ℕ → ℂ) :
    (∑ q ∈ historicalModuli B old fresh N cap w z,
      ‖historicalRho old fresh N cap w z L q‖ *
        ∑ short ∈ Mset, ‖polyDelta F G U V Z j b₁ b₂ short N q (alpha short)‖) ≤
      p2Price F G * ((Z^(2*j+1))^2 * ∑ short ∈ Mset, ‖alpha short‖) *
        momentBudget D := by
  let Q := historicalModuli B old fresh N cap w z
  let c := historicalRho old fresh N cap w z L
  let μ := ∑ short ∈ Mset, ‖alpha short‖
  let Y := Z^(2*j+1)
  let K := p2Price F G * (Y^2 * μ)
  have hK : 0 ≤ K := by
    have hP := p2Price_nonneg F G
    have hμ : 0 ≤ μ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    dsimp only [K]
    positivity
  have hpoint (q : ℕ) (hq : q ∈ Q) (short : ℕ) :
      ‖polyDelta F G U V Z j b₁ b₂ short N q (alpha short)‖ ≤
        p2Price F G * (Y^2 * ‖alpha short‖) * modulusBudget q := by
    obtain ⟨hqpos, hN, hsq, _⟩ :=
      historical_modulus_class B old fresh N cap w z L hq
    exact polynomial_P2 F G hF hG hU hV hZ j b₁ b₂ short N q hqpos hsq hN _
  have hinner (q : ℕ) :
      (∑ short ∈ Mset,
        p2Price F G * (Y^2 * ‖alpha short‖) * modulusBudget q) =
      K * modulusBudget q := by
    calc
      _ = (p2Price F G * Y^2 * modulusBudget q) * μ := by
        dsimp only [μ]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro short hshort
        ring
      _ = _ := by dsimp only [K]; ring
  calc
    _ ≤ ∑ q ∈ Q, ‖c q‖ * ∑ short ∈ Mset,
        p2Price F G * (Y^2 * ‖alpha short‖) * modulusBudget q := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun short _ => hpoint q hq short)) (norm_nonneg _)
    _ = ∑ q ∈ Q, K * (‖c q‖ * modulusBudget q) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hinner]
      ring
    _ = K * ∑ q ∈ Q, ‖c q‖ * modulusBudget q := by rw [Finset.mul_sum]
    _ ≤ K * momentBudget D := mul_le_mul_of_nonneg_left
      (historical_modulus_moment B old fresh N cap D w z L hlevel) hK

/-- Twice the exact mean, estimated for each q before summation.
The tau^0, tau^1 and tau^2 terms are jointly dominated by tau^4;
the actual epsilon term acquires only reciprocalMoment D. -/
theorem historical_twice_mean_sum (B : ℝ) (old fresh : List ℕ → Bool)
    (N cap D : ℕ) (w z L : ℝ)
    (hlevel : ∀ q ∈ historicalModuli B old fresh N cap w z, q ≤ D)
    {Z delta U V x : ℝ} (hZ : 1 ≤ Z) (hd : 0 < delta) (hs : delta ≤ 1/4)
    (hU : 0 < U) (hV : 0 < V) (hx : 1 ≤ x) (j : ℕ)
    (he1 : brunEpsilon j (smallPrimes Z) ≤ 1) (hy : Z^(2*j+1) ≤ x)
    (Mset : Finset ℕ) (alpha : ℕ → ℂ) :
    let E := envelopeSchwartz hd hs U
    let J := envelopeSchwartz hd hs V
    let μ := ∑ short ∈ Mset, ‖alpha short‖
    let Y := Z^(2*j+1)
    let ε := brunEpsilon j (smallPrimes Z)
    (∑ q ∈ historicalModuli B old fresh N cap w z,
      ‖historicalRho old fresh N cap w z L q‖ * ∑ short ∈ Mset,
        2 * ‖alpha short‖ * gapPairMean E J U V Z j q short) ≤
      2*μ*meanPrice delta U*meanPrice delta V*reciprocalMoment D*
        (2*U*V*ε*densityLog x + 2*densityLog x*(U+V)*Y + 2*Y^2) := by
  let Q := historicalModuli B old fresh N cap w z
  let c := historicalRho old fresh N cap w z L
  let E := envelopeSchwartz hd hs U
  let J := envelopeSchwartz hd hs V
  let μ := ∑ short ∈ Mset, ‖alpha short‖
  let Y := Z^(2*j+1)
  let ε := brunEpsilon j (smallPrimes Z)
  let P := meanPrice delta U * meanPrice delta V
  let A := 2*U*V*ε*densityLog x
  let C := 2*densityLog x*(U+V)*Y
  let H := 2*Y^2
  let K := 2*μ*P*(A+C+H)
  have he : 0 ≤ ε := (norm_nonneg _).trans (gap_density_B2 Z j 1 1)
  have hY : 0 ≤ Y := pow_nonneg (zero_le_one.trans hZ) _
  have hlog : 0 ≤ densityLog x := zero_le_one.trans (densityLog_one_le hx)
  have hP : 0 ≤ P := mul_nonneg (meanPrice_nonneg _ _) (meanPrice_nonneg _ _)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hμ : 0 ≤ μ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hpoint (q : ℕ) (hq : q ∈ Q) (short : ℕ) :
      gapPairMean E J U V Z j q short ≤
        P*(A+C+H)*(q.divisors.card : ℝ)^4 / (q.totient : ℝ) := by
    have hqpos := (historical_modulus_class B old fresh N cap w z L hq).1
    have hT := divisor_card_one_le hqpos
    have h0 : (1 : ℝ) ≤ (q.divisors.card : ℝ)^4 := by
      simpa only [pow_zero] using pow_le_pow_right₀ hT (by norm_num : (0 : ℕ) ≤ 4)
    have h1 : (q.divisors.card : ℝ) ≤ (q.divisors.card : ℝ)^4 := by
      simpa only [pow_one] using pow_le_pow_right₀ hT (by norm_num : (1 : ℕ) ≤ 4)
    have h2 : (q.divisors.card : ℝ)^2 ≤ (q.divisors.card : ℝ)^4 :=
      pow_le_pow_right₀ hT (by norm_num)
    have hg := gapPairMean_point hd hs hU hV hZ hx he he1 j q short hqpos hy
      (gap_density_B2 Z j q 1)
    change gapPairMean E J U V Z j q short ≤
      P*(A+C*(q.divisors.card : ℝ)+H*(q.divisors.card : ℝ)^2) /
        (q.totient : ℝ) at hg
    have hnum : A+C*(q.divisors.card : ℝ)+H*(q.divisors.card : ℝ)^2 ≤
        (A+C+H)*(q.divisors.card : ℝ)^4 := by
      calc
        _ = A*1+C*(q.divisors.card : ℝ)+H*(q.divisors.card : ℝ)^2 := by ring
        _ ≤ A*(q.divisors.card : ℝ)^4+C*(q.divisors.card : ℝ)^4+
            H*(q.divisors.card : ℝ)^4 :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left h0 hA)
            (mul_le_mul_of_nonneg_left h1 hC)) (mul_le_mul_of_nonneg_left h2 hH)
        _ = _ := by ring
    exact hg.trans ((div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnum hP) (Nat.cast_nonneg _)).trans_eq (by ring))
  calc
    _ ≤ ∑ q ∈ Q, ‖c q‖ * ∑ short ∈ Mset,
        2*‖alpha short‖ *
          (P*(A+C+H)*(q.divisors.card : ℝ)^4 / (q.totient : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.sum_le_sum (fun short _ =>
        mul_le_mul_of_nonneg_left (hpoint q hq short) (by positivity))
    _ = ∑ q ∈ Q, K * (‖c q‖*(q.divisors.card : ℝ)^4/(q.totient : ℝ)) := by
      apply Finset.sum_congr rfl
      intro q hq
      calc
        _ = ∑ short ∈ Mset,
            (2*P*(A+C+H)*‖c q‖*(q.divisors.card : ℝ)^4/(q.totient : ℝ)) *
              ‖alpha short‖ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro short hshort
          ring
        _ = (2*P*(A+C+H)*‖c q‖*(q.divisors.card : ℝ)^4/(q.totient : ℝ)) * μ := by
          dsimp only [μ]
          rw [Finset.mul_sum]
        _ = _ := by dsimp only [K]; ring
    _ = K * ∑ q ∈ Q, ‖c q‖*(q.divisors.card : ℝ)^4/(q.totient : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ K * reciprocalMoment D := mul_le_mul_of_nonneg_left
      (historical_tau_moment B old fresh N cap D w z L hlevel 4 (by norm_num)) hK
    _ = _ := by dsimp only [K, P, A, C, H, μ, Y, ε]; ring

/-- Finite historical rough-minus-upper comparison. The profile labels
and log flags are independent of the two positive Brun gap flags. -/
theorem finite_rough_comparison (B : ℝ) (old fresh : List ℕ → Bool)
    (N cap D : ℕ) (w z L : ℝ)
    (hlevel : ∀ q ∈ historicalModuli B old fresh N cap w z, q ≤ D)
    {Z delta U V x : ℝ} (hZ : 1 ≤ Z) (hd : 0 < delta) (hs : delta ≤ 1/4)
    (hU : 0 < U) (hV : 0 < V) (hx : 1 ≤ x) (j : ℕ)
    (he1 : brunEpsilon j (smallPrimes Z) ≤ 1) (hy : Z^(2*j+1) ≤ x)
    (t₁ t₂ : ℝ) (label : Fin 3) (log₁ log₂ : Bool)
    (Mset : Finset ℕ) (alpha : ℕ → ℂ) :
    let E := envelopeSchwartz hd hs U
    let J := envelopeSchwartz hd hs V
    let μ := ∑ short ∈ Mset, ‖alpha short‖
    let Y := Z^(2*j+1)
    let ε := brunEpsilon j (smallPrimes Z)
    ‖historicalRoughSum B old fresh N cap w z L
        (leftMellin delta U t₁ label log₁) (rightMellin delta V t₂ label log₂)
        U V Z Mset alpha -
      historicalPolynomialSum B old fresh N cap w z L
        (leftMellin delta U t₁ label log₁) (rightMellin delta V t₂ label log₂)
        U V Z j false false Mset alpha‖ ≤
      2*p2Price E J*Y^2*μ*momentBudget D +
      2*μ*meanPrice delta U*meanPrice delta V*reciprocalMoment D*
        (2*U*V*ε*densityLog x + 2*densityLog x*(U+V)*Y + 2*Y^2) := by
  let Q := historicalModuli B old fresh N cap w z
  let c := historicalRho old fresh N cap w z L
  let F := leftMellin delta U t₁ label log₁
  let G := rightMellin delta V t₂ label log₂
  let E := envelopeSchwartz hd hs U
  let J := envelopeSchwartz hd hs V
  let μ := ∑ short ∈ Mset, ‖alpha short‖
  let Y := Z^(2*j+1)
  let absAlpha := fun short => (‖alpha short‖ : ℂ)
  have hsE : Function.support (E : ℝ → ℂ) ⊆ Icc (1/2 : ℝ) (5/2) := by
    intro a ha
    exact envelope_support hd hs U
      (by simpa only [E, envelopeSchwartz_apply, Complex.ofReal_eq_zero] using ha)
  have hsJ : Function.support (J : ℝ → ℂ) ⊆ Icc (1/2 : ℝ) (5/2) := by
    intro a ha
    exact envelope_support hd hs V
      (by simpa only [J, envelopeSchwartz_apply, Complex.ofReal_eq_zero] using ha)
  have hB := historical_polynomial_norm_sum B old fresh N cap D w z L hlevel
    E J hsE hsJ hU hV hZ j true false Mset absAlpha
  have hC := historical_polynomial_norm_sum B old fresh N cap D w z L hlevel
    E J hsE hsJ hU hV hZ j false true Mset absAlpha
  have hmass : (∑ short ∈ Mset, ‖absAlpha short‖) = μ := by
    simp only [absAlpha, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), μ]
  rw [hmass] at hB hC
  have hmean := historical_twice_mean_sum B old fresh N cap D w z L hlevel
    hZ hd hs hU hV hx j he1 hy Mset alpha
  have hpoint (q short : ℕ) :
      ‖roughDelta F G U V Z short N q (alpha short) -
        polyDelta F G U V Z j false false short N q (alpha short)‖ ≤
      ‖polyDelta E J U V Z j true false short N q (absAlpha short)‖ +
      ‖polyDelta E J U V Z j false true short N q (absAlpha short)‖ +
        2*‖alpha short‖*gapPairMean E J U V Z j q short := by
    have hp := actual_pair_E3 (decide (label = 1)) log₁ (decide (label = 2)) log₂
      hd hs U V t₁ t₂ Z j short N q (alpha short)
    have hp' := hp.trans (add_le_add_right (norm_add_le _ _) _)
    simpa only [F, G, leftMellin, rightMellin, E, J,
      envelopeSchwartz_coe, absAlpha] using hp'
  have hdiff :
      historicalRoughSum B old fresh N cap w z L F G U V Z Mset alpha -
        historicalPolynomialSum B old fresh N cap w z L F G U V Z j false false Mset alpha =
      ∑ q ∈ Q, c q * ∑ short ∈ Mset,
        (roughDelta F G U V Z short N q (alpha short) -
          polyDelta F G U V Z j false false short N q (alpha short)) := by
    simp only [historicalRoughSum, historicalPolynomialSum, Q, c,
      ← Finset.sum_sub_distrib, ← mul_sub]
  have hsum :
      ‖historicalRoughSum B old fresh N cap w z L F G U V Z Mset alpha -
        historicalPolynomialSum B old fresh N cap w z L F G U V Z j false false Mset alpha‖ ≤
      (∑ q ∈ Q, ‖c q‖ * ∑ short ∈ Mset,
        ‖polyDelta E J U V Z j true false short N q (absAlpha short)‖) +
      (∑ q ∈ Q, ‖c q‖ * ∑ short ∈ Mset,
        ‖polyDelta E J U V Z j false true short N q (absAlpha short)‖) +
      (∑ q ∈ Q, ‖c q‖ * ∑ short ∈ Mset,
        2*‖alpha short‖*gapPairMean E J U V Z j q short) := by
    rw [hdiff]
    calc
      _ ≤ ∑ q ∈ Q, ‖c q‖ * ∑ short ∈ Mset,
          ‖roughDelta F G U V Z short N q (alpha short) -
            polyDelta F G U V Z j false false short N q (alpha short)‖ := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro q hq
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
      _ ≤ ∑ q ∈ Q, ‖c q‖ * ∑ short ∈ Mset,
          (‖polyDelta E J U V Z j true false short N q (absAlpha short)‖ +
            ‖polyDelta E J U V Z j false true short N q (absAlpha short)‖ +
              2*‖alpha short‖*gapPairMean E J U V Z j q short) :=
        Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun short _ => hpoint q short)) (norm_nonneg _))
      _ = _ := by simp only [Finset.sum_add_distrib, mul_add]
  exact hsum.trans ((add_le_add (add_le_add hB hC) hmean).trans_eq
    (by dsimp only [E, J, μ, Y]; ring))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact finite reindexing and the preserved Brun expansion attach the
upper polynomial to the already-owned historical row core. -/
theorem historicalPolynomialSum_eq_rowCore (B : ℝ) (old fresh : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) {Z delta U V : ℝ}
    (hZ : 1 ≤ Z) (hd : 0 < delta) (hs : delta ≤ 1/4) (hU : 0 < U) (hV : 0 < V)
    (j : ℕ) (b₁ b₂ : Bool) (t₁ t₂ : ℝ) (label : Fin 3) (log₁ log₂ : Bool)
    (bs : ι → Block) (y xi : ι → ℝ) (rs : ι → Role) :
    historicalPolynomialSum B old fresh N cap w z L
      (leftMellin delta U t₁ label log₁) (rightMellin delta V t₂ label log₂)
      U V Z j b₁ b₂ (shortSupport bs) (shortSequence bs Z y xi rs) =
    historicalRowCore B old fresh N cap w z L Z j b₁ b₂ delta U V t₁ t₂
      label log₁ log₂ bs y xi rs := by
  calc
    _ = ∑ short ∈ shortSupport bs, ∑ q ∈ historicalModuli B old fresh N cap w z,
        historicalRho old fresh N cap w z L q *
          polyDelta (leftMellin delta U t₁ label log₁) (rightMellin delta V t₂ label log₂)
            U V Z j b₁ b₂ short N q (shortSequence bs Z y xi rs short) := by
      simp only [historicalPolynomialSum, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      unfold historicalRowCore historicalBrunCore
      apply Finset.sum_congr rfl
      intro short hshort
      apply Finset.sum_congr rfl
      intro q hq
      congr 1
      change smoothBrunTupleCore Z j b₁ b₂ delta U V t₁ t₂ label log₁ log₂
        (shortSequence bs Z y xi rs short) short N q = _
      exact smoothBrunTupleCore_eq_expansion hZ hd hs hU hV j b₁ b₂ t₁ t₂
        label log₁ log₂ _ short N q

/-- Actual signed ordered HB pushforward. Its mass is derived from
shortSequence_mass under the original cap; it is not an extra mass premise. -/
theorem historical_shortSequence_rough_comparison (B : ℝ) (old fresh : List ℕ → Bool)
    (N cap D : ℕ) (w z L : ℝ)
    (hlevel : ∀ q ∈ historicalModuli B old fresh N cap w z, q ≤ D)
    {Z delta U V x : ℝ} (hZ : 1 ≤ Z) (hd : 0 < delta) (hs : delta ≤ 1/4)
    (hU : 0 < U) (hV : 0 < V) (hx : 1 ≤ x) (j : ℕ)
    (he1 : brunEpsilon j (smallPrimes Z) ≤ 1) (hy : Z^(2*j+1) ≤ x)
    (t₁ t₂ : ℝ) (label : Fin 3) (log₁ log₂ : Bool) {X : ℝ} (hX : 1 ≤ X)
    (bs : ι → Block) (y xi : ι → ℝ) (rs : ι → Role)
    (hcap : ∀ i, 2 * (lower (bs i) : ℝ) ≤ X) :
    let E := envelopeSchwartz hd hs U
    let J := envelopeSchwartz hd hs V
    let μ₀ := (shortScale bs : ℝ) * (1 + Real.log X)^Fintype.card ι
    let Y := Z^(2*j+1)
    let ε := brunEpsilon j (smallPrimes Z)
    ‖historicalRoughSum B old fresh N cap w z L
        (leftMellin delta U t₁ label log₁) (rightMellin delta V t₂ label log₂)
        U V Z (shortSupport bs) (shortSequence bs Z y xi rs) -
      historicalRowCore B old fresh N cap w z L Z j false false delta U V t₁ t₂
        label log₁ log₂ bs y xi rs‖ ≤
      2*p2Price E J*Y^2*μ₀*momentBudget D +
      2*μ₀*meanPrice delta U*meanPrice delta V*reciprocalMoment D*
        (2*U*V*ε*densityLog x + 2*densityLog x*(U+V)*Y + 2*Y^2) := by
  let E := envelopeSchwartz hd hs U
  let J := envelopeSchwartz hd hs V
  let Y := Z^(2*j+1)
  let ε := brunEpsilon j (smallPrimes Z)
  let μ₀ := (shortScale bs : ℝ) * (1 + Real.log X)^Fintype.card ι
  let K := 2*p2Price E J*Y^2*momentBudget D +
    2*meanPrice delta U*meanPrice delta V*reciprocalMoment D*
      (2*U*V*ε*densityLog x + 2*densityLog x*(U+V)*Y + 2*Y^2)
  have hP := p2Price_nonneg E J
  have hPU := meanPrice_nonneg delta U
  have hPV := meanPrice_nonneg delta V
  have hR := reciprocalMoment_nonneg D
  have hM := momentBudget_nonneg D
  have hY : 0 ≤ Y := pow_nonneg (zero_le_one.trans hZ) _
  have he : 0 ≤ ε := (norm_nonneg _).trans (gap_density_B2 Z j 1 1)
  have hlog : 0 ≤ densityLog x := zero_le_one.trans (densityLog_one_le hx)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hm := shortSequence_mass bs Z y xi rs hX hcap
  have hf := finite_rough_comparison B old fresh N cap D w z L hlevel
    hZ hd hs hU hV hx j he1 hy t₁ t₂ label log₁ log₂
      (shortSupport bs) (shortSequence bs Z y xi rs)
  dsimp only at hf
  rw [historicalPolynomialSum_eq_rowCore B old fresh N cap w z L hZ hd hs hU hV
    j false false t₁ t₂ label log₁ log₂ bs y xi rs] at hf
  calc
    _ ≤ K * ∑ short ∈ shortSupport bs, ‖shortSequence bs Z y xi rs short‖ :=
      hf.trans_eq (by dsimp only [K, E, J, Y, ε]; ring)
    _ ≤ K * μ₀ := mul_le_mul_of_nonneg_left hm hK
    _ = _ := by dsimp only [K, E, J, μ₀, Y, ε]; ring

end
end ImbalancedChen.P1OriginalHistoricalTwoLongRoughComparison
