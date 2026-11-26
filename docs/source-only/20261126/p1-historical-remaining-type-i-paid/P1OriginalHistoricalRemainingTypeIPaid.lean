import ImbalancedChen.P1OriginalSingletonRemainingRectangles
import ImbalancedChen.P1OriginalSingletonRetainedFourierInvoice
import ImbalancedChen.P1OriginalSingletonOneLongConsumer
import ImbalancedChen.P4BOriginalSharpEndpointPrices

/-!
SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE.

The original remaining-Type-I singleton atlas, with its actual historical
Q/rho and physical N, consumes the proved finite selector/witness and the
normalized Fourier invoice. Dead selected atoms are removed before a
source tuple or Fourier representation is requested.

The old chart/block/HB-scalar bounds supply exactly 9*graphHeight^7.
The existing physical rectangle scale supplies X0<=2*N and
N<=X0^(1+kappa). For kappa<=1 these give log N<=2*log X0.
The local accuracy A+80 and tail accuracy A+5 therefore give one common
row bill (CB*2^(A+153)+CT)*N/log(N)^(A+8). The original log^72 L1 loss
and seven inventory logarithms are accounted for explicitly.

The final constant is paid by the existing GENERIC eventually_inverse_log
with E=7 and B=A+8. No P4 long-variable threshold or A+40 terminal is used.
The public asymptotic conclusion has only original parameter conditions;
it assumes no row estimate, mass, error, derivative or payment bound.
This closes only the historical remainingTypeIAtlas summand. The medium
summand and the pre-existing source-owner/kernel-acceptance boundaries
remain separate.
-/

namespace ImbalancedChen.P1OriginalHistoricalRemainingTypeIPaid
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block)
open P5Z.ActualHBDyadicOccurrenceFamily (blockWords)
open P5Z.PerGroupIntegerHBAtlasPushforward (Row hbCap)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank cutoffIndex)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P5Z.OrderedFactorTupleRectangleReindex (blockVector)
open Part3.OriginalProperPowerActualChart (wordVector)
open P5Z.ActualLowerNormalizedAtlasOccurrence (scalarProfile)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open P5Z.CompleteProductTailDivisorBudgets (logScale)
open P5Z.ActualLowerNormalizedPostModulusTail (countingScale)
open Part3.TwoLongActualHBShortMass (shortScale)
open P5CanonicalTentNarrowSingletonTransfer (actualLicence)
open P1OriginalHistoricalTwoLongP2 (historicalModuli historicalRho)
open P1OriginalSingletonOneLongRectangle (remainingTypeIAtlas occurrenceAtom)
open P1OriginalSingletonRemainingRectangles
  (Remaining occurrenceChart original_remaining_to_actual_rectangles
    nonzero_selected_occurrence_has_source_tuple)
open P1OriginalSingletonRetainedFourierInvoice (exists_actual_remaining_fourier_invoice)
open P1OriginalSingletonLogNormalization (eventually_actual_tuple_normalized_profile)
open P1OriginalSingletonFixedRectangleScale (eventually_actual_singleton_fixed_rectangle_level)
open P1OriginalSingletonOneLongProfile (profileHeight)
open P1OriginalSingletonOneLongConsumer
  (graphHeight graphHeight_nonneg graphConstant graphConstant_one_le
    heightConstant heightConstant_one_le graphHeight_le_profileHeight
    eventually_height_le_log chart_block_cardinality chart_count original_HB_scalar_bound)
open P4BOriginalSharpEndpointPrices (eventually_inverse_log)

/-- The original physical source, with precisely its original signed
historical modulus coefficient inside both count and exact mean. -/
def sourceChannel (kap : ℝ) (N K : ℕ) (kap0 zeta levelB : ℝ)
    (old fresh : List ℕ → Bool) (cap : ℕ) (w z L : ℝ) : ℂ :=
  ∑ js ∈ chartBank (2*N) 1,
    remainingTypeIAtlas (actualLicence kap 6 N) K (2*N) N kap0
      (originalMediumLow zeta js) (originalMediumHigh zeta js)
      (historicalModuli levelB old fresh N cap w z)
      (historicalRho old fresh N cap w z L) js

def rowConstant (A : ℕ) (CB CT : ℝ) : ℝ := CB*2^(A+153)+CT

def rowBudget (A : ℕ) (CB CT : ℝ) (N : ℕ) : ℝ :=
  rowConstant A CB CT*(N : ℝ)/(Real.log (N : ℝ))^(A+8)

private theorem rowConstant_nonneg (A : ℕ) {CB CT : ℝ}
    (hCB : 0 ≤ CB) (hCT : 0 ≤ CT) : 0 ≤ rowConstant A CB CT := by
  unfold rowConstant
  positivity

private theorem rowBudget_nonneg (A : ℕ) {CB CT : ℝ} (N : ℕ)
    (hCB : 0 ≤ CB) (hCT : 0 ≤ CT) (hlog : 0 ≤ Real.log (N : ℝ)) :
    0 ≤ rowBudget A CB CT N :=
  div_nonneg (mul_nonneg (rowConstant_nonneg A hCB hCT) (Nat.cast_nonneg N))
    (pow_nonneg hlog _)

/-- Only numerical scale conversion: the genuine L1 price retains no
frequency-cube volume. The harmless factor 2^(-r)<=1 is dropped here. -/
private theorem retained_price_le_physical (A r N : ℕ) (hN : 2 ≤ N)
    {C x kappa : ℝ} (hC : 0 ≤ C) (hx : 1 < x)
    (hxN : x ≤ 2*(N : ℝ)) (hNx : (N : ℝ) ≤ x^(1+kappa)) (hk : kappa ≤ 1) :
    (C*Real.log ((N : ℝ)+2)^72/2^r)*(x/(Real.log x)^(A+80)) ≤
      (C*2^(A+153))*(N : ℝ)/(Real.log (N : ℝ))^(A+8) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hLN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hlogplus0 : 0 ≤ Real.log ((N : ℝ)+2) := Real.log_nonneg (by linarith)
  have hlogplus : Real.log ((N : ℝ)+2) ≤ 2*Real.log (N : ℝ) := by
    have h := Real.log_le_log (by linarith : (0 : ℝ) < (N : ℝ)+2)
      (by nlinarith [sq_nonneg ((N : ℝ)-2)] : (N : ℝ)+2 ≤ (N : ℝ)^2)
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hlocal : Real.log (N : ℝ) ≤ 2*Real.log x := by
    have h := Real.log_le_log hNp hNx
    rw [Real.log_rpow (zero_lt_one.trans hx)] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hlx.le)
  have hden : (Real.log (N : ℝ))^(A+80) ≤
      (2 : ℝ)^(A+80)*(Real.log x)^(A+80) := by
    simpa only [mul_pow] using pow_le_pow_left₀ hLN.le hlocal (A+80)
  have hratio : x/(Real.log x)^(A+80) ≤
      (2 : ℝ)^(A+81)*(N : ℝ)/(Real.log (N : ℝ))^(A+80) := by
    apply (div_le_div_iff₀ (pow_pos hlx _) (pow_pos hLN _)).mpr
    calc
      _ ≤ (2*(N : ℝ))*((2 : ℝ)^(A+80)*(Real.log x)^(A+80)) :=
        mul_le_mul hxN hden (pow_nonneg hLN.le _) (by positivity)
      _ = _ := by
        rw [show A+81 = (A+80)+1 by omega, pow_succ]
        ring
  have hcoeff : C*Real.log ((N : ℝ)+2)^72/2^r ≤
      C*(2*Real.log (N : ℝ))^72 := by
    apply (div_le_self (mul_nonneg hC (pow_nonneg hlogplus0 _))
      (show (1 : ℝ) ≤ 2^r from one_le_pow₀ (by norm_num))).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogplus0 hlogplus 72) hC
  have htwo : (2 : ℝ)^72*2^(A+81) = 2^(A+153) := by
    simpa only [show 72+(A+81) = A+153 by omega] using
      (pow_add (2 : ℝ) 72 (A+81)).symm
  have hsplit : (Real.log (N : ℝ))^(A+80) =
      (Real.log (N : ℝ))^(A+8)*(Real.log (N : ℝ))^72 := by
    simpa only [show (A+8)+72 = A+80 by omega] using
      (pow_add (Real.log (N : ℝ)) (A+8) 72)
  calc
    _ ≤ (C*(2*Real.log (N : ℝ))^72)*
        ((2 : ℝ)^(A+81)*(N : ℝ)/(Real.log (N : ℝ))^(A+80)) :=
      mul_le_mul hcoeff hratio (by positivity) (by positivity)
    _ = (C*((2 : ℝ)^72*2^(A+81)))*(N : ℝ)*
        ((Real.log (N : ℝ))^72/(Real.log (N : ℝ))^(A+80)) := by
      rw [mul_pow]
      ring
    _ = _ := by
      rw [htwo, hsplit]
      field_simp [hLN.ne'] <;> ring

private theorem omitted_price_le_physical (A N : ℕ) (hN : 2 ≤ N)
    {C : ℝ} (hC : 0 ≤ C) :
    C*(N : ℝ)/logScale (countingScale N)^((A+5)+3) ≤
      C*(N : ℝ)/(Real.log (N : ℝ))^(A+8) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hLN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hlog : Real.log (N : ℝ) ≤ logScale (countingScale N) := by
    have h := Real.log_le_log hNp
      (by nlinarith : (N : ℝ) ≤ 7*(128*(N : ℝ)))
    dsimp [logScale, countingScale]
    linarith
  rw [show (A+5)+3 = A+8 by omega]
  exact div_le_div_of_nonneg_left (mul_nonneg hC hNp.le) (pow_pos hLN _)
    (pow_le_pow_left₀ hLN.le hlog _)

/-- Common physical-N row budget after actually checking both exponent
choices. Its premises are scalar scale inequalities, not analytic bounds. -/
private theorem invoice_price_le_rowBudget (A r N : ℕ) (hN : 2 ≤ N)
    {CB CT x kappa : ℝ} (hCB : 0 ≤ CB) (hCT : 0 ≤ CT) (hx : 1 < x)
    (hxN : x ≤ 2*(N : ℝ)) (hNx : (N : ℝ) ≤ x^(1+kappa)) (hk : kappa ≤ 1) :
    (CB*Real.log ((N : ℝ)+2)^72/2^r)*(x/(Real.log x)^(A+80)) +
      CT*(N : ℝ)/logScale (countingScale N)^((A+5)+3) ≤ rowBudget A CB CT N := by
  calc
    _ ≤ (CB*2^(A+153))*(N : ℝ)/(Real.log (N : ℝ))^(A+8) +
        CT*(N : ℝ)/(Real.log (N : ℝ))^(A+8) :=
      add_le_add (retained_price_le_physical A r N hN hCB hx hxN hNx hk)
        (omitted_price_le_physical A N hN hCT)
    _ = _ := by unfold rowBudget rowConstant; ring

/-- Fully supplied finite outer invoice. Its constants precede all
accuracies, physical parameters, charts, tuples and historical policies.
No individual row estimate or mass budget is an input. -/
theorem exists_historical_remaining_finite_invoice :
    ∃ CB CT : ℝ, 0 ≤ CB ∧ 0 ≤ CT ∧
      ∀ (A K : ℕ) {kappa kap0 zeta : ℝ},
      0 < kappa → kappa ≤ zeta/10000 → zeta ≤ 1/20000 →
      kap0 < kappa/(4*(1+kappa)) →
      ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ), kap < 1 →
      ∀ (levelB : ℝ) (old fresh : List ℕ → Bool) (cap : ℕ) (w z L : ℝ),
      ‖sourceChannel kap N K kap0 zeta levelB old fresh cap w z L‖ ≤
        9*graphHeight N^7*rowBudget A CB CT N := by
  obtain ⟨CB, CT, hCB, hCT, hfourier⟩ := exists_actual_remaining_fourier_invoice
  refine ⟨CB, CT, hCB, hCT, ?_⟩
  intro A K kappa kap0 zeta hkappa hsmall hzeta htrim
  have hk1 : kappa ≤ 1 := by linarith
  have hzeta0 : 0 < zeta := by linarith only [hkappa, hsmall]
  have h400 : zeta ≤ 1/400 := hzeta.trans (by norm_num)
  have hkap0 : kap0 < 1 := by
    have h := manuscript_kappaZero_lt_quarter hkappa htrim
    linarith
  filter_upwards [hfourier (A+80) (A+5) K hkappa hsmall hzeta htrim,
    eventually_actual_tuple_normalized_profile hkap0 hzeta0 hzeta,
    eventually_actual_singleton_fixed_rectangle_level hkappa hsmall h400 htrim,
    eventually_ge_atTop (2 : ℕ)] with N hpaid hnorm hrectangle hN
  intro kap hkap levelB old fresh cap w z L
  let Q := historicalModuli levelB old fresh N cap w z
  let rho := historicalRho old fresh N cap w z L
  let Rb := rowBudget A CB CT N
  have hNp : 0 < N := by omega
  have hLN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hRb : 0 ≤ Rb := rowBudget_nonneg A N hCB hCT hLN.le
  have hG : 0 ≤ graphHeight N := graphHeight_nonneg N
  have hrow (cj j : ℕ) (hj : j ∈ Finset.range 3) (bs : List Block)
      (hbs : bs ∈ blockWords (hbCap cj) (2*(j+1))) :
      ‖if Remaining (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj]) bs then
        occurrenceAtom kap 6 N cj K kap0 j bs Q rho else 0‖ ≤ Rb := by
    by_cases hgate : Remaining (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj]) bs
    · simp only [if_pos hgate]
      by_cases hz : occurrenceAtom kap 6 N cj K kap0 j bs Q rho = 0
      · simpa only [hz, norm_zero] using hRb
      · obtain ⟨fs, _, hfs, hchart, hassigned, hremaining⟩ :=
          nonzero_selected_occurrence_has_source_tuple kap hkap 6 N cj K kap0
            (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj]) j bs
            hbs Q rho hgate hz
        let row : Row := {order := j, blocks := bs, factors := fs}
        let bv := blockVector (2*(j+1)) bs
        let ns := wordVector (2*(j+1)) fs
        let X0 : ℝ := shortScale bv
        have hi := hpaid kap hkap cj row levelB old fresh cap w z L
          hchart hj hfs hassigned hremaining
        have hatom := hi.2.2
        change ‖occurrenceAtom kap 6 N cj K kap0 j bs Q rho‖ ≤
          (CB*Real.log ((N : ℝ)+2)^72/2^(2*(j+1)))*(X0/(Real.log X0)^(A+80)) +
            CT*(N : ℝ)/logScale (countingScale N)^((A+5)+3) at hatom
        obtain ⟨hrect, _, _, hprofile, _, _, _⟩ :=
          hnorm kap hkap 6 K cj j fs.prod bs fs Q rho hchart hfs hassigned
        have hscalar : scalarProfile kap 6 N cj kap0 (completeProduct ns) ≠ 0 := by
          simpa only [P5Z.ActualLowerNormalizedAtlasOccurrence.integerProfile] using hprofile
        -- The complete-scale bounds do not depend on which two distinct
        -- occurrence indices are supplied to the existing fibre theorem.
        let i : Fin (2*(j+1)) := ⟨0, by omega⟩
        let k : Fin (2*(j+1)) := ⟨1, by omega⟩
        have hik : i ≠ k := by
          intro heq
          have hval := congrArg Fin.val heq
          norm_num [i, k] at hval
        obtain ⟨_, _, _, _, hxN, hx, _, hNx, _, _, _⟩ :=
          hrectangle kap hkap 6 cj j bv ns i k hj hik hrect hscalar
        exact hatom.trans (invoice_price_le_rowBudget A (2*(j+1)) N hN
          hCB hCT hx hxN hNx hk1)
    · simpa only [if_neg hgate, norm_zero] using hRb
  have hchart (cj : ℕ) (hcj : cj ∈ Finset.range (cutoffIndex (2*N)+1)) :
      ‖occurrenceChart kap 6 N cj K kap0 (originalMediumLow zeta [cj])
        (originalMediumHigh zeta [cj]) Q rho‖ ≤ 9*graphHeight N^6*Rb := by
    unfold occurrenceChart
    apply (norm_sum_le _ _).trans
    have hterm (j : ℕ) (hj : j ∈ Finset.range 3) :
        ‖P5Z.SmoothChartHBDyadicPartition.scalar j *
          ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
            if Remaining (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj]) bs then
              occurrenceAtom kap 6 N cj K kap0 j bs Q rho else 0‖ ≤
          3*graphHeight N^6*Rb := by
      have hj3 := Finset.mem_range.mp hj
      have hins :
          ‖∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
            if Remaining (originalMediumLow zeta [cj]) (originalMediumHigh zeta [cj]) bs then
              occurrenceAtom kap 6 N cj K kap0 j bs Q rho else 0‖ ≤ graphHeight N^6*Rb := by
        apply (norm_sum_le _ _).trans
        apply (Finset.sum_le_sum (hrow cj j hj)).trans
        simpa only [Finset.sum_const, nsmul_eq_mul] using
          mul_le_mul_of_nonneg_right (chart_block_cardinality N cj j hNp hcj hj3) hRb
      rw [norm_mul]
      have h := mul_le_mul (original_HB_scalar_bound j hj3) hins
        (norm_nonneg _) (by norm_num)
      simpa only [mul_assoc] using h
    calc
      _ ≤ ∑ _j ∈ Finset.range 3, 3*graphHeight N^6*Rb := Finset.sum_le_sum hterm
      _ = 9*graphHeight N^6*Rb := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
  change ‖∑ js ∈ chartBank (2*N) 1,
    remainingTypeIAtlas (actualLicence kap 6 N) K (2*N) N kap0
      (originalMediumLow zeta js) (originalMediumHigh zeta js) Q rho js‖ ≤ _
  rw [original_remaining_to_actual_rectangles kap hkap 6 N K kap0 zeta Q rho]
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hchart).trans
  calc
    _ = ((Finset.range (cutoffIndex (2*N)+1)).card : ℝ)*(9*graphHeight N^6*Rb) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ graphHeight N*(9*graphHeight N^6*Rb) :=
      mul_le_mul_of_nonneg_right (chart_count N hNp) (by positivity)
    _ = _ := by dsimp only [Rb]; ring

/-- The seven outer logarithms and the entire fixed row constant are
paid by the old generic inverse-log theorem. This has no analytic input. -/
theorem eventually_outer_log_payment (A : ℕ) (CB CT : ℝ)
    (hCB : 0 ≤ CB) (hCT : 0 ≤ CT) :
    ∀ᶠ N : ℕ in atTop, 9*graphHeight N^7*rowBudget A CB CT N ≤
      (N : ℝ)/(Real.log (N : ℝ))^A := by
  let G := graphConstant*heightConstant
  let C := 9*G^7*rowConstant A CB CT
  have hGC : 0 ≤ graphConstant := zero_le_one.trans graphConstant_one_le
  have hHC : 0 ≤ heightConstant := zero_le_one.trans heightConstant_one_le
  have hRC := rowConstant_nonneg A hCB hCT
  have hC : 0 ≤ C := by dsimp only [C, G]; positivity
  have hpay := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_inverse_log C hC 7 A (A+8) (by omega))
  filter_upwards [hpay, eventually_height_le_log, eventually_one_le_nat_log,
    eventually_ge_atTop (1 : ℕ)] with N hpaid hheight hlog hN
  have hNp : 0 < N := by omega
  have hG : 0 ≤ graphHeight N := graphHeight_nonneg N
  have hRb : 0 ≤ rowBudget A CB CT N :=
    rowBudget_nonneg A N hCB hCT (zero_le_one.trans hlog)
  have hheight' : graphHeight N ≤ G*Real.log (N : ℝ) := by
    calc
      _ ≤ graphConstant*profileHeight N := graphHeight_le_profileHeight N hNp
      _ ≤ graphConstant*(heightConstant*Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hheight hGC
      _ = _ := by dsimp only [G]; ring
  calc
    _ ≤ 9*(G*Real.log (N : ℝ))^7*rowBudget A CB CT N :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hG hheight' 7) (by norm_num)) hRb
    _ = (N : ℝ)*(C*(Real.log (N : ℝ))^7*((Real.log (N : ℝ))^(A+8))⁻¹) := by
      dsimp only [rowBudget, C]
      rw [mul_pow, div_eq_mul_inv]
      ring
    _ ≤ (N : ℝ)*(1/(Real.log (N : ℝ))^A) :=
      mul_le_mul_of_nonneg_left hpaid (Nat.cast_nonneg N)
    _ = _ := by ring

/-- The actual historical remainingTypeIAtlas sum is paid at physical N.
The common threshold precedes kap and every historical coefficient policy.
Only the original fixed parameter conditions appear as hypotheses. -/
theorem eventually_historical_remainingTypeI_paid (A K : ℕ)
    {kappa kap0 zeta : ℝ} (hkappa : 0 < kappa)
    (hsmall : kappa ≤ zeta/10000) (hzeta : zeta ≤ 1/20000)
    (htrim : kap0 < kappa/(4*(1+kappa))) :
    ∀ᶠ N : ℕ in atTop, ∀ (kap : ℝ), kap < 1 →
      ∀ (levelB : ℝ) (old fresh : List ℕ → Bool) (cap : ℕ) (w z L : ℝ),
      ‖sourceChannel kap N K kap0 zeta levelB old fresh cap w z L‖ ≤
        (N : ℝ)/(Real.log (N : ℝ))^A := by
  obtain ⟨CB, CT, hCB, hCT, hfinite⟩ := exists_historical_remaining_finite_invoice
  filter_upwards [hfinite A K hkappa hsmall hzeta htrim,
    eventually_outer_log_payment A CB CT hCB hCT] with N hsource hpay
  intro kap hkap levelB old fresh cap w z L
  exact (hsource kap hkap levelB old fresh cap w z L).trans hpay

theorem historical_remainingTypeI_paid (A K : ℕ)
    {kappa kap0 zeta : ℝ} (hkappa : 0 < kappa)
    (hsmall : kappa ≤ zeta/10000) (hzeta : zeta ≤ 1/20000)
    (htrim : kap0 < kappa/(4*(1+kappa))) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      ∀ (kap : ℝ), kap < 1 →
      ∀ (levelB : ℝ) (old fresh : List ℕ → Bool) (cap : ℕ) (w z L : ℝ),
      ‖sourceChannel kap N K kap0 zeta levelB old fresh cap w z L‖ ≤
        (N : ℝ)/(Real.log (N : ℝ))^A := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((eventually_historical_remainingTypeI_paid A K hkappa hsmall hzeta htrim).and
      (eventually_ge_atTop (2 : ℕ)))
  refine ⟨max 2 T, le_max_left _ _, ?_⟩
  intro N hN
  exact (hT N ((le_max_right _ _).trans hN)).1

end
end ImbalancedChen.P1OriginalHistoricalRemainingTypeIPaid
