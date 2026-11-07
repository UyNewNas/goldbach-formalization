import ImbalancedChen.Part5OriginalClassicalTailFullError
import ImbalancedChen.P2MarkedThetaLiNormalization
import MathlibNt.Wu2008DoubleSieve.LocalProductReal
import MathlibNt.Wu2008DoubleSieve.PhiBounded

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original classical U3 tail has a complete below-half modulus, but its
selected outer prime need not satisfy p^2<=Q. Normalize its actual initial
Rosser main terms directly with the native uniform real-cutoff Mertens
theorem. The actual cutoff floor N^(1/24) and p*N<=N^2 supply the polynomial
envelope; a Wu boxSquaredPrefixes hypothesis is neither used nor invented.

The final theorem supplies the ordinary two-sided tail count at the original
same-Q true-li parent Theta, including the physical clamp. It is not an adopted seed,
old analytic H/h licence, H430 table theorem, or the causal hstarts supplier.
-/

namespace ImbalancedChen.Part5OriginalClassicalTailThetaSeed

noncomputable section
open Set Finset Filter Topology Wu2008DoubleSieve
open scoped Classical BigOperators
open Part5UpperTables.OriginalU34 Part5UpperTables.OriginalU34.CountEntrance
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5OriginalH430ClassicalTailBV Part5OriginalClassicalTailFullError
open P2EnhancedTwentyOneSameQWeighted (Theta cutoff)
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- The actual per-parent contribution, including its singular series,
totient, physical residual, and installed literal-li convention. -/
def parentTheta (N p : ℕ) (tau : ℝ) : ℝ :=
  4 * logarithmicIntegral N * wuSingularSeries (p*N) /
    ((Nat.totient p : ℝ) * Real.log (rowTotalLevel N p (U3Residual tau) / (p : ℝ)))

def tailTheta (N : ℕ) (tau : ℝ) : ℝ :=
  Theta N ((N : ℝ)^(1/2-tau)) (tailPrimes N) (fun _ => 1)

/-- One common Q, and all original outer-prime labels, exactly. -/
theorem tailTheta_eq_sum_parentTheta (N : ℕ) (tau : ℝ) :
    tailTheta N tau = ∑ p ∈ tailPrimes N, parentTheta N p tau := by
  unfold tailTheta Theta
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  have ht := (mem_filter.mp hp).2
  unfold parentTheta
  rw [tail_row_Q ht]
  ring

/-- The actual U3 cutoff has a fixed lower power before tau or p is
chosen. This derives the Mertens envelope on the physical root. -/
theorem original_row_cutoff_envelope {N p : ℕ} {tau : ℝ}
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hp : p ∈ originalU3Primes N) :
    (N : ℝ)^(1/24 : ℝ) ≤ rowCutoff N p (U3Residual tau) ∧
      ((p*N : ℕ) : ℝ) ≤ (rowCutoff N p (U3Residual tau))^(48 : ℝ) := by
  have hpc := primeCoordinate_mem hN hp
  have hr := U3Residual_bounds htau htauhi ⟨hpc.1, hpc.2.le⟩
  have hphys := U3_physicalExponent_bounds htau htauhi ⟨hpc.1, hpc.2.le⟩
  have hpp : 0 < p := by
    have h := (chenSinglePrimeSelector_sieve_data hp).1
    omega
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcut : (N : ℝ)^(1/24 : ℝ) ≤ rowCutoff N p (U3Residual tau) := by
    rw [rowCutoff_eq_physical hN hpp (lt_of_lt_of_le (by norm_num) hr.1)]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hphys.1
  have hpN : (p : ℝ) ≤ N := by
    have hpu : (p : ℝ) < (N : ℝ)^(1/3 : ℝ) := (mem_filter.mp hp).2.2
    refine hpu.le.trans ?_
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num : (1/3 : ℝ) ≤ 1)
  refine ⟨hcut, ?_⟩
  calc
    ((p*N : ℕ) : ℝ) ≤ (N : ℝ)^(2 : ℝ) := by
      rw [Nat.cast_mul, Real.rpow_two, pow_two]
      exact mul_le_mul_of_nonneg_right hpN hNpos.le
    _ = ((N : ℝ)^(1/24 : ℝ))^(48 : ℝ) := by
      rw [← Real.rpow_mul hNpos.le]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hcut (by norm_num)

/-- Uniform normalization of the original moving rows. The theorem used
is for all even integers in a polynomial cutoff envelope; the actual
envelope is proved above, rather than imposed as a source licence. -/
theorem eventually_original_row_product_relative {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1/12 →
      ∀ p ∈ originalU3Primes N,
        |localSieveProduct (p*N) (rowCutoff N p (U3Residual tau)) /
          (2 * rootArgument (U3Residual tau) (primeCoordinate N p) * wuSingularSeries (p*N) /
            (Real.exp Real.eulerMascheroniConstant *
              Real.log (rowTotalLevel N p (U3Residual tau) / (p : ℝ)))) - 1| ≤ eta := by
  obtain ⟨Z, hZ⟩ := eventually_atTop.mp
    (eventually_localSieveProduct_relative 48 eta (by norm_num) heta)
  have hlarge : ∀ᶠ N : ℕ in atTop, max Z 3 ≤ (N : ℝ)^(1/24 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/24)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (max Z 3))
  filter_upwards [hlarge, eventually_ge_atTop (2 : ℕ)] with N hlargeN hN
  intro hEven tau htau htauhi p hp
  have hpp : 0 < p := by
    have h := (chenSinglePrimeSelector_sieve_data hp).1
    omega
  have hpc := primeCoordinate_mem hN hp
  have hr := U3Residual_bounds htau htauhi ⟨hpc.1, hpc.2.le⟩
  have hs := U3_rootArgument_mem htau htauhi ⟨hpc.1, hpc.2.le⟩
  have hR := row_residual_gt_one hN hpp (lt_of_lt_of_le (by norm_num) hr.1)
  have henv := original_row_cutoff_envelope hN htau htauhi hp
  have hz : Z ≤ rowCutoff N p (U3Residual tau) :=
    (le_max_left Z 3).trans (hlargeN.trans henv.1)
  have hrel := hZ (rowCutoff N p (U3Residual tau)) hz (p*N)
    (Nat.mul_pos hpp (by omega)) (hEven.mul_left p) henv.2
  have hsne : rootArgument (U3Residual tau) (primeCoordinate N p) ≠ 0 := by linarith [hs.1]
  have hlogR : Real.log (rowTotalLevel N p (U3Residual tau) / (p : ℝ)) ≠ 0 :=
    (Real.log_pos hR).ne'
  have hlogcut : Real.log (rowCutoff N p (U3Residual tau)) =
      (1 / rootArgument (U3Residual tau) (primeCoordinate N p)) *
        Real.log (rowTotalLevel N p (U3Residual tau) / (p : ℝ)) := by
    exact Real.log_rpow (by linarith : 0 < rowTotalLevel N p (U3Residual tau) / (p : ℝ)) _
  have hmain :
      2 * Real.exp (-Real.eulerMascheroniConstant) * wuSingularSeries (p*N) /
        Real.log (rowCutoff N p (U3Residual tau)) =
      2 * rootArgument (U3Residual tau) (primeCoordinate N p) * wuSingularSeries (p*N) /
        (Real.exp Real.eulerMascheroniConstant *
          Real.log (rowTotalLevel N p (U3Residual tau) / (p : ℝ))) := by
    rw [hlogcut, Real.exp_neg]
    field_simp [hsne, hlogR, (Real.exp_pos Real.eulerMascheroniConstant).ne']
    <;> ring
  rwa [hmain] at hrel

/-- Both signed Rosser main terms are normalized at the actual parent
Theta. The sign-safe lower budget is the existing native theorem. -/
theorem eventually_original_row_seed_Theta {eta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1/12 →
      ∀ p ∈ originalU3Primes N,
        (wuLowerCoefficient (rootArgument (U3Residual tau) (primeCoordinate N p)) - 15*eta) *
            parentTheta N p tau ≤
          rowSeed false N p (U3Residual tau) (Real.exp Real.eulerMascheroniConstant * eta / 2) ∧
        rowSeed true N p (U3Residual tau) (Real.exp Real.eulerMascheroniConstant * eta / 2) ≤
          (wuUpperCoefficient (rootArgument (U3Residual tau) (primeCoordinate N p)) + 15*eta) *
            parentTheta N p tau := by
  filter_upwards [eventually_original_row_product_relative heta, eventually_ge_atTop (2 : ℕ)]
    with N hlocal hN
  intro hEven tau htau htauhi p hp
  have hnorm := hlocal hEven tau htau htauhi p hp
  have hpp : 0 < p := by
    have h := (chenSinglePrimeSelector_sieve_data hp).1
    omega
  have hpc := primeCoordinate_mem hN hp
  have hr := U3Residual_bounds htau htauhi ⟨hpc.1, hpc.2.le⟩
  have hs := U3_rootArgument_mem htau htauhi ⟨hpc.1, hpc.2.le⟩
  have hs10 : rootArgument (U3Residual tau) (primeCoordinate N p) ≤ 10 := by linarith [hs.2]
  have hs1 : 1 ≤ rootArgument (U3Residual tau) (primeCoordinate N p) := by linarith [hs.1]
  have hR := row_residual_gt_one hN hpp (lt_of_lt_of_le (by norm_num) hr.1)
  have hC := wuSingularSeries_pos (p*N) (Nat.mul_pos hpp (by omega))
  have hlog := Real.log_pos hR
  have hli : 0 ≤ logarithmicIntegral N :=
    MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0 le_rfl
      (by exact_mod_cast hN)
  have hscale : 0 ≤ logarithmicIntegral N / (Nat.totient p : ℝ) :=
    div_nonneg hli (Nat.cast_nonneg _)
  have hlower := canonical_lower_bounded_normalization_budget hs.1 hs10 hC hlog
    heta.le heta1 hnorm
  have hmainpos : 0 <
      2 * rootArgument (U3Residual tau) (primeCoordinate N p) * wuSingularSeries (p*N) /
        (Real.exp Real.eulerMascheroniConstant *
          Real.log (rowTotalLevel N p (U3Residual tau) / (p : ℝ))) := by positivity
  have hprod : localSieveProduct (p*N) (rowCutoff N p (U3Residual tau)) ≤
      (1+eta) *
        (2 * rootArgument (U3Residual tau) (primeCoordinate N p) * wuSingularSeries (p*N) /
          (Real.exp Real.eulerMascheroniConstant *
            Real.log (rowTotalLevel N p (U3Residual tau) / (p : ℝ)))) := by
    apply (div_le_iff₀ hmainpos).mp
    linarith [(abs_le.mp hnorm).2]
  have hF : 0 ≤ jr1965F (rootArgument (U3Residual tau) (primeCoordinate N p)) +
      Real.exp Real.eulerMascheroniConstant * eta / 2 :=
    add_nonneg (jr1965F_pos (by linarith [hs.1])).le (by positivity)
  have hupper := (mul_le_mul_of_nonneg_left hprod hF).trans
    (canonical_upper_bounded_normalization_budget hs1 hs10 hC.le hlog heta.le heta1)
  constructor
  · have h := mul_le_mul_of_nonneg_left hlower hscale
    convert h using 1 <;>
      dsimp [rowSeed, P2SameQPhysicalRosserSeed.seedMain, parentTheta,
        wuLowerCoefficient, rowCutoff] <;> ring
  · have h := mul_le_mul_of_nonneg_left hupper hscale
    convert h using 1 <;>
      dsimp [rowSeed, P2SameQPhysicalRosserSeed.seedMain, parentTheta,
        wuUpperCoefficient, rowCutoff] <;> ring

/-- Every actual tail query lies in the ordinary A=1 interval, including
the physical max-two clamp. This is not an H table lookup. -/
theorem tail_upperCoefficient_eq_one {N p : ℕ} {tau : ℝ}
    (hN : 2 ≤ N) (htau : 0 ≤ tau) (htauhi : tau ≤ 1/12)
    (hp : p ∈ tailPrimes N) :
    wuUpperCoefficient (rootArgument (U3Residual tau) (primeCoordinate N p)) = 1 := by
  obtain ⟨hp', ht⟩ := mem_filter.mp hp
  have hpc := primeCoordinate_mem hN hp'
  have hs := U3_rootArgument_mem htau htauhi ⟨hpc.1, hpc.2.le⟩
  have hs3 : rootArgument (U3Residual tau) (primeCoordinate N p) ≤ 3 := by
    unfold rootArgument
    apply max_le (by norm_num)
    apply (div_le_iff₀ (by norm_num [a] : 0 < a)).mpr
    simp only [U3Residual, if_neg (not_lt.mpr ht), tailResidual]
    dsimp [tailCutoff] at ht
    norm_num [a]
    linarith
  exact jr1965F_normalized_initial (by linarith [hs.1]) hs3

def tailLowerMain (N : ℕ) (tau : ℝ) : ℝ :=
  ∑ p ∈ tailPrimes N,
    wuLowerCoefficient (rootArgument (U3Residual tau) (primeCoordinate N p)) * parentTheta N p tau

/-- Actual ordinary count supplier on the exact classical tail, with
the original same-Q Theta and both signed arithmetic errors already paid.
Only primitive positive accuracies and fixed 0<tau<=1/12 are premises.
No H/h value or count estimate is an input. -/
theorem eventually_original_tail_ordinary_Theta_count {tau eta epsilon : ℝ}
    (htau : 0 < tau) (htauhi : tau ≤ 1/12) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (he : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ bank : List P2ActualMarkedCountState.Query, ∀ rounds : ℕ,
      tailLowerMain N tau - 15*eta*tailTheta N tau - epsilon*singularNormalization N ≤
          tailStateLower N tau bank rounds ∧
      tailStateLower N tau bank rounds ≤ tailCount N tau ∧
      tailCount N tau ≤ tailStateUpper N tau bank rounds ∧
      tailStateUpper N tau bank rounds ≤
          (1+15*eta)*tailTheta N tau + epsilon*singularNormalization N := by
  have hrho : 0 < Real.exp Real.eulerMascheroniConstant * eta / 2 := by positivity
  filter_upwards [eventually_original_row_seed_Theta heta heta1,
    eventually_tail_count_initial_enclosure htau htauhi hrho he,
    eventually_ge_atTop (2 : ℕ)] with N hnorm hcount hN
  intro hEven bank rounds
  have hc := hcount hEven bank rounds
  have hl := sum_le_sum (fun p (hp : p ∈ tailPrimes N) =>
    (hnorm hEven tau htau.le htauhi p (mem_filter.mp hp).1).1)
  have hu := sum_le_sum (fun p (hp : p ∈ tailPrimes N) =>
    (hnorm hEven tau htau.le htauhi p (mem_filter.mp hp).1).2)
  have hlid :
      (∑ p ∈ tailPrimes N,
        (wuLowerCoefficient (rootArgument (U3Residual tau) (primeCoordinate N p)) - 15*eta) *
          parentTheta N p tau) = tailLowerMain N tau - 15*eta*tailTheta N tau := by
    rw [tailTheta_eq_sum_parentTheta]
    simp only [sub_mul, sum_sub_distrib, ← mul_sum, tailLowerMain]
  have huid :
      (∑ p ∈ tailPrimes N,
        (wuUpperCoefficient (rootArgument (U3Residual tau) (primeCoordinate N p)) + 15*eta) *
          parentTheta N p tau) = (1+15*eta)*tailTheta N tau := by
    rw [tailTheta_eq_sum_parentTheta, mul_sum]
    apply sum_congr rfl
    intro p hp
    rw [tail_upperCoefficient_eq_one hN htau.le htauhi hp]
  rw [hlid] at hl
  rw [huid] at hu
  change tailLowerMain N tau - 15*eta*tailTheta N tau ≤
    tailSeed false N tau (Real.exp Real.eulerMascheroniConstant * eta / 2) at hl
  change tailSeed true N tau (Real.exp Real.eulerMascheroniConstant * eta / 2) ≤
    (1+15*eta)*tailTheta N tau at hu
  refine ⟨?_, hc.2.1, hc.2.2.1, ?_⟩
  · linarith [hc.1]
  · linarith [hc.2.2.2]

/-- The manuscript's true-li normalizer, with the SAME complete family,
Q, singular factor, totient, physical residual and positive unit marks. -/
def trueTailTheta (N : ℕ) (tau : ℝ) : ℝ :=
  P2MarkedThetaLiNormalization.trueTheta N ((N : ℝ)^(1/2-tau))
    (tailPrimes N) (fun _ => 1)

/-- The lower ordinary main term is a positive marked family in its own
right. Its mark is exactly the physical parent's a_bar(s). -/
def trueTailLowerMain (N : ℕ) (tau : ℝ) : ℝ :=
  P2MarkedThetaLiNormalization.trueTheta N ((N : ℝ)^(1/2-tau)) (tailPrimes N)
    (fun p => wuLowerCoefficient (rootArgument (U3Residual tau) (primeCoordinate N p)))

theorem tailLowerMain_eq_markedTheta (N : ℕ) (tau : ℝ) :
    tailLowerMain N tau =
      Theta N ((N : ℝ)^(1/2-tau)) (tailPrimes N)
        (fun p => wuLowerCoefficient (rootArgument (U3Residual tau) (primeCoordinate N p))) := by
  unfold tailLowerMain Theta
  rw [mul_sum]
  apply sum_congr rfl
  intro p hp
  unfold parentTheta
  rw [tail_row_Q (mem_filter.mp hp).2]
  ring

/-- Actual original-family instantiation of the already proved true-li
transport. The threshold is before tau and the N-dependent marks. Neither
the AP payment nor a new assumed normalization is used to infer this. -/
theorem eventually_true_tail_main_transport {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1/12 →
      tailTheta N tau ≤ trueTailTheta N tau ∧
        trueTailLowerMain N tau ≤ (1+eta)*tailLowerMain N tau := by
  obtain ⟨N0, hN0, htransport⟩ :=
    P2MarkedThetaLiNormalization.uniform_trueTheta_relative_error eta heta
  filter_upwards [eventually_ge_atTop N0] with N hN
  intro tau htau htauhi
  have hN2 : 2 ≤ N := by omega
  have hpos (p : ℕ) (hp : p ∈ tailPrimes N) : 0 < p := by
    have h := (chenSinglePrimeSelector_sieve_data (mem_filter.mp hp).1).1
    omega
  have hlevel (p : ℕ) (hp : p ∈ tailPrimes N) :
      1 < (N : ℝ)^(1/2-tau)/(p : ℝ) := by
    obtain ⟨hp', ht⟩ := mem_filter.mp hp
    have hpc := primeCoordinate_mem hN2 hp'
    have hr := U3Residual_bounds htau htauhi ⟨hpc.1, hpc.2.le⟩
    simpa only [tail_row_Q ht] using
      row_residual_gt_one hN2 (hpos p hp) (lt_of_lt_of_le (by norm_num) hr.1)
  have hmark (p : ℕ) (hp : p ∈ tailPrimes N) :
      0 ≤ wuLowerCoefficient (rootArgument (U3Residual tau) (primeCoordinate N p)) := by
    have hpc := primeCoordinate_mem hN2 (mem_filter.mp hp).1
    have hs := U3_rootArgument_mem htau htauhi ⟨hpc.1, hpc.2.le⟩
    unfold wuLowerCoefficient
    exact div_nonneg
      (mul_nonneg (by linarith [hs.1]) (jr1965f_nonneg (by linarith [hs.1])))
      (by positivity)
  have hunit := htransport N hN ((N : ℝ)^(1/2-tau)) (tailPrimes N) (fun _ => 1)
    hpos (fun _ _ => zero_le_one) hlevel
  have hlower := htransport N hN ((N : ℝ)^(1/2-tau)) (tailPrimes N)
    (fun p => wuLowerCoefficient (rootArgument (U3Residual tau) (primeCoordinate N p)))
    hpos hmark hlevel
  refine ⟨hunit.1, ?_⟩
  rw [tailLowerMain_eq_markedTheta]
  exact hlower.2.1

/-- The ordinary initial count on the original TRUE-li same-Q family.
The factor 1/(1+eta) records the proved normalization error explicitly;
eta is fixed before N and may subsequently tend to zero. No division by
Theta or by the mass of the finite family occurs, including empty tails.
This supplies no positive adopted H/h defect. -/
theorem eventually_original_tail_ordinary_trueTheta_count {tau eta epsilon : ℝ}
    (htau : 0 < tau) (htauhi : tau ≤ 1/12) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (he : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ bank : List P2ActualMarkedCountState.Query, ∀ rounds : ℕ,
      trueTailLowerMain N tau / (1+eta) - 15*eta*trueTailTheta N tau -
          epsilon*singularNormalization N ≤ tailStateLower N tau bank rounds ∧
      tailStateLower N tau bank rounds ≤ tailCount N tau ∧
      tailCount N tau ≤ tailStateUpper N tau bank rounds ∧
      tailStateUpper N tau bank rounds ≤
          (1+15*eta)*trueTailTheta N tau + epsilon*singularNormalization N := by
  filter_upwards [eventually_original_tail_ordinary_Theta_count htau htauhi heta heta1 he,
    eventually_true_tail_main_transport heta] with N hcount htransport
  intro hEven bank rounds
  have hc := hcount hEven bank rounds
  have ht := htransport tau htau.le htauhi
  have hdiv : trueTailLowerMain N tau/(1+eta) ≤ tailLowerMain N tau :=
    (div_le_iff₀ (by linarith : 0 < 1+eta)).mpr (by simpa only [mul_comm] using ht.2)
  have hpenalty := mul_le_mul_of_nonneg_left ht.1 (by positivity : 0 ≤ 15*eta)
  have hupper := mul_le_mul_of_nonneg_left ht.1 (by positivity : 0 ≤ 1+15*eta)
  refine ⟨?_, hc.2.1, hc.2.2.1, ?_⟩
  · linarith [hc.1]
  · linarith [hc.2.2.2]

end
end ImbalancedChen.Part5OriginalClassicalTailThetaSeed
