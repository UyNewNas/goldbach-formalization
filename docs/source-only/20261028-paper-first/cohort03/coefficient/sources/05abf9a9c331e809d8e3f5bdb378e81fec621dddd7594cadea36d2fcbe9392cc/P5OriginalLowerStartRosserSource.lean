import ImbalancedChen.CurrentChenInitialRosser
import ImbalancedChen.OrdinaryRosserFirstExitPolicy
import ImbalancedChen.P2EnhancedNativeLowerResidualFactor
import ImbalancedChen.P5OriginalOrdinaryCommonBetaModel

-- SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT / NOT_ROOT_ACCEPTED.
-- Original L1/L2 starts: a=417/5000, h=19/125, nu=249/448.
-- The native ordinary lower weight is lambda-minus(e*d), not the physical
-- common-beta attachment. Even rough rank retains lower small parity;
-- odd rough rank switches to upper, always at the literal level L/d.
-- No enhanced H248 table or analytic PP estimate is used.
-- Manuscript-body.tex 693-735, eq:current-lower-exit and
-- eq:current-lower-projection; 256-275, eq:current-PP.
-- global-chen-lower-completion-20261010.txt lines 47, 109, 158.

namespace ImbalancedChen.P5Z.OriginalLowerStartRosserSource

noncomputable section
open Classical
open scoped BigOperators
open OriginalOrdinaryBetaRegroup OriginalOrdinaryConditionalPrefix
open OriginalOrdinaryCommonBetaModel
open ImbalancedChen.P2EnhancedNativeLowerResidualFactor
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

-- false is L1 at a; true is L2 at h. This Bool selects only the two
-- manuscript starts, not an arbitrary local receiver or feedback state.
def startExponent (second : Bool) : ℝ :=
  if second then 19 / 125 else 417 / 5000

def startCutoff (N : ℕ) (second : Bool) : ℝ :=
  (N : ℝ) ^ startExponent second

def initialLevel (N : ℕ) : ℝ := (N : ℝ) ^ (249 / 448 : ℝ)
def startCap (N : ℕ) (second : Bool) : ℕ := Nat.ceil (startCutoff N second)

def lowerStartSupport (N : ℕ) (second : Bool) : Finset ℕ :=
  actualSmallRosserSupport N (startCap N second) (startCutoff N second)

def lowerStartCoefficient (N : ℕ) (second : Bool) (q : ℕ) : ℝ :=
  actualSmallRosserMinus N (startCap N second) (startCutoff N second)
    (initialLevel N) q

-- The exact original prime labels coprime to a full sieve modulus q.
-- This is a finite count, not a trueLi proxy or an enhanced density.
def exactInitialCoprimeMass (N q : ℕ) : ℝ :=
  (((chenAdditivePrimeCarrier N).filter (fun P => P.Coprime q)).card : ℝ)

def exactInitialCoprimeMean (N q : ℕ) : ℝ :=
  exactInitialCoprimeMass N q / (Nat.totient q : ℝ)

def lowerStartSignedCount (N : ℕ) (second : Bool) : ℝ :=
  ∑ q ∈ lowerStartSupport N second,
    lowerStartCoefficient N second q *
      (chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q)

def lowerStartSignedExactMean (N : ℕ) (second : Bool) : ℝ :=
  ∑ q ∈ lowerStartSupport N second,
    lowerStartCoefficient N second q * exactInitialCoprimeMean N q

def lowerStartSignedDiscrepancy (N : ℕ) (second : Bool) : ℝ :=
  ∑ q ∈ lowerStartSupport N second,
    lowerStartCoefficient N second q *
      ((chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q) -
        exactInitialCoprimeMean N q)

-- The count and exact coprime mean use literally the same signed lower
-- coefficient. Neither summand changes the root's ordinary Rosser tree.
theorem lowerStartSignedDiscrepancy_eq_count_sub_mean (N : ℕ) (second : Bool) :
    lowerStartSignedDiscrepancy N second =
      lowerStartSignedCount N second - lowerStartSignedExactMean N second := by
  unfold lowerStartSignedDiscrepancy lowerStartSignedCount lowerStartSignedExactMean
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

-- The count side is the actual centre-deleted original prime carrier,
-- rather than an inclusive AP count with the centre primes suppressed by
-- an analytic error term.
theorem lowerStartSignedCount_eq_actualPrimeFilter (N : ℕ) (second : Bool) :
    lowerStartSignedCount N second =
      ∑ q ∈ lowerStartSupport N second,
        lowerStartCoefficient N second q *
          ((((chenAdditivePrimeCarrier N).filter
            (fun P => Nat.ModEq q P N)).card : ℝ)) := by
  unfold lowerStartSignedCount
  apply Finset.sum_congr rfl
  intro q hq
  rw [chenAdditivePrimeCarrier_AP_count]

private theorem startExponent_pos_lt_nu (second : Bool) :
    0 < startExponent second ∧ startExponent second < 249 / 448 := by
  cases second <;> norm_num [startExponent]

private theorem start_level_bounds (N : ℕ) (second : Bool) (hN : 1 < N) :
    1 < initialLevel N ∧ startCutoff N second ≤ initialLevel N := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have h := startExponent_pos_lt_nu second
  constructor
  · exact Real.one_lt_rpow hNr (by norm_num : (0 : ℝ) < 249 / 448)
  · exact Real.rpow_le_rpow_of_exponent_le hNr.le h.2.le

-- The full native L1/L2 coefficient is itself the ordinary lower
-- even-first-exit coefficient, before any presieve split or beta compiler.
theorem lowerStartCoefficient_eq_evenFirstExit
    (N : ℕ) (second : Bool) (hN : 1 < N) (q : ℕ) :
    lowerStartCoefficient N second q =
      (firstExitRetainedCoefficient
        (ordinaryParityRosserPolicy true (initialLevel N))
        (roughPrimeUniverse N (startCap N second) 0 (startCutoff N second)) q : ℝ) := by
  have hb := start_level_bounds N second hN
  exact (firstExitRetainedCoefficient_ordinaryParityRosser_eq_actualMinus
    N (startCap N second) (startCutoff N second) (initialLevel N)
    hb.1 hb.2 q).symm

private theorem lowerRoughWeight_eq_evenFirstExit
    (N cap d : ℕ) (w Z L : ℝ) (hL : 1 < L) (hZL : Z ≤ L) :
    lowerRoughWeight N cap w Z L d =
      fixedEvenRoughCoefficient
        (fun pre => decide (ordinaryRosserPrefixAdmissible true L pre))
        N cap w Z d := by
  calc
    lowerRoughWeight N cap w Z L d =
        ordinaryRosserWeight true (roughPrimeUniverse N cap w Z).prod L d := by
      simp only [lowerRoughWeight, ordinaryRosserWeight, if_true,
        roughProduct_eq_universe_prod]
    _ = (firstExitRetainedCoefficient (ordinaryParityRosserPolicy true L)
          (roughPrimeUniverse N cap w Z) d : ℝ) :=
      (firstExitRetainedCoefficient_ordinaryParityRosser true L hL
        (roughPrimeUniverse N cap w Z)
        (roughPrimeUniverse_pairwise_gt N cap w Z)
        (fun _ hp => mem_roughPrimeUniverse_prime hp)
        (fun _ p hp => (mem_roughPrimeUniverse.mp hp).2.2.2.2.trans_le hZL) d).symm
    _ = _ := rfl

-- The pointwise native lower factor is already proved in the predecessor.
-- This finite signed identity is the missing lower analogue of the upper
-- test split. It keeps all zero rows and the actual parity-selected L/d.
private theorem native_lower_test_residual
    (N cap : ℕ) {w Z : ℝ} (hwZ : w ≤ Z) (L : ℝ) (F : ℕ → ℝ) :
    (∑ q ∈ actualSmallRosserSupport N cap Z,
      actualSmallRosserMinus N cap Z L q * F q) =
      ∑ d ∈ roughSupport N cap w Z,
        lowerRoughWeight N cap w Z L d *
          ∑ e ∈ actualSmallRosserSupport N cap w,
            lowerResidualSmallWeight N cap w L d e * F (e * d) := by
  calc
    (∑ q ∈ actualSmallRosserSupport N cap Z,
      actualSmallRosserMinus N cap Z L q * F q) =
        ∑ e ∈ actualSmallRosserSupport N cap w,
          ∑ d ∈ roughSupport N cap w Z,
            actualSmallRosserMinus N cap Z L (e * d) * F (e * d) := by
      rw [nativeSupport_eq_products N cap hwZ]
      rw [sum_smallRoughModuli
        (fun d hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
        (fun d hd => roughSupport_rough hd)]
      exact Finset.sum_product _ _ _
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [native_lower_residual_factor_on_support hwZ he hd]
      ring

-- One actual L1 or L2 start, with its lower even-first-exit rough policy.
-- The auxiliary wall is a finite small/rough split inside that same tree.
theorem lowerStartSignedDiscrepancy_evenFirstExit_residual
    (N : ℕ) (hN : 1 < N) (second : Bool) {w : ℝ}
    (hw : w ≤ startCutoff N second) :
    lowerStartSignedDiscrepancy N second =
      ∑ d ∈ roughSupport N (startCap N second) w (startCutoff N second),
        fixedEvenRoughCoefficient
          (fun pre => decide (ordinaryRosserPrefixAdmissible true (initialLevel N) pre))
          N (startCap N second) w (startCutoff N second) d *
          ∑ e ∈ actualSmallRosserSupport N (startCap N second) w,
            (if Even d.primeFactors.card then
              actualSmallRosserMinus N (startCap N second) w
                (initialLevel N / (d : ℝ)) e
             else
              actualSmallRosserPlus N (startCap N second) w
                (initialLevel N / (d : ℝ)) e) *
            ((chenPrimeAPCount N N (e * d) - chenCentrePrimeAPCount N N (e * d)) -
              exactInitialCoprimeMean N (e * d)) := by
  have hb := start_level_bounds N second hN
  have h := native_lower_test_residual N (startCap N second) hw
    (initialLevel N)
    (fun q => (chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q) -
      exactInitialCoprimeMean N q)
  calc
    lowerStartSignedDiscrepancy N second =
        ∑ d ∈ roughSupport N (startCap N second) w (startCutoff N second),
          lowerRoughWeight N (startCap N second) w (startCutoff N second)
            (initialLevel N) d *
            ∑ e ∈ actualSmallRosserSupport N (startCap N second) w,
              (if Even d.primeFactors.card then
                actualSmallRosserMinus N (startCap N second) w
                  (initialLevel N / (d : ℝ)) e
               else
                actualSmallRosserPlus N (startCap N second) w
                  (initialLevel N / (d : ℝ)) e) *
              ((chenPrimeAPCount N N (e * d) - chenCentrePrimeAPCount N N (e * d)) -
                exactInitialCoprimeMean N (e * d)) := by
      simpa only [lowerStartSignedDiscrepancy, lowerStartSupport, lowerStartCoefficient,
        lowerResidualSmallWeight] using h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [lowerRoughWeight_eq_evenFirstExit N (startCap N second) d w
        (startCutoff N second) (initialLevel N) hb.1 hb.2]

-- Exact physical signed divisor sum on the genuine Chen receiver set.
-- The same lower weight is used by the pointwise ordinary minorant.
theorem lowerStart_physicalDivisorSum_eq_signedCount
    (N : ℕ) (second : Bool) :
    (∑ n ∈ chenPrimeReceiverSource N,
      supportedDivisorSum (lowerStartSupport N second)
        (lowerStartCoefficient N second) n) =
      lowerStartSignedCount N second := by
  exact currentChen_sum_supportedDivisorSum N
    (lowerStartSupport N second) (lowerStartCoefficient N second)

-- The ordinary lower coefficient's active modulus is squarefree,
-- coprime to N and strictly below the physical original level.
theorem lowerStart_active_modulus_support
    {N q : ℕ} (second : Bool)
    (hq : lowerStartCoefficient N second q ≠ 0) :
    q ∈ lowerStartSupport N second ∧ Squarefree q ∧ q.Coprime N ∧
      (q : ℝ) < initialLevel N := by
  have ha := actualSmallRosserMinus_active hq
  exact ⟨ha.1,
    actualSmallRosserSupport_squarefree N (startCap N second)
      (startCutoff N second) ha.1,
    actualSmallRosserSupport_coprime_target N (startCap N second)
      (startCutoff N second) ha.1, ha.2.1⟩

end
end ImbalancedChen.P5Z.OriginalLowerStartRosserSource
