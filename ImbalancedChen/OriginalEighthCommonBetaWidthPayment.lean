import ImbalancedChen.ActualNormalizedRhoError
import ImbalancedChen.P4AOriginalEighthParentPhysicalLedger

/-!
SOURCE ONLY / UNCOMPILED. Absolute payment of the actual common-beta
WIDTH term in an original old-minus-raised eighth charge. Both policies
use exactly the same small Rosser pair and positive presieve. The two
absolute rough masses are each bounded by the same proved envelope Q;
their difference therefore costs Q, not 2Q. Signed mass is not substituted
for absolute mass, and no charge-size or integral bound is assumed.

The companion paired attachment error is centered at V(w) times the
positive-w rough charge. This is not a two-sided identification with the
unpresieved native continuation. Its projection defect remains OPEN.
-/
namespace ImbalancedChen.OriginalEighthCommonBetaWidthPayment
noncomputable section
open scoped Classical BigOperators
open Filter Topology

def absoluteMass (ret : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) : ℝ :=
  reciprocalTotientDensity (fixedRoughSupport ret N cap w z)
    (fun d => |fixedRoughCoefficient ret N cap w z d|)

def widthTerm (old new : List ℕ → Bool) (N cap : ℕ) (w z B : ℝ) : ℝ :=
  ((actualSmallRosserPlusDensity N cap w B - actualSmallRosserMinusDensity N cap w B) / 2) *
    (absoluteMass old N cap w z - absoluteMass new N cap w z)

def pairedError (old new : List ℕ → Bool) (N cap : ℕ) (w z B : ℝ) : ℝ :=
  (physicalDensitySum (actualSmallRoughModuli old N cap w z) (actualSmallRoughRho old N cap w z B) -
    physicalDensitySum (actualSmallRoughModuli new N cap w z) (actualSmallRoughRho new N cap w z B)) -
    actualSmallEulerProduct N cap w *
      (reciprocalTotientDensity (fixedRoughSupport old N cap w z) (fixedRoughCoefficient old N cap w z) -
        reciprocalTotientDensity (fixedRoughSupport new N cap w z) (fixedRoughCoefficient new N cap w z))

private theorem absoluteMass_nonneg (ret : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :
    0 ≤ absoluteMass ret N cap w z :=
  Finset.sum_nonneg (fun _ _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))

/-- Genuine common constants and one threshold supply both actual width
and signed paired errors. No arithmetic policy, cap or target selects a
different beta pair. The envelope retains its logarithmic denominator. -/
theorem exists_pair_power_error_envelope :
    ∃ C K Kr : ℝ, 0 < C ∧ 1 < K ∧ 1 < Kr ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
        ∃ D0 : ℝ, 2 ≤ D0 ∧ ∀ D : ℝ, D0 ≤ D →
          ∀ N cap : ℕ, Even N → ∀ r : ℝ, epsilon ^ 2 ≤ r →
            ∀ old new : List ℕ → Bool,
              let w := D ^ (epsilon ^ 2)
              let z := D ^ r
              let B := D ^ epsilon
              let V := actualSmallEulerProduct N cap w
              let E := actualSmallRosserDensityError C K D epsilon
              let Q := (r / epsilon ^ 2) * (1 + Kr / (epsilon ^ 2 * Real.log D))
              |widthTerm old new N cap w z B| ≤ (V * E) * Q ∧
                |pairedError old new N cap w z B| ≤ (V * E) * Q := by
  obtain ⟨C, K, hC, hK, hsmall⟩ := exists_actualSmallRosser_density_sandwich
  obtain ⟨Kr, hKr, hrough⟩ := exists_fixedRoughAbsoluteDensity_le_powerParameters
  refine ⟨C, K, Kr, hC, hK, hKr, ?_⟩
  intro epsilon he he8
  obtain ⟨D0, hD0, hs⟩ := hsmall epsilon he he8
  refine ⟨D0, hD0, ?_⟩
  intro D hD N cap hEven r her old new
  dsimp only
  let w := D ^ (epsilon ^ 2)
  let z := D ^ r
  let B := D ^ epsilon
  let V := actualSmallEulerProduct N cap w
  let E := actualSmallRosserDensityError C K D epsilon
  let Q := (r / epsilon ^ 2) * (1 + Kr / (epsilon ^ 2 * Real.log D))
  let lo := actualSmallRosserMinusDensity N cap w B
  let hi := actualSmallRosserPlusDensity N cap w B
  have hD1 : 1 < D := by linarith
  have hV : 0 ≤ V := (actualSmallEulerProduct_pos N cap w hEven).le
  have hE : 0 ≤ E := by dsimp [E, actualSmallRosserDensityError]; positivity
  have hVE : 0 ≤ V * E := mul_nonneg hV hE
  have hS := hs D hD N cap hEven
  have hLoBound : V * (1 - E) ≤ lo := hS.1
  have hLoV : lo ≤ V := hS.2.1
  have hVHi : V ≤ hi := hS.2.2.1
  have hHiBound : hi ≤ V * (1 + E) := hS.2.2.2.1
  have hGap : hi - lo ≤ 2 * V * E := hS.2.2.2.2
  have ha0 := absoluteMass_nonneg old N cap w z
  have hb0 := absoluteMass_nonneg new N cap w z
  have ha : absoluteMass old N cap w z ≤ Q := hrough old N cap hEven D epsilon r hD1 he her
  have hb : absoluteMass new N cap w z ≤ Q := hrough new N cap hEven D epsilon r hD1 he her
  have hdiff : |absoluteMass old N cap w z - absoluteMass new N cap w z| ≤ Q := by
    apply abs_le.mpr
    constructor <;> linarith only [ha0, hb0, ha, hb]
  have hwidth0 : 0 ≤ (hi - lo) / 2 := by linarith only [hLoV, hVHi]
  have hwidth : (hi - lo) / 2 ≤ V * E := by linarith only [hGap]
  have hevent (ret : List ℕ → Bool) :
      0 ≤ physicalDensitySum (actualSmallRoughModuli ret N cap w z) (actualSmallRoughRho ret N cap w z B) -
          V * reciprocalTotientDensity (fixedRoughSupport ret N cap w z) (fixedRoughCoefficient ret N cap w z) ∧
      physicalDensitySum (actualSmallRoughModuli ret N cap w z) (actualSmallRoughRho ret N cap w z B) -
          V * reciprocalTotientDensity (fixedRoughSupport ret N cap w z) (fixedRoughCoefficient ret N cap w z) ≤
        (V * E) * Q := by
    have hh := signSensitiveReciprocalTotientDensity_error
      (fixedRoughSupport ret N cap w z) (fixedRoughCoefficient ret N cap w z)
      (V := V) (delta := V * E)
      (show V - V * E ≤ lo by nlinarith only [hLoBound])
      hLoV hVHi
      (show hi ≤ V + V * E by nlinarith only [hHiBound])
    rw [← actualSmallRoughRho_density_eq ret N cap w z B] at hh
    exact ⟨hh.1, hh.2.trans (mul_le_mul_of_nonneg_left
      (hrough ret N cap hEven D epsilon r hD1 he her) hVE)⟩
  refine ⟨?_, ?_⟩
  · change |((hi - lo) / 2) * (absoluteMass old N cap w z - absoluteMass new N cap w z)| ≤ _
    rw [abs_mul, abs_of_nonneg hwidth0]
    exact mul_le_mul hwidth hdiff (abs_nonneg _) hVE
  · have ho := hevent old
    have hn := hevent new
    unfold pairedError
    apply abs_le.mpr
    constructor <;> nlinarith only [ho.1, ho.2, hn.1, hn.2]

/-- Both errors receive an arbitrary common target-scale reserve, with
epsilon fixed before the targets, policies, caps and the rank-eight action. -/
theorem exists_pair_target_error_reserve
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hmax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) → ∀ old new : List ℕ → Bool,
          let w := (N : ℝ) ^ (nu * epsilon ^ 2)
          let z := (N : ℝ) ^ (nu * r)
          let B := (N : ℝ) ^ (nu * epsilon)
          |widthTerm old new N cap w z B| ≤ eta * singularSeries N / Real.log (N : ℝ) ∧
            |pairedError old new N cap w z B| ≤ eta * singularSeries N / Real.log (N : ℝ) := by
  obtain ⟨C, K, Kr, hC, hK, hKr, hsupply⟩ := exists_pair_power_error_envelope
  obtain ⟨B0, _hB0, hEuler⟩ := exists_actualSmallEulerProduct_le_singularSeries_log
  obtain ⟨epsilon, he, he8, hemax, her, hfloor⟩ :=
    exists_normalizedSmallRosser_epsilon_absorbing B0 C r (eta * nu) epsilonMax
      hr (mul_pos heta hnu) hmax
  have hlim := tendsto_normalizedSmallRosserDensityError_mul_roughMassEnvelope B0 C K Kr r epsilon he
  have hsmall : ∀ᶠ D : ℝ in atTop,
      (B0 / epsilon ^ 2) * actualSmallRosserDensityError C K D epsilon *
        (r / epsilon ^ 2) * (1 + Kr / (epsilon ^ 2 * Real.log D)) < eta * nu :=
    (tendsto_order.1 hlim).2 (eta * nu) hfloor
  obtain ⟨Ds, hDs⟩ := eventually_atTop.mp (hsmall.and (eventually_four_le_smallRosserPower epsilon he))
  obtain ⟨Df, hDf, hf⟩ := hsupply epsilon he he8
  have hpower : Tendsto (fun N : ℕ => (N : ℝ) ^ nu) atTop atTop :=
    (tendsto_rpow_atTop hnu).comp tendsto_natCast_atTop_atTop
  obtain ⟨Np, hNp⟩ := eventually_atTop.mp
    (hpower.eventually (eventually_ge_atTop (max Df Ds)))
  refine ⟨epsilon, he, he8, hemax, her, max Np 2, le_max_right _ _, ?_⟩
  intro N hN hEven cap hcap old new
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hNpos : 0 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpR : (0 : ℝ) < N := zero_lt_one.trans hNr
  let D := (N : ℝ) ^ nu
  have hDp := hNp N ((le_max_left _ _).trans hN)
  have hDge : Df ≤ D := (le_max_left _ _).trans hDp
  have hDsge : Ds ≤ D := (le_max_right _ _).trans hDp
  have hD1 : 1 < D := by dsimp [D]; exact Real.one_lt_rpow hNr hnu
  have hDpos : 0 < D := zero_lt_one.trans hD1
  have hlogD : 0 < Real.log D := Real.log_pos hD1
  have hwcap : D ^ (epsilon ^ 2) ≤ (cap : ℝ) := by
    dsimp [D]
    rw [← Real.rpow_mul hNpR.le]
    exact (Real.rpow_le_rpow_of_exponent_le hNr.le
      (mul_le_mul_of_nonneg_left her hnu.le)).trans hcap
  have hVbound := hEuler N cap hNpos hEven (D ^ (epsilon ^ 2)) (hDs D hDsge).2 hwcap
  rw [Real.log_rpow hDpos] at hVbound
  let E := actualSmallRosserDensityError C K D epsilon
  let Q := (r / epsilon ^ 2) * (1 + Kr / (epsilon ^ 2 * Real.log D))
  have hE : 0 ≤ E := by dsimp [E, actualSmallRosserDensityError]; positivity
  have hQ : 0 ≤ Q := by
    have hKrpos : 0 < Kr := by linarith
    dsimp [Q]
    positivity
  have hbudget : (actualSmallEulerProduct N cap (D ^ (epsilon ^ 2)) * E) * Q ≤
      (eta * nu) * singularSeries N / Real.log D := by
    calc
      _ ≤ (B0 * singularSeries N / (epsilon ^ 2 * Real.log D)) * E * Q :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hVbound hE) hQ
      _ = (singularSeries N / Real.log D) *
          ((B0 / epsilon ^ 2) * E * (r / epsilon ^ 2) *
            (1 + Kr / (epsilon ^ 2 * Real.log D))) := by dsimp [Q]; field_simp; ring
      _ ≤ (singularSeries N / Real.log D) * (eta * nu) :=
        mul_le_mul_of_nonneg_left (hDs D hDsge).1.le
          (div_nonneg (singularSeries_pos N).le hlogD.le)
      _ = _ := by ring
  have hpair := hf D hDge N cap hEven r her old new
  have hw := hpair.1.trans hbudget
  have hp := hpair.2.trans hbudget
  dsimp only at hw hp ⊢
  simp only [D, ← Real.rpow_mul hNpR.le, Real.log_rpow hNpR] at hw hp
  have hcancel : (eta * nu) * singularSeries N / (nu * Real.log (N : ℝ)) =
      eta * singularSeries N / Real.log (N : ℝ) := by field_simp [hnu.ne']
  rw [hcancel] at hw hp
  exact ⟨hw, hp⟩

/-- The actual original rank-eight old-minus-raised charge uses that same
positive-w beta pair. Its stopped continuations keep every selected history,
incoming mass and remaining prime carrier through the literal charge.
The estimate is centered at V(w) times this positive-w charge; it makes
no unproved comparison with the w=0 native charge. -/
theorem exists_original_eighth_width_and_paired_charge_reserve
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hmax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ (lambda6 : List ℕ → ℝ) (base : Bool → List ℕ → Bool),
            (∀ pre, base true pre = true) →
            ∀ a : P4AOriginalEighthParentPhysicalLedger.Action,
              let w := (N : ℝ) ^ (nu * epsilon ^ 2)
              let z := (N : ℝ) ^ (nu * r)
              let B := (N : ℝ) ^ (nu * epsilon)
              let old := P4AOriginalEighthParentPhysicalLedger.parentPolicy (N : ℝ) lambda6 base false
              let fresh := P4AOriginalEighthParentPhysicalLedger.actionPolicy a (N : ℝ) lambda6 base false
              |widthTerm old fresh N cap w z B| ≤ eta * singularSeries N / Real.log (N : ℝ) ∧
                |(physicalDensitySum (actualSmallRoughModuli old N cap w z)
                    (actualSmallRoughRho old N cap w z B) -
                  physicalDensitySum (actualSmallRoughModuli fresh N cap w z)
                    (actualSmallRoughRho fresh N cap w z B)) -
                  actualSmallEulerProduct N cap w *
                    P4AOriginalEighthParentPhysicalLedger.charge a N cap w z lambda6 base| ≤
                  eta * singularSeries N / Real.log (N : ℝ) := by
  obtain ⟨epsilon, he, he8, hemax, her, N0, hN0, hsupply⟩ :=
    exists_pair_target_error_reserve nu r eta epsilonMax hnu hr heta hmax
  refine ⟨epsilon, he, he8, hemax, her, N0, hN0, ?_⟩
  intro N hN hEven cap hcap lambda6 base hbase a
  let w := (N : ℝ) ^ (nu * epsilon ^ 2)
  let z := (N : ℝ) ^ (nu * r)
  let B := (N : ℝ) ^ (nu * epsilon)
  have hpair := hsupply N hN hEven cap hcap
    (P4AOriginalEighthParentPhysicalLedger.parentPolicy (N : ℝ) lambda6 base false)
    (P4AOriginalEighthParentPhysicalLedger.actionPolicy a (N : ℝ) lambda6 base false)
  refine ⟨hpair.1, ?_⟩
  have hp := hpair.2
  unfold pairedError at hp
  have hOld := UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (P4AOriginalEighthParentPhysicalLedger.parentPolicy (N : ℝ) lambda6 base)
    (P4AOriginalEighthParentPhysicalLedger.parent_even (N : ℝ) lambda6 base hbase) N cap w z
  have hNew := UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (P4AOriginalEighthParentPhysicalLedger.actionPolicy a (N : ℝ) lambda6 base)
    (P4AOriginalEighthParentPhysicalLedger.action_even a (N : ℝ) lambda6 base hbase) N cap w z
  rw [← hOld, ← hNew,
    P4AOriginalEighthParentPhysicalLedger.parent_sub_action_eq_charge a N cap w z lambda6 base] at hp
  exact hp

end
end ImbalancedChen.OriginalEighthCommonBetaWidthPayment
