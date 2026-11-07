import ImbalancedChen.P5ActualEuclideanPhysicalFourier
import ImbalancedChen.P5ActualOccurrencePlateauWordBudget
import Mathlib.MeasureTheory.Integral.Pi

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
This is the missing coordinate-and-integral connection from the actual
occurrence derivatives to the Euclidean mixedD used by Fourier IBP.
The logarithmic plateau support box is fixed before arithmetic parameters.
No mixedD, Fourier norm or target discrepancy bound is a premise.
-/
namespace ImbalancedChen.P5Z.OccurrenceEuclideanMixedIntegral
noncomputable section
open MeasureTheory Set
open scoped BigOperators
open AllRankCoordinateFourierIBP AllRankMixedOperatorBudget
open AllWordAmbientOccurrenceBound OccurrenceWordFourFactorLeibniz
open ActualOccurrencePlateauWordBudget ActualEuclideanPhysicalFourier

variable (m : ℕ)

abbrev coordinates : V m ≃L[ℝ] (Fin m → ℝ) := EuclideanSpace.equiv (Fin m) ℝ

def euclideanLift (w : (Fin m → ℝ) → ℝ) (z : V m) : ℂ :=
  (w (coordinates m z) : ℂ)

@[simp] theorem euclideanLift_toLp (w : (Fin m → ℝ) → ℝ) (z : Fin m → ℝ) :
    euclideanLift m w (WithLp.toLp 2 z) = (w z : ℂ) := rfl

theorem euclideanLift_smooth (w : (Fin m → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (euclideanLift m w) :=
  Complex.ofRealCLM.contDiff.comp
    (hw.comp (coordinates m).toContinuousLinearMap.contDiff)

theorem euclideanLift_compact (w : (Fin m → ℝ) → ℝ) (hw : HasCompactSupport w) :
    HasCompactSupport (euclideanLift m w) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hw.isCompact.image (coordinates m).symm.continuous)
  intro z hz
  have hwz : w (coordinates m z) ≠ 0 := by
    intro heq
    exact hz (by simp only [euclideanLift, heq, Complex.ofReal_zero])
  exact ⟨coordinates m z, subset_tsupport w hwz, (coordinates m).symm_apply_apply z⟩

/-- Differentiating the actual lifted function sends the Euclidean unit
vector to the genuine Pi coordinate tangent; no norm-dependent multiplier
is introduced by the coordinate change. -/
theorem coordDeriv_euclideanLift (w : (Fin m → ℝ) → ℝ)
    (hw : ContDiff ℝ ∞ w) (a : Fin m) :
    coordDeriv m a (euclideanLift m w) = euclideanLift m (occOne a w) := by
  funext z
  have hinner := ((hw.differentiable (by simp)) (coordinates m z)).hasFDerivAt.comp z
    ((coordinates m).toContinuousLinearMap.hasFDerivAt)
  have htotal := Complex.ofRealCLM.hasFDerivAt.comp z hinner
  change fderiv ℝ (euclideanLift m w) z (unit m a) =
    (occOne a w (coordinates m z) : ℂ)
  rw [htotal.fderiv, occOne_eq_fderiv a w (coordinates m z)
    ((hw.differentiable (by simp)) (coordinates m z))]
  change ((fderiv ℝ w (coordinates m z) ((coordinates m) (unit m a)) : ℝ) : ℂ) =
    (fderiv ℝ w (coordinates m z) (Pi.single a 1) : ℂ)
  congr 1
  congr 1
  ext i
  simp [coordinates, unit]

/-- Ordered repeated occurrence words are retained exactly. In particular
the two copies of each selected coordinate in twoWord are both present. -/
theorem coordWord_euclideanLift (w : (Fin m → ℝ) → ℝ)
    (hw : ContDiff ℝ ∞ w) (v : List (Fin m)) :
    coordWord m v (euclideanLift m w) = euclideanLift m (occWord v w) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
      change coordDeriv m a (coordWord m v (euclideanLift m w)) =
        euclideanLift m (occOne a (occWord v w))
      rw [ih]
      exact coordDeriv_euclideanLift m (occWord v w) (occWord_smooth v w hw) a

/-- The same native PiLp measure equivalence as in the preceding Fourier
Jacobian identifies the actual derivative integrals. -/
theorem integral_norm_coordWord (w : (Fin m → ℝ) → ℝ)
    (hw : ContDiff ℝ ∞ w) (v : List (Fin m)) :
    (∫ z : V m, ‖coordWord m v (euclideanLift m w) z‖) =
      ∫ z : Fin m → ℝ, |occWord v w z| := by
  rw [← integral_toLp m (fun z : V m => ‖coordWord m v (euclideanLift m w) z‖)]
  simp_rw [coordWord_euclideanLift m w hw v, euclideanLift_toLp,
    Complex.norm_real, Real.norm_eq_abs]

/-- Every occurrence derivative is supported in the original compact
chart, by the genuine Frechet derivative support theorem. -/
theorem occWord_tsupport_subset (w : (Fin m → ℝ) → ℝ)
    (hw : ContDiff ℝ ∞ w) (v : List (Fin m)) :
    tsupport (occWord v w) ⊆ tsupport w := by
  induction v with
  | nil => exact subset_rfl
  | cons a v ih =>
      have heq : occOne a (occWord v w) =
          fun z => fderiv ℝ (occWord v w) z (Pi.single a 1) := by
        funext z
        exact occOne_eq_fderiv a (occWord v w) z
          (((occWord_smooth v w hw).differentiable (by simp)) z)
      change tsupport (occOne a (occWord v w)) ⊆ tsupport w
      rw [heq]
      exact (tsupport_fderiv_apply_subset ℝ (Pi.single a 1)).trans ih

/-- This is the actual plateau box, independent of T, U, rank owners,
moduli, marked primes and the sign of any arithmetic remainder. -/
def plateauBox : Set (Fin m → ℝ) :=
  Set.pi Set.univ (fun _ => Icc (-1 : ℝ) (Real.log 2 + 1))

theorem plateauBox_compact : IsCompact (plateauBox m) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

theorem plateau_nonzero_mem_box (z : Fin m → ℝ) (hz : plateau m z ≠ 0) :
    z ∈ plateauBox m := by
  intro a ha
  have hca : c (z a) ≠ 0 := by
    intro hzero
    exact hz (Finset.prod_eq_zero (Finset.mem_univ a) hzero)
  exact ⟨(c_nonzero_support hca).1.le, (c_nonzero_support hca).2.le⟩

/-- For any multiplier, a genuine plateau factor constructs the fixed
compact support needed by the derivative integral budget. -/
theorem window_support (G : (Fin m → ℝ) → ℝ) :
    Function.support (fun z => G z * plateau m z) ⊆ plateauBox m := by
  intro z hz
  apply plateau_nonzero_mem_box m z
  intro hzero
  exact hz (by simp only [hzero, mul_zero])

theorem window_tsupport (G : (Fin m → ℝ) → ℝ) :
    tsupport (fun z => G z * plateau m z) ⊆ plateauBox m :=
  closure_minimal (window_support m G) (plateauBox_compact m).isClosed

/-- Its volume is a fixed real constant. Keeping the actual Lebesgue
mass avoids any replacement by a dimension-dependent loose carrier. -/
def intervalOne (x : ℝ) : ℝ :=
  (Icc (-1 : ℝ) (Real.log 2 + 1)).indicator (fun _ => 1) x

def boxMass : ℝ := volume.real (Icc (-1 : ℝ) (Real.log 2 + 1))

theorem boxMass_nonneg : 0 ≤ boxMass := ENNReal.toReal_nonneg

theorem intervalOne_integrable : Integrable intervalOne := by
  simpa only [intervalOne] using
    (continuous_const.integrableOn_Icc : IntegrableOn (fun _ : ℝ => (1 : ℝ))
      (Icc (-1 : ℝ) (Real.log 2 + 1))).integrable_indicator measurableSet_Icc

theorem intervalOne_integral : (∫ x : ℝ, intervalOne x) = boxMass := by
  rw [intervalOne, integral_indicator measurableSet_Icc]
  simp [boxMass]

def boxOne (z : Fin m → ℝ) : ℝ := ∏ a, intervalOne (z a)

theorem boxOne_nonneg (z : Fin m → ℝ) : 0 ≤ boxOne m z := by
  unfold boxOne
  apply Finset.prod_nonneg
  intro a ha
  unfold intervalOne
  split_ifs <;> norm_num

theorem boxOne_eq_one (z : Fin m → ℝ) (hz : z ∈ plateauBox m) : boxOne m z = 1 := by
  apply Finset.prod_eq_one
  intro a ha
  simp only [intervalOne, Set.indicator_of_mem (hz a (Set.mem_univ a))]

theorem boxOne_integrable : Integrable (boxOne m) := by
  simpa only [boxOne] using
    (Integrable.fintype_prod (μ := fun _ : Fin m => volume)
      (fun _ => intervalOne_integrable))

theorem boxOne_integral : (∫ z : Fin m → ℝ, boxOne m z) = boxMass ^ m := by
  simpa only [boxOne, intervalOne_integral, Fintype.card_fin] using
    integral_fintype_prod_volume_eq_pow (ι := Fin m) intervalOne

/-- Pointwise occurrence budgets are integrated over the actual support.
The factor is the exact fixed box volume, and derivatives cannot leak
outside it. This is the needed passage from a sup derivative to its L1. -/
theorem occurrence_word_l1_le (w : (Fin m → ℝ) → ℝ)
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hs : tsupport w ⊆ plateauBox m) (v : List (Fin m)) (B : ℝ)
    (hB : 0 ≤ B) (hbound : ∀ z, |occWord v w z| ≤ B) :
    (∫ z : Fin m → ℝ, |occWord v w z|) ≤ B * boxMass ^ m := by
  have hi : Integrable (fun z => |occWord v w z|) := by
    simpa only [Real.norm_eq_abs] using
      (occWord_smooth v w hw).continuous.norm.integrable_of_hasCompactSupport
        (occWord_compact v w hw hc).norm
  calc
    (∫ z : Fin m → ℝ, |occWord v w z|) ≤
        ∫ z : Fin m → ℝ, B * boxOne m z := by
      apply integral_mono hi ((boxOne_integrable m).const_mul B)
      intro z
      by_cases hz : z ∈ plateauBox m
      · rw [boxOne_eq_one m z hz, mul_one]
        exact hbound z
      · have hzero : occWord v w z = 0 := by
          by_contra hnonzero
          exact hz (hs ((occWord_tsupport_subset m w hw v)
            (subset_tsupport _ hnonzero)))
        rw [hzero, abs_zero]
        exact mul_nonneg hB (boxOne_nonneg m z)
    _ = B * boxMass ^ m := by rw [integral_const_mul, boxOne_integral]

theorem twoWord_length (S : Finset (Fin m)) : (twoWord m S).length = 2 * S.card := by
  have hlist (l : List (Fin m)) :
      (l.flatMap (fun a => [a, a])).length = 2 * l.length := by
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.flatMap_cons, List.length_append,
        List.length_cons, List.length_nil, ih]; omega
  simpa only [twoWord, Finset.length_toList] using hlist S.toList

/-- The true mixedD integral is derived from all required occurrence
words. The only derivative premise is a previously proved local word
budget, not the desired integral, Fourier norm or arithmetic estimate. -/
theorem mixedD_euclideanLift_le (w : (Fin m → ℝ) → ℝ)
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hs : tsupport w ⊆ plateauBox m) (B : ℝ) (hB : 0 ≤ B)
    (hword : ∀ v : List (Fin m), v.length ≤ 2 * m → ∀ z, |occWord v w z| ≤ B) :
    mixedD m (euclideanLift m w) ≤ (2 : ℝ) ^ m * boxMass ^ m * B := by
  classical
  have heach (S : Finset (Fin m)) :
      (∫ z : V m, ‖coordWord m (twoWord m S) (euclideanLift m w) z‖) ≤
        B * boxMass ^ m := by
    rw [integral_norm_coordWord m w hw]
    have hS : S.card ≤ m := by
      simpa using Finset.card_le_card (Finset.subset_univ S)
    exact occurrence_word_l1_le m w hw hc hs (twoWord m S) B hB
      (hword (twoWord m S) (by rw [twoWord_length]; omega))
  unfold mixedD
  calc
    (∑ S ∈ (Finset.univ : Finset (Fin m)).powerset,
      ∫ z : V m, ‖coordWord m (twoWord m S) (euclideanLift m w) z‖) ≤
        ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset, B * boxMass ^ m :=
      Finset.sum_le_sum (fun S hS => heach S)
    _ = (2 : ℝ) ^ m * boxMass ^ m * B := by
      simp only [Finset.sum_const, Finset.card_powerset, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

/-- A fixed finite constant covers every admitted occurrence dimension,
including zero. Its choice is before T, rank, scales or signs. -/
def dimensionBudget (kStar : ℕ) : ℝ :=
  ∑ j : Fin (6 * kStar + 1), (2 * boxMass) ^ j.val

theorem dimensionBudget_nonneg (kStar : ℕ) : 0 ≤ dimensionBudget kStar := by
  apply Finset.sum_nonneg
  intro j hj
  exact pow_nonneg (mul_nonneg (by norm_num) boxMass_nonneg) _

theorem dimension_factor_le {kStar m : ℕ} (hm : m ≤ 6 * kStar) :
    (2 : ℝ) ^ m * boxMass ^ m ≤ dimensionBudget kStar := by
  let j : Fin (6 * kStar + 1) := ⟨m, by omega⟩
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset (Fin (6 * kStar + 1))))
    (f := fun j => (2 * boxMass) ^ j.val)
    (fun i hi => pow_nonneg (mul_nonneg (by norm_num) boxMass_nonneg) _)
    (Finset.mem_univ j)
  simpa only [dimensionBudget, j, mul_pow] using h

end
end ImbalancedChen.P5Z.OccurrenceEuclideanMixedIntegral
