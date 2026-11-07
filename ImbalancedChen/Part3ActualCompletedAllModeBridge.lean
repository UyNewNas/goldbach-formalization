import ImbalancedChen.Part3ActualCompletedPairSharpL2
import ImbalancedChen.Part3PhysicalCompletedFrequencyDecay
import ImbalancedChen.Part3ActualCompletedSquarePushforward
import ImbalancedChen.Part3ActualFullLeftCollisionEnergy

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED / ZERO_FORMAL_CREDIT.

The ORIGINAL completedPiece has one common, absolutely summable completed
mode variable before all of its original signed f/u/v labels. In
particular every m=0, y=0, repeated fibre and unit gate survives. This
source bridge uses proved physical Schwartz summability, not an assumed
global truncation or a factorizable-source premise.

The true all-mode alias identifies the original source with the finite
operator and supplies a derived 9*M*(M+q) squared-norm cost times the TRUE
right collision energy. No finite-window cancellation shortcut is used.
The arithmetic right energy and c,z aggregation remain separate; the
full original spectral 7/32 return is not asserted.
-/

namespace ImbalancedChen.Part3.ActualCompletedAllModeBridge20261026b

noncomputable section
open Classical Finset CommonSmoothCutoff OriginalSmoothPoissonTail
open ActualReciprocalSquarePoissonSourceOnly
open ActualCompletedPairYFibres20261026b ActualCompletedPairSharpL220261026b
open ActualCompletedSquarePushforwardSourceOnly
open OriginalSmoothPoissonTail.HardCompletedSchwartz20261026b
open OriginalSmoothPoissonTail.FiniteSource20261026b
open OriginalSmoothPoissonTail.FiniteOperator20261026b
open ActualCompletedLeftAlias20261026b
open scoped BigOperators

def actualRawQSeries (A q : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ) (F : ℝ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N : ℝ) : ℂ :=
  (scaledDyadicCutoff N q : ℂ) *
    ∑ i ∈ originalFuvCarrier T H F,
      if i.1 ≠ 0 ∧ fixedUnit A a i.2.1.1 ∧ fixedUnit A a i.2.2.1 ∧
          q.Coprime (originalZ i) then
        (atomCoeff lambda omega i.2.1 * star (atomCoeff lambda omega i.2.2)) *
          ∑' mode : ℤ, frequency M q a (originalY i) (originalZ i : ℤ) mode else 0

private theorem actualQ_single_mode_summable (A q : ℕ) (hq : 0 < q) (a : ℤ)
    (T : Finset ℕ) (H : ℕ) (F : ℝ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (M N : ℝ) (hM : 0 < M) :
    Summable (fun mode : ℤ =>
      actualCompletedQWindow A q a T H F lambda omega M N {mode} (fun _ => 1)) := by
  simp only [actualCompletedQWindow, Finset.sum_singleton, one_mul]
  apply Summable.mul_left
  apply summable_sum
  intro i hi
  by_cases hg : i.1 ≠ 0 ∧ fixedUnit A a i.2.1.1 ∧ fixedUnit A a i.2.2.1 ∧
      q.Coprime (originalZ i)
  · simp only [if_pos hg]
    exact (frequency_summable M hM q hq a (originalY i) (originalZ i : ℤ)).mul_left _
  · simp only [if_neg hg]
    exact summable_zero

/-- Actual Schwartz summability justifies moving the one common mode
outside ALL original ordered f/u/v labels at fixed physical modulus. -/
theorem actualRawQSeries_eq_tsum_single_modes (A q : ℕ) (hq : 0 < q) (a : ℤ)
    (T : Finset ℕ) (H : ℕ) (F : ℝ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (M N : ℝ) (hM : 0 < M) :
    actualRawQSeries A q a T H F lambda omega M N =
      ∑' mode : ℤ,
        actualCompletedQWindow A q a T H F lambda omega M N {mode} (fun _ => 1) := by
  let term (i : FibreIndex) (mode : ℤ) : ℂ :=
    if i.1 ≠ 0 ∧ fixedUnit A a i.2.1.1 ∧ fixedUnit A a i.2.2.1 ∧
        q.Coprime (originalZ i) then
      (atomCoeff lambda omega i.2.1 * star (atomCoeff lambda omega i.2.2)) *
        frequency M q a (originalY i) (originalZ i : ℤ) mode else 0
  have hs (i : FibreIndex) : Summable (term i) := by
    dsimp only [term]
    split_ifs
    · exact (frequency_summable M hM q hq a (originalY i) (originalZ i : ℤ)).mul_left _
    · exact summable_zero
  have hi (i : FibreIndex) :
      (if i.1 ≠ 0 ∧ fixedUnit A a i.2.1.1 ∧ fixedUnit A a i.2.2.1 ∧
          q.Coprime (originalZ i) then
        (atomCoeff lambda omega i.2.1 * star (atomCoeff lambda omega i.2.2)) *
          ∑' mode : ℤ, frequency M q a (originalY i) (originalZ i : ℤ) mode else 0) =
        ∑' mode : ℤ, term i mode := by
    dsimp only [term]
    split_ifs <;> simp only [tsum_mul_left, tsum_zero]
  unfold actualRawQSeries
  simp_rw [hi]
  rw [← Summable.tsum_finsetSum (fun i hi => hs i), ← tsum_mul_left]
  apply tsum_congr
  intro mode
  simp only [actualCompletedQWindow, Finset.sum_singleton, one_mul, term]

/-- Exact original c/f/u/v source, not a replacement arbitrary coefficient
family. f!=0 and both fixedUnit tests remain literal. -/
theorem completedPiece_eq_actualRawQSeries (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N B C F : ℝ) :
    completedPiece A a T H lambda omega M N B C F =
      ∑ q ∈ Ioc 0 (Nat.floor (10 * C)),
        actualRawQSeries A q a T H F lambda omega M N := by
  unfold completedPiece actualRawQSeries originalFuvCarrier originalFWindow
  simp only [Finset.sum_product, originalY, originalZ]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  by_cases hfn : f ≠ 0
  · simp only [hfn, true_and, if_true]
  · simp only [hfn, false_and, if_false, Finset.sum_const_zero, mul_zero]

/-- The common all-integer completed series is genuinely summable from
its original finite c/f/u/v source, including the complete zero mode. -/
theorem actualFiniteCompletedPiece_single_mode_summable (A : ℕ) (a : ℤ)
    (T : Finset ℕ) (H : ℕ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (M N C F : ℝ) (hM : 0 < M) :
    Summable (fun mode : ℤ =>
      actualFiniteCompletedPiece A a T H lambda omega M N C F {mode} (fun _ => 1)) := by
  unfold actualFiniteCompletedPiece
  apply summable_sum
  intro q hq
  exact actualQ_single_mode_summable A q (Finset.mem_Ioc.mp hq).1 a
    T H F lambda omega M N hM

/-- One common m runs BEFORE all original physical labels. This equality
does not choose a tuple-dependent finite window or use an unproved tail. -/
theorem completedPiece_eq_tsum_actualFiniteCompletedPiece (A : ℕ) (a : ℤ)
    (T : Finset ℕ) (H : ℕ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (M N B C F : ℝ) (hM : 0 < M) :
    completedPiece A a T H lambda omega M N B C F =
      ∑' mode : ℤ,
        actualFiniteCompletedPiece A a T H lambda omega M N C F {mode} (fun _ => 1) := by
  rw [completedPiece_eq_actualRawQSeries]
  calc
    _ = ∑ q ∈ Ioc 0 (Nat.floor (10 * C)), ∑' mode : ℤ,
        actualCompletedQWindow A q a T H F lambda omega M N {mode} (fun _ => 1) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact actualRawQSeries_eq_tsum_single_modes A q (Finset.mem_Ioc.mp hq).1 a
        T H F lambda omega M N hM
    _ = _ := (Summable.tsum_finsetSum (fun q hq =>
      actualQ_single_mode_summable A q (Finset.mem_Ioc.mp hq).1 a
        T H F lambda omega M N hM)).symm

/-- These are projections of the TRUE joint image. Rectangular extension
below uses zero coefficients outside that image, not an independence
assertion about the original factor labels. -/
def jointZCarrier (U : Finset Source) : Finset ℕ := (U.image output).image Prod.fst
def jointYCarrier (U : Finset Source) : Finset ℤ := (U.image output).image Prod.snd

theorem joint_beta_rectangular_extension (U : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (K : Output → ℂ) :
    (∑ zy ∈ U.image output, beta U lambda omega zy * K zy) =
      ∑ z ∈ jointZCarrier U, ∑ y ∈ jointYCarrier U,
        beta U lambda omega (z,y) * K (z,y) := by
  have hsub : U.image output ⊆ jointZCarrier U ×ˢ jointYCarrier U := by
    intro zy hzy
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem Prod.fst hzy, Finset.mem_image_of_mem Prod.snd hzy⟩
  have hsum : (∑ zy ∈ U.image output, beta U lambda omega zy * K zy) =
      ∑ zy ∈ jointZCarrier U ×ˢ jointYCarrier U, beta U lambda omega zy * K zy := by
    apply Finset.sum_subset hsub
    intro zy _hzy hn
    have hz : beta U lambda omega zy = 0 := by
      by_contra hne
      exact hn (beta_ne_zero_mem_image hne)
    simp only [hz, zero_mul]
  simpa only [Finset.sum_product] using hsum

/-- An arbitrary actual source restriction U may be a closed-t row,
an original sign/dyadic-f block, or a further retained gcd slice. The
coefficient remains its original owned beta(U); mixed pairs are not
identified with same-chart pairs. -/
def carrierLevelSeries (U : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (M N : ℝ) (q z : ℕ) (a : ℤ) : ℂ :=
  actualCommonScalar q z N * ∑ y ∈ jointYCarrier U,
    beta U lambda omega (z,y) * ∑' mode : ℤ, frequency M q a y (z : ℤ) mode

/-- Exact c,z source disintegration applies before any norm. A genuine
actual closed-t/fBlock restriction can therefore be inserted AFTER its
original upstream inequality with the original cost. -/
theorem original_carrier_eq_sum_c_level_series (U : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N C : ℝ) (a : ℤ) :
    (∑ s ∈ U, weight lambda omega s * completedKernel M N C a (output s)) =
      ∑ q ∈ Ioc 0 (Nat.floor (10*C)), ∑ z ∈ jointZCarrier U,
        carrierLevelSeries U lambda omega M N q z a := by
  rw [weighted_pushforward, joint_beta_rectangular_extension]
  simp only [completedKernel, Finset.mul_sum]
  calc
    _ = ∑ z ∈ jointZCarrier U, ∑ q ∈ Ioc 0 (Nat.floor (10*C)),
        ∑ y ∈ jointYCarrier U,
          beta U lambda omega (z,y) *
            (if q.Coprime z then (scaledDyadicCutoff N q : ℂ) *
              ∑' mode : ℤ, frequency M q a y (z : ℤ) mode else 0) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact Finset.sum_comm
    _ = ∑ q ∈ Ioc 0 (Nat.floor (10*C)), ∑ z ∈ jointZCarrier U,
        ∑ y ∈ jointYCarrier U,
          beta U lambda omega (z,y) *
            (if q.Coprime z then (scaledDyadicCutoff N q : ℂ) *
              ∑' mode : ℤ, frequency M q a y (z : ℤ) mode else 0) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro z hz
      unfold carrierLevelSeries actualCommonScalar
      by_cases hqz : q.Coprime z
      · simp only [if_pos hqz, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      · simp only [if_neg hqz, mul_zero, zero_mul, Finset.sum_const_zero]

/-- The original owned beta(U) has no completed-m argument. Absolute
summability therefore binds its FULL original series to the finite
Kloosterman operator with the ACTUAL all-mode left alias. This applies
equally to the native closed-t/sign-f blocks; no raw-base chart identity
or independent coefficient-factorization hypothesis occurs. -/
theorem carrierLevelSeries_eq_operator_pairing (U : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N : ℝ) (hM : 0 < M)
    (q z : ℕ) [NeZero q] (a : ℤ) :
    carrierLevelSeries U lambda omega M N q z a =
      ∑ u : ZMod q, actualFullLeftCollision q z M N u *
        originalOperator q
          (packetRightCoefficient q (jointYCarrier U)
            (fun y => beta U lambda omega (z,y)) a) u := by
  let right := packetRightCoefficient q (jointYCarrier U)
    (fun y => beta U lambda omega (z,y)) a
  let left (mode : ℤ) := actualLeftCollision q z {mode} (fun _ => 1) M N
  have hpoint (mode : ℤ) :
      actualCommonScalar q z N * ∑ y ∈ jointYCarrier U,
        beta U lambda omega (z,y) * frequency M q a y (z : ℤ) mode =
      ∑ u : ZMod q, left mode u * originalOperator q right u := by
    calc
      _ = separablePhysicalPacket q {mode} (jointYCarrier U)
          (fun _ => actualCommonScalar q z N * 1)
          (fun y => beta U lambda omega (z,y)) M a (z : ℤ) := by
        simp only [separablePhysicalPacket, Finset.sum_singleton, mul_one,
          Finset.mul_sum, mul_assoc]
      _ = separableBilinear q (left mode) right :=
        separablePhysicalPacket_eq_separableBilinear q {mode} (jointYCarrier U)
          (fun _ => actualCommonScalar q z N * 1)
          (fun y => beta U lambda omega (z,y)) M a (z : ℤ)
      _ = _ := separableBilinear_eq_operator_pairing q (left mode) right
  have hys (y : ℤ) : Summable (fun mode : ℤ =>
      beta U lambda omega (z,y) * frequency M q a y (z : ℤ) mode) :=
    (frequency_summable M hM q (NeZero.pos q) a y (z : ℤ)).mul_left _
  have hswap : (∑ y ∈ jointYCarrier U, beta U lambda omega (z,y) *
      ∑' mode : ℤ, frequency M q a y (z : ℤ) mode) =
      ∑' mode : ℤ, ∑ y ∈ jointYCarrier U,
        beta U lambda omega (z,y) * frequency M q a y (z : ℤ) mode := by
    simp_rw [← tsum_mul_left]
    exact (Summable.tsum_finsetSum (fun y hy => hys y)).symm
  have hleft (u : ZMod q) : Summable (fun mode : ℤ => left mode u) :=
    (actualLeftCollision_singleton_summable_norm q z hM N u).of_norm
  calc
    _ = ∑' mode : ℤ, actualCommonScalar q z N *
        ∑ y ∈ jointYCarrier U,
          beta U lambda omega (z,y) * frequency M q a y (z : ℤ) mode := by
      unfold carrierLevelSeries
      rw [hswap, tsum_mul_left]
    _ = ∑' mode : ℤ, ∑ u : ZMod q,
        left mode u * originalOperator q right u := tsum_congr hpoint
    _ = ∑ u : ZMod q, (∑' mode : ℤ, left mode u) * originalOperator q right u := by
      rw [Summable.tsum_finsetSum (fun u _ => (hleft u).mul_right _)]
      simp only [tsum_mul_right]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [← actualFullLeftCollision_eq_tsum_singletons q z M N u]

/-- A real analytic bound on the COMPLETE original series, rather than
a chosen finite-m source. The 9*M*(M+q) factor is DERIVED from actual
positive-cutoff Parseval and the sharp complete Kloosterman operator.
The right energy still contains all original signed collisions. -/
theorem carrierLevelSeries_norm_sq_le (U : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (M N : ℝ) (hM : 0 < M)
    (q z : ℕ) [NeZero q] (a : ℤ) :
    ‖carrierLevelSeries U lambda omega M N q z a‖^2 ≤
      9 * M * (M + (q : ℝ)) *
        energy q (packetRightCoefficient q (jointYCarrier U)
          (fun y => beta U lambda omega (z,y)) a) := by
  let right := packetRightCoefficient q (jointYCarrier U)
    (fun y => beta U lambda omega (z,y)) a
  have hsource : carrierLevelSeries U lambda omega M N q z a =
      separableBilinear q (actualFullLeftCollision q z M N) right := by
    rw [carrierLevelSeries_eq_operator_pairing U lambda omega M N hM q z a]
    exact (separableBilinear_eq_operator_pairing q
      (actualFullLeftCollision q z M N) right).symm
  have hbase := separableBilinear_norm_sq_le q (actualFullLeftCollision q z M N) right
  rw [← hsource] at hbase
  have hright : 0 ≤ energy q right := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hleft := actualFullLeftCollision_energy_le q z hM N
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  calc
    _ ≤ (q : ℝ)^2 * (energy q (actualFullLeftCollision q z M N) * energy q right) := hbase
    _ ≤ (q : ℝ)^2 * ((9*(M/(q : ℝ))*(1+M/(q : ℝ))) * energy q right) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hleft hright) (sq_nonneg _)
    _ = _ := by
      dsimp only [right]
      field_simp [hq.ne']
      <;> ring

/-- The full literal original completedPiece is included, with its
genuine c range, f!=0 and both original t-unit gates. Applications to
chart/fBlock sources use original_carrier_eq_sum_c_level_series above
after their actual upstream split, retaining that split's cost. -/
theorem completedPiece_eq_sum_c_level_series (A : ℕ) (a : ℤ)
    (T : Finset ℕ) (H : ℕ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (M N B C F : ℝ) :
    let U := carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))
    completedPiece A a T H lambda omega M N B C F =
      ∑ q ∈ Ioc 0 (Nat.floor (10*C)), ∑ z ∈ jointZCarrier U,
        carrierLevelSeries U lambda omega M N q z a := by
  dsimp only
  rw [completedPiece_eq_source]
  exact original_carrier_eq_sum_c_level_series _ lambda omega M N C a

end
end ImbalancedChen.Part3.ActualCompletedAllModeBridge20261026b
