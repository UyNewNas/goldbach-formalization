import Mathlib
import ImbalancedChen.Part3TwoLongP2DivisorEnvelope
import ImbalancedChen.Part3TwoLongN2FourierDecay

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Internal P2 on the actual centered P1 modes. The only new external input
is the standard composite-modulus Weil estimate for a complete classical
Kloosterman sum, stated for arbitrary integer parameters. Primitive-center
gcd removal, both axes, the Ramanujan mean, actual Fourier decay and the
absolutely convergent two-integer sum are proved here.
-/
namespace ImbalancedChen.Part3.TwoLongInternalP2Modes
noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators SchwartzMap FourierTransform
open ImbalancedChen.Part3.TwoLongLiteralMellinModes
open ImbalancedChen.Part3.TwoLongInternalP2FrequencySums
open ImbalancedChen.Part3.TwoLongFilteredIntegerFrequency
open ImbalancedChen.Part3.TwoLongP2DivisorEnvelope
open ImbalancedChen.Part3.TwoLongP1AxisCancellation
open ImbalancedChen.Part3.TwoLongN2FourierDecay
open ImbalancedChen.Part3.OriginalSmoothPoissonTail
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode

/-- Genuine classical input, not P1, P2, E4 or an assumed profile estimate.
The Kloosterman sum is the existing complete production sum, including
its literal inverseResidue convention. No restriction on the integers r,s.
Source: the composite Weil bound used in the original PP module, 271-273.
Its formal supplier is outstanding and explicitly registered. -/
def CompositeWeilInput : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ (r s : ℤ),
    ‖kloosterman q r s‖ ≤ (q.divisors.card : ℝ) * Real.sqrt (q : ℝ) *
      Real.sqrt (Nat.gcd (Nat.gcd r.natAbs s.natAbs) q : ℝ)

/-- Removing the literal primitive center from the THREE-variable gcd.
This applies also to negative and zero frequencies. -/
theorem primitive_center_gcd {q : ℕ} (hq : 0 < q) (b j k : ℤ)
    (hb : IsUnit (b : ZMod q)) :
    Nat.gcd (Nat.gcd (b*j).natAbs k.natAbs) q =
      Nat.gcd (Nat.gcd j.natAbs k.natAbs) q := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hbc : Nat.Coprime b.natAbs q :=
    (isUnit_intCast_iff_natAbs_coprime b).mp hb
  have hc : q.gcd (b*j).natAbs = q.gcd j.natAbs := by
    rw [Int.natAbs_mul,Nat.mul_comm b.natAbs j.natAbs]
    exact hbc.gcd_mul_right_cancel_right _
  calc
    _ = Nat.gcd (Nat.gcd (b*j).natAbs q) k.natAbs := Nat.gcd_right_comm _ _ _
    _ = Nat.gcd (Nat.gcd j.natAbs q) k.natAbs := by
      rw [Nat.gcd_comm (b*j).natAbs q,hc,Nat.gcd_comm q j.natAbs]
    _ = _ := (Nat.gcd_right_comm _ _ _).symm

theorem centeredKernel_norm_le (hWeil : CompositeWeilInput)
    {q : ℕ} (hq : 0 < q) (b j k : ℤ) (hb : IsUnit (b : ZMod q)) :
    ‖centeredKernel q b j k‖ ≤
      (q.divisors.card : ℝ)*Real.sqrt (q : ℝ)*
        Real.sqrt (Nat.gcd (Nat.gcd j.natAbs k.natAbs) q : ℝ) +
      ‖ramanujan q j‖*‖ramanujan q k‖/(Nat.totient q : ℝ) := by
  have hw := hWeil q hq (b*j) k
  rw [primitive_center_gcd hq b j k hb] at hw
  calc
    _ ≤ ‖kloosterman q (b*j) k‖ +
        ‖ramanujan q j * ramanujan q k / (Nat.totient q : ℂ)‖ := norm_sub_le _ _
    _ = ‖kloosterman q (b*j) k‖ +
        ‖ramanujan q j‖*‖ramanujan q k‖/(Nat.totient q : ℝ) := by
      simp only [norm_div,norm_mul,Complex.norm_natCast]
    _ ≤ _ := add_le_add_right hw _

/-- Both actual divisor filters, including the exact 1/phi(q) mean.
This is a pointwise bound on the original kernel, not an invented series. -/
theorem weighted_centeredKernel_le (hWeil : CompositeWeilInput)
    (H K : ℝ) {q : ℕ} (hq : 0 < q) (b j k : ℤ) (hb : IsUnit (b : ZMod q)) :
    baseDecay H j*baseDecay K k*‖centeredKernel q b j k‖ ≤
      centeredEnvelope H K q (j,k) := by
  have hH := multipleDecay_nonneg H 1 j
  have hK := multipleDecay_nonneg K 1 k
  have hR := mul_le_mul (weighted_ramanujan_le H q hq j)
    (weighted_ramanujan_le K q hq k)
    (mul_nonneg hK (norm_nonneg _)) (ramanujanEnvelope_nonneg H q j)
  calc
    _ ≤ baseDecay H j*baseDecay K k*
        ((q.divisors.card : ℝ)*Real.sqrt (q : ℝ)*
          Real.sqrt (Nat.gcd (Nat.gcd j.natAbs k.natAbs) q : ℝ) +
          ‖ramanujan q j‖*‖ramanujan q k‖/(Nat.totient q : ℝ)) :=
      mul_le_mul_of_nonneg_left (centeredKernel_norm_le hWeil hq b j k hb)
        (mul_nonneg hH hK)
    _ = (q.divisors.card : ℝ)*Real.sqrt (q : ℝ)*
        (baseDecay H j*baseDecay K k*
          Real.sqrt (Nat.gcd (Nat.gcd j.natAbs k.natAbs) q : ℝ)) +
        (Nat.totient q : ℝ)⁻¹*
          ((baseDecay H j*‖ramanujan q j‖)*(baseDecay K k*‖ramanujan q k‖)) := by ring
    _ ≤ (q.divisors.card : ℝ)*Real.sqrt (q : ℝ)*weilEnvelope H K q (j,k) +
        (Nat.totient q : ℝ)⁻¹*(ramanujanEnvelope H q j*ramanujanEnvelope K q k) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (weighted_sqrt_gcd_le H K q hq j k) (by positivity))
        (mul_le_mul_of_nonneg_left hR (by positivity))
    _ = _ := rfl

theorem N2_nonneg (f : ℝ → ℂ) : 0 ≤ N2 f :=
  add_nonneg (integral_nonneg (fun _ => norm_nonneg _))
    (integral_nonneg (fun _ => norm_nonneg _))

/-- The frequency scale is exactly H=q/U; no lower bound H>=1 is used. -/
theorem fourier_nonzero_le (F : 𝓢(ℝ, ℂ)) {q : ℕ} (hq : 0 < q)
    {U : ℝ} (hU : 0 < U) (j : ℤ) (hj : j ≠ 0) :
    ‖(𝓕 F) ((U/q)*(j : ℝ))‖ ≤
      (fourierDecayConstant*N2 (F : ℝ → ℂ))*baseDecay ((q : ℝ)/U) j := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have he : |(U/(q : ℝ))*(j : ℝ)| = |(j : ℝ)|/((q : ℝ)/U) := by
    rw [show (U/(q : ℝ))*(j : ℝ) = (j : ℝ)/((q : ℝ)/U) by
      field_simp [hqR.ne',hU.ne'] <;> ring]
    rw [abs_div,abs_of_pos (div_pos hqR hU)]
  have hf := norm_fourier_le_N2 F ((U/q)*(j : ℝ))
  rw [he] at hf
  simpa only [baseDecay,multipleDecay,if_neg hj,one_mul,mul_one_div] using hf

def centeredMode (F G : 𝓢(ℝ, ℂ)) (U V : ℝ) (q : ℕ) (b : ℤ)
    (p : ℤ × ℤ) : ℂ :=
  (𝓕 F) ((U/q)*(p.1 : ℝ)) * (𝓕 G) ((V/q)*(p.2 : ℝ)) *
    centeredKernel q b p.1 p.2

/-- The full original Fourier coefficients are retained on both axes;
they are killed by the proved centered kernel identities, not by decay. -/
theorem centeredMode_norm_le (hWeil : CompositeWeilInput)
    (F G : 𝓢(ℝ, ℂ)) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    {q : ℕ} (hq : 0 < q) (b : ℤ) (hb : IsUnit (b : ZMod q)) (p : ℤ × ℤ) :
    ‖centeredMode F G U V q b p‖ ≤
      ((fourierDecayConstant*N2 (F : ℝ → ℂ))*(fourierDecayConstant*N2 (G : ℝ → ℂ))) *
        centeredEnvelope ((q : ℝ)/U) ((q : ℝ)/V) q p := by
  have hA : 0 ≤ fourierDecayConstant*N2 (F : ℝ → ℂ) :=
    mul_nonneg fourierDecayConstant_pos.le (N2_nonneg _)
  have hB : 0 ≤ fourierDecayConstant*N2 (G : ℝ → ℂ) :=
    mul_nonneg fourierDecayConstant_pos.le (N2_nonneg _)
  by_cases hj : p.1=0
  · simp only [centeredMode,hj,centeredKernel_left_axis hq,mul_zero,norm_zero]
    exact mul_nonneg (mul_nonneg hA hB) (centeredEnvelope_nonneg _ _ _ _)
  by_cases hk : p.2=0
  · simp only [centeredMode,hk,centeredKernel_right_axis hq b p.1 hb,mul_zero,norm_zero]
    exact mul_nonneg (mul_nonneg hA hB) (centeredEnvelope_nonneg _ _ _ _)
  have hf := fourier_nonzero_le F hq hU p.1 hj
  have hg := fourier_nonzero_le G hq hV p.2 hk
  calc
    _ = ‖(𝓕 F) ((U/q)*(p.1 : ℝ))‖*‖(𝓕 G) ((V/q)*(p.2 : ℝ))‖*
        ‖centeredKernel q b p.1 p.2‖ := by simp only [centeredMode,norm_mul]
    _ ≤ ((fourierDecayConstant*N2 (F : ℝ → ℂ))*baseDecay ((q : ℝ)/U) p.1)*
        ((fourierDecayConstant*N2 (G : ℝ → ℂ))*baseDecay ((q : ℝ)/V) p.2)*
        ‖centeredKernel q b p.1 p.2‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hf hg (norm_nonneg _)
          (mul_nonneg hA (multipleDecay_nonneg _ 1 _))) (norm_nonneg _)
    _ = ((fourierDecayConstant*N2 (F : ℝ → ℂ))*(fourierDecayConstant*N2 (G : ℝ → ℂ)))*
        (baseDecay ((q : ℝ)/U) p.1*baseDecay ((q : ℝ)/V) p.2*
          ‖centeredKernel q b p.1 p.2‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (weighted_centeredKernel_le hWeil _ _ hq b p.1 p.2 hb) (mul_nonneg hA hB)

/-- Actual product-index absolute convergence follows from the proved
divisor envelope. In particular the nested P1 sum can be commuted. -/
theorem centeredMode_norm_summable (hWeil : CompositeWeilInput)
    (F G : 𝓢(ℝ, ℂ)) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    {q : ℕ} (hq : 0 < q) (b : ℤ) (hb : IsUnit (b : ZMod q)) :
    Summable (fun p : ℤ × ℤ => ‖centeredMode F G U V q b p‖) := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hs := (centeredEnvelope_summable (div_pos hqR hU) (div_pos hqR hV) q).mul_left
    ((fourierDecayConstant*N2 (F : ℝ → ℂ))*(fourierDecayConstant*N2 (G : ℝ → ℂ)))
  exact hs.of_nonneg_of_le (fun _ => norm_nonneg _)
    (centeredMode_norm_le hWeil F G hU hV hq b hb)

theorem centeredMode_tsum_le (hWeil : CompositeWeilInput)
    (F G : 𝓢(ℝ, ℂ)) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    {q : ℕ} (hq : 0 < q) (b : ℤ) (hb : IsUnit (b : ZMod q)) :
    ‖∑' j : ℤ, ∑' k : ℤ, centeredMode F G U V q b (j,k)‖ ≤
      ((fourierDecayConstant*N2 (F : ℝ → ℂ))*(fourierDecayConstant*N2 (G : ℝ → ℂ)))*
      (4*((q : ℝ)/U)*((q : ℝ)/V)*
        ((q.divisors.card : ℝ)*Real.sqrt (q : ℝ)*weilConstant +
          (q.divisors.card : ℝ)^2/(Nat.totient q : ℝ))) := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  let A := (fourierDecayConstant*N2 (F : ℝ → ℂ))*(fourierDecayConstant*N2 (G : ℝ → ℂ))
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg fourierDecayConstant_pos.le (N2_nonneg _))
    (mul_nonneg fourierDecayConstant_pos.le (N2_nonneg _))
  have hs := (centeredEnvelope_summable (div_pos hqR hU) (div_pos hqR hV) q).mul_left A
  have hm := centeredMode_norm_summable hWeil F G hU hV hq b hb
  rw [← hm.of_norm.tsum_prod]
  calc
    _ ≤ ∑' p : ℤ × ℤ, A*centeredEnvelope ((q : ℝ)/U) ((q : ℝ)/V) q p :=
      tsum_of_norm_bounded hs.hasSum (centeredMode_norm_le hWeil F G hU hV hq b hb)
    _ = A * ∑' p : ℤ × ℤ, centeredEnvelope ((q : ℝ)/U) ((q : ℝ)/V) q p := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (centeredEnvelope_tsum_le (div_pos hqR hU) (div_pos hqR hV) q) hA

end
end ImbalancedChen.Part3.TwoLongInternalP2Modes
