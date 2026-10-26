import ImbalancedChen.Part3MellinPrimeIntervalSW
import ImbalancedChen.Part3PrimeProfileAuxiliarySW

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual complex Mellin prime blocks have UniformAuxiliarySW only after the
displayed logarithmic frequency restriction is paid. A stronger primary
prime exponent ceil(A+L) is chosen before all varying atoms/frequencies.
The original full auxiliary coprime mean, primitive residue and real
interval remain unchanged. No UniformSW premise or high-modulus PP is used.
-/

namespace ImbalancedChen.Part3.MellinPrimeAuxiliarySW20261026b
noncomputable section
open Classical Filter
open scoped BigOperators Topology
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MellinPrimeIntervalSW20261026b PrimeProfileAuxiliarySW20261026b

def mellinPrimeAtom (Phi : ℝ → ℝ) (t : ℝ) (d : MediumAtom) : MediumAtom :=
  { d with alpha := mellinPrimeCoefficient Phi t d.U }

/-- Literal attachment: no arithmetic mask or replacement mean is hidden
in the passage from the real interval to the original MediumAtom. -/
theorem mellinPrime_auxSWError_eq (Phi : ℝ → ℝ) (t : ℝ) (d : MediumAtom)
    (hU : 1 ≤ d.U) (hlo : d.U ≤ d.intervalLo)
    (huv : d.intervalLo ≤ d.intervalHi) (hhi : d.intervalHi ≤ 2*d.U)
    (k q b : ℕ) :
    (mellinPrimeAtom Phi t d).auxSWError k q b =
      auxiliarySWError (primeSWInterval d.intervalLo d.intervalHi)
        (mellinPrimeCoefficient Phi t d.U) k q b := by
  change auxiliarySWError d.alphaCarrier (mellinPrimeCoefficient Phi t d.U) k q b = _
  rw [alphaCarrier_eq_primeSWInterval d hU hlo huv hhi]

/-- A genuine SW supplier for the actual Mellin-modulated prime-block
family. The log-frequency restriction is mandatory, and the constant and
complete-scale threshold precede every atom, frequency, k,q and residue. -/
theorem uniformAuxiliarySW_mellinPrime {ι : Type*}
    (Phi : ℝ → ℝ) (hPhi : ContDiff ℝ 1 Phi)
    (F : ι → MediumAtom) (frequency : ι → ℝ)
    {theta L : ℝ} (htheta : 0 < theta) (hL : 0 ≤ L)
    (hgeometry : ∀ i, 1 ≤ (F i).U ∧ (F i).U ≤ (F i).intervalLo ∧
      (F i).intervalLo ≤ (F i).intervalHi ∧ (F i).intervalHi ≤ 2*(F i).U)
    (hscale : ∀ i, 1 ≤ (F i).scale)
    (hpower : ∀ i, (F i).scale^theta ≤ (F i).U)
    (hfrequency : ∀ i, |frequency i| ≤ Real.log (F i).scale^L) :
    UniformAuxiliarySW (fun i => mellinPrimeAtom Phi (frequency i) (F i)) 1 := by
  intro A hA
  let B : ℕ := Nat.ceil (A+L)
  obtain ⟨C,hC,hSW⟩ := mellin_prime_interval_SW Phi hPhi B
  refine ⟨2*C/theta^B,div_pos (by positivity) (pow_pos htheta B),Real.exp 1,
    Real.one_lt_exp_iff.mpr (by norm_num),?_⟩
  intro i hx k q b hk hq hb
  have hg := hgeometry i
  have hUpos : 0 < (F i).U := by linarith [hg.1]
  have hXpos : 0 < (F i).scale := zero_lt_one.trans_le (hscale i)
  have hlogX1 : 1 ≤ Real.log (F i).scale := by
    have hh := Real.log_le_log (Real.exp_pos 1) hx
    simpa only [Real.log_exp] using hh
  have hlogX : 0 < Real.log (F i).scale := zero_lt_one.trans_le hlogX1
  have hlogU : 0 < Real.log (2*(F i).U) := Real.log_pos (by linarith [hg.1])
  have hlogComparison : theta*Real.log (F i).scale ≤ Real.log (2*(F i).U) := by
    calc
      theta*Real.log (F i).scale = Real.log ((F i).scale^theta) := by
        rw [Real.log_rpow hXpos]
      _ ≤ Real.log (F i).U := Real.log_le_log
        (Real.rpow_pos_of_pos hXpos theta) (hpower i)
      _ ≤ Real.log (2*(F i).U) := Real.log_le_log hUpos (by linarith)
  have hlogL1 : 1 ≤ Real.log (F i).scale^L := Real.one_le_rpow hlogX1 hL
  have hfreq : 1+|frequency i| ≤ 2*Real.log (F i).scale^L := by
    linarith [hfrequency i]
  have hpowerAL : Real.log (F i).scale^(A+L) ≤ Real.log (F i).scale^B := by
    have hh := Real.rpow_le_rpow_of_exponent_le hlogX1 (Nat.le_ceil (A+L))
    simpa only [Real.rpow_natCast] using hh
  have hden : theta^B*Real.log (F i).scale^(A+L) ≤ Real.log (2*(F i).U)^B := by
    calc
      _ ≤ theta^B*Real.log (F i).scale^B :=
        mul_le_mul_of_nonneg_left hpowerAL (pow_nonneg htheta.le B)
      _ = (theta*Real.log (F i).scale)^B := (mul_pow _ _ _).symm
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg htheta.le hlogX.le) hlogComparison B
  have hraw := hSW (F i).U (F i).intervalLo (F i).intervalHi
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 (frequency i) k q b (by omega) (by omega) hb
  have hnum : C*(1+|frequency i|)*(F i).U*(fouvryTau 2 k : ℝ) ≤
      C*(2*Real.log (F i).scale^L)*(F i).U*(fouvryTau 2 k : ℝ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfreq hC.le) hUpos.le)
      (Nat.cast_nonneg _)
  change ‖(mellinPrimeAtom Phi (frequency i) (F i)).auxSWError k q b‖ ≤
    (2*C/theta^B)*(F i).U*(k.divisors.card : ℝ)^1/Real.log (F i).scale^A
  rw [mellinPrime_auxSWError_eq Phi (frequency i) (F i)
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2]
  calc
    _ ≤ _ := hraw
    _ ≤ C*(2*Real.log (F i).scale^L)*(F i).U*(fouvryTau 2 k : ℝ) /
        Real.log (2*(F i).U)^B :=
      div_le_div_of_nonneg_right hnum (pow_nonneg hlogU.le B)
    _ ≤ C*(2*Real.log (F i).scale^L)*(F i).U*(fouvryTau 2 k : ℝ) /
        (theta^B*Real.log (F i).scale^(A+L)) :=
      div_le_div_of_nonneg_left (by positivity)
        (mul_pos (pow_pos htheta B) (Real.rpow_pos_of_pos hlogX (A+L))) hden
    _ = _ := by
      rw [Real.rpow_add hlogX]
      simp only [fouvryTau_two,pow_one]
      field_simp [(pow_pos htheta B).ne',
        (Real.rpow_pos_of_pos hlogX A).ne', (Real.rpow_pos_of_pos hlogX L).ne']
      <;> ring

end
end ImbalancedChen.Part3.MellinPrimeAuxiliarySW20261026b
