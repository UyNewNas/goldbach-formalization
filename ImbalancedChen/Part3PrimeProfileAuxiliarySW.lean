import ImbalancedChen.Part3ScaledPrimeProfileSW

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual MediumAtom prime-block supplier. Only alpha is updated: the moving
signed physical residue, factor coefficients, U,V and the original real
interval are retained. The carrier is proved equal to the pinned (u,v]
prime interval. A fixed positive power lower bound U>=scale^theta changes
the logarithmic normalization to the complete scale. The exact independent
auxiliary coprimality remains in the coefficient mean. No UniformSW or
prime-product distribution target is an input.
-/

namespace ImbalancedChen.Part3.PrimeProfileAuxiliarySW20261026b

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open WeightedPrimeIntervalSW20261026b ScaledPrimeProfileSW20261026b

/-- Literal frozen real smooth prime coefficient, in the original atom. -/
def primeProfileAtom (Phi : ℝ → ℝ) (d : MediumAtom) : MediumAtom :=
  { d with alpha := fun n =>
      (weightedPrimeCoefficient (scaledProfile Phi d.U) n : ℂ) }

/-- Real interval conventions match exactly, including a nonintegral U
and a prime at the retained upper endpoint. -/
theorem alphaCarrier_eq_primeSWInterval (d : MediumAtom)
    (hU : 1 ≤ d.U) (hlo : d.U ≤ d.intervalLo)
    (horder : d.intervalLo ≤ d.intervalHi) (hhi : d.intervalHi ≤ 2*d.U) :
    d.alphaCarrier = primeSWInterval d.intervalLo d.intervalHi := by
  have hlo0 : 0 ≤ d.intervalLo := by linarith
  have hhi0 : 0 ≤ d.intervalHi := by linarith
  have htwo0 : 0 ≤ 2*d.U := by linarith
  ext n
  simp only [MediumAtom.alphaCarrier, primeSWInterval, Finset.mem_filter,
    Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hnlo,hnhi⟩,hrealLo,hrealHi⟩
    exact ⟨(Nat.floor_lt hlo0).mpr hrealLo, Nat.le_floor hrealHi⟩
  · rintro ⟨hnlo,hnhi⟩
    have hrealLo : d.intervalLo < (n : ℝ) := (Nat.floor_lt hlo0).mp hnlo
    have hrealHi : (n : ℝ) ≤ d.intervalHi :=
      (show (n : ℝ) ≤ (Nat.floor d.intervalHi : ℝ) by exact_mod_cast hnhi).trans
        (Nat.floor_le hhi0)
    exact ⟨⟨Nat.ceil_le.mpr (hlo.trans hrealLo.le),
      Nat.le_floor (hrealHi.trans hhi)⟩,hrealLo,hrealHi⟩

/-- Definition matching for the original complex SW error. Both auxiliary
and progression moduli are present in the same primitive-coprime mean. -/
theorem primeProfile_auxSWError_eq (Phi : ℝ → ℝ) (d : MediumAtom)
    (hU : 1 ≤ d.U) (hlo : d.U ≤ d.intervalLo)
    (horder : d.intervalLo ≤ d.intervalHi) (hhi : d.intervalHi ≤ 2*d.U)
    (k q b : ℕ) :
    (primeProfileAtom Phi d).auxSWError k q b =
      (betaCoprimeAPDiscrepancy (primeSWInterval d.intervalLo d.intervalHi)
        (weightedPrimeCoefficient (scaledProfile Phi d.U)) q k b : ℂ) := by
  let S := primeSWInterval d.intervalLo d.intervalHi
  let w := weightedPrimeCoefficient (scaledProfile Phi d.U)
  have hcarrier := alphaCarrier_eq_primeSWInterval d hU hlo horder hhi
  have hfirst :
      (∑ n ∈ S, if Nat.ModEq q n b ∧ n.Coprime k then (w n : ℂ) else 0) =
        ((∑ n ∈ S, if n.Coprime k ∧ Nat.ModEq q n b then w n else 0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : n.Coprime k <;> by_cases hm : Nat.ModEq q n b <;> simp [hc,hm]
  have hsecond :
      (∑ n ∈ S, if n.Coprime (k*q) then (w n : ℂ) else 0) =
        ((∑ n ∈ S, if n.Coprime (q*k) then w n else 0 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : n.Coprime (k*q) <;> simp [Nat.mul_comm q k,hc]
  change (∑ n ∈ d.alphaCarrier,
      if Nat.ModEq q n b ∧ n.Coprime k then (w n : ℂ) else 0) -
      (∑ n ∈ d.alphaCarrier, if n.Coprime (k*q) then (w n : ℂ) else 0) /
        (q.totient : ℂ) = _
  rw [hcarrier]
  change (∑ n ∈ S, if Nat.ModEq q n b ∧ n.Coprime k then (w n : ℂ) else 0) -
      (∑ n ∈ S, if n.Coprime (k*q) then (w n : ℂ) else 0) / (q.totient : ℂ) = _
  rw [hfirst,hsecond]
  simp only [betaCoprimeAPDiscrepancy, coprimeMass, Complex.ofReal_sub,
    Complex.ofReal_div, Complex.ofReal_natCast]
  rfl

/-- The actual smooth prime blocks have auxiliary SW of fixed divisor
order one. The complete-scale threshold precedes every original atom,
moving primitive residue, q and independent auxiliary k. U>=x^(2*zeta)
is the instance theta=2*zeta; no bound on k is needed for this supplier. -/
theorem uniformAuxiliarySW_primeProfile {ι : Type*}
    (Phi : ℝ → ℝ) (hPhi : ContDiff ℝ 1 Phi) (F : ι → MediumAtom)
    {theta : ℝ} (htheta : 0 < theta)
    (hgeometry : ∀ i, 1 ≤ (F i).U ∧ (F i).U ≤ (F i).intervalLo ∧
      (F i).intervalLo ≤ (F i).intervalHi ∧ (F i).intervalHi ≤ 2*(F i).U)
    (hscale : ∀ i, 1 ≤ (F i).scale)
    (hpower : ∀ i, (F i).scale^theta ≤ (F i).U) :
    UniformAuxiliarySW (fun i => primeProfileAtom Phi (F i)) 1 := by
  intro A hA
  let B : ℕ := Nat.ceil A
  obtain ⟨C,hC,hSW⟩ := scaled_prime_profile_SW Phi hPhi B
  refine ⟨C/theta^B,div_pos hC (pow_pos htheta B),Real.exp 1,
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
  have hlogComparison : theta * Real.log (F i).scale ≤ Real.log (2*(F i).U) := by
    calc
      theta * Real.log (F i).scale = Real.log ((F i).scale^theta) := by
        rw [Real.log_rpow hXpos]
      _ ≤ Real.log (F i).U := Real.log_le_log
        (Real.rpow_pos_of_pos hXpos theta) (hpower i)
      _ ≤ Real.log (2*(F i).U) := Real.log_le_log hUpos (by linarith)
  have hpowerA : Real.log (F i).scale^A ≤ Real.log (F i).scale^B := by
    have hh := Real.rpow_le_rpow_of_exponent_le hlogX1 (Nat.le_ceil A)
    simpa only [Real.rpow_natCast] using hh
  have hden : theta^B * Real.log (F i).scale^A ≤ Real.log (2*(F i).U)^B := by
    calc
      _ ≤ theta^B * Real.log (F i).scale^B :=
        mul_le_mul_of_nonneg_left hpowerA (pow_nonneg htheta.le B)
      _ = (theta * Real.log (F i).scale)^B := (mul_pow _ _ _).symm
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg htheta.le hlogX.le) hlogComparison B
  have hraw := hSW (F i).U (F i).intervalLo (F i).intervalHi
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 q k (by omega) (by omega) b hb
  change ‖(primeProfileAtom Phi (F i)).auxSWError k q b‖ ≤
    (C/theta^B)*(F i).U*(k.divisors.card : ℝ)^1 / Real.log (F i).scale^A
  rw [primeProfile_auxSWError_eq Phi (F i) hg.1 hg.2.1 hg.2.2.1 hg.2.2.2,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ _ := hraw
    _ ≤ C*(F i).U*(fouvryTau 2 k : ℝ) /
        (theta^B * Real.log (F i).scale^A) :=
      div_le_div_of_nonneg_left (by positivity)
        (mul_pos (pow_pos htheta B) (Real.rpow_pos_of_pos hlogX A)) hden
    _ = _ := by
      simp only [fouvryTau_two, pow_one, div_eq_mul_inv, mul_inv_rev]
      ring

end
end ImbalancedChen.Part3.PrimeProfileAuxiliarySW20261026b
