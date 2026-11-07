import ImbalancedChen.P5zMarkedPrimeFamilyVariableDensity
import ImbalancedChen.CurrentChenUpsilon8SharpKPhysicalPP
import ImbalancedChen.P5U8SharpKSourceMass
import ImbalancedChen.P5OriginalFixedDensitySupplierAssembly

/-! SOURCE ONLY / UNCOMPILED. Actual original U8 sharp-density route and
original h8 terminal slot. Independent P2 U8 integral certificate remains
OPEN; no U8 mean, source mass, small-prime or coprime target is a premise. -/
namespace ImbalancedChen
noncomputable section
open Filter
open scoped BigOperators
open Classical
open P5U8SharpKSource

/-- The literal marked physical rank-three source; no receiver-prime gate. -/
def p5z_u8MarkedSource (N : ℕ) : Finset (Fin 3 → Fin (N + 1)) :=
  (Part3.labelledPrimeTuples 3 N).filter (fun u => physicalWeight N u ≠ 0)

theorem p5z_u8MarkedSource_subset (N : ℕ) :
    p5z_u8MarkedSource N ⊆ Part3.labelledPrimeTuples 3 N := Finset.filter_subset _ _

/-- Restricting only zero-weight labels changes no signed test sum. -/
theorem p5z_u8Marked_test_sum (N : ℕ) (G : (Fin 3 → Fin (N + 1)) → ℝ) :
    (∑ u ∈ p5z_u8MarkedSource N, physicalWeight N u * G u) =
      ∑ u ∈ Part3.labelledPrimeTuples 3 N, physicalWeight N u * G u := by
  unfold p5z_u8MarkedSource
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h : physicalWeight N u = 0 <;> simp [h]

theorem p5z_u8Marked_mass_eq_card (N : ℕ) :
    p5z_labelledMass (p5z_u8MarkedSource N) (physicalWeight N) = ((arithmeticTriples N).card : ℝ) := by
  have h := physicalWeight_sum N (fun _ => 1)
  have hmarked := p5z_u8Marked_test_sum N (fun _ => 1)
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h hmarked
  exact hmarked.trans h.symm

/-- Marked source and the original arithmetic product weight count the
same prime receivers, before adding the actual unit fibres. -/
theorem p5z_u8_eq_markedPrimeMass_add_units (N : ℕ) :
    currentChenUpsilon8 N =
      p5z_labelledPrimeMass (p5z_u8MarkedSource N) Part3.labelledProduct (physicalWeight N) N +
        ((currentChenUpsilon8UnitFibres N).card : ℝ) := by
  have hphys := physicalWeight_sum N (fun m => if m < N ∧ Nat.Prime (N - m) then 1 else 0)
  have hprod := productWeight_sum N (fun m => if m < N ∧ Nat.Prime (N - m) then 1 else 0)
  have hmarked := p5z_u8Marked_test_sum N
    (fun u => if Part3.labelledProduct u < N ∧ Nat.Prime (N - Part3.labelledProduct u) then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at hphys hprod hmarked
  have hsame : p5z_labelledPrimeMass (Finset.range N) id (productWeight N) N =
      p5z_labelledPrimeMass (p5z_u8MarkedSource N) Part3.labelledProduct (physicalWeight N) N := by
    exact (hprod.trans hphys).trans hmarked.symm
  rw [currentChenUpsilon8_eq_primeMass_add_units, hsame]

/-- The generic marked coefficient is exactly the ACTUAL sharpK U8 PP
coefficient on every physical prime tuple. -/
theorem p5z_u8_markedPhysicalPP_eq (N : ℕ) (D : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError 3 N N D rho
      (p5z_markedPhysicalWeight (p5z_u8MarkedSource N) (physicalWeight N)) =
      Part3.primeProductSignedError 3 N N D rho (physicalWeight N) := by
  unfold Part3.primeProductSignedError
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  apply Finset.sum_congr rfl
  intro u hu
  have heq : p5z_markedPhysicalWeight (p5z_u8MarkedSource N) (physicalWeight N) u = physicalWeight N u := by
    by_cases h : physicalWeight N u = 0
    · simp only [p5z_markedPhysicalWeight, h, ite_self]
    · have hs : u ∈ p5z_u8MarkedSource N := Finset.mem_filter.mpr ⟨hu, h⟩
      simp only [p5z_markedPhysicalWeight, if_pos hs]
  rw [heq]

/-- Actual U8 mean at the SAME arbitrary nonnegative density k. All mass,
small-prime, coprime, unit and majorant suppliers are discharged inside. -/
theorem p5z_eventually_u8_le_kJ_of_fixed_actual_rho
    (k nu r e scopeNu : ℝ) (hk : 0 ≤ k) (hnu : 0 < nu) (he : 0 < e)
    (he8 : e < 1 / 8) (heR : e ^ 2 ≤ r) (hnur : nu * r < 1) (hscopeNu : 0 ≤ scopeNu)
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) (Licensed : ℕ → Prop)
    (hlicensed : ∀ᶠ N : ℕ in atTop, Even N → Licensed N)
    (hcap : ∀ᶠ N : ℕ in atTop, Even N → Licensed N → (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ))
    (hscope : ∀ᶠ N : ℕ in atTop, Even N → Licensed N → ∀ d : ℕ,
      d ∈ attachedUpperModuli nu r e retain cap N →
      attachedUpperCoefficient nu r e retain cap N d ≠ 0 → (d : ℝ) ≤ (N : ℝ) ^ scopeNu)
    (hdensity : ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      physicalDensitySum (attachedUpperModuli nu r e retain cap N)
        (attachedUpperCoefficient nu r e retain cap N) ≤ k * (singularSeries N / Real.log (N : ℝ)))
    (hPP : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e retain cap N)
        (attachedUpperCoefficient nu r e retain cap N) (physicalWeight N)| ≤
          C * (N : ℝ) / Real.log (N : ℝ) ^ 3) :
    ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N → currentChenUpsilon8 N ≤
      (k * currentChenUpsilon8HarmonicIntegral + eta) * singularNormalization N := by
  have hW : ∀ N, ∀ u ∈ p5z_u8MarkedSource N, 0 ≤ physicalWeight N u ∧ physicalWeight N u ≤ 1 := by
    intro N u hu
    constructor
    · unfold physicalWeight
      split_ifs <;> norm_num
    · exact (le_abs_self _).trans (physicalWeight_abs_le_one N u)
  have hsourceCap : ∀ N, ∀ u ∈ p5z_u8MarkedSource N, Part3.labelledProduct u ≤ N := by
    intro N u hu
    exact (physicalWeight_support_data (Finset.mem_filter.mp hu).2).2.2.1.le
  have hrough : ∀ᶠ N : ℕ in atTop, Even N → ∀ u ∈ p5z_u8MarkedSource N, ∀ i,
      (N : ℝ) ^ (417 / 5000 : ℝ) ≤ ((u i).val : ℝ) :=
    Filter.Eventually.of_forall (fun N _ u hu i => physicalWeight_lower_power (Finset.mem_filter.mp hu).2 i)
  have hmass : ∀ eta : ℝ, 0 < eta → ∀ᶠ N : ℕ in atTop, Even N →
      p5z_labelledMass (p5z_u8MarkedSource N) (physicalWeight N) ≤
        (currentChenUpsilon8HarmonicIntegral + eta) * ((N : ℝ) / Real.log (N : ℝ)) := by
    intro eta heta
    filter_upwards [P5U8SharpKSourceMassSourceOnly.eventually_arithmeticTriples_mass_le_harmonicIntegral eta heta]
      with N hN
    intro _
    rw [p5z_u8Marked_mass_eq_card]
    exact hN
  have hPPmarked : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N → Licensed N →
      |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e retain cap N)
        (attachedUpperCoefficient nu r e retain cap N)
        (p5z_markedPhysicalWeight (p5z_u8MarkedSource N) (physicalWeight N))| ≤
          C * (N : ℝ) / Real.log (N : ℝ) ^ 3 := by
    obtain ⟨C, hC, hbound⟩ := hPP
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound] with N hN
    intro hEven hL
    rw [p5z_u8_markedPhysicalPP_eq]
    exact hN hEven hL
  have hprime := p5z_eventually_markedFamily_upper_of_actual_rho_with_density k hk
    3 (by norm_num) p5z_u8MarkedSource physicalWeight p5z_u8MarkedSource_subset
    1 currentChenUpsilon8HarmonicIntegral (417 / 5000) (by norm_num)
    P5U8LiteralPrimeFibreMassSourceOnly.harmonicIntegral_nonneg (by norm_num)
    hW hsourceCap hrough hmass nu r e scopeNu hnu he he8 heR hnur hscopeNu
    retain cap Licensed hlicensed hcap hscope hdensity hPPmarked
  intro eta heta
  have hhalf := half_pos heta
  filter_upwards [hprime (eta / 2) hhalf,
    eventually_units_add_diagonal_negligible (eta / 2) hhalf] with N hprimeN hunitN
  intro hEven
  rw [p5z_u8_eq_markedPrimeMass_add_units]
  have hp := hprimeN hEven
  have hd0 : (0 : ℝ) ≤ (diagonalTriples N).card := Nat.cast_nonneg _
  nlinarith only [hp, hunitN, hd0]

end ImbalancedChen

namespace ImbalancedChen.P5OriginalCoefficientArithmetic
noncomputable section
open Filter
open P5U8SharpKSource

def p5z_originalU8UpperIntegralEndpoint : ℝ := savedU8 / K0
def p5z_originalU8LowerIntegralEndpoint : ℝ := lowerU8AtK0 / K0

theorem p5z_originalU8_integral_endpoints_exact :
    p5z_originalU8UpperIntegralEndpoint =
      ((4904703865205402441361491 : ℝ) / 1208925819614629174706176) / ((67619 : ℝ) / 10000) ∧
    p5z_originalU8LowerIntegralEndpoint =
      ((21065542644621920270107869035005941 : ℝ) / 5192296858534827628530496329220096) /
        ((67619 : ℝ) / 10000) := by
  norm_num [p5z_originalU8UpperIntegralEndpoint, p5z_originalU8LowerIntegralEndpoint,
    savedU8, lowerU8AtK0, K0]

/-- Independent P2 integral inequalities imply the original U8 envelope;
the LOWER Simpson endpoint is the slope. Neither certificate is asserted. -/
theorem p5z_originalU8_envelope_of_integral_certificates
    (hUpper : currentChenUpsilon8HarmonicIntegral ≤ p5z_originalU8UpperIntegralEndpoint)
    (hLower : p5z_originalU8LowerIntegralEndpoint ≤ currentChenUpsilon8HarmonicIntegral) :
    fixedProductDensityCoefficient * currentChenUpsilon8HarmonicIntegral ≤
      U8Envelope fixedProductDensityCoefficient := by
  have hK0 : 0 < K0 := by norm_num [K0]
  have hup : K0 * currentChenUpsilon8HarmonicIntegral ≤ savedU8 := by
    simpa only [mul_comm] using (le_div_iff₀ hK0).mp hUpper
  have hk : fixedProductDensityCoefficient ≤ K0 := allowedDensityDelta_below_original_anchors.2.le
  exact complete_switched_cost_envelope currentChenUpsilon8HarmonicIntegral savedU8
    lowerU8AtK0 fixedProductDensityCoefficient hup hLower hk

/-- Exact original h8 output, with policy density chosen at the SAME original
fixed k. Source mass, small-prime, coprime, units and majorant are discharged.
Genuine policy integral/certificate, independent P2 J8 certificates, active
scope, geometric licence and actual physical PP remain explicit obligations. -/
theorem p5z_original_h8_of_actual_full_policy
    (nu r epsilonMax rawBound scopeNu : ℝ) (hnu : 0 < nu) (hr : 0 < r) (hnur : nu * r < 1)
    (hepsilonMax : 0 < epsilonMax) (hscopeNu : 0 ≤ scopeNu)
    (retainOdd : ℝ → ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (integral : ℝ → ℝ) (Licensed : ℝ → ℕ → Prop)
    (hUpper : currentChenUpsilon8HarmonicIntegral ≤ p5z_originalU8UpperIntegralEndpoint)
    (hLower : p5z_originalU8LowerIntegralEndpoint ≤ currentChenUpsilon8HarmonicIntegral)
    (hcap : ∀ᶠ N : ℕ in atTop, Even N → (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ))
    (hIntegral : ∀ e : ℝ, 0 < e → e < epsilonMax →
      Tendsto (fun N : ℕ =>
        reciprocalTotientDensity
          (fixedRoughSupport (retainOdd e N) N (cap N) 0 ((N : ℝ) ^ (nu * r)))
          (fixedRoughCoefficient (retainOdd e N) N (cap N) 0 ((N : ℝ) ^ (nu * r))) *
            Real.log (N : ℝ) / singularSeries N)
        (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (nhds (integral e)))
    (hCertificate : ∀ e : ℝ, 0 < e → e < epsilonMax → integral e ≤ rawBound)
    (hgap : rawBound < fixedProductDensityCoefficient)
    (hlicensed : ∀ e : ℝ, 0 < e → e < 1 / 8 → e < epsilonMax → e ^ 2 ≤ r →
      ∀ᶠ N : ℕ in atTop, Even N → Licensed e N)
    (hscope : ∀ e : ℝ, 0 < e → e < 1 / 8 → e < epsilonMax → e ^ 2 ≤ r →
      ∀ᶠ N : ℕ in atTop, Even N → Licensed e N → ∀ d : ℕ,
        d ∈ attachedUpperModuli nu r e (retainOdd e) cap N →
        attachedUpperCoefficient nu r e (retainOdd e) cap N d ≠ 0 → (d : ℝ) ≤ (N : ℝ) ^ scopeNu)
    (hPP : ∀ e : ℝ, 0 < e → e < 1 / 8 → e < epsilonMax → e ^ 2 ≤ r →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, Even N → Licensed e N →
        |Part3.primeProductSignedError 3 N N (attachedUpperModuli nu r e (retainOdd e) cap N)
          (attachedUpperCoefficient nu r e (retainOdd e) cap N) (physicalWeight N)| ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ 3) :
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop, Even N → currentChenUpsilon8 N ≤
      (U8Envelope fixedProductDensityCoefficient + delta) * singularNormalization N := by
  have hcapF : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ) := by
    rw [Filter.eventually_inf_principal]
    filter_upwards [hcap] with N hN
    exact fun hposEven => hN hposEven.2
  obtain ⟨e, he, he8, heMax, heR, N₀, _hN₀, hdensity⟩ :=
    exists_actualSmallRoughRho_density_le_of_full_policy_limits nu r epsilonMax rawBound
      fixedProductDensityCoefficient hnu hr hepsilonMax retainOdd cap integral
      hcapF hIntegral hCertificate hgap
  have hcapFixed : ∀ᶠ N : ℕ in atTop, Even N → Licensed e N →
      (N : ℝ) ^ (nu * r) ≤ (cap N : ℝ) := by
    filter_upwards [hcap] with N hN
    exact fun hEven _ => hN hEven
  have hdensityFixed : ∀ᶠ N : ℕ in atTop, Even N → Licensed e N →
      physicalDensitySum (attachedUpperModuli nu r e (retainOdd e) cap N)
        (attachedUpperCoefficient nu r e (retainOdd e) cap N) ≤
          fixedProductDensityCoefficient * (singularSeries N / Real.log (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop N₀] with N hN
    exact fun hEven _ => hdensity N hN hEven
  have hk : 0 ≤ fixedProductDensityCoefficient := by
    norm_num [fixedProductDensityCoefficient, currentK, allowedDensityDelta]
  have hraw := p5z_eventually_u8_le_kJ_of_fixed_actual_rho fixedProductDensityCoefficient
    nu r e scopeNu hk hnu he he8 heR hnur hscopeNu (retainOdd e) cap (Licensed e)
    (hlicensed e he he8 heMax heR) hcapFixed (hscope e he he8 heMax heR)
    hdensityFixed (hPP e he he8 heMax heR)
  have hcoef := p5z_originalU8_envelope_of_integral_certificates hUpper hLower
  intro delta hdelta
  filter_upwards [hraw delta hdelta] with N hN
  intro hEven
  have hH : 0 ≤ singularNormalization N :=
    div_nonneg (mul_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  exact (hN hEven).trans (mul_le_mul_of_nonneg_right (add_le_add_right hcoef delta) hH)

end
end ImbalancedChen.P5OriginalCoefficientArithmetic
