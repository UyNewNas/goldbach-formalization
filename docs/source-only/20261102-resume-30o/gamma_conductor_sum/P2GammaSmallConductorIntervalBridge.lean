import ImbalancedChen.P2GammaConductorScaleThreshold
import ImbalancedChen.P2GammaVariablePrimeSmallConductor

/-! SOURCE ONLY. UNCOMPILED. ZERO FORMAL CREDIT.
This file consumes the implemented O small-conductor prime theorem. It
does not replace that theorem with an SW/BV hypothesis. The finite carrier
bridge retains BOTH quotient projectors, exact phi(r*k), and all repetitions
in the complementary coefficients.
-/

namespace ImbalancedChen.P2GammaSmallConductorIntervalBridge
noncomputable section
open scoped Classical BigOperators Topology
open Set MeasureTheory
open AnalyticNumberTheory.LargeSieve
open P2GammaConvolutionLargeConductor P2GammaExactConductorRegrouping
open P2GammaConductorScaleThreshold
open P2GammaPrimeCharacterSW P2GammaPrimeTargetDeletion
open P2GammaVariablePrimeProfile P2GammaVariablePrimeSmallConductor
open P2GammaPrimeSmallConductorSum
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def paddedRow (S : Finset ℕ) (a : ℕ → ℂ) (n : ℤ) : ℂ :=
  if n.toNat∈S then a n.toNat else 0

theorem sum_integer_interval_nat (P : ℕ) (F : ℤ → ℂ) :
    (∑ n ∈ Finset.Icc (1 : ℤ) (P : ℤ),F n)=
      ∑ n ∈ Finset.Icc 1 P,F (n : ℤ) := by
  refine Finset.sum_bij' (fun n _ => n.toNat) (fun n _ => (n : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  · intro n hn
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hlo,by exact_mod_cast hhi⟩
  · intro n hn
    have hlo := (Finset.mem_Icc.mp hn).1
    exact Int.toNat_of_nonneg (by omega)
  · intro n hn
    simp only [Int.toNat_natCast]
  · intro n hn
    have hlo := (Finset.mem_Icc.mp hn).1
    rw [Int.toNat_of_nonneg (by omega)]

/-- Exact transform of a finite positive row after zero-padding. -/
theorem paddedRow_transform (S : Finset ℕ) (a : ℕ → ℂ) (P k r : ℕ)
    (hS : S⊆Finset.Icc 1 P) (psi : DirichletCharacter ℂ r) :
    (∑ n ∈ Finset.Icc (0+1 : ℤ) (0+P : ℤ),
      unitMask k (paddedRow S a) n*psi (n : ZMod r))=
      rowTransform S a k r psi := by
  simp only [zero_add]
  rw [sum_integer_interval_nat]
  have hf : (Finset.Icc 1 P).filter (fun n => n∈S)=S := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hS h,h⟩⟩
  calc
    _ = ∑ n ∈ (Finset.Icc 1 P).filter (fun n => n∈S),
        (if n.Coprime k then a n else 0)*psi (n : ZMod r) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hs : n∈S <;> by_cases hc : n.Coprime k <;>
        simp [unitMask,paddedRow,hs,hc]
    _ = rowTransform S a k r psi := by rw [hf]; rfl

theorem paddedRow_amplitude (S : Finset ℕ) (a : ℕ → ℂ) (P k r : ℕ)
    (hS : S⊆Finset.Icc 1 P) (psi : PrimitiveCharacter r) :
    rowAmplitude (unitMask k (paddedRow S a)) 0 P r psi=
      ‖rowTransform S a k r psi.1‖ := by
  unfold rowAmplitude
  rw [paddedRow_transform S a P k r hS]

theorem paddedRow_unmasked_transform (S : Finset ℕ) (a : ℕ → ℂ) (P q : ℕ)
    (hS : S⊆Finset.Icc 1 P) (chi : DirichletCharacter ℂ q) :
    (∑ n ∈ Finset.Icc (0+1 : ℤ) (0+P : ℤ),paddedRow S a n*chi (n : ZMod q))=
      ∑ n ∈ S,a n*chi (n : ZMod q) := by
  simpa only [unitMask,Nat.coprime_one_right,if_true,rowTransform] using
    paddedRow_transform S a P 1 q hS chi

/-- The literal progression-minus-q-coprime-mean rectangle. Its complex
coefficients and multiplicities survive exactly. -/
def naturalRectangleDiscrepancy (S T : Finset ℕ) (a b : ℕ → ℂ)
    (target q : ℕ) : ℂ :=
  ∑ m ∈ S,∑ n ∈ T,a m*b n*
    ((P2OriginalGammaUpperLowRankConsumer.gammaKernel target q (m*n) : ℝ) : ℂ)

/-- Exact attachment to the original Gamma kernel. This uses the proved
principal cancellation against the same q-coprime mean, before norms. -/
theorem naturalRectangleDiscrepancy_eq_character
    (S T : Finset ℕ) (a b : ℕ → ℂ) (P V target q : ℕ)
    (hS : S⊆Finset.Icc 1 P) (hT : T⊆Finset.Icc 1 V)
    (hq : 0<q) (htarget : target.Coprime q) :
    naturalRectangleDiscrepancy S T a b target q=
      rectangleCharacterDiscrepancy (paddedRow S a) (paddedRow T b) 0 0 P V q
        ((target : ZMod q)⁻¹) := by
  unfold naturalRectangleDiscrepancy rectangleCharacterDiscrepancy
  simp_rw [paddedRow_unmasked_transform S a P q hS,
    paddedRow_unmasked_transform T b V q hT]
  let c : ℂ := (q.totient : ℂ)⁻¹
  let z : ZMod q := (target : ZMod q)⁻¹
  calc
    _ = ∑ m ∈ S,∑ n ∈ T,∑ chi ∈ nonprincipalCharacters q,
        c*(chi z*(a m*chi (m : ZMod q))*(b n*chi (n : ZMod q))) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [P2GammaInducedCharacterDictionary.gammaKernel_eq_nonprincipal hq htarget]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro chi hchi
      simp only [Nat.cast_mul,map_mul]
      dsimp [c,z]
      ring
    _ = ∑ m ∈ S,∑ chi ∈ nonprincipalCharacters q,∑ n ∈ T,
        c*(chi z*(a m*chi (m : ZMod q))*(b n*chi (n : ZMod q))) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]
    _ = ∑ chi ∈ nonprincipalCharacters q,∑ m ∈ S,∑ n ∈ T,
        c*(chi z*(a m*chi (m : ZMod q))*(b n*chi (n : ZMod q))) :=
      Finset.sum_comm
    _ = _ := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rfl

/-- The small carrier used by the peer theorem is exactly the original
quotient/conductor carrier, including the truncated rk<=Q boundary. -/
theorem lowConductorTotal_eq_smallConductorContribution
    (S T : Finset ℕ) (a b : ℕ → ℂ) (P V Q b0 : ℕ)
    (hS : S⊆Finset.Icc 1 P) (hT : T⊆Finset.Icc 1 V) :
    lowConductorTotal (paddedRow S a) (paddedRow T b) 0 0 P V Q b0=
      smallConductorContribution (2^b0) Q S T a b := by
  unfold lowConductorTotal smallConductorContribution
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 := (Finset.mem_Icc.mp hk).1
  have hcarrier : (Finset.Icc 2 (Q/k)).filter (fun r => r≤2^b0)=
      (Finset.Icc 2 (2^b0)).filter (fun r => r*k≤Q) := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hr2,hrQ⟩,hrR⟩
      exact ⟨⟨hr2,hrR⟩,(Nat.le_div_iff_mul_le hk0).mp hrQ⟩
    · rintro ⟨⟨hr2,hrR⟩,hrQ⟩
      exact ⟨⟨hr2,(Nat.le_div_iff_mul_le hk0).mpr hrQ⟩,hrR⟩
  unfold inducedShell
  rw [hcarrier]
  apply Finset.sum_congr rfl
  intro r hr
  congr 2
  apply Finset.sum_congr rfl
  intro psi hpsi
  rw [paddedRow_amplitude S a P k r hS,paddedRow_amplitude T b V k r hT]

/-- Actual variable-profile target-deleted prime theorem, now on the SAME
interval rows as the finite large-sieve and exact-regrouping consumers. -/
theorem actual_variable_prime_lowConductorTotal
    {eta J A W Ctarget : ℝ} (heta : 0<eta) (hW : 0≤W) (hCtarget : 0≤Ctarget) :
    ∃ C : ℝ,0<C ∧ ∃ x0 : ℝ,1<x0 ∧
      ∀ x M u v : ℝ,x0≤x → x^eta≤M → 1≤M → M≤u → u≤v → v≤2*M →
      ∀ f : ℝ → ℂ,
      (∀ y∈Icc u v,DifferentiableAt ℝ f y) →
      IntegrableOn (deriv f) (Icc u v) →
      profileAbelNorm f u v≤W*Real.log x^J →
      (∀ y∈Icc u v,‖f y‖≤W*Real.log x^J) →
      ∀ target : ℕ,0<target → (target : ℝ)≤x^Ctarget →
      ∀ P V Q b0 : ℕ,∀ T : Finset ℕ,∀ b : ℕ → ℂ,
      primeSWInterval u v⊆Finset.Icc 1 P → T⊆Finset.Icc 1 V →
      lowConductorTotal
        (paddedRow (primeSWInterval u v) (targetDeleted target (profilePrimeCoefficient f)))
        (paddedRow T b) 0 0 P V Q b0 ≤
      C*M*rowMass T b*((2^b0 : ℕ) : ℝ)^2*(logGauge Q)^2/Real.log x^A := by
  obtain ⟨C,hC,x0,hx0,hactual⟩ :=
    variable_profile_small_conductors heta hW hCtarget (A:=A) (J:=J)
  refine ⟨C,hC,x0,hx0,?_⟩
  intro x M u v hx hpow hM hlu huv hhi f hfd hfi hvar hsize target ht htarget
    P V Q b0 T b hS hT
  rw [lowConductorTotal_eq_smallConductorContribution _ _ _ _ _ _ _ _ hS hT]
  exact hactual x M u v hx hpow hM hlu huv hhi f hfd hfi hvar hsize
    target ht htarget (2^b0) Q T b

/-- Actual prime small conductors plus the proved entire high-conductor
sum. Every nonprincipal character is covered once. There is no SW,
convolution-BV or geometric-separation conclusion among the premises. -/
theorem actual_variable_prime_full_rectangle
    {eta J A W Ctarget : ℝ} (heta : 0<eta) (hW : 0≤W) (hCtarget : 0≤Ctarget) :
    ∃ C : ℝ,0<C ∧ ∃ x0 : ℝ,1<x0 ∧
      ∀ x M u v : ℝ,x0≤x → x^eta≤M → 1≤M → M≤u → u≤v → v≤2*M →
      ∀ f : ℝ → ℂ,
      (∀ y∈Icc u v,DifferentiableAt ℝ f y) →
      IntegrableOn (deriv f) (Icc u v) →
      profileAbelNorm f u v≤W*Real.log x^J →
      (∀ y∈Icc u v,‖f y‖≤W*Real.log x^J) →
      ∀ target : ℕ,0<target → (target : ℝ)≤x^Ctarget →
      ∀ P V Q b0 : ℕ,∀ T : Finset ℕ,∀ b : ℕ → ℂ,
      primeSWInterval u v⊆Finset.Icc 1 P → T⊆Finset.Icc 1 V →
      ∀ z : (q : ℕ) → ZMod q,
      let a := paddedRow (primeSWInterval u v)
        (targetDeleted target (profilePrimeCoefficient f))
      let beta := paddedRow T b
      (∑ q ∈ Finset.Icc 1 Q,‖rectangleCharacterDiscrepancy a beta 0 0 P V q (z q)‖)≤
        C*M*rowMass T b*((2^b0 : ℕ) : ℝ)^2*(logGauge Q)^2/Real.log x^A+
          4*logGauge Q*P2GammaDyadicConductorSum.highU a beta 0 0 P V Q b0+
          8*P2GammaDyadicConductorSum.highV a beta 0 0 P V Q := by
  obtain ⟨C,hC,x0,hx0,hlow⟩ := actual_variable_prime_lowConductorTotal
    heta hW hCtarget (A:=A) (J:=J)
  refine ⟨C,hC,x0,hx0,?_⟩
  intro x M u v hx hpow hM hlu huv hhi f hfd hfi hvar hsize target ht htarget
    P V Q b0 T b hS hT z
  dsimp only
  have hs := hlow x M u v hx hpow hM hlu huv hhi f hfd hfi hvar hsize
    target ht htarget P V Q b0 T b hS hT
  have h := full_rectangle_norm_le_low_add_high
    (paddedRow (primeSWInterval u v) (targetDeleted target (profilePrimeCoefficient f)))
    (paddedRow T b) 0 0 (by norm_num) (by norm_num) P V Q b0 z
  linarith

theorem natural_rectangle_norm_sum_le_character_sum
    (S T : Finset ℕ) (a b : ℕ → ℂ) (P V target Q : ℕ)
    (hS : S⊆Finset.Icc 1 P) (hT : T⊆Finset.Icc 1 V) :
    (∑ q ∈ (Finset.Icc 1 Q).filter (fun q => target.Coprime q),
      ‖naturalRectangleDiscrepancy S T a b target q‖)≤
      ∑ q ∈ Finset.Icc 1 Q,
        ‖rectangleCharacterDiscrepancy (paddedRow S a) (paddedRow T b) 0 0 P V q
          ((target : ZMod q)⁻¹)‖ := by
  calc
    _ = ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => target.Coprime q),
        ‖rectangleCharacterDiscrepancy (paddedRow S a) (paddedRow T b) 0 0 P V q
          ((target : ZMod q)⁻¹)‖ := by
      apply Finset.sum_congr rfl
      intro q hq
      obtain ⟨hqI,hcop⟩ := Finset.mem_filter.mp hq
      rw [naturalRectangleDiscrepancy_eq_character S T a b P V target q hS hT
        (Finset.mem_Icc.mp hqI).1 hcop]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => norm_nonneg _)

end
end ImbalancedChen.P2GammaSmallConductorIntervalBridge
