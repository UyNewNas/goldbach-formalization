import ImbalancedChen.ActualPrimeBoxMass
import ImbalancedChen.MovingWeightTransport
import ImbalancedChen.Part3RoughWeightedPrimeMass
import ImbalancedChen.P1OriginalFifthMovingScaleLimit

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An arithmetic moment for the literal catalog-five small-third box.
The first two coordinates stay in [3/16,19/96); only the third approaches
zero. Chebyshev's proved log-prime mass pays that coordinate, including
all finite prime atoms and target exclusions. No different policy or
dyadic selection is introduced. The imported moving-scale theorem is a
scalar actual-source majorant; no fifth-policy identity is used.
-/

namespace ImbalancedChen.P4ACatalogFiveSmallThirdMass
noncomputable section
open Filter Topology
open scoped Classical BigOperators
open Part3.RoughWeightedPrimeMass20261026b
open Part3.RoughSlotCharacterLift20261026b
open P1OriginalFifthMovingHarmonicEnvelope P1OriginalFifthMovingScaleLimit

def lower : Fin 3 → ℝ := ![3/16,3/16,0]
def upper (h : ℝ) : Fin 3 → ℝ := ![19/96,19/96,h]
def tailBox (N : ℕ) (h : ℝ) : Finset (Fin 3 → ℕ) :=
  actualPrimeBoxTuples N lower (upper h)

def pairMass (N : ℕ) : ℝ :=
  actualPrimeBoxMass N (fun _ : Fin 2 => (3/16:ℝ)) (fun _ => (19/96:ℝ))

def lastLogMass (N : ℕ) (h : ℝ) : ℝ :=
  ∑ p ∈ roughPrimeFinset N (Nat.ceil ((N:ℝ)^h)) 1 ((N:ℝ)^h),
    (1/((p:ℝ)-1)) * (Real.log (p:ℝ)/Real.log (N:ℝ))

def firstMoment (N : ℕ) (h : ℝ) : ℝ :=
  ∑ p ∈ tailBox N h, (∏ i, 1/((p i:ℝ)-1)) * actualPrimeTupleLog N p 2

def secondMoment (N : ℕ) (h : ℝ) : ℝ :=
  ∑ p ∈ tailBox N h, (∏ i, 1/((p i:ℝ)-1)) * (actualPrimeTupleLog N p 2)^2

theorem firstMoment_eq (N : ℕ) (h : ℝ) :
    firstMoment N h = pairMass N * lastLogMass N h := by
  let S (i : Fin 3) := roughPrimeFinset N (Nat.ceil ((N:ℝ)^(upper h i)))
    ((N:ℝ)^lower i) ((N:ℝ)^(upper h i))
  let f (i : Fin 3) (p : ℕ) := (1/((p:ℝ)-1)) *
    (if i=2 then Real.log (p:ℝ)/Real.log (N:ℝ) else 1)
  calc
    firstMoment N h = ∏ i, ∑ p ∈ S i, f i p := by
      rw [Finset.prod_univ_sum]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [f,Fin.prod_univ_three,actualPrimeTupleLog]
      norm_num <;> ring
    _ = pairMass N * lastLogMass N h := by
      simp [S,f,lower,upper,pairMass,actualPrimeBoxMass_eq_prod,
        actualPrimeReciprocalMass,lastLogMass,Fin.prod_univ_three,Fin.prod_univ_two]

/-- Inclusive Chebyshev mass dominates the actual strict, target-deleted
third-prime interval. The endpoint atom is not discarded. -/
theorem lastLogMass_le (N : ℕ) (hN : 1 < N) (h : ℝ)
    (hcut : 2 ≤ (N:ℝ)^h) :
    lastLogMass N h ≤ (2*primeMassConstant)*h := by
  have hn : (1:ℝ) < N := by exact_mod_cast hN
  have hl : 0 < Real.log (N:ℝ) := Real.log_pos hn
  have hz : 0 < (N:ℝ)^h := Real.rpow_pos_of_pos (zero_lt_one.trans hn) h
  have hsub : roughPrimeFinset N (Nat.ceil ((N:ℝ)^h)) 1 ((N:ℝ)^h) ⊆ smallPrimes ((N:ℝ)^h) := by
    intro p hp
    have hh := mem_roughPrimeFinset.mp hp
    exact (mem_smallPrimes hz.le).mpr ⟨hh.2.1,hh.2.2.2.2.le⟩
  have hm : (∑ p ∈ roughPrimeFinset N (Nat.ceil ((N:ℝ)^h)) 1 ((N:ℝ)^h),
      Real.log (p:ℝ)/((p:ℝ)-1)) ≤
      (∑ p ∈ smallPrimes ((N:ℝ)^h), Real.log (p:ℝ)/((p:ℝ)-1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    have hp1 : (1:ℝ) < p := by exact_mod_cast (smallPrimes_prime hp).one_lt
    exact div_nonneg (Real.log_nonneg hp1.le) (sub_pos.mpr hp1).le
  have heq : lastLogMass N h =
      (∑ p ∈ roughPrimeFinset N (Nat.ceil ((N:ℝ)^h)) 1 ((N:ℝ)^h),
        Real.log (p:ℝ)/((p:ℝ)-1)) / Real.log (N:ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [heq]
  calc
    _ ≤ ((2*primeMassConstant)*Real.log (max 2 ((N:ℝ)^h)))/Real.log (N:ℝ) :=
      div_le_div_of_nonneg_right (hm.trans (prime_log_div_pred_sum_le hcut)) hl.le
    _ = (2*primeMassConstant)*h := by
      rw [max_eq_right hcut,Real.log_rpow (zero_lt_one.trans hn)]
      field_simp [hl.ne'] <;> ring

theorem secondMoment_le (N : ℕ) (hN : 1 < N) (h : ℝ) :
    secondMoment N h ≤ h * firstMoment N h := by
  rw [firstMoment,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hw := actualPrimeBoxWeight_nonneg hp
  have ht := (mem_actualPrimeBoxTuples_log_iff hN lower (upper h) p).mp hp
  have hz := mem_logPrimeBox.mp ht.2 2
  have hz0 : 0 ≤ actualPrimeTupleLog N p 2 := by simpa [lower] using hz.1
  have hzh : actualPrimeTupleLog N p 2 ≤ h := by simpa [upper] using hz.2.le
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hzh hz0) hw
  nlinarith only [hh]

/-- The constant precedes h. Unlike a zero-endpoint Mertens claim, the
third-coordinate bound is a proved finite Chebyshev moment. -/
theorem exists_uniform_secondMoment_bound :
    ∃ M : ℝ, 0 < M ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ N : ℕ, N0 ≤ N → ∀ h : ℝ, 0 < h → 2 ≤ (N:ℝ)^h →
        secondMoment N h ≤ M*h^2 := by
  obtain ⟨B,hB,hb⟩ := exists_eventually_bounded_mass_of_tendsto
    (tendsto_actualPrimeBoxMass (fun _ : Fin 2 => (3/16:ℝ)) (fun _ => (19/96:ℝ))
      (fun _ => by norm_num) (fun _ => by norm_num))
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp hb
  let M := (B+1)*(2*primeMassConstant)
  have hC : 0 < 2*primeMassConstant := mul_pos (by norm_num) primeMassConstant_pos
  refine ⟨M,by dsimp [M]; positivity,max 2 N0,le_max_left _ _,?_⟩
  intro N hN h hh hcut
  have hN1 : 1 < N := by omega
  have hp : pairMass N ≤ B+1 := by
    have hb' := hN0 N ((le_max_right _ _).trans hN)
    change pairMass N ≤ B at hb'
    linarith
  have hp0 : 0 ≤ pairMass N := actualPrimeBoxMass_nonneg _ _ _
  have hfirst : firstMoment N h ≤ (B+1)*((2*primeMassConstant)*h) := by
    rw [firstMoment_eq]
    exact (mul_le_mul_of_nonneg_left (lastLogMass_le N hN1 h hcut) hp0).trans
      (mul_le_mul_of_nonneg_right hp (mul_pos hC hh).le)
  calc
    _ ≤ h*firstMoment N h := secondMoment_le N hN1 h
    _ ≤ h*((B+1)*((2*primeMassConstant)*h)) := mul_le_mul_of_nonneg_left hfirst hh.le
    _ = M*h^2 := by dsimp [M]; ring

theorem tailBox_subset_full (N : ℕ) (hN : 1 < N) (h : ℝ) (hh : h ≤ (19/96:ℝ)) :
    tailBox N h ⊆ actualPrimeBoxTuples N (fun _ : Fin 3 => 0) (fun _ => (19/96:ℝ)) := by
  intro p hp
  apply mem_actualPrimeBoxTuples_iff.mpr
  intro i
  have hi := mem_actualPrimeBoxTuples_iff.mp hp i
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN.le
  refine ⟨hi.1,hi.2.1,?_,?_⟩
  · exact (Real.rpow_le_rpow_of_exponent_le hn (by fin_cases i <;> norm_num [lower])).trans hi.2.2.1
  · exact hi.2.2.2.trans_le (Real.rpow_le_rpow_of_exponent_le hn
      (by fin_cases i <;> simp [upper] <;> linarith))

theorem tailBox_mass_le_harmonic (N : ℕ) (hN : 1 < N) (h : ℝ) (hh : h ≤ (19/96:ℝ)) :
    (∑ p ∈ tailBox N h, ∏ i, 1/((p i:ℝ)-1)) ≤ (harmonicFactor N)^3 := by
  have hm : (∑ p ∈ tailBox N h, ∏ i, 1/((p i:ℝ)-1)) ≤
      actualPrimeBoxMass N (fun _ : Fin 3 => 0) (fun _ => (19/96:ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (tailBox_subset_full N hN h hh)
    intro p hp _
    exact actualPrimeBoxWeight_nonneg hp
  exact hm.trans (by simpa [harmonicFactor,Fin.prod_univ_three,pow_succ] using
    actualPrimeBoxMass_le_harmonic_product N (fun _ : Fin 3 => 0) (fun _ => (19/96:ℝ)))

theorem harmonicFactor_ge_one (N : ℕ) (hN : 1 < N) : 1 ≤ harmonicFactor N := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN.le
  have hc : (1:ℝ) ≤ (Nat.ceil ((N:ℝ)^(19/96:ℝ)):ℝ) :=
    (Real.one_le_rpow hn (by norm_num)).trans (Nat.le_ceil _)
  have hl := Real.log_nonneg hc
  unfold harmonicFactor
  linarith

end
end ImbalancedChen.P4ACatalogFiveSmallThirdMass
