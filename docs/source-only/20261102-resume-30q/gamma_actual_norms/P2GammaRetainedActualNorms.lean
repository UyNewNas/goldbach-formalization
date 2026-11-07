import ImbalancedChen.P2GammaRetainedInteriorGeometry
import ImbalancedChen.P2GammaSmallConductorIntervalBridge

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The coefficients below are the actual retained original Gamma coefficients.
The complementary support is the image of the NONZERO weighted original
projected labels. Product collisions are summed, never discarded. The old
marked pair and the original quotient, including quotient 1, remain inside
the product. Neither row nor its support has a q, r, k or residue argument.

Only after constructing these rows do we apply the already existing quotient
unit projector. No large-sieve, conductor-sum or distribution proof is repeated.
-/

namespace ImbalancedChen.P2GammaRetainedActualNorms
noncomputable section
open scoped Classical BigOperators
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P2OriginalGammaDivisorNorm P2GammaOriginalCartesianMask
open P2GammaSmoothLogGrid P2GammaRetainedInteriorGeometry
open P2GammaSmallConductorIntervalBridge P2GammaConvolutionLargeConductor
open P2GammaPrimeCharacterSW P2GammaPrimeTargetDeletion P2GammaVariablePrimeProfile
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open Wu2008DoubleSieve
open P5OriginalU5CausalFinite (pairSupport)

def retainedComplementLabels (N : ℕ) (t : ℕ × ℕ) (c : ℕ) (cs : List ℕ)
    (H δ : ℝ) (j l : ℕ) : Finset Label :=
  (rootComplementLabels N t (c::cs)).filter
    (fun y => betaLabel N t H δ j l y ≠ 0)

def retainedComplementSupport (N : ℕ) (t : ℕ × ℕ) (c : ℕ) (cs : List ℕ)
    (H δ : ℝ) (j l : ℕ) : Finset ℕ :=
  (retainedComplementLabels N t c cs H δ j l).image (product (t.1*t.2))

def retainedBeta (N : ℕ) (t : ℕ × ℕ) (c : ℕ) (cs : List ℕ)
    (H δ : ℝ) (j l : ℕ) : ℕ → ℂ :=
  rootComplementCoefficient N t (c::cs) (betaLabel N t H δ j l)

/-- The prime row used by the actual variable-profile SW supplier. The
colour is carried by the interval, not by a new arithmetic filter. -/
def primeHeadCoefficient (N : ℕ) (δ : ℝ) (j : ℕ) : ℕ → ℂ :=
  targetDeleted N (profilePrimeCoefficient (complexWeight δ j))

theorem retainedComplementSupport_window {N c : ℕ} {t : ℕ × ℕ}
    {cs : List ℕ} (ht : t ∈ pairSupport N) {H δ : ℝ} (hδ : 0 < δ)
    {j l m : ℕ} (hm : m ∈ retainedComplementSupport N t c cs H δ j l) :
    0 < m ∧ lower δ l < (m : ℝ) ∧ (m : ℝ) < upper δ l := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hy,hb⟩ := Finset.mem_filter.mp hy
  have hp := complement_product_pos ht hy
  have hr : Retain N H δ j l y := by
    by_contra hn
    exact hb (by simp [betaLabel,hn])
  have hw : weight δ l (product (t.1*t.2) y) ≠ 0 := by
    intro hz
    exact hb (by simp [betaLabel,hr,complexWeight,hz])
  exact ⟨hp,weight_nonzero_support hδ (by exact_mod_cast hp) l hw⟩

/-- The natural padded cap is a proved consequence of the actual hat
support. No assertion about the number of admissible labels is needed. -/
theorem retainedComplementSupport_subset_cap {N c : ℕ} {t : ℕ × ℕ}
    {cs : List ℕ} (ht : t ∈ pairSupport N) {H δ : ℝ} (hδ : 0 < δ)
    (hwidth : 2*δ ≤ Real.log 2) (j l : ℕ) :
    retainedComplementSupport N t c cs H δ j l ⊆
      Finset.Icc 1 (Nat.floor (2*lower δ l)) := by
  intro m hm
  obtain ⟨hp,_,hu⟩ := retainedComplementSupport_window ht hδ hm
  exact Finset.mem_Icc.mpr ⟨hp,Nat.le_floor
    (hu.le.trans (upper_le_two_lower hwidth l))⟩

theorem retainedBeta_eq_retained_fiber (N : ℕ) (t : ℕ × ℕ)
    (c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l m : ℕ) :
    retainedBeta N t c cs H δ j l m =
      ∑ y ∈ (retainedComplementLabels N t c cs H δ j l).filter
        (fun y => product (t.1*t.2) y=m), betaLabel N t H δ j l y := by
  simp only [retainedBeta,rootComplementCoefficient,rootComplementFiber,
    retainedComplementLabels,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hm : product (t.1*t.2) y=m <;>
    by_cases hb : betaLabel N t H δ j l y=0 <;> simp [hm,hb]

theorem retainedBeta_zero_off_support (N : ℕ) (t : ℕ × ℕ)
    (c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l m : ℕ)
    (hm : m ∉ retainedComplementSupport N t c cs H δ j l) :
    retainedBeta N t c cs H δ j l m=0 := by
  unfold retainedBeta rootComplementCoefficient
  apply Finset.sum_eq_zero
  intro y hy
  obtain ⟨hy,hprod⟩ := Finset.mem_filter.mp hy
  by_contra hb
  apply hm
  exact Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨hy,hb⟩,hprod⟩

/-- Literal complementary regrouping, with all representation
multiplicities and signs. The test is chosen AFTER the row and support. -/
theorem retained_complement_test_eq_grouped (N : ℕ) (t : ℕ × ℕ)
    (c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l : ℕ) (F : ℕ → ℂ) :
    (∑ y ∈ rootComplementLabels N t (c::cs),
      betaLabel N t H δ j l y * F (product (t.1*t.2) y)) =
      ∑ m ∈ retainedComplementSupport N t c cs H δ j l,
        retainedBeta N t c cs H δ j l m * F m := by
  have hfilter : (∑ y ∈ rootComplementLabels N t (c::cs),
      betaLabel N t H δ j l y * F (product (t.1*t.2) y)) =
      ∑ y ∈ retainedComplementLabels N t c cs H δ j l,
        betaLabel N t H δ j l y * F (product (t.1*t.2) y) := by
    rw [retainedComplementLabels,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hb : betaLabel N t H δ j l y=0 <;> simp [hb]
  rw [hfilter]
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := retainedComplementLabels N t c cs H δ j l)
    (t := retainedComplementSupport N t c cs H δ j l)
    (g := product (t.1*t.2)) (fun y hy => Finset.mem_image_of_mem _ hy)
    (fun y => betaLabel N t H δ j l y * F (product (t.1*t.2) y))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro m hm
  rw [retainedBeta_eq_retained_fiber,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y hy
  rw [(Finset.mem_filter.mp hy).2]

/-- Exact natural-to-integer ENERGY conversion for the existing padding.
The already proved complex reindex is reused; this is not another interval
character dictionary. -/
theorem paddedRow_energy (S : Finset ℕ) (a : ℕ → ℂ) (P : ℕ)
    (hS : S ⊆ Finset.Icc 1 P) :
    rowEnergy (paddedRow S a) 0 P = ∑ n ∈ S, ‖a n‖^2 := by
  have hcomplex := sum_integer_interval_nat P
    (fun n => ((‖paddedRow S a n‖^2 : ℝ) : ℂ))
  have hreal := congrArg Complex.re hcomplex
  simp only [Complex.re_sum,Complex.ofReal_re] at hreal
  unfold rowEnergy
  simp only [zero_add]
  rw [hreal]
  have hf : (Finset.Icc 1 P).filter (fun n => n ∈ S)=S := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hS h,h⟩⟩
  calc
    _ = ∑ n ∈ (Finset.Icc 1 P).filter (fun n => n ∈ S), ‖a n‖^2 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hs : n ∈ S <;> simp [paddedRow,hs]
    _ = _ := by rw [hf]

/-- The actual prime coefficient has supremum one, including both the
prime indicator and the deletion of prime divisors of the target. -/
theorem primeHeadCoefficient_norm_le_one (N : ℕ) (δ : ℝ) (j p : ℕ) :
    ‖primeHeadCoefficient N δ j p‖ ≤ 1 := by
  by_cases hc : p.Coprime N
  · by_cases hp : p.Prime
    · simpa [primeHeadCoefficient,targetDeleted,profilePrimeCoefficient,
        primeSWBeta,hc,hp] using complexWeight_norm_le_one δ j (p : ℝ)
    · simp [primeHeadCoefficient,targetDeleted,profilePrimeCoefficient,primeSWBeta,hc,hp]
  · simp [primeHeadCoefficient,targetDeleted,hc]

theorem primeInterval_subset_cap {M u v : ℝ} (hv : v ≤ 2*M) :
    primeSWInterval u v ⊆ Finset.Icc 1 (Nat.floor (2*M)) := by
  intro n hn
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ioc.mp hn
  exact Finset.mem_Icc.mpr ⟨by omega,hhi.trans (Nat.floor_mono hv)⟩

/-- Raw actual alpha L1/L2, before any logarithmic normalization. These
bounds hold on arbitrarily short or empty clipped intervals. -/
theorem prime_head_raw_norms (N : ℕ) (δ : ℝ) (j : ℕ)
    {M u v : ℝ} (hM : 0 ≤ M) (hv : v ≤ 2*M) :
    rowMass (primeSWInterval u v) (primeHeadCoefficient N δ j) ≤ 2*M ∧
    rowEnergy (paddedRow (primeSWInterval u v) (primeHeadCoefficient N δ j))
      0 (Nat.floor (2*M)) ≤ 2*M := by
  have hS := primeInterval_subset_cap (u:=u) hv
  have hcard : ((primeSWInterval u v).card : ℝ) ≤ Nat.floor (2*M) := by
    exact_mod_cast (show (primeSWInterval u v).card ≤ Nat.floor (2*M) from by
      simpa using Finset.card_le_card hS)
  have hcard' : ((primeSWInterval u v).card : ℝ) ≤ 2*M :=
    hcard.trans (Nat.floor_le (by positivity))
  constructor
  · calc
      _ ≤ ∑ _n ∈ primeSWInterval u v, (1 : ℝ) :=
        Finset.sum_le_sum (fun n _ => primeHeadCoefficient_norm_le_one N δ j n)
      _ ≤ 2*M := by simpa using hcard'
  · rw [paddedRow_energy _ _ _ hS]
    calc
      _ ≤ ∑ _n ∈ primeSWInterval u v, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        simpa only [one_pow] using pow_le_pow_left₀
          (norm_nonneg _) (primeHeadCoefficient_norm_le_one N δ j n) 2
      _ ≤ 2*M := by simpa using hcard'

/-- Raw actual beta L1 and padded L2. The FIRST divisor moment pays L1;
the pre-existing actual mother second moment pays L2. Its exponent is fixed
by the original word, independently of q, k, the requested accuracy, or N. -/
theorem mother_retained_beta_raw_norms {N c i : ℕ} {t : ℕ × ℕ}
    {cs : List ℕ} (ht : t ∈ pairSupport N)
    (hi : i ∈ secondFunctionalMotherPrefixIndices)
    (hcs : (c::cs) ∈ secondFunctionalMotherGammaWords i)
    {H δ : ℝ} (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2)
    (j l : ℕ) (hB : 1 ≤ lower δ l) :
    rowMass (retainedComplementSupport N t c cs H δ j l)
      (retainedBeta N t c cs H δ j l) ≤
        (2*lower δ l)*(1+Real.log (2*lower δ l))^(c::cs).length ∧
    rowEnergy (paddedRow (retainedComplementSupport N t c cs H δ j l)
      (retainedBeta N t c cs H δ j l)) 0 (Nat.floor (2*lower δ l)) ≤
        (2*lower δ l)*(1+Real.log (2*lower δ l))^(((c::cs).length+1)^2-1) := by
  let S := retainedComplementSupport N t c cs H δ j l
  have hS := retainedComplementSupport_subset_cap ht hδ hwidth j l
  have hSIoc : S ⊆ Finset.Ioc 0 (Nat.floor (2*lower δ l)) := by
    intro m hm
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp (hS hm)
    exact Finset.mem_Ioc.mpr ⟨hlo,hhi⟩
  have hX : 1 ≤ 2*lower δ l := by linarith
  constructor
  · calc
      _ ≤ ∑ m ∈ S, (fouvryTau ((c::cs).length+1) m : ℝ) :=
        Finset.sum_le_sum (fun m _ => retained_complement_norm ht c cs H δ j l m)
      _ ≤ ∑ m ∈ Finset.Ioc 0 (Nat.floor (2*lower δ l)),
          (fouvryTau ((c::cs).length+1) m : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hSIoc (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ _ := by
        simpa only [Nat.add_sub_cancel] using
          sum_fouvryTau_le_real (k:=(c::cs).length+1) (by omega) hX
  · rw [paddedRow_energy _ _ _ hS]
    exact actual_mother_complement_square_sum ht hi hcs
      (betaLabel N t H δ j l) (fun y _ => betaLabel_norm_le_one N t H δ j l y)
      hX S hSIoc

/-- A quotient gate is a contraction of the physical L1 norm. It is not
baked into the coefficient before the q-independent row is constructed. -/
theorem quotientMask_mass_le (S : Finset ℕ) (a : ℕ → ℂ) (k : ℕ) :
    rowMass S (fun n => if n.Coprime k then a n else 0) ≤ rowMass S a := by
  apply Finset.sum_le_sum
  intro n hn
  by_cases hc : n.Coprime k <;> simp [hc,norm_nonneg]

/-- Both induced quotient masks use the same already-built rows. The
existing projector-energy theorem supplies this consequence without a
factor depending on k or any growth of the divisor exponent. -/
theorem quotientMasked_raw_norms {N c i : ℕ} {t : ℕ × ℕ}
    {cs : List ℕ} (ht : t ∈ pairSupport N)
    (hi : i ∈ secondFunctionalMotherPrefixIndices)
    (hcs : (c::cs) ∈ secondFunctionalMotherGammaWords i)
    {H δ : ℝ} (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2)
    (j l : ℕ) (hB : 1 ≤ lower δ l) {u v : ℝ}
    (hv : v ≤ 2*lower δ j) (k : ℕ) :
    rowEnergy (unitMask k (paddedRow (primeSWInterval u v)
      (primeHeadCoefficient N δ j))) 0 (Nat.floor (2*lower δ j)) ≤ 2*lower δ j ∧
    rowEnergy (unitMask k (paddedRow (retainedComplementSupport N t c cs H δ j l)
      (retainedBeta N t c cs H δ j l))) 0 (Nat.floor (2*lower δ l)) ≤
      (2*lower δ l)*(1+Real.log (2*lower δ l))^(((c::cs).length+1)^2-1) := by
  exact ⟨(unitMask_energy_le _ _ _ _).trans
      (prime_head_raw_norms N δ j (lower_pos δ j).le hv).2,
    (unitMask_energy_le _ _ _ _).trans
      (mother_retained_beta_raw_norms ht hi hcs hδ hwidth j l hB).2⟩

end
end ImbalancedChen.P2GammaRetainedActualNorms
