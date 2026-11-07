import ImbalancedChen.P5ActualLowerNormalizedHBSource
import ImbalancedChen.P5ActualHBPostModulusLogCutoff
import ImbalancedChen.P5ActualHBDyadicProductWindow

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Literal unit/right-closed HB rectangles for the normalized lower singleton.
The original group logarithm is retained at every integer, including units.
The counting scale is derived from a rectangle meeting the real profile;
no complete-product restriction is inserted into the rectangle carrier.
-/
namespace ImbalancedChen.P5Z.ActualLowerNormalizedBlockGeometry
noncomputable section
open Classical MeasureTheory Set
open scoped BigOperators
open ActualLowerNormalizedHBSource ActualHBPostModulusLogCutoff
open HBRightClosedDyadicRoles ActualHBDyadicProductWindow
open ActualAllRankOccurrenceFourierBridge ActualOccurrencePlateauWordBudget
open ActualEtaPsiOccurrenceBudget (eta psi actualEta actualPsi)
open GroupedOccurrenceLogShift
open OccurrenceEuclideanMixedIntegral ActualEuclideanPhysicalFourier

variable {m : ℕ}

def blockIntegers : Block → Finset ℕ
  | .unit => {1}
  | .dyadic j => Finset.Ioc (2^j) (2^(j+1))

theorem mem_blockIntegers (b : Block) (n : ℕ) :
    n ∈ blockIntegers b ↔ Owns b n := by
  cases b <;> simp [blockIntegers, Owns]

def rectangle (bs : Fin m → Block) : Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun a => blockIntegers (bs a))

def scales (bs : Fin m → Block) : Fin m → ℝ := fun a => (lower (bs a) : ℝ)

theorem scales_pos (bs : Fin m → Block) (a : Fin m) : 0 < scales bs a := by
  exact_mod_cast lower_pos (bs a)

theorem rectangle_owns (bs : Fin m → Block) {n : Fin m → ℕ}
    (hn : n ∈ rectangle bs) (a : Fin m) : Owns (bs a) (n a) :=
  (mem_blockIntegers _ _).mp (Fintype.mem_piFinset.mp hn a)

theorem rectangle_bounds (bs : Fin m → Block) {n : Fin m → ℕ}
    (hn : n ∈ rectangle bs) (a : Fin m) :
    0 < n a ∧ scales bs a ≤ (n a : ℝ) ∧ (n a : ℝ) ≤ 2 * scales bs a := by
  have h := owns_bounds (rectangle_owns bs hn a)
  refine ⟨(lower_pos (bs a)).trans_le h.1, ?_, ?_⟩
  · exact_mod_cast h.1
  · exact_mod_cast h.2

/-- The unit block has logarithmic coordinate zero. The same compact
plateau is one there, so units are never removed to obtain a strict atom. -/
theorem rectangle_plateau (bs : Fin m → Block) {n : Fin m → ℕ}
    (hn : n ∈ rectangle bs) : plateau m (logOccurrence (scales bs) n) = 1 := by
  unfold plateau
  apply Finset.prod_eq_one
  intro a ha
  obtain ⟨hnpos, hlo, hhi⟩ := rectangle_bounds bs hn a
  apply c_eq_one
  constructor
  · apply Real.log_nonneg
    exact (le_div_iff₀ (scales_pos bs a)).mpr (by simpa using hlo)
  · apply Real.log_le_log (div_pos (by exact_mod_cast hnpos) (scales_pos bs a))
    exact (div_le_iff₀ (scales_pos bs a)).mpr hhi

/-- One genuine original group; its whole product is independent of
every marked or small-prime factor in the modulus. -/
def singletonOwner (m : ℕ) : Fin m → Fin 1 := fun _ => 0

theorem singleton_group (n : Fin m → ℕ) (i : Fin 1) :
    integerGroupProduct (singletonOwner m) n i = completeProduct n := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [integerGroupProduct, singletonOwner, completeProduct]

/-- Independently defined integer value of the original normalized
geometric factor. There is one reciprocal GROUP log, not one per slot. -/
def integerProfile (kappa : ℝ) (B N : ℕ) (cj : ℕ) (kappa0 : ℝ)
    (n : Fin m → ℕ) : ℝ :=
  ActualSingletonLogCollarFamily.integerWeight (1-kappa)
      (ActualSingletonLogCollarFamily.logWidth B N) N
      (fun _ : Fin 1 => completeProduct n) /
    Real.log (completeProduct n : ℝ) *
    eta ((completeProduct n : ℝ) / (N : ℝ)^(1-kappa0)) *
    psi ((completeProduct n : ℝ) / ExactOriginalSmoothDyadicPartition.R cj)

theorem integerProfile_eq_ambient (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ)
    (n : Fin m → ℕ) :
    integerProfile kappa B N cj kappa0 n =
      ambient kappa B N (fun _ : Fin 1 => (completeProduct n : ℝ)) *
        eta ((completeProduct n : ℝ) / (N : ℝ)^(1-kappa0)) *
        psi ((completeProduct n : ℝ) / ExactOriginalSmoothDyadicPartition.R cj) := by
  rw [ambient_integer]
  simp only [Fin.prod_univ_one, integerProfile]

def blockChart (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ)
    (bs : Fin m → Block) :=
  euclideanChart kappa B N (singletonOwner m) (scales bs)
    (fun _ => ExactOriginalSmoothDyadicPartition.R cj) kappa0

/-- Exact evaluation of the SAME H normalized chart on the full unit/
dyadic rectangle, including its eta and original group psi. -/
theorem blockChart_integer (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ)
    (bs : Fin m → Block) {n : Fin m → ℕ} (hn : n ∈ rectangle bs) :
    blockChart kappa B N cj kappa0 bs
        (WithLp.toLp 2 (logOccurrence (scales bs) n)) =
      (integerProfile kappa B N cj kappa0 n : ℂ) := by
  have hpos : ∀ a, 0 < n a := fun a => (rectangle_bounds bs hn a).1
  rw [blockChart, euclideanChart, euclideanLift_toLp]
  unfold chart actualEta actualPsi
  simp_rw [groupProduct_logOccurrence (singletonOwner m) (scales bs) n
    (scales_pos bs) hpos, singleton_group]
  rw [rectangle_plateau bs hn]
  simp only [Fin.prod_univ_one, mul_one]
  rw [← integerProfile_eq_ambient]

/-- Retention tests the actual normalized integer profile. It does not
take a support-window or a final Fourier-error bound as an input. -/
def Meets (kappa : ℝ) (B N cj : ℕ) (kappa0 : ℝ) (bs : Fin m → Block) : Prop :=
  ∃ n ∈ rectangle bs, integerProfile kappa B N cj kappa0 n ≠ 0

theorem integerProfile_support (kappa : ℝ) (hkappa : kappa < 1)
    (B N cj : ℕ) (kappa0 : ℝ) {n : Fin m → ℕ}
    (hn : integerProfile kappa B N cj kappa0 n ≠ 0) :
    (completeProduct n : ℝ) ≤ 2 * (N : ℝ) := by
  rw [integerProfile_eq_ambient] at hn
  have hamb : ambient kappa B N (fun _ : Fin 1 => (completeProduct n : ℝ)) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
  simpa only [Fin.prod_univ_one] using (ambient_support kappa hkappa B N _ hamb).2

theorem rectangle_product_lower (bs : Fin m → Block) {n : Fin m → ℕ}
    (hn : n ∈ rectangle bs) : (∏ a, scales bs a) ≤ (completeProduct n : ℝ) := by
  rw [completeProduct, Nat.cast_prod]
  exact Finset.prod_le_prod (fun a ha => (scales_pos bs a).le)
    (fun a ha => (rectangle_bounds bs hn a).2.1)

theorem rectangle_product_upper (bs : Fin m → Block) {n : Fin m → ℕ}
    (hn : n ∈ rectangle bs) :
    (completeProduct n : ℝ) ≤ (2 : ℝ)^m * ∏ a, scales bs a := by
  rw [completeProduct, Nat.cast_prod]
  calc
    _ ≤ ∏ a : Fin m, 2 * scales bs a := Finset.prod_le_prod
      (fun a ha => Nat.cast_nonneg _) (fun a ha => (rectangle_bounds bs hn a).2.2)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

/-- Every point of a retained rank-one HB rectangle is bounded BEFORE
Fourier truncation. The whole rectangle is kept; there is no coupled
product filter. The absolute factor 128 is 2^6 times the source cap 2N. -/
theorem rectangle_counting_scale (kappa : ℝ) (hkappa : kappa < 1)
    (B N cj : ℕ) (kappa0 : ℝ) (bs : Fin m → Block) (hm : m ≤ 6)
    (hMeet : Meets kappa B N cj kappa0 bs) {n : Fin m → ℕ}
    (hn : n ∈ rectangle bs) :
    (∀ a, 0 < n a) ∧ (completeProduct n : ℝ) ≤ 128 * (N : ℝ) := by
  obtain ⟨v, hv, hvnz⟩ := hMeet
  have hlo := (rectangle_product_lower bs hv).trans
    (integerProfile_support kappa hkappa B N cj kappa0 hvnz)
  have hpow : (2 : ℝ)^m ≤ 64 := by
    calc
      _ ≤ (2 : ℝ)^6 := pow_le_pow_right₀ (by norm_num) hm
      _ = 64 := by norm_num
  refine ⟨fun a => (rectangle_bounds bs hn a).1, ?_⟩
  calc
    _ ≤ (2 : ℝ)^m * ∏ a, scales bs a := rectangle_product_upper bs hn
    _ ≤ 64 * (2 * (N : ℝ)) := mul_le_mul hpow hlo
      (Finset.prod_nonneg (fun a ha => (scales_pos bs a).le)) (by norm_num)
    _ = _ := by ring

end
end ImbalancedChen.P5Z.ActualLowerNormalizedBlockGeometry
