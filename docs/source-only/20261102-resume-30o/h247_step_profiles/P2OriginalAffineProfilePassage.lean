import ImbalancedChen.P2OriginalHalfOpenProfileCarrier
import ImbalancedChen.P2OriginalCompactScaledPrimeMass

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Uniform passage for actual half-open affine cells. The intermediate
boundary error is an ACTUAL prime sum majorized by a continuous wall
majorant. Thus nullity is used only after the arithmetic error is paid.
This consumes O/moving_mass's implemented compact finite-net theorem.
-/
namespace ImbalancedChen.P2OriginalAffineProfilePassage

noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology
open P2OriginalBankChildPrimeMass P2OriginalHalfOpenProfileCarrier
open P2OriginalCompactScaledPrimeMass

def closedGates {d r : ℕ} (A : Fin r → Coord d →L[ℝ] ℝ) (c : Fin r → ℝ) :
    Set (Coord d) := {x | ∀ j, A j x ≤ c j}

def AffineSandwich {d r : ℕ} (A : Fin r → Coord d →L[ℝ] ℝ)
    (c : Fin r → ℝ) (D : Set (Coord d)) : Prop :=
  primeAffineGateRegion A c ⊆ D ∧ D ⊆ closedGates A c

theorem sandwich_ae {d r : ℕ} (A : Fin r → Coord d →L[ℝ] ℝ)
    (c : Fin r → ℝ) (hA : ∀ j, A j ≠ 0) {D : Set (Coord d)}
    (hD : AffineSandwich A c D) : D =ᵐ[volume] primeAffineGateRegion A c := by
  filter_upwards [ae_primeAffineGate_no_wall A c hA] with x hx
  change (x ∈ D ↔ x ∈ primeAffineGateRegion A c)
  constructor
  · intro hd j
    exact lt_of_le_of_ne (hD.2 hd j) (hx j)
  · exact fun hd => hD.1 hd

theorem sandwich_integral {d r : ℕ} (A : Fin r → Coord d →L[ℝ] ℝ)
    (c : Fin r → ℝ) (hA : ∀ j, A j ≠ 0) {D : Set (Coord d)}
    (hD : AffineSandwich A c D) (f : Coord d → ℝ) :
    (∫ x in D, f x * ∏ i, 1/x i) =
      ∫ x in primeAffineGateRegion A c, f x * ∏ i, 1/x i :=
  setIntegral_congr_set (sandwich_ae A c hA hD)

/-- Every changed point is on an original affine wall. In particular
equality atoms and half-open lower endpoints are retained in this bound. -/
theorem sandwich_boundary {d r : ℕ} (A : Fin r → Coord d →L[ℝ] ℝ)
    (c : Fin r → ℝ) {D : Set (Coord d)} (hD : AffineSandwich A c D)
    {x : Coord d} (hx : x ∈ D) (ho : x ∉ primeAffineGateRegion A c) :
    ∃ j, A j x = c j := by
  obtain ⟨j,hj⟩ : ∃ j, c j ≤ A j x := by
    simpa only [primeAffineGateRegion,mem_setOf_eq,not_forall,not_lt] using ho
  exact ⟨j,le_antisymm (hD.2 hx j) hj⟩

theorem sandwich_indicator_error {d r s : ℕ}
    (A : Fin r → Coord d →L[ℝ] ℝ) (c : Fin r → ℝ)
    (U : Fin s → Coord d →L[ℝ] ℝ) (v : Fin s → ℝ)
    {D : Set (Coord d)} (hD : AffineSandwich A c D)
    (hU : D ⊆ primeAffineGateRegion U v) {B : ℝ} (hB : 0 ≤ B)
    (f : Coord d → ℝ) (hf : ∀ x, |f x| ≤ B) (m : ℕ) (x : Coord d) :
    |D.indicator f x - (primeAffineGateRegion A c).indicator f x| ≤
      (primeAffineGateRegion U v).indicator
        (fun y => B * affinePrimeWallMajorant A c m y) x := by
  by_cases hd : x ∈ D
  · have hu := hU hd
    rw [indicator_of_mem hd,indicator_of_mem hu]
    by_cases ho : x ∈ primeAffineGateRegion A c
    · rw [indicator_of_mem ho,sub_self,abs_zero]
      exact mul_nonneg hB (affinePrimeWallMajorant_bounds A c m x).1
    · rw [indicator_of_notMem ho,sub_zero]
      obtain ⟨j,hj⟩ := sandwich_boundary A c hD hd ho
      have hw : x ∈ primeAffineWallStrip A c (1/(m+1:ℝ)) :=
        ⟨j,by rw [hj,sub_self,abs_zero]; positivity⟩
      exact (hf x).trans (by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (affinePrimeWallMajorant_ge_one A c m hw) hB)
  · have ho : x ∉ primeAffineGateRegion A c := fun ho => hd (hD.1 ho)
    rw [indicator_of_notMem hd,indicator_of_notMem ho,sub_self,abs_zero]
    by_cases hu : x ∈ primeAffineGateRegion U v
    · rw [indicator_of_mem hu]
      exact mul_nonneg hB (affinePrimeWallMajorant_bounds A c m x).1
    · simp only [indicator_of_notMem hu,le_refl]

theorem sandwich_prime_error {d r s : ℕ} (N : ℕ) (L : ℝ)
    (A : Fin r → Coord d →L[ℝ] ℝ) (c : Fin r → ℝ)
    (U : Fin s → Coord d →L[ℝ] ℝ) (v : Fin s → ℝ)
    {D : Set (Coord d)} (hD : AffineSandwich A c D)
    (hU : D ⊆ primeAffineGateRegion U v) {B : ℝ} (hB : 0 ≤ B)
    (f : Coord d → ℝ) (hf : ∀ x, |f x| ≤ B) (m : ℕ) :
    |scaledPrimeSum N L D f - scaledPrimeSum N L (primeAffineGateRegion A c) f| ≤
      scaledPrimeSum N L (primeAffineGateRegion U v)
        (fun x => B * affinePrimeWallMajorant A c m x) := by
  unfold scaledPrimeSum actualPrimeBoxTestSum
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [← mul_sub,abs_mul,abs_of_nonneg (actualPrimeBoxWeight_nonneg hp)]
  exact mul_le_mul_of_nonneg_left
    (sandwich_indicator_error A c U v hD hU hB f hf m _) (actualPrimeBoxWeight_nonneg hp)

/-- Actual arithmetic boundary payment, uniform over moving L in the
original fixed positive compact interval. No endpoint-mass estimate is
an assumption; the finite target threshold follows from the peer's
implemented finite-net theorem and the proved affine-wall majorant. -/
theorem compact_uniform_sandwich {d r s : ℕ} {Lmin Lmax B epsilon : ℝ}
    (hmin : 0 < Lmin) (hmax : Lmin ≤ Lmax) (hB : 0 ≤ B) (he : 0 < epsilon)
    (A : Fin r → Coord d →L[ℝ] ℝ) (c : Fin r → ℝ) (hA : ∀ j, A j ≠ 0)
    (U : Fin s → Coord d →L[ℝ] ℝ) (v : Fin s → ℝ) (hUn : ∀ j, U j ≠ 0)
    (hUc : primeAffineGateRegion U v ⊆ cube d)
    {D : Set (Coord d)} (hD : AffineSandwich A c D)
    (hU : D ⊆ primeAffineGateRegion U v)
    (f : Coord d → ℝ) (hf : Continuous f) (hbound : ∀ x, |f x| ≤ B) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ L ∈ Icc Lmin Lmax,
      |scaledPrimeSum N L D f - (∫ x in D, f x * ∏ i, 1/x i)| < epsilon := by
  have hpos : (0:ℝ) < 1/10 := by norm_num
  have hI := (tendsto_integral_affinePrimeWallMajorant (b:=(3/5:ℝ)) hpos A c hA).const_mul B
  have hIsmall : ∀ᶠ m : ℕ in atTop,
      B * (∫ x in cube d,affinePrimeWallMajorant A c m x * ∏ i,1/x i) < epsilon/4 := by
    simpa only [cube,mul_zero] using hI.eventually
      (gt_mem_nhds (by positivity : (0:ℝ) < epsilon/4))
  obtain ⟨m,hm⟩ := hIsmall.exists
  let g : Coord d → ℝ := fun x => B * affinePrimeWallMajorant A c m x
  have hg : Continuous g := continuous_const.mul (continuous_affinePrimeWallMajorant A c m)
  have hgb (x : Coord d) : |g x| ≤ B*r := by
    rw [abs_of_nonneg (mul_nonneg hB (affinePrimeWallMajorant_bounds A c m x).1)]
    exact mul_le_mul_of_nonneg_left (affinePrimeWallMajorant_bounds A c m x).2 hB
  have hgi : IntegrableOn (fun x => g x * ∏ i,1/x i) (cube d) :=
    integrableOn_logPrimeBox_test_cube hpos g hg.continuousOn
  have hgn : ∀ᵐ x ∂volume.restrict (cube d), 0 ≤ g x * ∏ i,1/x i := by
    filter_upwards [ae_restrict_mem (measurableSet_logPrimeBox _ _)] with x hx
    apply mul_nonneg (mul_nonneg hB (affinePrimeWallMajorant_bounds A c m x).1)
    exact Finset.prod_nonneg (fun i _ =>
      (one_div_pos.mpr (hpos.trans_le (mem_logPrimeBox.mp hx i).1)).le)
  have hgm : (∫ x in primeAffineGateRegion U v,g x * ∏ i,1/x i) < epsilon/4 := by
    have hm' := setIntegral_mono_set hgi hgn (Filter.Eventually.of_forall hUc)
    have heq : (∫ x in cube d,g x * ∏ i,1/x i) =
        B * (∫ x in cube d,affinePrimeWallMajorant A c m x * ∏ i,1/x i) := by
      simp only [g,← mul_assoc,integral_const_mul]
    exact hm'.trans_lt (heq.trans_lt hm)
  obtain ⟨T₁,hT₁⟩ := compact_uniform_scaled_affine hmin hmax hB
    (by positivity : (0:ℝ) < epsilon/4) A c hA
    (hD.1.trans (hU.trans hUc)) f hf hbound
  obtain ⟨T₂,hT₂⟩ := compact_uniform_scaled_affine hmin hmax
    (mul_nonneg hB (Nat.cast_nonneg r)) (by positivity : (0:ℝ) < epsilon/4)
    U v hUn hUc g hg hgb
  refine ⟨max T₁ T₂,?_⟩
  intro N hN L hL
  have h₁ := hT₁ N ((le_max_left _ _).trans hN) L hL
  have h₂ := hT₂ N ((le_max_right _ _).trans hN) L hL
  have hb := sandwich_prime_error N L A c U v hD hU hB f hbound m
  rw [sandwich_integral A c hA hD f]
  have ht := abs_sub_le (scaledPrimeSum N L D f)
    (scaledPrimeSum N L (primeAffineGateRegion A c) f)
    (∫ x in primeAffineGateRegion A c,f x * ∏ i,1/x i)
  have hgupper := (abs_le.mp (le_of_lt h₂)).2
  change scaledPrimeSum N L (primeAffineGateRegion U v) g -
    (∫ x in primeAffineGateRegion U v,g x * ∏ i,1/x i) ≤ epsilon/4 at hgupper
  change |scaledPrimeSum N L D f-scaledPrimeSum N L (primeAffineGateRegion A c) f| ≤
    scaledPrimeSum N L (primeAffineGateRegion U v) g at hb
  linarith

end
end ImbalancedChen.P2OriginalAffineProfilePassage
