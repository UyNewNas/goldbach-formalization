import ImbalancedChen.P5OriginalU9MidpointCurvature
import ImbalancedChen.P5OriginalSignedMidpoint
import ImbalancedChen.CurrentChenP5U9RealFubini

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Complete signed midpoint enclosure for the literal original U9 integral.
The original 1024 equal panels, log density, second derivative, signs and
1/24 remainder are retained. Logarithms use the existing proved directed
rational API. This is an unrounded rational semantic model of the producer;
identification with its historical Q80 intermediate/output integers is OPEN.
The saved upper and independent Simpson lower endpoints are not assumed.
-/

namespace ImbalancedChen.P5OriginalU9MidpointIntegral

noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2U9DirectedRationalCover P5U9DirectedLowerCertificate
open P5OriginalU9MidpointCurvature

def midpoint (l r : ℚ) : ℚ := (l+r)/2

def midpointCellLower (n : ℕ) (l r : ℚ) : ℚ :=
  (r-l)*(cellLower n (midpoint l r)+(curvatureBox n l r).lower*(r-l)^2/24)

def midpointCellUpper (n : ℕ) (l r : ℚ) : ℚ :=
  (r-l)*(cellUpper n (midpoint l r)+(curvatureBox n l r).upper*(r-l)^2/24)

/-- A real integral enclosure on every closed original cell, including
both endpoints. All curvature and logarithm bounds are derived here. -/
theorem midpoint_cell_enclosure (n : ℕ) {l r : ℚ}
    (hl : a ≤ l) (hlr : l ≤ r) (hr : r ≤ b) :
    (midpointCellLower n l r : ℝ) ≤ (∫ x in (l:ℝ)..(r:ℝ),logDensity x) ∧
      (∫ x in (l:ℝ)..(r:ℝ),logDensity x) ≤ (midpointCellUpper n l r : ℝ) := by
  have hlR : (a:ℝ) ≤ (l:ℝ) := by exact_mod_cast hl
  have hrR : (r:ℝ) ≤ (b:ℝ) := by exact_mod_cast hr
  have hlrR : (l:ℝ) ≤ (r:ℝ) := by exact_mod_cast hlr
  have hsub : Icc (l:ℝ) (r:ℝ) ⊆ Icc (a:ℝ) (b:ℝ) :=
    fun x hx => ⟨hlR.trans hx.1,hx.2.trans hrR⟩
  have hi := P5OriginalSignedMidpoint.midpoint_bounds hlrR
    (fun x hx => hasDerivAt_logDensity (hsub hx))
    (fun x hx => hasDerivAt_densitySlope (hsub hx))
    (continuousOn_densityCurvature.mono hsub)
    (fun x hx => curvatureBox_contains n hl hr hx)
  have hmidl : a ≤ midpoint l r := by dsimp [midpoint]; linarith only [hl,hlr]
  have hmidr : midpoint l r ≤ b := by dsimp [midpoint]; linarith only [hlr,hr]
  have hmidlR : (a:ℝ) ≤ (midpoint l r:ℝ) := by exact_mod_cast hmidl
  have hmidrR : (midpoint l r:ℝ) ≤ (b:ℝ) := by exact_mod_cast hmidr
  have hmideq : (midpoint l r:ℝ)=((l:ℝ)+(r:ℝ))/2 := by simp [midpoint]
  have hlo := cellLower_le_logDensity n (midpoint l r) hmidlR le_rfl hmidr
  have hup := logDensity_le_cellUpper n (midpoint l r) hmidl le_rfl hmidrR
  rw [hmideq] at hlo hup
  have hw : 0 ≤ (r:ℝ)-(l:ℝ) := sub_nonneg.mpr hlrR
  constructor
  · calc
      (midpointCellLower n l r:ℝ) =
          ((r:ℝ)-(l:ℝ))*((cellLower n (midpoint l r):ℝ)+
            ((curvatureBox n l r).lower:ℝ)*((r:ℝ)-(l:ℝ))^2/24) := by
        simp only [midpointCellLower,Rat.cast_mul,Rat.cast_sub,Rat.cast_add,
          Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]
      _ ≤ ((r:ℝ)-(l:ℝ))*(logDensity (((l:ℝ)+(r:ℝ))/2)+
          ((curvatureBox n l r).lower:ℝ)*((r:ℝ)-(l:ℝ))^2/24) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hlo _) hw
      _ ≤ _ := hi.1
  · calc
      _ ≤ ((r:ℝ)-(l:ℝ))*(logDensity (((l:ℝ)+(r:ℝ))/2)+
          ((curvatureBox n l r).upper:ℝ)*((r:ℝ)-(l:ℝ))^2/24) := hi.2
      _ ≤ ((r:ℝ)-(l:ℝ))*((cellUpper n (midpoint l r):ℝ)+
          ((curvatureBox n l r).upper:ℝ)*((r:ℝ)-(l:ℝ))^2/24) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hup _) hw
      _ = (midpointCellUpper n l r:ℝ) := by
        simp only [midpointCellUpper,Rat.cast_mul,Rat.cast_sub,Rat.cast_add,
          Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]

def midpointLower (n m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range m,midpointCellLower n (mesh m k) (mesh m (k+1))

def midpointUpper (n m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range m,midpointCellUpper n (mesh m k) (mesh m (k+1))

/-- The moving inner boundary has already been integrated exactly by the
actual Fubini/log dictionary. Adjacent cells cover the entire outer range. -/
theorem original_integral_midpoint_enclosure (n m : ℕ) (hm : 0 < m) :
    (midpointLower n m:ℝ) ≤ currentChenUpsilon9HarmonicIntegral ∧
      currentChenUpsilon9HarmonicIntegral ≤ (midpointUpper n m:ℝ) := by
  have hcell (k : ℕ) (hk : k < m) :
      IntervalIntegrable logDensity volume (mesh m k:ℝ) (mesh m (k+1):ℝ) := by
    have hl := (mesh_bounds m hm k hk.le).1
    have hr := (mesh_bounds m hm (k+1) (by omega)).2
    have hlR : (a:ℝ) ≤ (mesh m k:ℝ) := by exact_mod_cast hl
    have hrR : (mesh m (k+1):ℝ) ≤ (b:ℝ) := by exact_mod_cast hr
    have ho : (mesh m k:ℝ) ≤ (mesh m (k+1):ℝ) := by
      exact_mod_cast mesh_monotone m hm (Nat.le_succ k)
    exact (continuousOn_logDensity.mono
      (fun x hx => ⟨hlR.trans hx.1,hx.2.trans hrR⟩)).intervalIntegrable_of_Icc ho
  have hpartition := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k => (mesh m k:ℝ)) hcell
  rw [mesh_zero,mesh_last m hm] at hpartition
  have hJ : currentChenUpsilon9HarmonicIntegral =
      ∫ x in (a:ℝ)..(b:ℝ),logDensity x := by
    rw [currentChenUpsilon9HarmonicIntegral_eq_logIntegral,
      integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num)]
    rfl
  have hbounds : ∀ k ∈ Finset.range m,
      (midpointCellLower n (mesh m k) (mesh m (k+1)):ℝ) ≤
        (∫ x in (mesh m k:ℝ)..(mesh m (k+1):ℝ),logDensity x) ∧
      (∫ x in (mesh m k:ℝ)..(mesh m (k+1):ℝ),logDensity x) ≤
        (midpointCellUpper n (mesh m k) (mesh m (k+1)):ℝ) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    exact midpoint_cell_enclosure n (mesh_bounds m hm k hk'.le).1
      (mesh_monotone m hm (Nat.le_succ k))
      (mesh_bounds m hm (k+1) (by omega)).2
  rw [hJ,← hpartition]
  constructor
  · have hh := Finset.sum_le_sum (fun k hk => (hbounds k hk).1)
    simpa [midpointLower] using hh
  · have hh := Finset.sum_le_sum (fun k hk => (hbounds k hk).2)
    simpa [midpointUpper] using hh

/-- Literal original 1024-panel analytic enclosure. No 1024-term sum has
been executed, expanded into literals, or claimed to pass an endpoint test. -/
theorem original_1024_midpoint_enclosure (n : ℕ) :
    (midpointLower n 1024:ℝ) ≤ currentChenUpsilon9HarmonicIntegral ∧
      currentChenUpsilon9HarmonicIntegral ≤ (midpointUpper n 1024:ℝ) :=
  original_integral_midpoint_enclosure n 1024 (by norm_num)

/-- Three-exponent dictionary for the SAME original integral. The squared
terminal kernel is a real integral dictionary, not an unweighted prime law. -/
theorem original_ordered_domain_midpoint_enclosure (n m : ℕ) (hm : 0 < m) :
    (midpointLower n m:ℝ) ≤
        (∫ x in P5U9RealDomain.domain,P5U9RealDomain.squaredTerminalKernel x) ∧
      (∫ x in P5U9RealDomain.domain,P5U9RealDomain.squaredTerminalKernel x) ≤
        (midpointUpper n m:ℝ) := by
  rw [P5U9RealDomain.squaredTerminalKernel_integral_eq_originalJ]
  exact original_integral_midpoint_enclosure n m hm

/-- Exact K0 factor used by the saved original 1024-panel producer.
Neither K0 nor the actual adopted currentK is substituted for the other. -/
theorem original_1024_cost_enclosure (n : ℕ) :
    (((67619/10000:ℚ)*midpointLower n 1024):ℝ) ≤
        P5OriginalCoefficientArithmetic.K0*currentChenUpsilon9HarmonicIntegral ∧
      P5OriginalCoefficientArithmetic.K0*currentChenUpsilon9HarmonicIntegral ≤
        (((67619/10000:ℚ)*midpointUpper n 1024):ℝ) := by
  have hh := original_1024_midpoint_enclosure n
  have hK : P5OriginalCoefficientArithmetic.K0=(67619/10000:ℝ) := by
    norm_num [P5OriginalCoefficientArithmetic.K0]
  rw [hK]
  push_cast
  exact ⟨mul_le_mul_of_nonneg_left hh.1 (by norm_num),
    mul_le_mul_of_nonneg_left hh.2 (by norm_num)⟩

end
end ImbalancedChen.P5OriginalU9MidpointIntegral
