import ImbalancedChen.Part3ActualBetaNativeSource
import ImbalancedChen.Part3SignedResiduePushforwardEnergy
import ImbalancedChen.Part3ActualChartTagHeightCount

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26, phase 9.
True native joint-beta energy is transported through y -> a*y mod c,
including nonunit/zero a, using the independently proved signed-interval
occupancy. The physical support is DERIVED from original source members.
The actual closed-T/sign/dyadic-f chart uses the EXISTING 576 supplier at
its proved h-tag height. No integer-y incidence is re-counted.

This consumer is after actual_base_sixSmoothMass_closed_split, whose
COST2 precedes squaring. It asserts NO full-base beta = two same-chart
betas identity; mixed lower/endpoint pairs are not deleted. Native y=0
is paid separately by the existing zeroPiece supplier, since nonzero y
may also alias residue zero. Full retained spectral 7/32 remains OPEN.
-/

namespace ImbalancedChen.Part3.ActualChartResidueEnergy20261026b
noncomputable section
open Classical Finset CommonSmoothCutoff ActualCompletedSquarePushforwardSourceOnly
open ActualReciprocalSquarePoissonSourceOnly ActualClosedTCountLicenseSourceOnly
open ActualRestrictedChartWeightCountSourceOnly ActualChartTagHeight576SourceOnly
open ActualM2FinitePoissonAdapterSourceOnly ActualSeparatedRowPacketMatchSourceOnly
open ActualPositiveLatticeSmoothCoverSourceOnly ActualLogTagHSupportSourceOnly
open SignedResiduePushforwardEnergy20261026b
open OriginalSmoothPoissonTail.FiniteOperator20261026b
open scoped BigOperators

def nativeLevels (U : Finset Source) : Finset ℕ := (U.image output).image Prod.fst
def nativeY (U : Finset Source) (z : ℕ) : Finset ℤ :=
  ((U.image output).filter (fun zy => zy.1 = z)).image Prod.snd

def nativeResidueEnergy (U : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (c : ℕ) [NeZero c] (a : ℤ) : ℝ :=
  ∑ z ∈ nativeLevels U, energy c
    (packetRightCoefficient c (nativeY U z) (fun y => beta U lambda omega (z,y)) a)

theorem native_integer_energy_by_level (U : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) :
    (∑ z ∈ nativeLevels U, ∑ y ∈ nativeY U z, ‖beta U lambda omega (z,y)‖^2) =
      ∑ zy ∈ U.image output, ‖beta U lambda omega zy‖^2 := by
  have hfibre (z : ℕ) :
      (∑ y ∈ nativeY U z, ‖beta U lambda omega (z,y)‖^2) =
        ∑ zy ∈ (U.image output).filter (fun zy => zy.1 = z), ‖beta U lambda omega zy‖^2 := by
    unfold nativeY
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro zy hzy
      have he : (z,zy.2) = zy := Prod.ext (Finset.mem_filter.mp hzy).2.symm rfl
      rw [he]
    · intro zy hzy zy' hzy' heq
      exact Prod.ext ((Finset.mem_filter.mp hzy).2.trans (Finset.mem_filter.mp hzy').2.symm) heq
  simp_rw [hfibre]
  exact Finset.sum_fiberwise_of_maps_to
    (fun zy hzy => Finset.mem_image_of_mem Prod.fst hzy)
    (fun zy => ‖beta U lambda omega zy‖^2)

theorem nativeResidueEnergy_le_integer_energy
    (U : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (c : ℕ) [NeZero c] (a L R : ℤ) (hLR : L ≤ R)
    (hsupport : ∀ z y, beta U lambda omega (z,y) ≠ 0 → L ≤ y ∧ y ≤ R) :
    nativeResidueEnergy U lambda omega c a ≤ collisionFactor c a L R *
      ∑ zy ∈ U.image output, ‖beta U lambda omega zy‖^2 := by
  unfold nativeResidueEnergy
  calc
    _ ≤ ∑ z ∈ nativeLevels U, collisionFactor c a L R *
        ∑ y ∈ nativeY U z, ‖beta U lambda omega (z,y)‖^2 := by
      apply Finset.sum_le_sum
      intro z hz
      exact packetRight_energy_le_of_weight_support c (nativeY U z)
        (fun y => beta U lambda omega (z,y)) a L R hLR (fun y hy hb => hsupport z y hb)
    _ = collisionFactor c a L R *
        ∑ z ∈ nativeLevels U, ∑ y ∈ nativeY U z, ‖beta U lambda omega (z,y)‖^2 :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [native_integer_energy_by_level]

def actualTagPhysicalY (e : MediumAtom) (D delta g : ℕ) (tag : ℕ × Bool) : ℝ :=
  4*(scaleF e D g)*(tagFrequencyBound tag : ℝ)*(e.Q2 / ((D/delta : ℕ) : ℝ))

def actualChartResidueEnergy (e : MediumAtom) (D delta g l : ℕ) [NeZero (g*l)]
    (Z : ℝ) (tag : ℕ × Bool) (m : ℤ × ℤ) (negative : Bool)
    (u : (ZMod (g*l))ˣ) (k : ZMod (g*l)) (upper : Bool) (fj : ℕ × Bool)
    (c : ℕ) [NeZero c] : ℝ :=
  let U := fBlock (g*l) (signedResidue negative e.residue)
    (e.Q2 / ((D/delta : ℕ) : ℝ)) upper (tagFrequencyBound tag) (scaleF e D g) fj
  nativeResidueEnergy U (actualModeLambda e D delta g l m negative u k)
    (actualModeOmega e D g l Z tag m negative k) c (signedResidue negative e.residue)

def actualChart576Budget (e : MediumAtom) (D delta : ℕ) (tag : ℕ × Bool)
    (upper : Bool) (fj : ℕ × Bool) : ℝ :=
  let S := e.Q2 / ((D/delta : ℕ) : ℝ)
  let H := tagFrequencyBound tag
  let R := countScale S upper
  let G := fScale fj.1
  576*(LichtmanSignedDifferenceMultiplicity.divisorMaximum R H G : ℝ)^5*
    (harmonic (Nat.floor (2*R)) : ℝ)*(1+(H : ℝ)/R)*((H : ℝ)*R)^2*G

/-- Every integer-L2 and physical-support input is supplied by the
original actual chart. The multiplier a need not be a unit modulo c. -/
theorem actual_chart_residue_energy_le_576
    {B : ℕ} {sigma kappa c0 : ℝ} {e : MediumAtom}
    (he : MediumAdmissible B sigma kappa c0 e)
    (D delta g l : ℕ) [NeZero (g*l)] (Z : ℝ) (tag : ℕ × Bool)
    (m : ℤ × ℤ) (negative : Bool) (u : (ZMod (g*l))ˣ) (k : ZMod (g*l))
    (hq : 0 < D/delta) (upper : Bool) (fj : ℕ × Bool) (c : ℕ) [NeZero c] :
    actualChartResidueEnergy e D delta g l Z tag m negative u k upper fj c ≤
      collisionFactor c (signedResidue negative e.residue)
        (Int.ceil (-actualTagPhysicalY e D delta g tag))
        (Int.floor (actualTagPhysicalY e D delta g tag)) *
          actualChart576Budget e D delta tag upper fj := by
  let S := e.Q2 / ((D/delta : ℕ) : ℝ)
  let H := tagFrequencyBound tag
  let F := scaleF e D g
  let U := fBlock (g*l) (signedResidue negative e.residue) S upper H F fj
  let lam := actualModeLambda e D delta g l m negative u k
  let om := actualModeOmega e D g l Z tag m negative k
  let Y := actualTagPhysicalY e D delta g tag
  have hS : 0 < S := div_pos (zero_lt_one.trans_le he.2.2.2.1) (by exact_mod_cast hq)
  have hF : 0 ≤ F := by
    dsimp [F,scaleF]
    have hU : 0 < e.U := zero_lt_one.trans_le he.1
    have hQ : 0 < e.Q1 := zero_lt_one.trans_le he.2.2.1
    positivity
  have hY : 0 ≤ Y := by change 0 ≤ 4*F*(H : ℝ)*S; positivity
  have hLR : Int.ceil (-Y) ≤ Int.floor Y := by
    have hl : Int.ceil (-Y) ≤ (0 : ℤ) := Int.ceil_le.mpr (by simpa using neg_nonpos.mpr hY)
    have hr : (0 : ℤ) ≤ Int.floor Y := Int.le_floor.mpr (by simpa using hY)
    exact hl.trans hr
  have hsupp (z : ℕ) (y : ℤ) (hb : beta U lam om (z,y) ≠ 0) :
      Int.ceil (-Y) ≤ y ∧ y ≤ Int.floor Y := by
    obtain ⟨s,hs,hout⟩ := Finset.mem_image.mp (beta_ne_zero_mem_image hb)
    have hfull := fBlock_subset_fullSource (g*l) (signedResidue negative e.residue)
      S upper H F fj hs
    have hbound := output_support hS hF (by intro t ht; exact ht)
      (fun f hf => actual_f_window_bound F hf) (Finset.mem_filter.mp hfull).1
    have habs : |(y : ℝ)| ≤ Y := by simpa only [hout,Prod.snd] using hbound.2.2.2
    exact ⟨Int.ceil_le.mpr (abs_le.mp habs).1,Int.le_floor.mpr (abs_le.mp habs).2⟩
  have hres := nativeResidueEnergy_le_integer_energy U lam om c
    (signedResidue negative e.residue) (Int.ceil (-Y)) (Int.floor Y) hLR hsupp
  have heq : (∑ zy ∈ U.image output, ‖beta U lam om zy‖^2) =
      actualChartWeightedEnergy e D delta g l Z tag m negative u k upper fj 1 := by
    rw [actual_chart_energy_eq_tag_height]
    simp only [tagChartWeightedEnergy,Nat.cast_one,one_dvd,if_true] <;> rfl
  have hcount : actualChartWeightedEnergy e D delta g l Z tag m negative u k upper fj 1 ≤
      actualChart576Budget e D delta tag upper fj := by
    simpa only [actualChart576Budget,Nat.cast_one,div_one] using
      (actual_chart_weighted_576_tag_height he D delta g l Z tag m negative u k hq upper fj 1 (by decide)).1
  change nativeResidueEnergy U lam om c (signedResidue negative e.residue) ≤ _
  calc
    _ ≤ collisionFactor c (signedResidue negative e.residue) (Int.ceil (-Y)) (Int.floor Y) *
        (∑ zy ∈ U.image output, ‖beta U lam om zy‖^2) := hres
    _ ≤ collisionFactor c (signedResidue negative e.residue) (Int.ceil (-Y)) (Int.floor Y) *
        actualChart576Budget e D delta tag upper fj := by
      rw [heq]
      exact mul_le_mul_of_nonneg_left hcount (collisionFactor_nonneg _ _ _ _ hLR)
    _ = _ := rfl

end
end ImbalancedChen.Part3.ActualChartResidueEnergy20261026b
