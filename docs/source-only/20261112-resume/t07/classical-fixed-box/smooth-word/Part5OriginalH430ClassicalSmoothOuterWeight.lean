import ImbalancedChen.Part5OriginalH430ClassicalSmoothSharpGates

/-! The original positive outer approximation in exponent and radial
coordinates. A factor-two low prime cutoff is kept at every actual slot.
The small radial piece is added once for the whole word and rank. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothOuterWeight
noncomputable section
open Finset Real Wu2008DoubleSieve
open P4B
open Part5OriginalH430ClassicalSmoothWordGates
open Part5OriginalH430ClassicalSmoothWordPhysical (logPoint)
open Part5OriginalH430ClassicalSmoothSharpGates (code displayed physicalProduct exact_sharp)
open Part5OriginalH430ClassicalFixedClampPrimeGeometry (sharp)
open scoped Classical Topology BigOperators ContDiff

def floorGate (z : ℝ) : ℝ := smoothGateUpperStep (1/2) (z-1)
def allFloors {s r : ℕ} (z : Point s r) : ℝ :=
  floorGate z.1 * (∏ i,floorGate (z.2.1 i)) * (∏ i,floorGate (z.2.2 i))

def thinGate (c y : ℝ) := smoothGateUpperStep (c/2) (c/2-y)
def radialGate (h y : ℝ) := smoothGateUpperStep h (1-y)

def outerWeight {s r : ℕ} (C : Fin s → ℕ) (ν δ h c : ℝ) (t z : Point s r) (y : ℝ) :=
  allFloors z*(thinGate c y+(1-thinGate c y)*(radialGate h y*weight C ν δ t))

def ratioPoint {s r : ℕ} (N p : ℕ) (qs : Fin s → ℕ) (rs : Fin r → ℕ) : Point s r :=
  let A := (N:ℝ)^(1/90:ℝ)
  ((p:ℝ)/A,fun i => (qs i:ℝ)/A,fun j => (rs j:ℝ)/A)

def physicalWeight {r : ℕ} (cs : List ℕ) (N p : ℕ) (qs : Fin cs.length → ℕ) (rs : Fin r → ℕ)
    (ν δ h c : ℝ) : ℝ :=
  outerWeight (code cs) ν δ h c (logPoint N p qs rs) (ratioPoint N p qs rs)
    ((physicalProduct p qs rs:ℝ)/(N:ℝ))

theorem floors_bounds {s r : ℕ} (z : Point s r) : 0≤allFloors z ∧ allFloors z≤1 := by
  have h {d : ℕ} (x : Fin d → ℝ) : 0≤∏ i,floorGate (x i) ∧ (∏ i,floorGate (x i))≤1 :=
    ⟨prod_nonneg (fun _ _ => smoothGateUpperStep_nonneg _ _),
      prod_le_one (fun _ _ => smoothGateUpperStep_nonneg _ _) (fun _ _ => smoothGateUpperStep_le_one _ _)⟩
  have hp := smoothGateUpperStep_bounds (1/2) (z.1-1)
  exact ⟨mul_nonneg (mul_nonneg hp.1 (h z.2.1).1) (h z.2.2).1,
    mul_le_one₀ (mul_le_one₀ hp.2 (h z.2.1).1 (h z.2.1).2) (h z.2.2).1 (h z.2.2).2⟩

theorem outer_bounds {s r : ℕ} (C : Fin s → ℕ) (ν δ h c : ℝ) (t z : Point s r) (y : ℝ) :
    0≤outerWeight C ν δ h c t z y ∧ outerWeight C ν δ h c t z y≤1 := by
  have hF := floors_bounds z
  have hB : 0≤thinGate c y ∧ thinGate c y≤1 := smoothGateUpperStep_bounds _ _
  have hA : 0≤radialGate h y ∧ radialGate h y≤1 := smoothGateUpperStep_bounds _ _
  have hW := weight_bounds C ν δ t
  have hJ0 := mul_nonneg hA.1 hW.1
  have hJ1 := mul_le_one₀ hA.2 hW.1 hW.2
  have hnu := sub_nonneg.mpr hB.2
  have hl := add_nonneg hB.1 (mul_nonneg hnu hJ0)
  have hh := mul_le_mul_of_nonneg_left hJ1 hnu
  exact ⟨mul_nonneg hF.1 hl,mul_le_one₀ hF.2 hl (by linarith only [hh])⟩

theorem one_on_closed_floors {s r : ℕ} {z : Point s r} (hp : 1≤z.1)
    (hq : ∀i,1≤z.2.1 i) (hr : ∀j,1≤z.2.2 j) : allFloors z=1 := by
  have one {x : ℝ} (hx : 1≤x) : floorGate x=1 :=
    smoothGateUpperStep_eq_one (by norm_num) (sub_nonneg.mpr hx)
  rw [allFloors,one hp,prod_eq_one (fun i _ => one (hq i)),prod_eq_one (fun j _ => one (hr j))] <;> norm_num

theorem floors_of_nonzero {s r : ℕ} {z : Point s r} (hz : allFloors z≠0) :
    1/2<z.1 ∧ (∀i,1/2<z.2.1 i) ∧ ∀j,1/2<z.2.2 j := by
  obtain ⟨hpair,hR⟩ := mul_ne_zero_iff.mp hz
  obtain ⟨hP,hQ⟩ := mul_ne_zero_iff.mp hpair
  have good {x : ℝ} (h : floorGate x≠0) : 1/2<x := by
    have hh := smoothGateUpperStep_nonzero_support (by norm_num : (0:ℝ)<1/2) h
    linarith only [hh]
  exact ⟨good hP,fun i => good ((prod_ne_zero_iff.mp hQ) i (mem_univ i)),
    fun j => good ((prod_ne_zero_iff.mp hR) j (mem_univ j))⟩

theorem outer_one {s r : ℕ} {C : Fin s → ℕ} {ν δ h c y : ℝ} {t z : Point s r}
    (hd : 0<δ) (hh : 0<h) (hp : 1≤z.1) (hq : ∀i,1≤z.2.1 i) (hr : ∀j,1≤z.2.2 j)
    (haccept : accepted C ν t) (hy : y≤1) : outerWeight C ν δ h c t z y=1 := by
  have hA : radialGate h y=1 := smoothGateUpperStep_eq_one hh (sub_nonneg.mpr hy)
  rw [outerWeight,one_on_closed_floors hp hq hr,hA,weight_one hd haccept]
  ring

/-- Once y is beyond the thin piece, positive weight forces the original
exponent program and upper radial gate to have positive support. -/
theorem positive_outside_thin {s r : ℕ} {C : Fin s → ℕ} {ν δ h c y : ℝ} {t z : Point s r}
    (hc : 0<c) (hy : c≤y) (hw : outerWeight C ν δ h c t z y≠0) :
    weight C ν δ t≠0 ∧ radialGate h y≠0 ∧ allFloors z≠0 := by
  have hB : thinGate c y=0 := smoothGateUpperStep_eq_zero (half_pos hc) (by linarith only [hy])
  rw [outerWeight,hB,sub_zero,one_mul,zero_add] at hw
  have hparts := mul_ne_zero_iff.mp hw
  have hG := mul_ne_zero_iff.mp hparts.2
  exact ⟨hG.2,hG.1,hparts.1⟩

theorem radial_support {s r : ℕ} {C : Fin s → ℕ} {ν δ h c y : ℝ} {t z : Point s r}
    (hh : 0<h) (hc : 0<c) (hc' : c≤1/8) (hw : outerWeight C ν δ h c t z y≠0) : y<1+h := by
  by_cases hy : y<c
  · linarith only [hy,hc',hh]
  · have h := (positive_outside_thin hc (le_of_not_gt hy) hw).2.1
    have hgate := smoothGateUpperStep_nonzero_support hh h
    linarith only [hgate]

theorem contDiff_outer {s r : ℕ} (C : Fin s → ℕ) (ν δ h c : ℝ) {d : ℕ∞} :
    ContDiff ℝ d (fun u : Point s r × Point s r × ℝ => outerWeight C ν δ h c u.1 u.2.1 u.2.2) := by
  have hgate (w : ℝ) : ContDiff ℝ d (smoothGateUpperStep w) := contDiff_smoothGateUpperStep w
  have hF : ContDiff ℝ d (fun z : Point s r => allFloors z) := by
    unfold allFloors floorGate
    apply ContDiff.mul
    · apply ContDiff.mul
      · exact (hgate _).comp (contDiff_fst.sub contDiff_const)
      · apply contDiff_prod
        intro i _
        exact (hgate _).comp (((contDiff_apply ℝ ℝ i).comp (contDiff_fst.comp contDiff_snd)).sub contDiff_const)
    · apply contDiff_prod
      intro j _
      exact (hgate _).comp (((contDiff_apply ℝ ℝ j).comp (contDiff_snd.comp contDiff_snd)).sub contDiff_const)
  have hW := contDiff_weight (r:=r) (d:=d) C ν δ
  have hY : ContDiff ℝ d (fun u : Point s r × Point s r × ℝ => u.2.2) :=
    contDiff_snd.comp contDiff_snd
  have hA := (hgate h).comp (contDiff_const.sub hY : ContDiff ℝ d (fun u => 1-u.2.2))
  have hT := (hgate (c/2)).comp (contDiff_const.sub hY : ContDiff ℝ d (fun u => c/2-u.2.2))
  exact (hF.comp (contDiff_fst.comp contDiff_snd)).mul (hT.add
    ((contDiff_const.sub hT).mul (hA.mul (hW.comp contDiff_fst))))

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothOuterWeight

