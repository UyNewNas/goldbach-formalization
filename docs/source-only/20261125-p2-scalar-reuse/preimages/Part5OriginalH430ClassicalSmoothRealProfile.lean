import ImbalancedChen.Part5OriginalH430ClassicalSmoothFamilyLicence
import ImbalancedChen.P5AdmissibleAllRankIntegerGeometricFamily

/-! The physical real function behind the actual W has a globally smooth
zero extension. On its support the original positive logarithms are exact. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothRealProfile
noncomputable section
open Finset Real Wu2008DoubleSieve
open P4B
open Part5OriginalH430ClassicalSmoothWordGates
open Part5OriginalH430ClassicalSmoothSharpGates (code physicalProduct)
open Part5OriginalH430ClassicalSmoothOuterWeight
open Part5OriginalH430ClassicalSmoothRankCoordinates
open Part5OriginalH430ClassicalSmoothRankSupport (W)
open Part5OriginalH430ClassicalSmoothEulerBounds (E)
open Part5OriginalH430ClassicalSmoothEulerProfile (split coord)
open scoped Classical Topology BigOperators ContDiff

def raw {s r : ℕ} (N : ℕ) (C : Fin s → ℕ) (ν δ h c : ℝ) (v : E (rank s r)) : ℝ :=
  outerWeight C ν δ h c (split (fun i => log (v i)/log (N:ℝ)))
    (split (fun i => v i/(N:ℝ)^(1/90:ℝ))) ((∏ i,v i)/(N:ℝ))

/-- A smooth positive argument equal to the physical coordinate once x≥b.
It changes the logarithm only where the full physical weight vanishes. -/
def positiveArg (b x : ℝ) := b+(x-b)*smoothGateUpperStep (b/2) (x-b)

theorem positiveArg_eq {b x : ℝ} (hb : 0<b) (h : b≤x) : positiveArg b x=x := by
  rw [positiveArg,smoothGateUpperStep_eq_one (half_pos hb) (sub_nonneg.mpr h)]
  ring

theorem positiveArg_pos {b : ℝ} (hb : 0<b) (x : ℝ) : 0<positiveArg b x := by
  by_cases h : b≤x
  · rw [positiveArg_eq hb h]
    exact hb.trans_le h
  by_cases hx : x≤b/2
  · have h0 := smoothGateUpperStep_eq_zero (half_pos hb) (show x-b≤ -(b/2) by linarith only [hx])
    simpa only [positiveArg,h0,mul_zero,add_zero] using hb
  have hp := lt_of_not_ge hx
  have hn := mul_le_mul_of_nonpos_left (smoothGateUpperStep_le_one (b/2) (x-b))
    (sub_nonpos.mpr (le_of_not_ge h))
  dsimp only [positiveArg]
  linarith only [lt_trans (half_pos hb) hp,hn]

theorem positiveArg_smooth (b : ℝ) : ContDiff ℝ ∞ (positiveArg b) :=
  contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    ((contDiff_smoothGateUpperStep _).comp (contDiff_id.sub contDiff_const)))

def splitCLM {s r : ℕ} : E (rank s r) →L[ℝ] Point s r :=
  (coord 0).prod ((ContinuousLinearMap.pi (fun i : Fin s => coord (qi i))).prod
    (ContinuousLinearMap.pi (fun i : Fin r => coord (ri i))))

theorem all_floor_values {s r : ℕ} {v : E (rank s r)} {A : ℝ} (hA : 0<A)
    (hn : allFloors (split (fun i => v i/A))≠0) (i : Fin (rank s r)) : A/2<v i := by
  obtain ⟨hp,hq,hr⟩ := floors_of_nonzero hn
  have get {y : ℝ} (hy : 1/2<y/A) : A/2<y := by
    have h := (lt_div_iff₀ hA).mp hy
    linarith only [h]
  have hi : v i∈List.ofFn v := List.mem_ofFn.mpr ⟨i,rfl⟩
  rw [all_slots v,List.mem_cons,List.mem_append] at hi
  rcases hi with hi | hi | hi
  · rw [hi]; exact get hp
  · obtain ⟨j,hj⟩ := List.mem_ofFn.mp hi
    rw [←hj]; exact get (hq j)
  · obtain ⟨j,hj⟩ := List.mem_ofFn.mp hi
    rw [←hj]; exact get (hr j)

theorem raw_smooth {s r N : ℕ} (hN : 2≤N) (C : Fin s → ℕ) (ν δ h c : ℝ) :
    ContDiff ℝ ∞ (raw (r:=r) N C ν δ h c) := by
  let A := (N:ℝ)^(1/90:ℝ)
  let b := A/2
  have hA : 0<A := rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _
  have hb : 0<b := half_pos hA
  let x := fun (v : E (rank s r)) => split (s:=s) (r:=r) (fun i => log (positiveArg b (v i))/log (N:ℝ))
  let z := fun (v : E (rank s r)) => split (s:=s) (r:=r) (fun i => v i/A)
  let y := fun (v : E (rank s r)) => (∏ i,v i)/(N:ℝ)
  have hx : ContDiff ℝ ∞ x := by
    apply (splitCLM (s:=s) (r:=r)).contDiff.comp
    apply contDiff_pi.mpr
    intro i
    exact (((positiveArg_smooth b).comp (contDiff_apply ℝ ℝ i)).log
      (fun v => (positiveArg_pos hb (v i)).ne')).div_const _
  have hz : ContDiff ℝ ∞ z := by
    apply (splitCLM (s:=s) (r:=r)).contDiff.comp
    exact contDiff_pi.mpr (fun i => (contDiff_apply ℝ ℝ i).div_const A)
  have hy : ContDiff ℝ ∞ y := (contDiff_prod (fun i _ => contDiff_apply ℝ ℝ i)).div_const _
  have he : raw (r:=r) N C ν δ h c = fun v => outerWeight C ν δ h c (x v) (z v) (y v) := by
    funext v
    by_cases hF : allFloors (z v)=0
    · change allFloors (z v)*_=allFloors (z v)*_
      simp only [hF,zero_mul]
    · have hv : (fun i => log (positiveArg b (v i))/log (N:ℝ))=
          (fun i => log (v i)/log (N:ℝ)) := by
        funext i
        rw [positiveArg_eq hb (all_floor_values hA hF i).le]
      change outerWeight C ν δ h c _ (z v) (y v)=
        outerWeight C ν δ h c (split (fun i => log (positiveArg b (v i))/log (N:ℝ))) (z v) (y v)
      rw [hv]
  rw [he]
  exact (contDiff_outer (d:=∞) C ν δ h c).comp (hx.prodMk (hz.prodMk hy))

theorem raw_support {s r N : ℕ} (hN : 2≤N) {C : Fin s → ℕ} {ν δ h c : ℝ}
    (hh : 0<h) (hh' : h≤1/8) (hc : 0<c) (hc' : c≤1/8) {v : E (rank s r)}
    (hw : raw N C ν δ h c v≠0) :
    (∀ i,((N:ℝ)^(1/90:ℝ))/2<v i) ∧ (∏ i,v i)≤2*(N:ℝ) := by
  have h0 : (0:ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hF := (mul_ne_zero_iff.mp hw).1
  have hcap := (div_lt_iff₀ h0).mp (radial_support hh hc hc' hw)
  exact ⟨all_floor_values (rpow_pos_of_pos h0 _) hF,
    hcap.le.trans (mul_le_mul_of_nonneg_right (by linarith only [hh']) h0.le)⟩

theorem prime_agrees {r N : ℕ} (cs : List ℕ) (ν δ h c : ℝ)
    (t : Fin (rank cs.length r) → Fin (2*N+1)) :
    raw N (code cs) ν δ h c (fun i => ((t i).val:ℝ))=W cs t ν δ h c := by
  have hm : (∏ i,((t i).val:ℝ))=
      (physicalProduct (first (fun i => (t i).val)) (qVec (fun i => (t i).val)) (rVec (fun i => (t i).val)):ℝ) := by
    exact_mod_cast entire_product t
  unfold raw
  rw [hm]
  rfl

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothRealProfile

