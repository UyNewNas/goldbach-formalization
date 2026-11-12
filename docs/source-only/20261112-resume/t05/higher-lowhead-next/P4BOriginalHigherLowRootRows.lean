import ImbalancedChen.P4BOriginalMediumLowTriple
import ImbalancedChen.P4AFinitePPLastOddSupport

/-! Read a factorisation licence from the actual 475q closed ordered cell.
The first test is the C0 singleton substitution. The two rescue entries
use the same third-slot ceiling, since the swapped ceiling is smaller. -/
namespace ImbalancedChen.P4BOriginalHigherLowRootRows
noncomputable section
open Classical Set VariableEnvelope
open P4AOriginalOrderedThirdTable
abbrev Cell := HistoricalThirdCoarse.Cell

inductive Row | first | xy | xyz | rescue | xz | yz
  deriving DecidableEq

def base {m : ℕ} (j : Cell m) (k : Fin 6) :=
  infimum m j (actualExtendedThirdRobustBaseBranch k)

def licensed {m : ℕ} (e : ℝ) (j : Cell m) (b : Row) : Prop :=
  let G := envelope e m j
  let L := capValue e m j
  match b with
  | .first => L+e/2≤base j 0
  | _ => base j 0<L+e/2 ∧ logPrimeMeshHi 0 (19/96) m j 0≤mu-4*e ∧
      match b with
      | .xy => G=base j 2
      | .xyz => G=base j 3
      | .rescue => G=base j 4
      | .xz => e≤infimum m j actualExtendedThirdGateXZ ∧ G=infimum m j actualExtendedThirdPairXZ
      | .yz => e≤infimum m j actualExtendedThirdGateYZ ∧ G=infimum m j actualExtendedThirdPairYZ
      | .first => False

theorem level_eq {m : ℕ} {e : ℝ} (he : 0≤e) {j : Cell m} {t : Point}
    (ht : t∈portion m j) : capValue e m j=envelope e m j-2*e := by
  have H := cap_on_ordered he ht
  change min (299/500-2*e) (envelope e m j-2*e)≤(153/256:ℝ)-2*e at H
  apply min_eq_right
  by_contra! h
  rw [min_eq_left h.le] at H
  linarith

private theorem inf_mono {m : ℕ} {j : Cell m} {t : Point} (ht : t∈portion m j)
    {f g : Point → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀u∈portion m j,f u≤g u) : infimum m j f≤infimum m j g := by
  apply le_csInf ((show (portion m j).Nonempty from ⟨t,ht⟩).image _)
  rintro _ ⟨u,hu,rfl⟩
  exact (inf_le hf hu).trans (h u hu)

theorem exists_licensed {m : ℕ} {e : ℝ} (he : 0<e) {j : Cell m} {t : Point}
    (ht : t∈portion m j) : ∃b,licensed e j b := by
  let G := envelope e m j
  let L := capValue e m j
  have hg : L=G-2*e := level_eq he.le ht
  by_cases h0 : L+e/2≤base j 0
  · exact ⟨.first,h0⟩
  have h0' := lt_of_not_ge h0
  have hfull : logPrimeMeshHi 0 (19/96) m j 0≤mu-4*e := by
    by_contra h
    have : G=base j 0 := by simp [G,envelope,h,base]
    linarith
  have ord (u : Point) (hu : u∈portion m j) : Ordered (u 0) (u 1) (u 2) :=
    ⟨hu.2.1,hu.2.2.1,hu.2.2.2,by linarith only [(hu.1 0 (mem_univ _)).2,hfull,he]⟩
  have h1 : base j 1≤base j 0 := by
    apply inf_mono ht (continuous_actualExtendedThirdRobustBaseBranch 1)
      (continuous_actualExtendedThirdRobustBaseBranch 0)
    intro u hu
    have H := ord u hu
    change v (u 1)≤v (u 0)
    rw [v_eq_A (H.2.2.1.trans H.2.2.2),v_eq_A H.2.2.2]
    dsimp [A]; linarith only [H.2.2.1]
  have h5 : base j 5≤base j 4 := by
    apply inf_mono ht (continuous_actualExtendedThirdRobustBaseBranch 5)
      (continuous_actualExtendedThirdRobustBaseBranch 4)
    intro u hu
    have H := ord u hu
    change max (v (u 0)) (wInner (u 0) (u 2) (u 1))≤max (v (u 0)) (wInner (u 0) (u 1) (u 2))
    rw [wInner_eq_B _ (H.2.1.trans (H.2.2.1.trans H.2.2.2)) (H.1.trans H.2.1),
      wInner_eq_B _ (H.2.2.1.trans H.2.2.2) H.1]
    exact max_le_max_left _ (by dsimp [B]; linarith only [H.2.1])
  let X := infimum m j actualExtendedThirdPairXZ
  let Y := infimum m j actualExtendedThirdPairYZ
  let gx := e≤infimum m j actualExtendedThirdGateXZ
  let gy := e≤infimum m j actualExtendedThirdGateYZ
  have eq : G=max (base j 0) (max (base j 1) (max (base j 2) (max (base j 3)
      (max (base j 4) (max (base j 5) (max (if gx then X else base j 0)
      (if gy then Y else base j 0))))))) := by simp only [G,envelope,if_pos hfull]; rfl
  have hbranches := le_of_eq eq
  simp only [le_max_iff] at hbranches
  have ub : max (base j 0) (max (base j 1) (max (base j 2) (max (base j 3)
      (max (base j 4) (max (base j 5) (max (if gx then X else base j 0)
      (if gy then Y else base j 0)))))))≤G := eq.ge
  simp only [max_le_iff] at ub
  obtain ⟨u0,u1,u2,u3,u4,u5,uX,uY⟩ := ub
  rcases hbranches with H|H|H|H|H|H|H|H
  · linarith
  · linarith
  · exact ⟨.xy,h0',hfull,le_antisymm H u2⟩
  · exact ⟨.xyz,h0',hfull,le_antisymm H u3⟩
  · exact ⟨.rescue,h0',hfull,le_antisymm H u4⟩
  · exact ⟨.rescue,h0',hfull,le_antisymm (H.trans h5) u4⟩
  · by_cases hx : gx
    · rw [if_pos hx] at H uX
      exact ⟨.xz,h0',hfull,hx,le_antisymm H uX⟩
    · rw [if_neg hx] at H; linarith
  · by_cases hy : gy
    · rw [if_pos hy] at H uY
      exact ⟨.yz,h0',hfull,hy,le_antisymm H uY⟩
    · rw [if_neg hy] at H; linarith

/-- Deterministic original order on ties, after the baseline substitution. -/
def read {m : ℕ} (e : ℝ) (j : Cell m) : Row :=
  if licensed e j .first then .first else if licensed e j .xy then .xy
  else if licensed e j .xyz then .xyz else if licensed e j .rescue then .rescue
  else if licensed e j .xz then .xz else .yz

theorem read_licensed {m : ℕ} {e : ℝ} (he : 0<e) {j : Cell m} {t : Point}
    (ht : t∈portion m j) : licensed e j (read e j) := by
  obtain ⟨b,hb⟩ := exists_licensed he ht
  unfold read
  split_ifs <;> first | assumption | cases b <;> first | assumption | contradiction

def sum (b : Row) (t : Point) : ℝ := match b with
  | .first => t 0 | .xy => t 0+t 1 | .xyz => t 0+t 1+t 2
  | .xz => t 0+t 2 | .yz => t 1+t 2 | .rescue => 0

private theorem oscillation {m : ℕ} {j : Cell m} {t u : Point} (ht : t∈portion m j)
    (hu : u∈portion m j) (i : Fin 3) : |t i-u i|≤logPrimeMeshStep 0 (19/96) m := by
  have h := logPrimeMeshHi_eq_lo_add_step 0 (19/96) m j i
  have h1 := ht.1 i (mem_univ _)
  have h2 := hu.1 i (mem_univ _)
  exact abs_le.mpr ⟨by linarith [h1.1,h2.2],by linarith [h1.2,h2.1]⟩

private theorem near_inf {m : ℕ} {j : Cell m} {t : Point} (ht : t∈portion m j)
    (f : Point → ℝ) {a : ℝ} (h : ∀u∈portion m j,|f t-f u|≤a) :
    f t≤infimum m j f+a := by
  suffices f t-a≤infimum m j f by linarith
  apply le_csInf ((show (portion m j).Nonempty from ⟨t,ht⟩).image _)
  rintro _ ⟨u,hu,rfl⟩
  linarith only [(abs_le.mp (h u hu)).2]

/-- The exceptional initial complement square is needed exactly for xz
and yz. All later complement squares are the original full squares. -/
theorem gates {m : ℕ} {e : ℝ} (he : 0<e) (hes : e≤1/2048)
    (hs : logPrimeMeshStep 0 (19/96) m≤e/20) {j : Cell m} {t : Point} (ht : t∈portion m j)
    (hlow : t 0≤mu) {b : Row} (hb : licensed e j b) :
    let L := capValue e m j
    (if b=.rescue then A (t 0)≤L+11*e/20 ∧ L+2*e≤B (t 2)
      else L+e/2≤v (sum b t)) ∧
    (b=.xz → t 0+2*t 1+t 2≤L) ∧ (b=.yz → 2*t 0+t 1+t 2≤L) := by
  let L := capValue e m j
  let G := envelope e m j
  have eq : L=G-2*e := level_eq he.le ht
  have ho : Ordered (t 0) (t 1) (t 2) := ⟨ht.2.1,ht.2.2.1,ht.2.2.2,hlow⟩
  have baseHi (hfull : logPrimeMeshHi 0 (19/96) m j 0≤mu-4*e) :
      A (t 0)≤base j 0+e/40 := by
    rw [←v_eq_A hlow]
    apply near_inf ht (actualExtendedThirdRobustBaseBranch 0)
    intro u hu
    have h0 : u 0≤mu := by linarith only [(hu.1 0 (mem_univ _)).2,hfull,he]
    change |v (t 0)-v (u 0)|≤_
    rw [v_eq_A hlow,v_eq_A h0]
    have H := abs_le.mp (oscillation ht hu 0)
    dsimp [A]; exact abs_le.mpr ⟨by linarith [H.1],by linarith [H.2]⟩
  have pairHi (i k : Fin 3) :
      v (t i+t k)≤infimum m j (fun v' => v (v' i+v' k))+3*(e/20) := by
    apply near_inf ht
    intro u hu
    refine (v_abs_sub_le_of_le (d:=2*(e/20)) ?_).trans_eq (by ring)
    have H := abs_le.mp (oscillation ht hu i)
    have K := abs_le.mp (oscillation ht hu k)
    exact abs_le.mpr ⟨by linarith [H.1,K.1],by linarith [H.2,K.2]⟩
  cases b with
  | first =>
    exact ⟨(show L+e/2≤base j 0 from hb).trans (inf_le (continuous_actualExtendedThirdRobustBaseBranch 0) ht),
      by simp,by simp⟩
  | xy =>
    obtain ⟨_,_,h⟩ := hb
    have H := inf_le (continuous_actualExtendedThirdRobustBaseBranch 2) ht
    change base j 2≤v (t 0+t 1) at H
    exact ⟨by change L+e/2≤v (t 0+t 1); linarith only [eq,h,H,he],by simp,by simp⟩
  | xyz =>
    obtain ⟨_,_,h⟩ := hb
    have H := inf_le (continuous_actualExtendedThirdRobustBaseBranch 3) ht
    change base j 3≤v (t 0+t 1+t 2) at H
    exact ⟨by change L+e/2≤v (t 0+t 1+t 2); linarith only [eq,h,H,he],by simp,by simp⟩
  | rescue =>
    obtain ⟨h0,hfull,h⟩ := hb
    have ha := baseHi hfull
    have H := inf_le (continuous_actualExtendedThirdRobustBaseBranch 4) ht
    change base j 4≤max (v (t 0)) (wInner (t 0) (t 1) (t 2)) at H
    rw [v_eq_A hlow,wInner_eq_B _ (ho.2.2.1.trans hlow) ho.1] at H
    rcases le_max_iff.mp H with H|H
    · exfalso; linarith only [eq,h,H,h0,ha,he]
    · exact ⟨⟨by linarith only [ha,h0,he],by linarith only [eq,h,H]⟩,by simp,by simp⟩
  | xz =>
    obtain ⟨h0,hfull,_,h⟩ := hb
    have ha := baseHi hfull
    have H := inf_le continuous_actualExtendedThirdPairXZ ht
    change infimum m j actualExtendedThirdPairXZ≤v (t 0+t 2) at H
    have w : v (t 0)≤v (t 0+t 2) := by rw [v_eq_A hlow]; linarith only [eq,h,H,h0,ha,he]
    have up : v (t 0+t 2)≤infimum m j actualExtendedThirdPairXZ+3*(e/20) := pairHi 0 2
    exact ⟨by change L+e/2≤v (t 0+t 2); linarith only [eq,h,H,he],
      fun _ => by linarith only [xz_gate_margin ho w,up,h,eq,hes],by simp⟩
  | yz =>
    obtain ⟨h0,hfull,_,h⟩ := hb
    have ha := baseHi hfull
    have H := inf_le continuous_actualExtendedThirdPairYZ ht
    change infimum m j actualExtendedThirdPairYZ≤v (t 1+t 2) at H
    have w : v (t 0)≤v (t 1+t 2) := by rw [v_eq_A hlow]; linarith only [eq,h,H,h0,ha,he]
    have up : v (t 1+t 2)≤infimum m j actualExtendedThirdPairYZ+3*(e/20) := pairHi 1 2
    exact ⟨by change L+e/2≤v (t 1+t 2); linarith only [eq,h,H,he],by simp,
      fun _ => by linarith only [yz_gate_margin ho w,up,h,eq,hes]⟩

theorem half_le {m : ℕ} {e : ℝ} (he : 0<e) (hes : e≤1/2048)
    (hs : logPrimeMeshStep 0 (19/96) m≤e/20) {j : Cell m} {t : Point} (ht : t∈portion m j)
    (hlow : t 0≤mu) : 1/2≤capValue e m j := by
  rw [level_eq he.le ht]
  by_cases hf : logPrimeMeshHi 0 (19/96) m j 0≤mu-4*e
  · have hw : 1/2+2*e≤base j 4 := by
      apply le_csInf ((show (portion m j).Nonempty from ⟨t,ht⟩).image _)
      rintro _ ⟨u,hu,rfl⟩
      have hu0 : u 0≤mu := by linarith only [(hu.1 0 (mem_univ _)).2,hf,he]
      have hu1 := hu.2.2.2.trans hu0
      have hu2 := hu.2.2.1.trans hu1
      change _≤max _ (wInner _ _ _)
      apply le_max_of_le_right
      rw [wInner_eq_B _ hu1 hu.2.1]
      dsimp [B,cap,mu] at *
      linarith
    have hG : base j 4≤envelope e m j := by
      rw [envelope,if_pos hf]; dsimp only [full,base]; simp only [le_max_iff]; tauto
    linarith
  · have low : 1/2+2*e≤base j 0 := by
      apply le_csInf ((show (portion m j).Nonempty from ⟨t,ht⟩).image _)
      rintro _ ⟨u,hu,rfl⟩
      change _≤v (u 0)
      have hw := (oscillation hu ht 0)
      have hhi := logPrimeMeshHi_eq_lo_add_step 0 (19/96) m j 0
      have hlo := (hu.1 0 (mem_univ _)).1
      rw [v_eq_min]; apply le_min <;> dsimp [A,C,mu] at * <;>
        linarith only [lt_of_not_ge hf,hhi,hlo,hs,hes,he,(abs_le.mp hw).2,hlow]
    rw [envelope,if_neg hf]; linarith only [low]

end
end ImbalancedChen.P4BOriginalHigherLowRootRows
