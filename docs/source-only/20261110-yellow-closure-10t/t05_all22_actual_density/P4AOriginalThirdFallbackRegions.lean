import ImbalancedChen.P4AOriginalThirdFallbackJacobian
import ImbalancedChen.P4AOriginalThirdFallbackOccurrence

/-! The physical images of the original 4096 open cells are disjoint.
Their descriptions below use ordinary affine slacks in the three prime
logarithms. All original admission and support inequalities hold on each
image with strict margins. -/
namespace ImbalancedChen.P4AOriginalThirdFallbackRegions
noncomputable section
open Set MeasureTheory
open scoped Function
open P4AOriginalThirdFallbackArchive
open P4AOriginalThirdFallbackSlope
open P4AOriginalThirdFallbackChartIntegral
open P4AOriginalThirdFallbackJacobian
open P5OriginalAboveMuThirdLowerPhysicalCoefficient (ThirdRegion rho)

def orientation (b : Bool) : ℝ := if b then 1 else -1
def numer (b : Bool) (p : Point) : Point :=
  ![p 0-(mu : ℝ),orientation b*(p 1+p 2-(mu : ℝ)),2*p 2]
def denom (b : Bool) (p : Point) : Point := ![(h : ℝ),|(branch b : ℝ)|*(p 0-(mu : ℝ)),p 1+p 2]
def wall (c : Cell) (i j : Fin 3) (p : Point) : ℝ :=
  ![denom c.1 p i,numer c.1 p i-lo c i*denom c.1 p i,hi c i*denom c.1 p i-numer c.1 p i] j

theorem continuous_wall (c : Cell) (i j : Fin 3) : Continuous (wall c i j) := by
  fin_cases i <;> fin_cases j <;> simp [wall,numer,denom] <;> fun_prop

private theorem inverse_ratio (b : Bool) (p : Point) (hx : 0 < p 0-(mu : ℝ)) :
    ∀ i, inverse b p i = numer b p i/denom b p i := by
  intro i
  fin_cases i
  · rfl
  · cases b <;> norm_num [inverse,numer,denom,orientation,branch] <;>
      field_simp [hx.ne'] <;> ring
  · rfl

private theorem right_inverse (b : Bool) (p : Point) (hx : 0 < p 0-(mu : ℝ)) (hs : 0 < p 1+p 2) :
    chart b (inverse b p) = p := by
  let t := inverse b p
  have hh : (h : ℝ) ≠ 0 := by norm_num [h]
  have hk : (branch b : ℝ) ≠ 0 := by cases b <;> norm_num [branch]
  have hX : X (t 0) = p 0 := by
    change (mu : ℝ)+(h : ℝ)*((p 0-(mu : ℝ))/(h : ℝ)) = _
    field_simp [hh] <;> ring
  have hS : S b (t 0) (t 1) = p 1+p 2 := by
    change (mu : ℝ)+(branch b : ℝ)*(h : ℝ)*((p 0-(mu : ℝ))/(h : ℝ))*
      ((p 1+p 2-(mu : ℝ))/((branch b : ℝ)*(p 0-(mu : ℝ)))) = _
    field_simp [hh,hk,hx.ne'] <;> ring
  have hZ : Z b (t 0) (t 1) (t 2) = p 2 := by
    rw [Z,hS]
    change (p 1+p 2)*(2*p 2/(p 1+p 2))/2 = _
    field_simp [hs.ne'] <;> ring
  funext i
  fin_cases i
  · exact hX
  · change S b (t 0) (t 1)-Z b (t 0) (t 1) (t 2) = _
    rw [hS,hZ]; ring
  · exact hZ

theorem region_iff_walls (c : Cell) (p : Point) : p ∈ region c ↔ ∀ i j, 0 < wall c i j p := by
  have hh : 0 < (h : ℝ) := by norm_num [h]
  have hk : 0 < |(branch c.1 : ℝ)| := by cases c.1 <;> norm_num [branch]
  constructor
  · rintro ⟨t,ht,rfl⟩
    obtain ⟨hu,hv,_⟩ := strict_unit c ht
    let p := chart c.1 t
    have hx : 0 < p 0-(mu : ℝ) := by
      change 0 < (mu : ℝ)+(h : ℝ)*t 0-(mu : ℝ)
      linarith only [mul_pos hh hu.1]
    have hs : 0 < p 1+p 2 := by
      change 0 < S c.1 (t 0) (t 1)-Z c.1 (t 0) (t 1) (t 2)+Z c.1 (t 0) (t 1) (t 2)
      linarith only [positive_s (b := c.1) ⟨hu.1.le,hu.2.le⟩ ⟨hv.1.le,hv.2.le⟩]
    have hd (i : Fin 3) : 0 < denom c.1 p i := by
      fin_cases i
      · exact hh
      · exact mul_pos hk hx
      · exact hs
    have ht' : inverse c.1 p ∈ box c := by rwa [inverse_on_box c ht]
    intro i j
    have hi := ht' i (mem_univ _)
    rw [mem_Ioo,inverse_ratio c.1 p hx i] at hi
    fin_cases j
    · exact hd i
    · exact sub_pos.mpr ((lt_div_iff₀ (hd i)).mp hi.1)
    · exact sub_pos.mpr ((div_lt_iff₀ (hd i)).mp hi.2)
  · intro hw
    have hd (i : Fin 3) : 0 < denom c.1 p i := hw i 0
    have hx : 0 < p 0-(mu : ℝ) := pos_of_mul_pos_right (hd 1) hk.le
    have hs : 0 < p 1+p 2 := hd 2
    refine ⟨inverse c.1 p,?_,right_inverse _ _ hx hs⟩
    intro i _
    rw [mem_Ioo,inverse_ratio _ _ hx i]
    exact ⟨(lt_div_iff₀ (hd i)).mpr (sub_pos.mp (hw i 1)),
      (div_lt_iff₀ (hd i)).mpr (sub_pos.mp (hw i 2))⟩

theorem region_measurable (c : Cell) : MeasurableSet (region c) := by
  have he : region c = ⋂ i, ⋂ j, {p | 0 < wall c i j p} := by
    ext p
    simp only [mem_iInter,mem_setOf_eq,region_iff_walls]
  rw [he]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
    (isOpen_lt continuous_const (continuous_wall c i j)).measurableSet))

private theorem index_unique {i j : ℕ} {t : ℝ} (hi : (i : ℝ) < t) (hi' : t < (i : ℝ)+1)
    (hj : (j : ℝ) < t) (hj' : t < (j : ℝ)+1) : i = j := by
  rcases lt_trichotomy i j with hlt | he | hgt
  · have h : (i : ℝ)+1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
    linarith
  · exact he
  · have h : (j : ℝ)+1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hgt
    linarith

private theorem unique_params {c d : Cell} (hb : c.1=d.1) {t : Point} (hc : t ∈ box c) (hd : t ∈ box d) :
    c = d := by
  obtain ⟨bc,ic,jc,lc⟩ := c
  obtain ⟨bd,id,jd,ld⟩ := d
  change bc = bd at hb
  subst bd
  have irow : ∀ a b : Fin 8, ∀ x : ℝ, (a.val : ℝ)/8 < x → x < ((a.val : ℝ)+1)/8 →
      (b.val : ℝ)/8 < x → x < ((b.val : ℝ)+1)/8 → a = b := by
    intro a b x h0 h1 h2 h3
    exact Fin.ext (index_unique (t := 8*x) (by linarith) (by linarith) (by linarith) (by linarith))
  have h0 := hc 0 (mem_univ _)
  have h1 := hc 1 (mem_univ _)
  have h2 := hc 2 (mem_univ _)
  have g0 := hd 0 (mem_univ _)
  have g1 := hd 1 (mem_univ _)
  have g2 := hd 2 (mem_univ _)
  simp [lo,hi,ua,ub,va,vb,wa,wb,Set.mem_Ioo] at h0 h1 h2 g0 g1 g2
  have hi := irow ic id (t 0) h0.1 h0.2 g0.1 g0.2
  have hj := irow jc jd (t 1) h1.1 h1.2 g1.1 g1.2
  have hl : lc = ld := Fin.ext (index_unique (t := 72*(t 2-5/9))
    (by linarith [h2.1]) (by linarith [h2.2]) (by linarith [g2.1]) (by linarith [g2.2]))
  rw [hi,hj,hl]

theorem unique_region {c d : Cell} {p : Point} (hc : p ∈ region c) (hd : p ∈ region d) : c=d := by
  obtain ⟨t,ht,he⟩ := hc
  obtain ⟨s,hs,he'⟩ := hd
  have hsum (b : Bool) (p : Point) : chart b p 1 + chart b p 2 = S b (p 0) (p 1) := by
    change S b (p 0) (p 1)-Z b (p 0) (p 1) (p 2)+Z b (p 0) (p 1) (p 2) = _
    ring
  have hg := congrArg (fun p : Point => p 1+p 2) (he.trans he'.symm)
  change chart c.1 t 1+chart c.1 t 2 = chart d.1 s 1+chart d.1 s 2 at hg
  rw [hsum,hsum] at hg
  have ht' := strict_unit c ht
  have hs' := strict_unit d hs
  have hsign (b : Bool) (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
      S b u v > (mu : ℝ) ↔ b = true := by
    cases b <;> norm_num [S,h,branch] <;> nlinarith [mul_pos hu hv]
  have hb : c.1 = d.1 := by
    have hleft := hsign c.1 _ _ ht'.1.1 ht'.2.1.1
    rw [hg] at hleft
    have hiff := hleft.symm.trans (hsign d.1 _ _ hs'.1.1 hs'.2.1.1)
    cases hc' : c.1 <;> cases hd' : d.1 <;> simp_all
  have eqinv := congrArg (inverse c.1) (he.trans he'.symm)
  have hi : t=s := by
    rw [inverse_on_box c ht] at eqinv
    simpa only [hb,inverse_on_box d hs] using eqinv
  exact unique_params hb (hi ▸ ht) hs

theorem pairwise_regions : Pairwise (Disjoint on region) := by
  intro c d hcd
  exact disjoint_left.mpr (fun _ hc hd => hcd (unique_region hc hd))

theorem region_guard {c : Cell} {p : Point} (hp : p ∈ region c) :
    ThirdRegion (p 0) (p 1) (p 2) := by
  obtain ⟨t,ht,rfl⟩ := hp
  let u := t 0
  let v := t 1
  let w := t 2
  obtain ⟨hu,hv,hw⟩ := strict_unit c ht
  have hx : VariableEnvelope.mu < X u ∧ X u < rho := by
    norm_num [X,u,mu,h,VariableEnvelope.mu,rho]
    constructor <;> linarith [hu.1,hu.2]
  have hS := positive_s (b := c.1) ⟨hu.1.le,hu.2.le⟩ ⟨hv.1.le,hv.2.le⟩
  have uv : 0 < u*v := mul_pos hu.1 hv.1
  have uv' : u*v < u := by simpa using mul_lt_mul_of_pos_left hv.2 hu.1
  have hSband : 2*VariableEnvelope.v (X u)-1 < S c.1 u v ∧ S c.1 u v < X u := by
    rw [old_cap hu.1.le]
    cases c.1 <;> norm_num [X,S,O,h,mu,peak,branch] <;> constructor <;>
      nlinarith [hu.1,uv,uv']
  have hSlo : 3/16 < S c.1 u v := by
    rw [old_cap hu.1.le] at hSband
    norm_num [O,h,peak] at hSband
    linarith [hu.2,hSband.1]
  have hShi : S c.1 u v < 19/96 := hSband.2.trans hx.2
  have hw' : 0 < w := by linarith [hw.1]
  have hZcut : 5/96 < Z c.1 u v w := by
    have ha := mul_lt_mul_of_pos_left hw.1 hS
    unfold Z
    nlinarith only [ha,hSlo]
  have hYcut : Y c.1 u v w < 3/16 := by
    have ha := mul_lt_mul_of_pos_left hw.1 hS
    unfold Y Z
    nlinarith only [ha,hShi]
  have hzy : Z c.1 u v w < Y c.1 u v w := by
    have ha := mul_lt_mul_of_pos_left hw.2 hS
    unfold Y Z
    linarith
  have hsum : Y c.1 u v w+Z c.1 u v w = S c.1 u v := by unfold Y; ring
  have hr : 2*Z c.1 u v w/S c.1 u v = w := by unfold Z; field_simp [hS.ne'] <;> ring
  change ThirdRegion (X u) (Y c.1 u v w) (Z c.1 u v w)
  unfold ThirdRegion
  rw [hsum,hr]
  exact ⟨hx.1,hx.2,by linarith,hzy,hSband.1,hSband.2,hw.1.le,hw.2.le,hZcut.le,hYcut⟩

end
end ImbalancedChen.P4AOriginalThirdFallbackRegions

