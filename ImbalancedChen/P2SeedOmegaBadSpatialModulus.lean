import ImbalancedChen.P2SeedOmegaBadParameterModulus

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual original bad Gamma5 kernel: one explicit coordinate modulus holds
on its full enclosing prime rectangle and for ALL alpha>=2. No modulus,
integral error, omega cap or numerical coefficient is a premise.
No max-two argument replacement is made, even at mesh corners.
-/

namespace ImbalancedChen.P2SeedOmegaBadSpatialModulus
noncomputable section
open Set LiLiuPrereqBuchstab
open P2SeedOmegaLiteralFibre
open P2SeedOmegaBadCellSemantics (actualBadKernel)

def primeRectangle : Set (ℝ×ℝ) := Icc (corner,corner) (a2,a2)
def coordinateDistance (p q : ℝ×ℝ) : ℝ := |p.1-q.1|+|p.2-q.2|

private theorem rectangle_geometry {p : ℝ×ℝ} (hp : p ∈ primeRectangle) :
    (1/4:ℝ)≤p.1 ∧ (1/4:ℝ)≤p.2 ∧ p.1≤1 ∧ p.2≤1 ∧
      (1/16:ℝ)≤p.1*p.2 := by
  have hu : p.1 ∈ Icc corner a2 := ⟨hp.1.1,hp.2.1⟩
  have hv : p.2 ∈ Icc corner a2 := ⟨hp.1.2,hp.2.2⟩
  have hu4 : (1/4:ℝ)≤p.1 := by dsimp [corner] at hu; linarith only [hu.1]
  have hv4 : (1/4:ℝ)≤p.2 := by dsimp [corner] at hv; linarith only [hv.1]
  have hprod := mul_le_mul hu4 hv4 (by norm_num : (0:ℝ)≤1/4)
    (by linarith only [hu4] : 0≤p.1)
  refine ⟨hu4,hv4,?_,?_,?_⟩
  · dsimp [a2] at hu; linarith only [hu.2]
  · dsimp [a2] at hv; linarith only [hv.2]
  · simpa only [show (1/4:ℝ)*(1/4)=1/16 by norm_num] using hprod

private theorem rectangle_inverse_bound {p : ℝ×ℝ} (hp : p ∈ primeRectangle) :
    |1/(p.1*p.2)|≤16 := by
  have hg := rectangle_geometry hp
  have hd : 0<p.1*p.2 := lt_of_lt_of_le (by norm_num) hg.2.2.2.2
  rw [abs_of_pos (one_div_pos.mpr hd)]
  apply (div_le_iff₀ hd).mpr
  nlinarith only [hg.2.2.2.2]

private theorem rectangle_product_distance {p q : ℝ×ℝ}
    (hp : p ∈ primeRectangle) (hq : q ∈ primeRectangle) :
    |p.1*p.2-q.1*q.2|≤coordinateDistance p q := by
  have hpG := rectangle_geometry hp
  have hqG := rectangle_geometry hq
  have hp2 : |p.2|≤1 := by
    rw [abs_of_nonneg (by linarith only [hpG.2.1] : 0≤p.2)]
    exact hpG.2.2.2.1
  have hq1 : |q.1|≤1 := by
    rw [abs_of_nonneg (by linarith only [hqG.1] : 0≤q.1)]
    exact hqG.2.2.1
  have he : p.1*p.2-q.1*q.2=(p.1-q.1)*p.2+q.1*(p.2-q.2) := by ring
  rw [he]
  have h1 : |(p.1-q.1)*p.2|≤|p.1-q.1| := by
    rw [abs_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp2 (abs_nonneg _)
  have h2 : |q.1*(p.2-q.2)|≤|p.2-q.2| := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hq1 (abs_nonneg _)
  exact (abs_add _ _).trans (add_le_add h1 h2)

private theorem rectangle_inverse_distance {p q : ℝ×ℝ}
    (hp : p ∈ primeRectangle) (hq : q ∈ primeRectangle) :
    |1/(p.1*p.2)-1/(q.1*q.2)|≤256*coordinateDistance p q := by
  have hpG := rectangle_geometry hp
  have hqG := rectangle_geometry hq
  have hp0 : 0<p.1*p.2 := lt_of_lt_of_le (by norm_num) hpG.2.2.2.2
  have hq0 : 0<q.1*q.2 := lt_of_lt_of_le (by norm_num) hqG.2.2.2.2
  have hden : (1/256:ℝ)≤(p.1*p.2)*(q.1*q.2) := by
    have h := mul_le_mul hpG.2.2.2.2 hqG.2.2.2.2
      (by norm_num : (0:ℝ)≤1/16) hp0.le
    simpa only [show (1/16:ℝ)*(1/16)=1/256 by norm_num] using h
  have he : 1/(p.1*p.2)-1/(q.1*q.2)=
      (q.1*q.2-p.1*p.2)/((p.1*p.2)*(q.1*q.2)) := by
    field_simp [hp0.ne',hq0.ne']
    <;> ring
  rw [he,abs_div,abs_of_pos (mul_pos hp0 hq0),abs_sub_comm (q.1*q.2) (p.1*p.2)]
  calc
    _ ≤ |p.1*p.2-q.1*q.2|/(1/256) :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hden
    _ ≤ coordinateDistance p q/(1/256) :=
      div_le_div_of_nonneg_right (rectangle_product_distance hp hq) (by norm_num)
    _ = _ := by ring

theorem actual_bad_kernel_spatial_modulus {alpha : ℝ} (ha : 2≤alpha)
    {p q : ℝ×ℝ} (hp : p ∈ primeRectangle) (hq : q ∈ primeRectangle) :
    |actualBadKernel alpha p.1 p.2-actualBadKernel alpha q.1 q.2|≤
      4096*coordinateDistance p q := by
  have hD : 0≤coordinateDistance p q := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hpArg := bad_argument_lower ha hp.2.1 hp.2.2
  have hqArg := bad_argument_lower ha hq.2.1 hq.2.2
  have hω := P5Z.U1011BuchstabTailLipschitz.abs_sub_le_half
    (by linarith only [hpArg] : 2≤badArgument alpha p.1 p.2)
    (by linarith only [hqArg] : 2≤badArgument alpha q.1 q.2)
  have heArg : badArgument alpha p.1 p.2-badArgument alpha q.1 q.2=
      s0*((q.1-p.1)+(q.2-p.2)) := by unfold badArgument; ring
  have hargdist : |badArgument alpha p.1 p.2-badArgument alpha q.1 q.2|≤
      s0*coordinateDistance p q := by
    rw [heArg,abs_mul,abs_of_pos (by norm_num [s0] : 0<s0)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num [s0])
    simpa only [coordinateDistance,abs_sub_comm] using abs_add (q.1-p.1) (q.2-p.2)
  have hω3 : |buchstab (badArgument alpha p.1 p.2)-
      buchstab (badArgument alpha q.1 q.2)|≤3*coordinateDistance p q := by
    have hd := div_le_div_of_nonneg_right hargdist (by norm_num : (0:ℝ)≤2)
    have hs : s0≤6 := by norm_num [s0]
    have hm := mul_le_mul_of_nonneg_right hs hD
    nlinarith only [hω,hd,hm]
  have hω1 : |buchstab (badArgument alpha q.1 q.2)|≤1 := by
    rw [abs_of_nonneg (buchstab_nonneg (by linarith only [hqArg]))]
    exact buchstab_le_one (by linarith only [hqArg])
  have hterm1 : |(buchstab (badArgument alpha p.1 p.2)-
      buchstab (badArgument alpha q.1 q.2))*(1/(p.1*p.2))|≤
      48*coordinateDistance p q := by
    rw [abs_mul]
    have h := mul_le_mul hω3 (rectangle_inverse_bound hp) (abs_nonneg _)
      (mul_nonneg (by norm_num) hD)
    nlinarith only [h]
  have hterm2 : |buchstab (badArgument alpha q.1 q.2)*
      (1/(p.1*p.2)-1/(q.1*q.2))|≤256*coordinateDistance p q := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul hω1 (rectangle_inverse_distance hp hq)
      (abs_nonneg _) zero_le_one
  have he : actualBadKernel alpha p.1 p.2-actualBadKernel alpha q.1 q.2=
      (K*s0/4)*((buchstab (badArgument alpha p.1 p.2)-
        buchstab (badArgument alpha q.1 q.2))*(1/(p.1*p.2))+
        buchstab (badArgument alpha q.1 q.2)*(1/(p.1*p.2)-1/(q.1*q.2))) := by
    unfold actualBadKernel
    ring
  have hsum := (abs_add _ _).trans (add_le_add hterm1 hterm2)
  have hcoef : 0≤K*s0/4 := by norm_num [K,s0]
  have hcoef8 : K*s0/4≤8 := by norm_num [K,s0]
  rw [he,abs_mul,abs_of_nonneg hcoef]
  have h := mul_le_mul_of_nonneg_left hsum hcoef
  have h8 := mul_le_mul_of_nonneg_right hcoef8 hD
  nlinarith only [h,h8,hD]

end
end ImbalancedChen.P2SeedOmegaBadSpatialModulus
