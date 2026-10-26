import ImbalancedChen.P2EnhancedSeedPairD6Primitive

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original repaired ordinary second seed: exact double-integral fibre semantics.
The two BAD Gamma5 pieces here are complementary to the ordinary D5+ lease.
All constants are the original ones in certify_second_seed_omega_envelope.py.
No asserted certificate result, desired lower bound, or numerical statistic
is a hypothesis. In particular, this file does not prove 20249/1000000.
-/

namespace ImbalancedChen.P2SeedOmegaLiteralFibre

noncomputable section
open Set MeasureTheory
open scoped Interval

def s : ℝ := 11/5
def s0 : ℝ := 227/50
def phi1 : ℝ := 353/100
def phi2 : ℝ := 29/10
def phi3 : ℝ := 61/25
def a0 : ℝ := 50/227
def a1 : ℝ := 100/353
def a2 : ℝ := 10/29
def a3 : ℝ := 25/61
def b : ℝ := 5/11
def K : ℝ := 681/100
def omegaCap : ℝ := 70893/125000
def corner : ℝ := 19/58

theorem original_reciprocals : a0=1/s0 ∧ a1=1/phi1 ∧
    a2=1/phi2 ∧ a3=1/phi3 ∧ b=1/s := by
  norm_num [a0,a1,a2,a3,b,s0,phi1,phi2,phi3,s]

theorem original_order : 0<a0 ∧ a0<a1 ∧ a1<corner ∧
    corner<(1/3:ℝ) ∧ (1/3:ℝ)<a2 ∧ a2<a3 ∧ a3<b ∧ b<1/2 := by
  norm_num [a0,a1,a2,a3,b,corner]

def pairKernel (u v : ℝ) : ℝ := 1/(u*v*(1-u-v))
def roughPairKernel (u v : ℝ) : ℝ := 1/(u*v)
def pairLog (u l r : ℝ) : ℝ :=
  Real.log (r*(1-u-l)/(l*(1-u-r)))/(u*(1-u))
def roughPairLog (u l r : ℝ) : ℝ := Real.log (r/l)/u

/-- Closed-endpoint version of the genuine original pair primitive. -/
theorem pair_fibre {u l r : ℝ} (hu : 0<u) (hl : 0<l)
    (hlr : l≤r) (hr : r<1-u) :
    (∫ v in l..r,pairKernel u v)=pairLog u l r := by
  have h := P2EnhancedSeedPairD6Primitive.pair_inner_log_integral hu hl hlr hr
  rw [integral_Ioo_eq_integral_Ioc,← intervalIntegral.integral_of_le hlr] at h
  simpa only [pairKernel,pairLog,one_div,div_eq_mul_inv,mul_comm] using h

/-- The positive rough mass, including equality of fibre endpoints. -/
theorem rough_pair_fibre {u l r : ℝ} (hu : 0<u) (hl : 0<l)
    (hlr : l≤r) :
    (∫ v in l..r,roughPairKernel u v)=roughPairLog u l r := by
  let F := fun v : ℝ => Real.log v/u
  have hc : ContinuousOn (roughPairKernel u) (Icc l r) := by
    apply continuousOn_const.div
    · fun_prop
    · intro v hv
      exact (mul_pos hu (hl.trans_le hv.1)).ne'
  have hd : ∀ v ∈ uIcc l r,HasDerivAt F (roughPairKernel u v) v := by
    intro v hv
    rw [uIcc_of_le hlr] at hv
    have hv0 := hl.trans_le hv.1
    have h := (Real.hasDerivAt_log hv0.ne').div_const u
    apply h.congr_deriv
    dsimp [roughPairKernel]
    field_simp [hu.ne',hv0.ne'] <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hc.intervalIntegrable_of_Icc hlr)]
  dsimp [F,roughPairLog]
  rw [← sub_div,← Real.log_div (hl.trans_le hlr).ne' hl.ne']

def ordinaryTriangle (top : ℝ) : ℝ :=
  ∫ u in a0..top,∫ v in u..top,pairKernel u v
def ordinaryRectangle (lo hi : ℝ) : ℝ :=
  ∫ u in a0..a1,∫ v in lo..hi,pairKernel u v

/-- The triangle's upper endpoint is included; its last fibre vanishes. -/
theorem triangle_fibre {top u : ℝ} (htop : top≤a2)
    (hu : u ∈ Icc a0 top) :
    (∫ v in u..top,pairKernel u v)=
      Real.log (top*(1-2*u)/(u*(1-u-top)))/(u*(1-u)) := by
  have hu0 : 0<u := lt_of_lt_of_le (by norm_num [a0]) hu.1
  have hr : top<1-u := by
    dsimp [a2] at htop
    linarith only [hu.2,htop]
  have h := pair_fibre hu0 hu0 hu.2 hr
  simpa only [pairLog,show 1-u-u=1-2*u by ring] using h

theorem ordinaryTriangle_eq_original_log {top : ℝ}
    (hlo : a0≤top) (hhi : top≤a2) :
    ordinaryTriangle top=∫ u in a0..top,
      Real.log (top*(1-2*u)/(u*(1-u-top)))/(u*(1-u)) := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hlo] at hu
  exact triangle_fibre hhi hu

theorem rectangle_fibre {lo hi u : ℝ} (hl : 0<lo) (hlh : lo≤hi)
    (hh : hi≤a3) (hu : u ∈ Icc a0 a1) :
    (∫ v in lo..hi,pairKernel u v)=pairLog u lo hi := by
  apply pair_fibre (lt_of_lt_of_le (by norm_num [a0]) hu.1) hl hlh
  dsimp [a1] at hu
  dsimp [a3] at hh
  linarith only [hu.2,hh]

theorem ordinaryRectangle_eq_original_log {lo hi : ℝ}
    (hl : 0<lo) (hlh : lo≤hi) (hh : hi≤a3) :
    ordinaryRectangle lo hi=∫ u in a0..a1,
      Real.log (hi*(1-u-lo)/(lo*(1-u-hi)))/(u*(1-u)) := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (by norm_num [a0,a1])] at hu
  exact rectangle_fibre hl hlh hh hu

def badDomain : Set (ℝ×ℝ) :=
  {x | a0<x.1 ∧ x.1<x.2 ∧ x.2<a2 ∧ 1<x.2+2*x.1}

/-- Exact bad-corner support. The switching equality belongs to neither
open branch; it is retained explicitly by the closed-fibre versions below. -/
theorem badDomain_dictionary (u v : ℝ) :
    (u,v) ∈ badDomain ↔ corner<u ∧ u<a2 ∧ max u (1-2*u)<v ∧ v<a2 := by
  dsimp [badDomain]
  simp only [max_lt_iff]
  dsimp [a0,a2,corner]
  constructor
  · rintro ⟨h0,huv,hv,hgate⟩
    exact ⟨by linarith,by linarith,⟨huv,by linarith⟩,hv⟩
  · rintro ⟨hu0,hu2,⟨huv,hgate⟩,hv⟩
    exact ⟨by linarith,huv,hv,by linarith⟩

theorem bad_first_lower {u : ℝ} (hu : u≤(1/3:ℝ)) :
    max u (1-2*u)=1-2*u := max_eq_right (by linarith)

theorem bad_second_lower {u : ℝ} (hu : (1/3:ℝ)≤u) :
    max u (1-2*u)=u := max_eq_left (by linarith)

theorem corner_is_original_cut : corner=(1-a2)/2 := by norm_num [corner,a2]

theorem bad_closed_geometry {u v : ℝ}
    (hu : u ∈ Icc corner a2) (hv : v ∈ Icc (max u (1-2*u)) a2) :
    0<u ∧ 0<v ∧ 0<1-u-v ∧ 2*v<1 ∧ 1≤v+2*u := by
  have hmax1 := (le_max_left u (1-2*u)).trans hv.1
  have hmax2 := (le_max_right u (1-2*u)).trans hv.1
  dsimp [corner,a2] at hu hv
  constructor
  · linarith only [hu.1]
  constructor
  · linarith only [hu.1,hmax1]
  constructor
  · linarith only [hu.2,hv.2]
  constructor
  · linarith only [hv.2]
  · linarith only [hmax2]

/-- Actual rough argument with the inherited parameter, no max-two
replacement. The lower endpoint is the manuscript's exact 4313/725. -/
def badArgument (alpha u v : ℝ) : ℝ := s0*(alpha-u-v)

theorem bad_argument_lower {alpha u v : ℝ} (ha : 2≤alpha)
    (hu : u≤a2) (hv : v≤a2) :
    (4313/725:ℝ)≤badArgument alpha u v := by
  dsimp [badArgument,s0,a2] at *
  linarith only [ha,hu,hv]

theorem bad_first_pair_fibre {u : ℝ} (hu : u ∈ Icc corner (1/3:ℝ)) :
    (∫ v in (1-2*u)..a2,pairKernel u v)=
      Real.log (a2*u/((1-2*u)*(1-u-a2)))/(u*(1-u)) := by
  have hu0 : 0<u := by dsimp [corner] at hu; linarith only [hu.1]
  have hl : 0<1-2*u := by linarith only [hu.2]
  have hlr : 1-2*u≤a2 := by dsimp [corner,a2] at *; linarith only [hu.1]
  have hr : a2<1-u := by dsimp [a2]; linarith only [hu.2]
  have h := pair_fibre hu0 hl hlr hr
  simpa only [pairLog,show 1-u-(1-2*u)=u by ring] using h

theorem bad_second_pair_fibre {u : ℝ} (hu : u ∈ Icc (1/3:ℝ) a2) :
    (∫ v in u..a2,pairKernel u v)=
      Real.log (a2*(1-2*u)/(u*(1-u-a2)))/(u*(1-u)) := by
  apply triangle_fibre le_rfl
  exact ⟨(by norm_num [a0] : a0≤(1/3:ℝ)).trans hu.1,hu.2⟩

theorem bad_first_rough_fibre {u : ℝ} (hu : u ∈ Icc corner (1/3:ℝ)) :
    (∫ v in (1-2*u)..a2,roughPairKernel u v)=Real.log (a2/(1-2*u))/u := by
  apply rough_pair_fibre
  · dsimp [corner] at hu; linarith only [hu.1]
  · linarith only [hu.2]
  · dsimp [corner,a2] at *; linarith only [hu.1]

theorem bad_second_rough_fibre {u : ℝ} (hu : u ∈ Icc (1/3:ℝ) a2) :
    (∫ v in u..a2,roughPairKernel u v)=Real.log (a2/u)/u := by
  exact rough_pair_fibre (by linarith only [hu.1])
    (by linarith only [hu.1]) hu.2

def badLower (u : ℝ) : ℝ := max u (1-2*u)

theorem bad_fibre_geometry {u : ℝ} (hu : u ∈ Icc corner a2) :
    0<u ∧ 0<badLower u ∧ badLower u≤a2 ∧ a2<1-u := by
  have hu0 : 0<u := by dsimp [corner] at hu; linarith only [hu.1]
  have hlo : u≤badLower u := le_max_left _ _
  have hlhi : badLower u≤a2 := by
    apply max_le_iff.mpr
    refine ⟨hu.2,?_⟩
    dsimp [corner,a2] at *
    linarith only [hu.1]
  exact ⟨hu0,hu0.trans_le hlo,hlhi,
    by dsimp [a2] at *; linarith only [hu.2]⟩

private theorem continuousOn_bad_pair_log :
    ContinuousOn (fun u => pairLog u (badLower u) a2) (Icc corner a2) := by
  have hlo : ContinuousOn badLower (Icc corner a2) := by
    unfold badLower
    fun_prop
  have hn : ContinuousOn (fun u => a2*(1-u-badLower u)) (Icc corner a2) :=
    continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).sub hlo)
  have hd : ContinuousOn (fun u => badLower u*(1-u-a2)) (Icc corner a2) :=
    hlo.mul ((continuousOn_const.sub continuousOn_id).sub continuousOn_const)
  have hp (u : ℝ) (hu : u ∈ Icc corner a2) :
      0<a2*(1-u-badLower u) ∧ 0<badLower u*(1-u-a2) := by
    have hg := bad_fibre_geometry hu
    exact ⟨mul_pos (by norm_num [a2]) (by linarith only [hg.2.2.1,hg.2.2.2]),
      mul_pos hg.2.1 (by linarith only [hg.2.2.2])⟩
  have hlog := (hn.div hd (fun u hu => (hp u hu).2.ne')).log
    (fun u hu => (div_pos (hp u hu).1 (hp u hu).2).ne')
  apply hlog.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
  intro u hu
  have hg := bad_fibre_geometry hu
  exact (mul_pos hg.1 (by linarith only [hg.2.2.2,show 0<a2 by norm_num [a2]])).ne'

private theorem continuousOn_bad_rough_log :
    ContinuousOn (fun u => roughPairLog u (badLower u) a2) (Icc corner a2) := by
  have hlo : ContinuousOn badLower (Icc corner a2) := by unfold badLower; fun_prop
  have hq := continuousOn_const.div hlo (fun u hu => (bad_fibre_geometry hu).2.1.ne')
  have hlog := hq.log (fun u hu =>
    (div_pos (by norm_num [a2]) (bad_fibre_geometry hu).2.1).ne')
  exact hlog.div continuousOn_id (fun u hu => (bad_fibre_geometry hu).1.ne')

/-- Genuine partition of the UNPARTITIONED literal bad-corner double
integral. Outer integrability is proved before splitting at one third. -/
theorem bad_pair_partition :
    (∫ u in corner..a2,∫ v in badLower u..a2,pairKernel u v)=
      (∫ u in corner..(1/3:ℝ),∫ v in (1-2*u)..a2,pairKernel u v)+
      (∫ u in (1/3:ℝ)..a2,∫ v in u..a2,pairKernel u v) := by
  have hleft : Icc corner (1/3:ℝ) ⊆ Icc corner a2 := by
    intro u hu
    exact ⟨hu.1,hu.2.trans (by norm_num [a2])⟩
  have hright : Icc (1/3:ℝ) a2 ⊆ Icc corner a2 := by
    intro u hu
    exact ⟨(by norm_num [corner] : corner≤(1/3:ℝ)).trans hu.1,hu.2⟩
  have hiL := (continuousOn_bad_pair_log.mono hleft).intervalIntegrable_of_Icc
    (by norm_num [corner] : corner≤(1/3:ℝ))
  have hiR := (continuousOn_bad_pair_log.mono hright).intervalIntegrable_of_Icc
    (by norm_num [a2] : (1/3:ℝ)≤a2)
  have hiLf : IntervalIntegrable
      (fun u => ∫ v in badLower u..a2,pairKernel u v) volume corner (1/3:ℝ) := by
    apply hiL.congr
    intro u hu
    rw [uIoc_of_le (by norm_num [corner])] at hu
    have hg := bad_fibre_geometry (hleft ⟨hu.1.le,hu.2⟩)
    exact (pair_fibre hg.1 hg.2.1 hg.2.2.1 hg.2.2.2).symm
  have hiRf : IntervalIntegrable
      (fun u => ∫ v in badLower u..a2,pairKernel u v) volume (1/3:ℝ) a2 := by
    apply hiR.congr
    intro u hu
    rw [uIoc_of_le (by norm_num [a2])] at hu
    have hg := bad_fibre_geometry (hright ⟨hu.1.le,hu.2⟩)
    exact (pair_fibre hg.1 hg.2.1 hg.2.2.1 hg.2.2.2).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals hiLf hiRf]
  congr 1
  · apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num [corner])] at hu
    rw [badLower,bad_first_lower hu.2]
  · apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num [a2])] at hu
    rw [badLower,bad_second_lower hu.1]

theorem bad_rough_partition :
    (∫ u in corner..a2,∫ v in badLower u..a2,roughPairKernel u v)=
      (∫ u in corner..(1/3:ℝ),∫ v in (1-2*u)..a2,roughPairKernel u v)+
      (∫ u in (1/3:ℝ)..a2,∫ v in u..a2,roughPairKernel u v) := by
  have hleft : Icc corner (1/3:ℝ) ⊆ Icc corner a2 := by
    intro u hu
    exact ⟨hu.1,hu.2.trans (by norm_num [a2])⟩
  have hright : Icc (1/3:ℝ) a2 ⊆ Icc corner a2 := by
    intro u hu
    exact ⟨(by norm_num [corner] : corner≤(1/3:ℝ)).trans hu.1,hu.2⟩
  have hiL := (continuousOn_bad_rough_log.mono hleft).intervalIntegrable_of_Icc
    (by norm_num [corner] : corner≤(1/3:ℝ))
  have hiR := (continuousOn_bad_rough_log.mono hright).intervalIntegrable_of_Icc
    (by norm_num [a2] : (1/3:ℝ)≤a2)
  have hiLf : IntervalIntegrable
      (fun u => ∫ v in badLower u..a2,roughPairKernel u v) volume corner (1/3:ℝ) := by
    apply hiL.congr
    intro u hu
    rw [uIoc_of_le (by norm_num [corner])] at hu
    have hg := bad_fibre_geometry (hleft ⟨hu.1.le,hu.2⟩)
    exact (rough_pair_fibre hg.1 hg.2.1 hg.2.2.1).symm
  have hiRf : IntervalIntegrable
      (fun u => ∫ v in badLower u..a2,roughPairKernel u v) volume (1/3:ℝ) a2 := by
    apply hiR.congr
    intro u hu
    rw [uIoc_of_le (by norm_num [a2])] at hu
    have hg := bad_fibre_geometry (hright ⟨hu.1.le,hu.2⟩)
    exact (rough_pair_fibre hg.1 hg.2.1 hg.2.2.1).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals hiLf hiRf]
  congr 1
  · apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num [corner])] at hu
    rw [badLower,bad_first_lower hu.2]
  · apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num [a2])] at hu
    rw [badLower,bad_second_lower hu.1]

end
end ImbalancedChen.P2SeedOmegaLiteralFibre
