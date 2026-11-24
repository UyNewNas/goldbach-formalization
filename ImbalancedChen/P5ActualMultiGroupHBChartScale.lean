import ImbalancedChen.P5SmoothChartPhysicalHBBranch

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- Original PP (S): all original smooth HB groups, followed by an actual
-- dyadic grouping of the complementary INTEGER product. Every comparison
-- below is derived from the literal group coefficients and interval atoms.
namespace ImbalancedChen.P5Z.ActualMultiGroupHBChartScale
noncomputable section
open Classical
open scoped BigOperators
open LiteralHeathBrownOccurrenceWords ActualRoughHeathBrownWords
open HBRightClosedDyadicRoles ActualHBDyadicOccurrenceFamily
open ActualHBDyadicProductWindow ActualHBMediumBranchPartition
open SmoothChartHBDyadicPartition SmoothChartPhysicalHBBranch

structure Group where
  psi : ℝ → ℂ
  R z y : ℝ
  j n : ℕ
  bs : List Block
  w : ℕ → ℂ
  positive : 0 < R
  rough_nonneg : 0 ≤ z
  hb_nonneg : 0 ≤ y
  hb_cube : y^3 = 2*R
  lower_support : ∀ t : ℝ, t < 1/2 → psi t = 0
  upper_support : ∀ t : ℝ, 2 < t → psi t = 0
  order : j ∈ Finset.range 3
  active : chartWeight psi R w n * blockCoefficient z y j n bs ≠ 0

def tuple (g : Group) : List ℕ :=
  Classical.choose (active_coefficient_tuple g.rough_nonneg (mul_ne_zero_iff.mp g.active).2)

theorem tuple_owns (g : Group) : List.Forall₂ Owns g.bs (tuple g) := by
  exact (Classical.choose_spec
    (active_coefficient_tuple g.rough_nonneg (mul_ne_zero_iff.mp g.active).2)).2.2.1

def blocks : List Group → List Block
  | [] => []
  | g::gs => g.bs ++ blocks gs

def integers : List Group → List ℕ
  | [] => []
  | g::gs => tuple g ++ integers gs

def chartX : List Group → ℝ
  | [] => 1
  | g::gs => g.R * chartX gs

def chartN : List Group → ℝ
  | [] => 1
  | g::gs => (g.n : ℝ) * chartN gs

def chartXplus (gs : List Group) : ℝ := (2 : ℝ)^gs.length * chartX gs

def scaleConstant (k : ℕ) : ℝ := 2*(128 : ℝ)^k

theorem scaleConstant_pos (k : ℕ) : 0 < scaleConstant k := by
  unfold scaleConstant
  positivity

theorem scaleConstant_ge_two (k : ℕ) : 2 ≤ scaleConstant k := by
  have h : (1 : ℝ) ≤ 128^k := one_le_pow₀ (by norm_num)
  unfold scaleConstant
  linarith

theorem scaleConstant_mono {k K : ℕ} (hk : k ≤ K) :
    scaleConstant k ≤ scaleConstant K := by
  unfold scaleConstant
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 128) hk) (by norm_num)

theorem raw_append (bs cs : List Block) :
    rawProduct (bs++cs) = rawProduct bs * rawProduct cs := by
  simp [rawProduct,List.map_append,List.prod_append]

theorem all_owns (gs : List Group) : List.Forall₂ Owns (blocks gs) (integers gs) := by
  induction gs with
  | nil => exact List.Forall₂.nil
  | cons g gs ih => exact List.rel_append (tuple_owns g) ih

-- The lower constant is 2^(-7k), and Xplus is exactly 2^k X.
-- No physical R/128 floor or complete-scale comparison is supplied.
theorem whole_geometry (gs : List Group) :
    0 < chartX gs ∧ (blocks gs).length ≤ 6*gs.length ∧
      (1/128 : ℝ)^gs.length * chartX gs ≤ rawProduct (blocks gs) ∧
      rawProduct (blocks gs) ≤ chartXplus gs := by
  induction gs with
  | nil => norm_num [chartX,chartXplus,blocks,rawProduct]
  | cons g gs ih =>
    obtain ⟨hXp,hlen,hlo,hhi⟩ := ih
    obtain ⟨hglen,hg6,hgnlo,hgnhi,hglo,hghi⟩ :=
      active_smooth_rectangle g.positive g.rough_nonneg g.lower_support
        g.upper_support g.w g.order g.active
    have hraw := rawProduct_nonneg (blocks gs)
    refine ⟨mul_pos g.positive hXp,?_,?_,?_⟩
    · simp only [blocks,List.length_append,List.length_cons]
      omega
    · calc
        (1/128 : ℝ)^(g::gs).length * chartX (g::gs) =
            (g.R/128)*((1/128 : ℝ)^gs.length * chartX gs) := by
          simp only [List.length_cons,chartX,pow_succ]
          ring
        _ ≤ rawProduct g.bs * rawProduct (blocks gs) :=
          mul_le_mul hglo hlo (by positivity) (rawProduct_nonneg g.bs)
        _ = rawProduct (blocks (g::gs)) := (raw_append _ _).symm
    · calc
        rawProduct (blocks (g::gs)) = rawProduct g.bs * rawProduct (blocks gs) := raw_append _ _
        _ ≤ (2*g.R)*chartXplus gs :=
          mul_le_mul hghi hhi hraw (by positivity)
        _ = chartXplus (g::gs) := by
          simp only [chartXplus,List.length_cons,chartX,pow_succ]
          ring

-- The original complete integer product is comparable with X before
-- selecting any occurrence. These are consequences of the SAME psi.
theorem original_product_geometry (gs : List Group) :
    0 < chartN gs ∧ chartN gs ≤ (2 : ℝ)^gs.length*chartX gs ∧
      chartX gs ≤ (2 : ℝ)^gs.length*chartN gs := by
  induction gs with
  | nil => norm_num [chartN,chartX]
  | cons g gs ih =>
    have hs := smooth_group_support g.positive g.lower_support g.upper_support
      g.w (mul_ne_zero_iff.mp g.active).1
    obtain ⟨hNp,hN,hX⟩ := ih
    have hn : 0 < (g.n : ℝ) := by linarith
    have hR : g.R ≤ 2*(g.n : ℝ) := by linarith
    refine ⟨mul_pos hn hNp,?_,?_⟩
    · calc
        chartN (g::gs) = (g.n : ℝ)*chartN gs := rfl
        _ ≤ (2*g.R)*((2 : ℝ)^gs.length*chartX gs) :=
          mul_le_mul hs.2 hN hNp.le (by positivity)
        _ = (2 : ℝ)^(g::gs).length*chartX (g::gs) := by
          simp only [List.length_cons,chartX,pow_succ]
          ring
    · calc
        chartX (g::gs) = g.R*chartX gs := rfl
        _ ≤ (2*(g.n : ℝ))*((2 : ℝ)^gs.length*chartN gs) :=
          mul_le_mul hR hX (whole_geometry gs).1.le (by positivity)
        _ = (2 : ℝ)^(g::gs).length*chartN (g::gs) := by
          simp only [List.length_cons,chartN,pow_succ]
          ring

theorem member_scale_le (gs : List Group) (h : ∀ g ∈ gs, 1 ≤ g.R) :
    1 ≤ chartX gs ∧ ∀ g ∈ gs, g.R ≤ chartX gs := by
  revert h
  induction gs with
  | nil => intro h; simp [chartX]
  | cons g gs ih =>
    intro h
    have hg := h g (by simp)
    obtain ⟨hX,hm⟩ := ih (fun b hb => h b (List.mem_cons_of_mem g hb))
    have hp : 0 ≤ chartX gs := (whole_geometry gs).1.le
    have hXmul : chartX gs ≤ g.R*chartX gs := by
      simpa using mul_le_mul_of_nonneg_right hg hp
    refine ⟨le_trans hX hXmul,?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · simpa [chartX] using mul_le_mul_of_nonneg_left hX g.positive.le
    · exact (hm b hb).trans hXmul

-- Select any actual occurrence by a list split. The aligned integer
-- occurrence and both complementary lists are DERIVED from all_owns.
theorem owns_split (left right : List Block) (b : Block) :
    ∀ ps : List ℕ, List.Forall₂ Owns (left++b::right) ps →
      ∃ pl p pr, ps = pl++p::pr ∧ List.Forall₂ Owns left pl ∧
        Owns b p ∧ List.Forall₂ Owns right pr := by
  induction left with
  | nil =>
    intro ps h
    cases h with
    | @cons b p right pr hp hr => exact ⟨[],p,pr,rfl,List.Forall₂.nil,hp,hr⟩
  | cons a left ih =>
    intro ps h
    cases h with
    | @cons a q tail qs hq ht =>
      obtain ⟨pl,p,pr,he,hl,hp,hr⟩ := ih qs ht
      refine ⟨q::pl,p,pr,?_,List.Forall₂.cons hq hl,hp,hr⟩
      simp only [he,List.cons_append]

-- x is not an input. It is the actual selected lower length times the
-- lower atom of the actual complementary integer product. The exact (S)
-- upper constant 2^(6k-1) Xplus and both fixed comparisons are derived.
theorem actual_complementary_scale (gs : List Group)
    (left right : List Block) (b : Block)
    (hsplit : blocks gs = left++b::right) :
    ∃ pl p pr, integers gs = pl++p::pr ∧
      List.Forall₂ Owns left pl ∧ Owns b p ∧ List.Forall₂ Owns right pr ∧
      Owns (owner (pl++pr).prod) (pl++pr).prod ∧
      let x : ℝ := (lower b : ℝ) * (lower (owner (pl++pr).prod) : ℝ)
      0 < x ∧ chartX gs ≤ scaleConstant gs.length*x ∧
        x ≤ (2 : ℝ)^(6*gs.length-1)*chartXplus gs ∧
        x ≤ scaleConstant gs.length*chartX gs := by
  have hall := all_owns gs
  rw [hsplit] at hall
  obtain ⟨pl,p,pr,hints,hl,hp,hr⟩ := owns_split left right b (integers gs) hall
  have hc := owns_product_window (List.rel_append hl hr)
  have hlowerPos : 0 < ((left++right).map lower).prod := by
    apply List.prod_pos
    intro u hu
    obtain ⟨bb,hbb,rfl⟩ := List.mem_map.mp hu
    exact lower_pos bb
  have hcpos : 0 < (pl++pr).prod := hlowerPos.trans_le hc.1
  have howner := owner_owns hcpos
  have ho := owns_bounds howner
  let U : ℝ := lower b
  let M : ℝ := lower (owner (pl++pr).prod)
  let x : ℝ := U*M
  have hU : 0 < U := by exact_mod_cast lower_pos b
  have hM : 0 < M := by exact_mod_cast lower_pos (owner (pl++pr).prod)
  have hrawid : rawProduct (blocks gs) = U*rawProduct (left++right) := by
    rw [hsplit,raw_append,rawProduct_cons,raw_append]
    ring
  have hcLo : rawProduct (left++right) ≤ ((pl++pr).prod : ℝ) := by exact_mod_cast hc.1
  have hcHi : ((pl++pr).prod : ℝ) ≤
      (2 : ℝ)^(left++right).length * rawProduct (left++right) := by exact_mod_cast hc.2
  have hoLo : M ≤ ((pl++pr).prod : ℝ) := by exact_mod_cast ho.1
  have hoHi : ((pl++pr).prod : ℝ) ≤ 2*M := by exact_mod_cast ho.2
  have hrawTwo : rawProduct (blocks gs) ≤ 2*x := by
    have h := mul_le_mul_of_nonneg_left (hcLo.trans hoHi) hU.le
    rw [hrawid]
    dsimp [x]
    nlinarith
  have hxRaw : x ≤ (2 : ℝ)^(left++right).length * rawProduct (blocks gs) := by
    have h := mul_le_mul_of_nonneg_left (hoLo.trans hcHi) hU.le
    rw [hrawid]
    dsimp [x]
    nlinarith
  obtain ⟨hXp,hlen,hrawLo,hrawHi⟩ := whole_geometry gs
  have hlenSplit := congrArg List.length hsplit
  simp only [List.length_append,List.length_cons] at hlenSplit
  have hcompLen : (left++right).length ≤ 6*gs.length-1 := by
    simp only [List.length_append]
    omega
  have hcompLen' : (left++right).length ≤ 6*gs.length := by omega
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcompLen
  have hpow' := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcompLen'
  have hSupper : x ≤ (2 : ℝ)^(6*gs.length-1)*chartXplus gs := by
    calc
      x ≤ (2 : ℝ)^(left++right).length*rawProduct (blocks gs) := hxRaw
      _ ≤ (2 : ℝ)^(6*gs.length-1)*rawProduct (blocks gs) :=
        mul_le_mul_of_nonneg_right hpow (rawProduct_nonneg _)
      _ ≤ (2 : ℝ)^(6*gs.length-1)*chartXplus gs :=
        mul_le_mul_of_nonneg_left hrawHi (by positivity)
  have hupper : x ≤ scaleConstant gs.length*chartX gs := by
    have heq : (2 : ℝ)^(6*gs.length) * 2^gs.length = 128^gs.length := by
      rw [← pow_add,show 6*gs.length+gs.length = 7*gs.length by omega,pow_mul]
      norm_num
    calc
      x ≤ (2 : ℝ)^(left++right).length*rawProduct (blocks gs) := hxRaw
      _ ≤ (2 : ℝ)^(6*gs.length)*rawProduct (blocks gs) :=
        mul_le_mul_of_nonneg_right hpow' (rawProduct_nonneg _)
      _ ≤ (2 : ℝ)^(6*gs.length)*chartXplus gs :=
        mul_le_mul_of_nonneg_left hrawHi (by positivity)
      _ = 128^gs.length*chartX gs := by rw [chartXplus,← mul_assoc,heq]
      _ ≤ scaleConstant gs.length*chartX gs := by
        unfold scaleConstant
        have hnonneg : 0 ≤ (128 : ℝ)^gs.length*chartX gs := by positivity
        nlinarith
  have hcancel : (128 : ℝ)^gs.length *
      ((1/128 : ℝ)^gs.length * chartX gs) = chartX gs := by
    rw [← mul_assoc,← mul_pow]
    norm_num
  have hlower : chartX gs ≤ scaleConstant gs.length*x := by
    calc
      chartX gs = (128 : ℝ)^gs.length*((1/128 : ℝ)^gs.length*chartX gs) := hcancel.symm
      _ ≤ (128 : ℝ)^gs.length*(2*x) :=
        mul_le_mul_of_nonneg_left (hrawLo.trans hrawTwo) (by positivity)
      _ = scaleConstant gs.length*x := by unfold scaleConstant; ring
  exact ⟨pl,p,pr,hints,hl,hp,hr,howner,mul_pos hU hM,hlower,hSupper,hupper⟩

end
end ImbalancedChen.P5Z.ActualMultiGroupHBChartScale
