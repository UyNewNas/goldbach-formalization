import ImbalancedChen.Part5OriginalH430ClassicalRadialSeedCredit
import ImbalancedChen.AffinePrimeWallReserve
import MathlibNt.Wu2008DoubleSieve.NonunitRoughUniformCore

/-! The two outer walls, the five native colour walls, and the order or
penultimate wall. For any one such wall only two prime slots are fixed.
Each remaining complete nonunit rough quotient has its genuine uniform cost. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalProperWallPairs
noncomputable section
open Finset Filter Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2SeedOmegaLiteralFibre (a0 a1 a2 a3 b)
open Part5UpperTables.OriginalU34 (clampStart)
open Part5OriginalH430ClassicalRadialRoughMass (cut)
open scoped Classical Topology BigOperators

abbrev V := Fin 2 → ℝ
abbrev Pair := Fin 2 → ℕ
def proj (i : Fin 2) : V →L[ℝ] ℝ := ContinuousLinearMap.proj i

def forms : Fin 8 → V →L[ℝ] ℝ := ![proj 0,proj 0,
  a0 • proj 0+proj 1,a1 • proj 0+proj 1,a2 • proj 0+proj 1,
  a3 • proj 0+proj 1,b • proj 0+proj 1,proj 0-proj 1]
def intercept (ν : ℝ) : Fin 8 → ℝ := ![clampStart,1/3,a0*ν,a1*ν,a2*ν,a3*ν,b*ν,0]

theorem forms_nonzero (j : Fin 8) : forms j≠0 := by
  intro he
  have hh := congrArg (fun F : V →L[ℝ] ℝ => F ![(1:ℝ),0]) he
  fin_cases j <;> norm_num [forms,proj,a0,a1,a2,a3,b] at hh

def near (N : ℕ) (ν δ : ℝ) (v : Pair) : Prop :=
  actualPrimeTupleLog N v∈primeAffineWallStrip forms (intercept ν) δ

theorem literal_near (N : ℕ) (ν δ : ℝ) (v : Pair) :
    let x := log (v 0:ℝ)/log (N:ℝ); let y := log (v 1:ℝ)/log (N:ℝ)
    near N ν δ v ↔ |x-clampStart|≤δ ∨ |x-1/3|≤δ ∨
      |a0*x+y-a0*ν|≤δ ∨ |a1*x+y-a1*ν|≤δ ∨ |a2*x+y-a2*ν|≤δ ∨
      |a3*x+y-a3*ν|≤δ ∨ |b*x+y-b*ν|≤δ ∨ |x-y|≤δ := by
  dsimp only [near,primeAffineWallStrip,Set.mem_setOf_eq]
  simp [Fin.exists_fin_succ,forms,intercept,proj,actualPrimeTupleLog,smul_eq_mul]

def pairs (N : ℕ) (ν δ : ℝ) : Finset Pair :=
  (actualPrimeBoxTuples N (fun _ : Fin 2 => (1/96:ℝ)) (fun _ => (2:ℝ))).filter (near N ν δ)

def quotient (N : ℕ) (v : Pair) : Finset ℕ :=
  (roughNumbers (2*(N:ℝ)/((v 0*v 1:ℕ):ℝ)) (cut N)).erase 1

def outputs (N : ℕ) (ν δ : ℝ) : Finset ℕ :=
  ((pairs N ν δ).sigma (quotient N)).image (fun u => u.1 0*u.1 1*u.2)

/-- The estimate holds at all real nonintegral heights and includes the
case x<z where the nonunit carrier is empty. -/
theorem nonunit_quotient_bound :
    ∃ A : ℝ,0<A ∧ ∀ᶠ N : ℕ in atTop,∀ v : Pair,0<v 0 → 0<v 1 →
      (log (N:ℝ)/(N:ℝ))*((quotient N v).card:ℝ)≤A*(1/(v 0:ℝ))*(1/(v 1:ℝ)) := by
  obtain ⟨C,hC,hcount⟩ := roughCount_buchstab_band_100
  let A := 192*(1+2*C)
  refine ⟨A,by dsimp [A]; positivity,?_⟩
  have hcut : Tendsto cut atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/96)).comp tendsto_natCast_atTop_atTop
  have hpow := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/24)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop (1:ℕ),hcut.eventually_ge_atTop primeErrorStart,
    (tendsto_buchstabRemainder.comp hcut).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    hpow.eventually_ge_atTop 2] with N hN hstart herr hpowN
  intro v hp hq
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have h0 := zero_lt_one.trans hNr
  have hlog := log_pos hNr
  have hz : 1<cut N := one_lt_rpow hNr (by norm_num)
  have hden : (0:ℝ)<(v 0*v 1:ℕ) := Nat.cast_pos.mpr (Nat.mul_pos hp hq)
  let x := 2*(N:ℝ)/((v 0*v 1:ℕ):ℝ)
  have hx : 0<x := div_pos (by positivity) hden
  have hzlog : log (cut N)=(1/96)*log (N:ℝ) := log_rpow h0 _
  have hnorm : 0≤log (N:ℝ)/(N:ℝ) := div_nonneg hlog.le h0.le
  by_cases hzx : cut N≤x
  · have hden1 : 1≤v 0*v 1 := Nat.mul_pos hp hq
    have hxcap : x≤2*(N:ℝ) := div_le_self (by positivity) (by exact_mod_cast hden1)
    have hhi : 2*(N:ℝ)≤cut N^100 := by
      calc
        _ ≤ (N:ℝ)^(1/24:ℝ)*(N:ℝ) := mul_le_mul_of_nonneg_right hpowN h0.le
        _ = (N:ℝ)^(1/24+1:ℝ) := by rw [rpow_add h0,rpow_one]
        _ = cut N^100 := by rw [show (1/24+1:ℝ)=(1/96)*(100:ℝ) by norm_num,
          rpow_mul h0.le,rpow_natCast] <;> rfl
    have h := (abs_le.mp (hcount x (cut N) hstart hzx (hxcap.trans hhi))).2
    have hratio : 1≤log x/log (cut N) := (one_le_div (log_pos hz)).mpr
      (log_le_log (zero_lt_one.trans hz) hzx)
    have hb := mul_le_mul_of_nonneg_left (buchstab_le_one hratio) hx.le
    have hb' := div_le_div_of_nonneg_right hb (log_pos hz).le
    have hr := mul_le_mul_of_nonneg_right herr.le (div_nonneg hx.le (log_pos hz).le)
    have hc := div_le_div_of_nonneg_right hzx (log_pos hz).le
    have he := mul_le_mul_of_nonneg_left (add_le_add hr hc) hC.le
    have hqcard : ((quotient N v).card:ℝ)≤(roughCount x (cut N):ℝ) :=
      Nat.cast_le.mpr (card_le_card (erase_subset _ _))
    have hu : ((quotient N v).card:ℝ)≤(1+2*C)*(x/log (cut N)) := by
      linarith only [h,hb',he,hqcard]
    apply (mul_le_mul_of_nonneg_left hu hnorm).trans_eq
    dsimp only [x,A]
    rw [hzlog,Nat.cast_mul]
    field_simp [h0.ne',hlog.ne',(Nat.cast_pos.mpr hp : (0:ℝ)<v 0).ne',
      (Nat.cast_pos.mpr hq : (0:ℝ)<v 1).ne'] <;> ring
  · have he : quotient N v=∅ := NonunitRoughUniform.nonunit_empty hz.le (lt_of_not_ge hzx)
    rw [he,card_empty,Nat.cast_zero,mul_zero]
    dsimp only [A]
    positivity

theorem output_wall_budget (ν : ℝ) {ε : ℝ} (he : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ᶠ N : ℕ in atTop,
      (log (N:ℝ)/(N:ℝ))*((outputs N ν δ).card:ℝ)≤ε := by
  obtain ⟨A,hA,hQ⟩ := nonunit_quotient_bound
  obtain ⟨δ,hd,T,hT,hstrip⟩ := exists_actualPrimeAffineWallStrip_mass_lt
    (by norm_num : (0:ℝ)<1/96) (by norm_num : (1/96:ℝ)<2) forms (intercept ν) forms_nonzero
    (ε/A) (div_pos he hA)
  refine ⟨δ,hd,?_⟩
  filter_upwards [hQ,eventually_ge_atTop T] with N hq hN
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hn : 0≤log (N:ℝ)/(N:ℝ) := div_nonneg (log_pos hNr).le (Nat.cast_nonneg _)
  have hs : ((outputs N ν δ).card:ℝ)≤∑ v∈pairs N ν δ,((quotient N v).card:ℝ) := by
    have hcard : (outputs N ν δ).card≤((pairs N ν δ).sigma (quotient N)).card :=
      card_image_le
    rw [card_sigma] at hcard
    exact_mod_cast hcard
  have hmain := (mul_le_mul_of_nonneg_left hs hn).trans_eq (mul_sum ..)
  have hrow (v : Pair) (hv : v∈pairs N ν δ) :
      (log (N:ℝ)/(N:ℝ))*((quotient N v).card:ℝ)≤A*∏ i,1/((v i:ℝ)-1) := by
    have hh := mem_actualPrimeBoxTuples_iff.mp (mem_filter.mp hv).1
    have hpos (i : Fin 2) : (1:ℝ)<v i := by exact_mod_cast (hh i).1.one_lt
    have ht (i : Fin 2) : 1/(v i:ℝ)≤1/((v i:ℝ)-1) :=
      one_div_le_one_div_of_le (sub_pos.mpr (hpos i)) (by linarith)
    rw [Fin.prod_univ_two]
    exact (hq v (hh 0).1.pos (hh 1).1.pos).trans (by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (ht 0) (ht 1)
        (by positivity) (one_div_pos.mpr (sub_pos.mpr (hpos 0))).le) hA.le)
  have hu := hmain.trans (sum_le_sum hrow)
  rw [←mul_sum] at hu
  have hstripN := hstrip N hN
  have heq : (∑ v∈pairs N ν δ,∏ i,1/((v i:ℝ)-1))=
      actualPrimeAffineWallStripMass N (fun _ : Fin 2 => 1/96) (fun _ => 2) forms (intercept ν) δ := rfl
  rw [heq] at hu
  exact hu.trans (by have h' := (lt_div_iff₀ hA).mp hstripN; linarith only [h'])

end
end ImbalancedChen.Part5OriginalH430ClassicalProperWallPairs
