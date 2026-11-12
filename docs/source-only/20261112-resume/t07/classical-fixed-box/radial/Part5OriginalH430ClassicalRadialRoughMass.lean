import ImbalancedChen.Part5OriginalH430ClassicalFixedClampSeedPrice
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabBands

/-! Two physical endpoint counts on a single fixed large-prime cutoff.
Their absolute Buchstab errors tend to zero after the N/log N normalization.
The product wall is measured in y=M/N. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalRadialRoughMass
noncomputable section
open Filter Finset Real LiLiuPrereqBuchstab
open scoped Classical Topology BigOperators

def cut (N : ℕ) : ℝ := (N:ℝ)^(1/96:ℝ)
def norm (N : ℕ) : ℝ := log (N:ℝ)/(N:ℝ)
def shell (N : ℕ) (b c : ℝ) : Finset ℕ :=
  roughNumbers (c*(N:ℝ)) (cut N) \ roughNumbers (b*(N:ℝ)) (cut N)

private theorem cut_div_N :
    Tendsto (fun N : ℕ => cut N/(N:ℝ)) atTop (𝓝 0) := by
  apply ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<95/96)).comp
    tendsto_natCast_atTop_atTop).congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have h0 : (0:ℝ)<N := Nat.cast_pos.mpr hN
  change (N:ℝ)^(-(95/96:ℝ))=(N:ℝ)^(1/96:ℝ)/(N:ℝ)
  rw [show -(95/96:ℝ)=1/96-1 by norm_num,rpow_sub h0,rpow_one]

private theorem parameters {c : ℝ} (hc : 0<c) :
    Tendsto (fun N : ℕ => log (c*(N:ℝ))/log (cut N)) atTop (𝓝 96) := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ => (96*log c)/log (N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hh := hsmall.const_add 96
  rw [add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1:ℕ)] with N hN
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have h0 := zero_lt_one.trans hNr
  simp only [cut,log_mul hc.ne' h0.ne',log_rpow h0]
  field_simp [(log_pos hNr).ne'] <;> ring

theorem endpoint {c : ℝ} (hc : 0<c) :
    Tendsto (fun N : ℕ => norm N*(roughCount (c*(N:ℝ)) (cut N):ℝ))
      atTop (𝓝 (96*c*buchstab 96)) := by
  obtain ⟨C,hC,hband⟩ := roughCount_buchstab_band_100
  let main := fun N : ℕ => 96*c*buchstab (log (c*(N:ℝ))/log (cut N))
  let error := fun N : ℕ => (96*C)*(c*buchstabRemainder (cut N)+cut N/(N:ℝ))
  let X := fun N : ℕ => norm N*(roughCount (c*(N:ℝ)) (cut N):ℝ)
  have hcut : Tendsto cut atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/96)).comp tendsto_natCast_atTop_atTop
  have hmain : Tendsto main atTop (𝓝 (96*c*buchstab 96)) :=
    ((continuous_buchstab.tendsto 96).comp (parameters hc)).const_mul _
  have herror : Tendsto error atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using
      ((((tendsto_buchstabRemainder.comp hcut).const_mul c).add cut_div_N).const_mul (96*C))
  have hpow := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/24)).comp tendsto_natCast_atTop_atTop
  have hb : ∀ᶠ N : ℕ in atTop,|X N-main N|≤error N := by
    filter_upwards [eventually_gt_atTop (1:ℕ),hcut.eventually_ge_atTop primeErrorStart,
      cut_div_N.eventually (gt_mem_nhds hc),hpow.eventually_ge_atTop c] with N hN hstart hlo hhi
    have hNr : (1:ℝ)<N := by exact_mod_cast hN
    have h0 := zero_lt_one.trans hNr
    have hL := log_pos hNr
    have hlogcut : log (cut N)=(1/96)*log (N:ℝ) := log_rpow h0 _
    have hhigh : c*(N:ℝ)≤cut N^100 := by
      have hh := mul_le_mul_of_nonneg_right hhi h0.le
      calc
        _ ≤ (N:ℝ)^(1/24:ℝ)*(N:ℝ) := hh
        _ = (N:ℝ)^(1/24+1:ℝ) := by rw [rpow_add h0,rpow_one]
        _ = cut N^100 := by
          rw [show (1/24+1:ℝ)=(1/96)*(100:ℝ) by norm_num,rpow_mul h0.le,rpow_natCast] <;> rfl
    have hlow : cut N<c*(N:ℝ) := (div_lt_iff₀ h0).mp hlo
    have hm := hband (c*(N:ℝ)) (cut N) hstart hlow.le hhigh
    have hnorm : 0≤norm N := div_nonneg hL.le h0.le
    have heq : X N-main N=norm N*((roughCount (c*(N:ℝ)) (cut N):ℝ)-
        (c*(N:ℝ))*buchstab (log (c*(N:ℝ))/log (cut N))/log (cut N)) := by
      dsimp only [X,main,norm]
      rw [hlogcut]
      field_simp [h0.ne',hL.ne'] <;> ring
    rw [heq,abs_mul,abs_of_nonneg hnorm]
    apply (mul_le_mul_of_nonneg_left hm hnorm).trans_eq
    dsimp only [norm,error]
    rw [hlogcut]
    field_simp [h0.ne',hL.ne'] <;> ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [sub_zero] using hmain.sub herror)
    (by simpa only [add_zero] using hmain.add herror)
  · filter_upwards [hb] with N hN
    linarith only [(abs_le.mp hN).1]
  · filter_upwards [hb] with N hN
    linarith only [(abs_le.mp hN).2]

theorem mem_shell {N M : ℕ} {b c : ℝ} :
    M∈shell N b c ↔ 0<M ∧ b*(N:ℝ)<(M:ℝ) ∧ (M:ℝ)≤c*(N:ℝ) ∧ Rough (cut N) M := by
  simp only [shell,mem_sdiff,mem_roughNumbers]
  constructor
  · rintro ⟨⟨hM,hhi,hr⟩,he⟩
    exact ⟨hM,lt_of_not_ge (fun h => he ⟨hM,h,hr⟩),hhi,hr⟩
  · rintro ⟨hM,hlo,hhi,hr⟩
    exact ⟨⟨hM,hhi,hr⟩,fun h => (not_le_of_gt hlo) h.2.1⟩

theorem shell_limit {b c : ℝ} (hb : 0<b) (hbc : b≤c) :
    Tendsto (fun N : ℕ => norm N*((shell N b c).card:ℝ)) atTop
      (𝓝 (96*(c-b)*buchstab 96)) := by
  have h := (endpoint (hb.trans_le hbc)).sub (endpoint hb)
  have he : 96*c*buchstab 96-96*b*buchstab 96=96*(c-b)*buchstab 96 := by ring
  rw [he] at h
  apply h.congr'
  filter_upwards [] with N
  have hs : roughNumbers (b*(N:ℝ)) (cut N)⊆roughNumbers (c*(N:ℝ)) (cut N) := by
    intro m hm
    obtain ⟨hm0,hmle,hr⟩ := mem_roughNumbers.mp hm
    exact mem_roughNumbers.mpr ⟨hm0,hmle.trans (mul_le_mul_of_nonneg_right hbc (Nat.cast_nonneg N)),hr⟩
  have hh := card_sdiff_add_card_eq_card hs
  have hcast : ((shell N b c).card:ℝ)+(roughCount (b*(N:ℝ)) (cut N):ℝ)=
      (roughCount (c*(N:ℝ)) (cut N):ℝ) := by exact_mod_cast hh
  dsimp only
  rw [←hcast]
  ring

end
end ImbalancedChen.Part5OriginalH430ClassicalRadialRoughMass
