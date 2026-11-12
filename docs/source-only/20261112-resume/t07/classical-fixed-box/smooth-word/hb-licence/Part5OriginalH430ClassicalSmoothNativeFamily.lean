import ImbalancedChen.Part5OriginalH430ClassicalSmoothAllOccurrences

/-! The actual aggregate as one all-rank integer geometric family. Its
original real argument is a full marked product, with the same prime tuple
weights and an integer extension independent of modulus and arithmetic tests. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothNativeFamily
noncomputable section
open Finset Real Wu2008DoubleSieve
open P5Z.AdmissibleAllRankIntegerGeometricFamily (Family eulerWord licence integerWeight originalWeight)
open P5Z.LicensedOriginalIntegerProfile (chartAmbient groupedProducts listExtension)
open P5Z.PerGroupIntegerHBAtlasPushforward (atlasEval originalProducts sourceTuple)
open Part5OriginalH430ClassicalSmoothEulerBounds (E)
open Part5OriginalH430ClassicalSmoothAllOccurrences
open scoped Classical Topology BigOperators ContDiff

theorem finite_prime_support (ν δ h c : ℝ) (hh : 0<h) (hh' : h≤1/8) (hc : 0<c) (hc' : c≤1/8)
    (N : ℕ) (k : Fin 201) :
    Set.Finite {u : Fin k.val → ℕ | (∀ i,(u i).Prime) ∧
      ambient ν δ h c N k (fun i => (u i:ℝ))≠0} := by
  have hs : Set.Finite ((Set.univ : Set (Fin k.val)).pi (fun _ => Set.Iic (2*N))) :=
    Set.Finite.pi (fun _ => Set.finite_Iic _)
  apply hs.subset
  intro u hu i _
  have hpr : ∀j,(u j).Prime := hu.1
  have hp : 0<∏ j,u j := prod_pos (fun j _ => (hpr j).pos)
  have hcap := (ambient_support hh hh' hc hc' hu.2).2
  have hnat : (∏ j,u j)≤2*N := by
    exact_mod_cast (show ((∏ j,u j:ℕ):ℝ)≤2*(N:ℝ) by simpa only [Nat.cast_prod] using hcap)
  exact (Nat.le_of_dvd hp (dvd_prod_of_mem u (mem_univ i))).trans hnat

def family (ν : ℝ) {δ h c : ℝ} (hd : 0<δ) (hh : 0<h) (hh' : h≤1/8)
    (hc : 0<c) (hc' : c≤1/8) : Family 200 where
  aStar := 1/90
  aStar_pos := by norm_num
  lower := 1/2
  lower_pos := by norm_num
  upper := 2
  upper_pos := by norm_num
  ambient := ambient ν δ h c
  smooth := ambient_smooth ν δ h c
  support := by
    intro N k v hv
    have H := ambient_support hh hh' hc hc' hv
    exact ⟨fun i => by linarith only [H.1 i],H.2⟩
  finitePrimeSupport := finite_prime_support ν δ h c hh hh' hc hc'
  mixedEuler := by
    intro m
    obtain ⟨C,hC,H⟩ := ambient_word_bound ν hd hh hh' hc hc' m
    refine ⟨Nat.ceil C+1,0,Nat.zero_lt_succ _,?_⟩
    intro N k w v hw
    rw [pow_zero,mul_one]
    exact (H N k w hw v).trans ((Nat.le_ceil C).trans
      (by exact_mod_cast (Nat.le_succ (Nat.ceil C))))

/-- This integer pullback uses independent original groups, the original
normalizing dyadic psi factors and the one eta in the complete product. -/
theorem original_hb_pullback (ν : ℝ) {δ h c : ℝ} (hd : 0<δ) (hh : 0<h) (hh' : h≤1/8)
    (hc : 0<c) (hc' : c≤1/8) (N : ℕ) (k : Fin 201) (χ η : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η) (κ₀ : ℝ) (R : Fin k.val → ℝ)
    {m : ℕ} (slots : Fin k.val → Finset (Fin m)) :
    ContDiff ℝ ∞ (fun u => chartAmbient (licence (family ν hd hh hh' hc hc') N k)
      χ η (N:ℝ) κ₀ R (groupedProducts slots u)) :=
  P5Z.AdmissibleAllRankIntegerGeometricFamily.smooth_hb_pullback
    (family ν hd hh hh' hc hc') N k χ η hχ hη κ₀ R slots

/-- Exact per-original-group expansion of the rough normalized von Mangoldt
source of this licensed family, with a test on the original group products. -/
theorem original_lambda_atlas (ν : ℝ) {δ h c : ℝ} (hd : 0<δ) (hh : 0<h) (hh' : h≤1/8)
    (hc : 0<c) (hc' : c≤1/8) (N : ℕ) (k : Fin 201) (χ η : ℝ → ℝ)
    (hone : ∀x : ℝ,x≤1 → χ x=1) (hzero : ∀x : ℝ,2≤x → χ x=0)
    {z : ℝ} (hz : 0≤z) (κ₀ : ℝ) (cjs ns : List ℕ) (hj : cjs.length=k.val)
    (hn : ns.length=k.val) (F : List ℕ → ℂ) :
    let L := licence (family ν hd hh hh' hc hc') N k
    atlasEval χ z cjs ns (fun rows => (listExtension L (originalProducts rows):ℂ)*
      (η (((originalProducts rows).prod:ℝ)/(N:ℝ)^(1-κ₀)):ℂ)*F (originalProducts rows))=
      sourceTuple χ z cjs ns*((listExtension L ns:ℂ)*(η ((ns.prod:ℝ)/(N:ℝ)^(1-κ₀)):ℂ)*F ns) :=
  P5Z.AdmissibleAllRankIntegerGeometricFamily.per_chart_all_rank_atlas
    (family ν hd hh hh' hc hc') N k χ η hone hzero hz κ₀ cjs ns hj hn F

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothNativeFamily

