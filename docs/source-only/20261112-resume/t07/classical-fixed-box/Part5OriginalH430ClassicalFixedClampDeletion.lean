import ImbalancedChen.Part5OriginalH430ClassicalFixedClampGeometry
import ImbalancedChen.P5U7ActualRoughTargetExclusion
import ImbalancedChen.PowerErrorBudget
import MathlibNt.Wu2008DoubleSieve.Omega3Multiplicity

/-! Deleting p or a specified colour prime dividing N changes the
untested sum by o(N/log N). The multiplicity proof retains p and
every ordered colour slot at a fixed complete output. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalFixedClampDeletion
noncomputable section
open Finset Filter Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedExactExceptionTheta (original_word_arity)
open Part5OriginalH430ClassicalSeedIntegralCap
open Part5OriginalH430ClassicalFixedClampMarks
open Part5OriginalH430ClassicalFixedClampGeometry
open Part5OriginalH430ClassicalSmallSwitchedIntegers (testWeight)
open scoped Classical Topology BigOperators

def deletionCost (N : ℕ) : ℝ :=
  (20*200^7)*(log (N:ℝ)/log 2)*((N:ℝ)/(N:ℝ)^(1/200:ℝ))

private theorem word_deletion {N : ℕ} {ν κ : ℝ} (j : Fin 13) {cs : List ℕ}
    (hc : cs∈secondFunctionalMotherGammaWords (9+j.val)) (hN : 1<N)
    (hν : 1/3+7/128≤ν) (hν' : ν≤1/2) (hk : κ≤1/112) :
    ((marks 1 N ν κ cs \ marks N N ν κ cs).card:ℝ)≤
      (200:ℝ)^7*(log (N:ℝ)/log 2)*((N:ℝ)/(N:ℝ)^(1/200:ℝ)) := by
  let S := marks 1 N ν κ cs \ marks N N ν κ cs
  let H := (N:ℝ)^(1/200:ℝ)
  let E := p5U7ActualBadRough N N H
  let coords := fun u : Mark => fun i : Fin (cs.length+1) => (letters u).getD i 0
  have hknown {u : Mark} (h : u∈S) := prefix_data hN hν (mem_sdiff.mp h).1
  have hinj : Set.InjOn (fun u : Mark => (product u,coords u)) S := by
    rintro ⟨p,qs,m⟩ hu ⟨p',qs',m'⟩ hv he
    have hcoords := congrArg Prod.snd he
    have hl := HighNonunit.list_eq_of_getD (hknown hu).1 (hknown hv).1 hcoords
    change p::qs=p'::qs' at hl
    obtain ⟨hp,hqs⟩ := List.cons.inj hl
    subst p'
    subst qs'
    have hprod := congrArg Prod.fst he
    change (p*qs.prod)*m=(p*qs.prod)*m' at hprod
    have hm := Nat.eq_of_mul_eq_mul_left (hknown hu).2.1 hprod
    subst m'
    rfl
  have hout (u : Mark) (hu : u∈S) : product u∈E := by
    obtain ⟨hu1,huN⟩ := mem_sdiff.mp hu
    obtain ⟨_,_,hprod,hs,_,_⟩ := expanded_geometry j hc hN hν hν' hk hu1
    obtain ⟨_,_,_,_,hM,hcap,_⟩ := hknown hu
    apply mem_filter.mpr
    refine ⟨mem_roughNumbers.mpr ⟨hM,by exact_mod_cast hcap,?_⟩,?_⟩
    · intro q hq hdiv
      exact prime_divisor_floor hs q hq (hprod.symm ▸ hdiv)
    · intro hcop
      apply huN
      refine exact_target_mask.mpr ⟨hu1,fun q hq => hcop.of_dvd_left ?_⟩
      exact (List.dvd_prod hq).trans (dvd_mul_right (letters u).prod u.2.2)
  have hlabel (u : Mark) (hu : u∈S) (i : Fin (cs.length+1)) :
      (coords u i).Prime ∧ coords u i∣product u ∧ H≤(coords u i:ℝ) := by
    have hi : i.val<(letters u).length := by rw [(hknown hu).1]; exact i.isLt
    have hm : coords u i∈letters u := by
      change (letters u).getD i.val 0∈letters u
      rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    obtain ⟨hprime,hlo⟩ := (hknown hu).2.2.1 _ hm
    exact ⟨hprime,(List.dvd_prod hm).trans (dvd_mul_right (letters u).prod u.2.2),hlo⟩
  have hcard := omega3_labels_card_le_outputs S product coords E hinj hout hN
    (by norm_num : (0:ℝ)<1/200) (fun u hu => ⟨(hknown hu).2.2.2.2.1,(hknown hu).2.2.2.2.2.1⟩) hlabel
  have hE := p5U7ActualBadRough_card_le_log (N:=N) (x:=(N:ℝ)) (z:=H) (by omega)
    (Nat.cast_nonneg N) (rpow_pos_of_pos (by exact_mod_cast (show 0<N by omega)) _)
  have hr := original_word_arity (by omega) (by omega) hc
  calc
    _ ≤ (200:ℝ)^(cs.length+1)*(E.card:ℝ) := by convert hcard using 1 <;> norm_num
    _ ≤ (200:ℝ)^7*(E.card:ℝ) := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤200) (by omega)) (Nat.cast_nonneg _)
    _ ≤ (200:ℝ)^7*((log (N:ℝ)/log 2)*((N:ℝ)/H)) :=
      mul_le_mul_of_nonneg_left hE (by norm_num)
    _ = _ := by ring

theorem complete_deletion_le {N : ℕ} {ν κ : ℝ} (hN : 1<N)
    (hν : 1/3+7/128≤ν) (hν' : ν≤1/2) (hk : κ≤1/112) :
    count false 1 N ν κ≤count false N N ν κ+deletionCost N := by
  let C := (200:ℝ)^7*(log (N:ℝ)/log 2)*((N:ℝ)/(N:ℝ)^(1/200:ℝ))
  have h := words_mono (F:=fun w => ((marks 1 N ν κ w).card:ℝ))
    (G:=fun w => ((marks N N ν κ w).card:ℝ)+C) (by
      intro j w hw
      have hsub : marks N N ν κ w⊆marks 1 N ν κ w := fun u h => (exact_target_mask.mp h).1
      have hh := word_deletion j hw hN hν hν' hk
      have he := Finset.card_sdiff_add_card_eq_card hsub
      have he' : (((marks 1 N ν κ w \ marks N N ν κ w).card:ℝ)+(marks N N ν κ w).card)=
          (marks 1 N ν κ w).card := by exact_mod_cast he
      dsimp only [C]
      linarith only [he',hh])
  rw [words_add,words_const] at h
  simpa only [count,testWeight,Bool.false_eq_true,if_false,sum_const,nsmul_eq_mul,mul_one,
    C,deletionCost,mul_assoc] using h

theorem deletion_vanishes :
    Tendsto (fun N : ℕ => log (N:ℝ)/(N:ℝ)*deletionCost N) atTop (𝓝 0) := by
  have h := (tendsto_nat_log_pow_div_rpow 2 (by norm_num : (0:ℝ)<1/200)).const_mul
    ((20*200^7:ℝ)/log 2)
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have hN' : (N:ℝ)≠0 := (Nat.cast_pos.mpr hN).ne'
  dsimp only [deletionCost]
  field_simp [hN',(log_pos (by norm_num : (1:ℝ)<2)).ne',
    (rpow_pos_of_pos (Nat.cast_pos.mpr hN) (1/200:ℝ)).ne'] <;> ring

end
end ImbalancedChen.Part5OriginalH430ClassicalFixedClampDeletion
