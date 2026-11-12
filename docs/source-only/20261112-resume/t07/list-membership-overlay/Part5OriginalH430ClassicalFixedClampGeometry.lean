import ImbalancedChen.Part5OriginalH430ClassicalFixedClampMarks

/-! Sharp product geometry of all twenty unmasked occurrences on the whole
clamp. The outer prime is the first letter of M. The quotient factors are
nondecreasing and may coincide with each other or with a prefix prime. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalFixedClampGeometry
noncomputable section
open Finset Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedNonunitLabelGeometry (label_data label_prod_pos)
open P2EnhancedShortWordUnitBound (label_product_cap)
open P2EnhancedExactExceptionTheta (original_word_arity)
open P2SeedOmegaLiteralFibre (a0 b)
open Part5UpperTables.OriginalU34 (clampStart)
open Part5OriginalH430ClassicalCausalSeedScale (smallProduct)
open Part5OriginalH430ClassicalSmallSwitchedIntegers (largeIntegers)
open Part5OriginalH430ClassicalFixedClampMarks
open scoped Classical BigOperators

def expanded (u : Mark) := letters u++u.2.2.primeFactorsList

theorem prime_divisor_floor {L : List ℕ} {z : ℝ}
    (hL : ∀q∈L,q.Prime ∧ z≤(q:ℝ)) (v : ℕ) (hv : v.Prime) (hd : v∣L.prod) : z≤(v:ℝ) := by
  induction L with
  | nil => exact (hv.not_dvd_one hd).elim
  | cons p L ih =>
    rcases hv.dvd_mul.mp hd with h | h
    · have hp := hL p (List.mem_cons_self)
      rw [(Nat.prime_dvd_prime_iff_eq hv hp.1).mp h]
      exact hp.2
    · exact ih (fun q hq => hL q (List.mem_cons_of_mem _ hq)) h

theorem prefix_data {N : ℕ} {ν κ : ℝ} {cs : List ℕ} {u : Mark}
    (hN : 1<N) (hν : 1/3+7/128≤ν) (hu : u∈marks 1 N ν κ cs) :
    (letters u).length=cs.length+1 ∧ 0<(letters u).prod ∧
      (∀ q∈letters u,q.Prime ∧ (N:ℝ)^(1/200:ℝ)≤(q:ℝ)) ∧
      0<u.2.2 ∧ 0<product u ∧ product u≤N ∧ smallProduct N κ<(product u:ℝ) := by
  obtain ⟨hp,hq,hm⟩ := flags.mp hu
  have h := mem_primeWindow.mp hp
  have hw := label_data hq
  have hscale := platform hN hν hp
  have hpos : 0<u.1*u.2.1.prod := Nat.mul_pos h.1.pos (label_prod_pos hq)
  obtain ⟨hr,hh⟩ := mem_filter.mp hm
  obtain ⟨hmpos,hmcap,_⟩ := mem_roughNumbers.mp hr
  refine ⟨by simp only [letters,List.length_cons,hw.1],hpos,?_,hmpos,Nat.mul_pos hpos hmpos,?_,hh⟩
  · intro q hmem
    rcases List.mem_cons.mp hmem with he | he
    · rw [he]
      exact ⟨h.1,hscale.2.2.2⟩
    · have hv := mem_primeWindow.mp (hw.2.2.1 q he)
      exact ⟨hv.1,hscale.2.2.1.trans hv.2.2.1⟩
  · have hreal := (le_div_iff₀ (Nat.cast_pos.mpr hpos : (0:ℝ)<(u.1*u.2.1.prod:ℕ))).mp hmcap
    unfold product
    exact_mod_cast (by simpa only [mul_comm] using hreal :
      ((u.1*u.2.1.prod:ℕ):ℝ)*(u.2.2:ℝ)≤(N:ℝ))

private theorem original_minimum {cs : List ℕ} (j : Fin 13)
    (hc : cs∈secondFunctionalMotherGammaWords (9+j.val)) : 3≤cs.length := by
  fin_cases j <;> norm_num [secondFunctionalMotherGammaWords] at hc <;> aesop

theorem prefix_unit_below {N : ℕ} {ν κ : ℝ} {cs : List ℕ} {u : Mark} (j : Fin 13)
    (hc : cs∈secondFunctionalMotherGammaWords (9+j.val))
    (hN : 1<N) (hν : 1/3+7/128≤ν) (hν' : ν≤1/2) (hk : κ≤1/112)
    (hu : u∈marks 1 N ν κ cs) : ((letters u).prod:ℝ)≤smallProduct N κ := by
  obtain ⟨hp,hq,_⟩ := flags.mp hu
  let p := u.1
  let R := (N:ℝ)^ν/(p:ℝ)
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have h0 := zero_lt_one.trans hNr
  have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr (mem_primeWindow.mp hp).1.pos
  have hR : 1<R := (platform hN hν hp).2.1
  have hR0 := zero_lt_one.trans hR
  have hlen := original_word_arity (by omega) (by omega) hc
  have hlen' : (cs.length:ℝ)≤6 := by exact_mod_cast hlen
  have hprod := (label_product_cap hR hq).trans (rpow_le_rpow_of_exponent_le hR.le
    (show b*(cs.length:ℝ)≤3 by unfold b; linarith only [hlen']))
  have hlp := log_le_log (rpow_pos_of_pos h0 _) (mem_primeWindow.mp hp).2.2.1
  rw [log_rpow h0] at hlp
  change ((p*u.2.1.prod:ℕ):ℝ)≤(N:ℝ)^(1-κ)
  rw [Nat.cast_mul]
  apply (mul_le_mul_of_nonneg_left hprod hp0.le).trans
  apply (log_le_log_iff (mul_pos hp0 (rpow_pos_of_pos hR0 _)) (rpow_pos_of_pos h0 _)).mp
  rw [log_mul hp0.ne' (rpow_pos_of_pos hR0 _).ne',log_rpow hR0,log_rpow h0,
    show log R=ν*log (N:ℝ)-log (p:ℝ) by rw [R,log_div (rpow_pos_of_pos h0 _).ne' hp0.ne',log_rpow h0]]
  have hνlog := mul_le_mul_of_nonneg_right hν' (log_pos hNr).le
  have hklog := mul_le_mul_of_nonneg_right hk (log_pos hNr).le
  norm_num [clampStart] at hlp
  linarith only [hlp,hνlog,hklog,log_pos hNr]

theorem expanded_geometry {N : ℕ} {ν κ : ℝ} {cs : List ℕ} {u : Mark} (j : Fin 13)
    (hc : cs∈secondFunctionalMotherGammaWords (9+j.val))
    (hN : 1<N) (hν : 1/3+7/128≤ν) (hν' : ν≤1/2) (hk : κ≤1/112)
    (hu : u∈marks 1 N ν κ cs) :
    let rs := u.2.2.primeFactorsList
    rs.Pairwise (·≤·) ∧ (∀ q∈rs,u.2.1.getD (u.2.1.length-2) 0≤q) ∧
      (expanded u).prod=product u ∧ (∀ q∈expanded u,q.Prime ∧ (N:ℝ)^(1/200:ℝ)≤(q:ℝ)) ∧
      5≤(expanded u).length ∧ (expanded u).length≤200 := by
  obtain ⟨hp,hq,hm⟩ := flags.mp hu
  obtain ⟨hl,hpos,hs,hmpos,hM,hMN,hX⟩ := prefix_data hN hν hu
  let qs := u.2.1
  let m := u.2.2
  let rs := m.primeFactorsList
  have hlen : 3≤qs.length := (label_data hq).1.symm ▸ original_minimum j hc
  have hi : qs.length-2<qs.length := by omega
  have hpen : qs.getD (qs.length-2) 0∈qs := by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  have hh := (mem_roughNumbers.mp (mem_filter.mp hm).1).2.2
  have htail (q : ℕ) (hqrs : q∈rs) : q.Prime ∧ qs.getD (qs.length-2) 0≤q := by
    have hpq := Nat.prime_of_mem_primeFactorsList hqrs
    exact ⟨hpq,by exact_mod_cast hh q hpq (Nat.dvd_of_mem_primeFactorsList hqrs)⟩
  have h1 : m≠1 := by
    intro he
    have hP : product u=(letters u).prod := by change _*m=_; rw [he,mul_one] <;> rfl
    rw [hP] at hX
    exact (not_lt_of_ge (prefix_unit_below j hc hN hν hν' hk hu)) hX
  have htailLen : 0<rs.length := List.length_pos_iff.mpr (by
    intro he
    have h : rs.prod=m := Nat.prod_primeFactorsList hmpos.ne'
    rw [he,List.prod_nil] at h
    exact h1 h.symm)
  have hprod : (expanded u).prod=product u := by
    simp only [expanded,letters,List.prod_append,List.prod_cons,Nat.prod_primeFactorsList hmpos.ne',product]
  have hletters (q : ℕ) (h : q∈expanded u) : q.Prime ∧ (N:ℝ)^(1/200:ℝ)≤(q:ℝ) := by
    rcases List.mem_append.mp h with h | h
    · exact hs q h
    · exact ⟨(htail q h).1,(hs _ (List.mem_cons_of_mem _ hpen)).2.trans
        (by exact_mod_cast (htail q h).2)⟩
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have hbound := List.prod_map_le_prod_map₀ (s:=expanded u) (fun _ : ℕ => (N:ℝ)^(1/200:ℝ))
    (fun q : ℕ => (q:ℝ)) (fun _ _ => rpow_nonneg (Nat.cast_nonneg N) _) (fun q h => (hletters q h).2)
  have hpow : (N:ℝ)^((1/200)*((expanded u).length:ℝ))≤(N:ℝ)^(1:ℝ) := by
    rw [rpow_mul (Nat.cast_nonneg N),rpow_natCast,rpow_one]
    have hbound' : ((N:ℝ)^(1/200:ℝ))^(expanded u).length≤((expanded u).prod:ℝ) := by
      simpa only [List.map_const',List.prod_replicate,Nat.cast_list_prod] using hbound
    rw [hprod] at hbound'
    exact hbound'.trans (by exact_mod_cast hMN)
  have hmax := (rpow_le_rpow_left_iff hNr).mp hpow
  refine ⟨(Nat.primeFactorsList_sorted _).pairwise,fun q h => (htail q h).2,hprod,hletters,?_,?_⟩
  · change 5≤(letters u++rs).length
    rw [List.length_append,hl]
    have hcs := original_minimum j hc
    omega
  · exact_mod_cast (by linarith only [hmax] : ((expanded u).length:ℝ)≤200)

end
end ImbalancedChen.Part5OriginalH430ClassicalFixedClampGeometry
