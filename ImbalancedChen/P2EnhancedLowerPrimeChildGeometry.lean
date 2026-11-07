import ImbalancedChen.P2EnhancedLowerPrimeChildCarriers

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Same-Q residual/logarithmic identities for actual child MEMBERS, literal
physical child cutoffs, and the residual full-square gates derived from
the original BH/W1/W2 domains. Old history is untouched; parent admission
is not supplied as a fake field. No analytical count licence is inferred.
-/

namespace ImbalancedChen.P2EnhancedLowerPrimeChildGeometry
noncomputable section
open Set Classical
open P2EnhancedLowerPrimeChildCarriers P5OriginalActionMassBound

def physicalLevel (N : ℕ) (Q : ℝ) (old : List ℕ) : ℝ :=
  Real.log (residualLevel Q old)/Real.log (N : ℝ)

theorem parentWindow_logs {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    (h : parentWindow N Q old chi) :
    0<Real.log (N : ℝ) ∧ 1<residualLevel Q old ∧ 0<physicalLevel N Q old := by
  have hN : (1 : ℝ)<N := by exact_mod_cast h.1
  have hB : (0 : ℝ)<parentProduct old := by exact_mod_cast h.2.1
  have hR : 1<residualLevel Q old := by
    apply (lt_div_iff₀ hB).mpr
    simpa only [one_mul] using h.2.2.1
  exact ⟨Real.log_pos hN,hR,div_pos (Real.log_pos hR) (Real.log_pos hN)⟩

theorem relativePrime_physical {N p : ℕ} {Q chi : ℝ} {old : List ℕ}
    (h : parentWindow N Q old chi) :
    physicalLevel N Q old*relativePrime Q old p=physicalPrime N p := by
  have hl := parentWindow_logs h
  unfold physicalLevel relativePrime physicalPrime
  field_simp [(Real.log_pos hl.2.1).ne',hl.1.ne'] <;> ring

theorem single_residual_level (Q : ℝ) (old : List ℕ) (p : ℕ) :
    residualLevel Q (singleWord old p)=residualLevel Q old/(p : ℝ) := by
  simp [residualLevel,parentProduct,singleWord,Nat.cast_mul,div_div]

theorem pair_residual_level (Q : ℝ) (old : List ℕ) (small large : ℕ) :
    residualLevel Q (pairWord old small large)=
      residualLevel Q old/((large : ℝ)*(small : ℝ)) := by
  simp [residualLevel,parentProduct,pairWord,Nat.cast_mul,div_div,mul_assoc]

theorem single_actual_residual {rule : SingleRule} {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    {p : Fin (N+1)} (hp : p ∈ singleChildren rule N Q old chi) :
    1<residualLevel Q (singleWord old p.val) ∧
      (singleWord old p.val).prod≤N ∧
      physicalLevel N Q (singleWord old p.val)=physicalLevel N Q old-physicalPrime N p.val := by
  have h := mem_singleChildren.mp hp
  have hw := h.2.1
  have hlogs := parentWindow_logs hw
  have hP : 0<parentProduct old*p.val := mul_pos hw.2.1 h.1.1.pos
  have hPReal : (0 : ℝ)<((parentProduct old*p.val : ℕ) : ℝ) := by exact_mod_cast hP
  have hres : 1<residualLevel Q (singleWord old p.val) := by
    change 1<Q/((singleWord old p.val).prod : ℝ)
    rw [(singleWord_history old p.val).2.2]
    apply (lt_div_iff₀ hPReal).mpr
    simpa only [one_mul] using h.2.2.2.2
  refine ⟨hres,?_,?_⟩
  · have hcap := h.2.2.2.2.trans_le hw.2.2.2.1
    rw [(singleWord_history old p.val).2.2]
    exact_mod_cast hcap.le
  · unfold physicalLevel
    rw [single_residual_level,Real.log_div
      (zero_lt_one.trans hlogs.2.1).ne' (Nat.cast_pos.mpr h.1.1.pos).ne']
    exact sub_div _ _ _

theorem pair_actual_residual {bank : Fin 36} {piece : Fin 4} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : Fin (N+1) × Fin (N+1)}
    (hp : p ∈ pairChildren bank piece N Q old chi) :
    1<residualLevel Q (pairWord old p.1.val p.2.val) ∧
      (pairWord old p.1.val p.2.val).prod≤N ∧
      physicalLevel N Q (pairWord old p.1.val p.2.val)=
        physicalLevel N Q old-physicalPrime N p.2.val-physicalPrime N p.1.val := by
  have h := mem_pairChildren.mp hp
  have hw := h.2.1
  have hlogs := parentWindow_logs hw
  have hP : 0<parentProduct old*p.2.val*p.1.val :=
    mul_pos (mul_pos hw.2.1 h.1.2.1.pos) h.1.1.1.pos
  have hPReal : (0 : ℝ)<((parentProduct old*p.2.val*p.1.val : ℕ) : ℝ) := by exact_mod_cast hP
  have hres : 1<residualLevel Q (pairWord old p.1.val p.2.val) := by
    change 1<Q/((pairWord old p.1.val p.2.val).prod : ℝ)
    rw [(pairWord_history old p.1.val p.2.val).2.2]
    apply (lt_div_iff₀ hPReal).mpr
    simpa only [one_mul] using h.2.2.2.2.2.2
  refine ⟨hres,?_,?_⟩
  · have hcap := h.2.2.2.2.2.2.trans_le hw.2.2.2.1
    rw [(pairWord_history old p.1.val p.2.val).2.2]
    exact_mod_cast hcap.le
  · unfold physicalLevel
    rw [pair_residual_level,Real.log_div (zero_lt_one.trans hlogs.2.1).ne'
      (mul_pos (Nat.cast_pos.mpr h.1.2.1.pos) (Nat.cast_pos.mpr h.1.1.1.pos)).ne',
      Real.log_mul (Nat.cast_pos.mpr h.1.2.1.pos).ne' (Nat.cast_pos.mpr h.1.1.1.pos).ne']
    unfold physicalPrime
    ring

def singleCutoff (rule : SingleRule) (N : ℕ) (Q : ℝ) (old : List ℕ) (p : ℕ) : ℝ :=
  match rule with
  | .buchstab _ _ => physicalPrime N p
  | .w1 _ anchor => physicalLevel N Q old/W1Anchor anchor
  | .w2 bank _ => physicalLevel N Q old/(originalW2At bank).s0

def pairCutoff (bank : Fin 36) (piece : Fin 4) (N : ℕ) (Q : ℝ)
    (old : List ℕ) (small : ℕ) : ℝ :=
  if piece.val<2 then physicalLevel N Q old/(originalW2At bank).s0 else physicalPrime N small

theorem W2_singleton_left {bank : Fin 36} {piece : Fin 3} {u : ℝ}
    (hu : u ∈ W2SingletonDomain (originalW2At bank) piece) : a0 (originalW2At bank)<u := by
  fin_cases piece <;> exact hu.1

theorem W2_singleton_square {bank : Fin 36} {piece : Fin 3} {u : ℝ}
    (hu : u ∈ W2SingletonDomain (originalW2At bank) piece) : 2*u<1 := by
  rcases originalRepairedW2Bank_geometry _ (originalW2At_mem bank) with
    ⟨_,_,h12,h23,h3,hb,_,_,_⟩
  fin_cases piece
  · have h : u<b (originalW2At bank) := hu.2
    linarith only [h,hb]
  · have h : u<a2 (originalW2At bank) := hu.2
    linarith only [h,h23,h3]
  · have h : u<a3 (originalW2At bank) := hu.2
    linarith only [h,h3]

theorem single_cutoff_below_prime {rule : SingleRule} {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    {p : Fin (N+1)} (hp : p ∈ singleChildren rule N Q old chi) :
    singleCutoff rule N Q old p.val≤physicalPrime N p.val ∧ physicalPrime N p.val<chi := by
  have h := mem_singleChildren.mp hp
  have hl := (parentWindow_logs h.2.1).2.2
  refine ⟨?_,h.2.2.2.1⟩
  cases rule with
  | buchstab up s => exact le_rfl
  | w1 target anchor =>
      have hu : 1/W1Anchor anchor<relativePrime Q old p.val := h.2.2.1.1
      have hm := mul_lt_mul_of_pos_left hu hl
      rw [relativePrime_physical h.2.1] at hm
      simpa only [singleCutoff,mul_one_div] using hm.le
  | w2 bank piece =>
      have hu := W2_singleton_left (show relativePrime Q old p.val ∈
        W2SingletonDomain (originalW2At bank) piece from h.2.2.1)
      have hm := mul_lt_mul_of_pos_left hu hl
      rw [relativePrime_physical h.2.1] at hm
      simpa only [singleCutoff,a0,mul_one_div] using hm.le

theorem single_residual_square {rule : SingleRule} {N : ℕ} {Q chi : ℝ} {old : List ℕ}
    {p : Fin (N+1)} (hp : p ∈ singleChildren rule N Q old chi) :
    2*physicalPrime N p.val≤physicalLevel N Q old := by
  have h := mem_singleChildren.mp hp
  have hlog := parentWindow_logs h.2.1
  cases rule with
  | buchstab up s =>
      have hw : 1≤buchstabArgument Q old p.val := by
        have hd := h.2.2.1
        cases up
        · have hs : 2≤s := hd.1
          have hm : s-1≤buchstabArgument Q old p.val := hd.2.1
          linarith only [hs,hm]
        · have hm : max 2 (s-1)≤buchstabArgument Q old p.val := hd.2.1
          exact le_trans (by linarith [le_max_left (2 : ℝ) (s-1)]) hm
      have hp0 : 0<Real.log (p.val : ℝ) := Real.log_pos (by exact_mod_cast h.1.1.one_lt)
      have hh := (le_div_iff₀ hp0).mp hw
      dsimp [buchstabArgument] at hh
      have hraw : 2*Real.log (p.val : ℝ)≤Real.log (residualLevel Q old) := by
        linarith only [hh]
      have hdiv := div_le_div_of_nonneg_right hraw hlog.1.le
      unfold physicalPrime physicalLevel
      convert hdiv using 1 <;> ring
  | w1 target anchor =>
      have hu : relativePrime Q old p.val<1/W1Target target := h.2.2.1.2
      have hs : (2 : ℝ)≤W1Target target := by
        have hi : (0 : ℝ)≤target.val := Nat.cast_nonneg _
        dsimp [W1Target]
        linarith only [hi]
      have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<2) hs
      have hsquare : 2*relativePrime Q old p.val<1 := by linarith only [hu,hi]
      have hm := mul_lt_mul_of_pos_left hsquare hlog.2.2
      rw [mul_one] at hm
      have heq := relativePrime_physical h.2.1 (p:=p.val)
      nlinarith only [hm,heq]
  | w2 bank piece =>
      have hsquare := W2_singleton_square (show relativePrime Q old p.val ∈
        W2SingletonDomain (originalW2At bank) piece from h.2.2.1)
      have hm := mul_lt_mul_of_pos_left hsquare hlog.2.2
      rw [mul_one] at hm
      have heq := relativePrime_physical h.2.1 (p:=p.val)
      nlinarith only [hm,heq]

theorem pair_residual_squares {bank : Fin 36} {piece : Fin 4} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : Fin (N+1) × Fin (N+1)}
    (hp : p ∈ pairChildren bank piece N Q old chi) :
    2*physicalPrime N p.2.val<physicalLevel N Q old ∧
      physicalPrime N p.2.val+2*physicalPrime N p.1.val<physicalLevel N Q old := by
  have h := mem_pairChildren.mp hp
  have hl := (parentWindow_logs h.2.1).2.2
  have hg := P5OriginalFeedbackDomains.W2PairDomain_gates
    (originalRepairedW2Bank_geometry _ (originalW2At_mem bank)) piece h.2.2.2.1
  have h1 := mul_lt_mul_of_pos_left hg.2.2.1 hl
  have h2 := mul_lt_mul_of_pos_left hg.2.2.2 hl
  have es := relativePrime_physical h.2.1 (p:=p.1.val)
  have el := relativePrime_physical h.2.1 (p:=p.2.val)
  dsimp [pairPoint] at h1 h2
  constructor <;> nlinarith only [h1,h2,es,el]

theorem pair_cutoff_below_prime {bank : Fin 36} {piece : Fin 4} {N : ℕ} {Q chi : ℝ}
    {old : List ℕ} {p : Fin (N+1) × Fin (N+1)}
    (hp : p ∈ pairChildren bank piece N Q old chi) :
    pairCutoff bank piece N Q old p.1.val≤physicalPrime N p.1.val ∧
      physicalPrime N p.1.val<chi ∧ physicalPrime N p.2.val<chi := by
  have h := mem_pairChildren.mp hp
  refine ⟨?_,h.2.2.2.2.1,h.2.2.2.2.2.1⟩
  unfold pairCutoff
  split_ifs with hpiece
  · have hg := P5OriginalFeedbackDomains.W2PairDomain_gates
      (originalRepairedW2Bank_geometry _ (originalW2At_mem bank)) piece h.2.2.2.1
    have hm := mul_lt_mul_of_pos_left hg.1 (parentWindow_logs h.2.1).2.2
    have heq := relativePrime_physical h.2.1 (p:=p.1.val)
    dsimp [pairPoint,a0] at hm
    rw [heq] at hm
    simpa only [mul_one_div] using hm.le
  · exact le_rfl

end
end ImbalancedChen.P2EnhancedLowerPrimeChildGeometry
