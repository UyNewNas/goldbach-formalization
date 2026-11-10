import ImbalancedChen.P4AExactModulusLogCut
import ImbalancedChen.Part3ActualCommonIntervalCompletionL1

/-! Exact separable weights on the actual modulus-prime slots. No change
to the counted prime tuple, its geometric weight, the signs or the mean. -/
namespace ImbalancedChen.P4AModulusSlotFourierCut
noncomputable section
open scoped Classical BigOperators
open Classical P4AExactModulusLogCut
open P3ActualLiteralPacketIntegralSourceOnly
open Part3.ActualCommonIntervalCompletionSourceOnly
open Part3.ActualCommonIntervalCompletionL1SourceOnly

private def cutInterval (b : ℕ) : PacketData Empty where
  rows := ∅
  packet := Empty.elim
  nCarrier := Empty.elim
  lo := 0
  hi := b
  V := (b:ℝ)+1
  U := 1
  Z := 1
  Y0 := 1
  rho := 0
  sigma := 0
  negativeCusp := false
  kernel := Empty.elim
  V_pos := by positivity
  U_pos := by norm_num
  Z_pos := by norm_num
  Y0_pos := by norm_num
  m_normalized := by
    intro m hm
    have hmb : (m:ℝ)<b := by exact_mod_cast (Finset.mem_Ico.mp hm).2
    have hb : (0:ℝ)<b+1 := by positivity
    exact ⟨(lt_div_iff₀ hb).mpr (by nlinarith [Nat.cast_nonneg (α:=ℝ) m]),
      (div_lt_iff₀ hb).mpr (by nlinarith [Nat.cast_nonneg (α:=ℝ) b])⟩
  n_normalized := by intro j; exact j.elim
  level_normalized := by intro j; exact j.elim

def weight (t : ℕ) [NeZero t] (r : ZMod t) (m : ℕ) : ℂ :=
  ZMod.stdAddChar (r*(m:ZMod t))

theorem weight_norm (t : ℕ) [NeZero t] (r : ZMod t) (m : ℕ) : ‖weight t r m‖=1 := by
  simp only [weight,ZMod.stdAddChar_apply,Circle.norm_coe]

private theorem weight_sum {ι : Type*} (t : ℕ) [NeZero t] (r : ZMod t)
    (s : Finset ι) (f : ι → ℕ) :
    weight t r (∑ i ∈ s, f i) = ∏ i ∈ s, weight t r (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weight,AddChar.map_zero_eq_one]
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj,Finset.prod_insert hj,← ih]
    simp only [weight,Nat.cast_add,mul_add,AddChar.map_add_eq_mul]

theorem split_cut {k H : ℕ} (u v : Fin k → ℕ → ℕ) (T : Finset (Fin k → ℕ))
    (hT : ∀ p ∈ T, bounded u v H p) (good : (Fin k → ℕ) → Prop)
    (hord : ∀ p ∈ T, ∀ q ∈ T, good p → ¬good q → score u v p < score u v q) :
    ∃ c : ZMod (period k H) → ℂ,
      (∑ r, ‖c r‖) ≤ 2 + Real.log (period k H) ∧
      ∃ g : ZMod (period k H) → Fin k → ℕ → ℂ,
        (∀ r i x, ‖g r i x‖=1) ∧ ∀ p ∈ T, (if good p then (1:ℂ) else 0) =
          ∑ r, c r * ∏ i, g r i (p i) := by
  classical
  let t := period k H
  have ht : 2≤t := by dsimp [t,period]; omega
  letI : NeZero t := ⟨by omega⟩
  obtain ⟨b,hb,hcut⟩ := exists_cut u v H T hT good hord
  let P := cutInterval b
  let c := normalizedFourierCoeff P 0 b t
  let g (r : ZMod t) (i : Fin k) (x : ℕ) := weight t r (digit (scale k H) (u i x) (v i x))
  refine ⟨c,actual_common_interval_completion_l1 P 0 b t ht hb,g,?_,?_⟩
  · exact fun r i x => weight_norm _ _ _
  · intro p hp
    let m := code u v (scale k H) p
    have hm : m<t := by
      have h := code_le u v (hT p hp)
      change code u v (scale k H) p < scale k H*H+3
      omega
    have hi : (if good p then (1:ℂ) else 0) = cyclicIndicator P 0 b t (m : ZMod t) := by
      rw [hcut p hp]
      simp [cyclicIndicator,commonInterval,P,cutInterval,PacketData.mCarrier,
        ZMod.val_natCast_of_lt hm,m]
    rw [hi,cyclicIndicator_inversion,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    have hw := weight_sum t r Finset.univ (fun i => digit (scale k H) (u i (p i)) (v i (p i)))
    change (t:ℂ)⁻¹ * (finiteFourierCoeff P 0 b t r * weight t r m) = _
    rw [show weight t r m = ∏ i, g r i (p i) from hw]
    simp only [c,normalizedFourierCoeff,mul_assoc]

def numerator {k : ℕ} (N : ℕ) (A B : Fin k → ℕ) (i : Fin k) (p : ℕ) :=
  p^(A i)*N^(B i)
def denominator {k : ℕ} (B : Fin k → ℕ) (i : Fin k) (p : ℕ) := p^(B i)
def height {k : ℕ} (N : ℕ) (A B : Fin k → ℕ) := N ^ (∑ i, (A i+B i))

theorem powers_bounded {k N : ℕ} (hN : 1≤N) (A B : Fin k → ℕ) (p : Fin k → ℕ)
    (hp : ∀ i, 1≤p i ∧ p i≤N) :
    bounded (numerator N A B) (denominator B) (height N A B) p := by
  constructor
  · intro i
    have hp1 := (hp i).1
    have h1 : 1 ≤ (p i)^(A i) := Nat.one_le_pow _ _ hp1
    refine ⟨pow_pos (by omega) _,?_⟩
    calc
      (p i)^(B i) ≤ N^(B i) := Nat.pow_le_pow_left (hp i).2 _
      _ = 1*N^(B i) := (one_mul _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ h1
  · calc
      (∏ i, numerator N A B i (p i)) ≤ ∏ i, N^(A i+B i) := by
        apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        intro i _
        rw [pow_add]
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (hp i).2 _)
      _ = height N A B := Finset.prod_pow_eq_pow_sum _ _ _

theorem powers_score {k N : ℕ} (hN : 0<N) (A B : Fin k → ℕ) (p : Fin k → ℕ)
    (hp : ∀ i, 0<p i) :
    score (numerator N A B) (denominator B) p =
      (∑ i, (B i:ℝ)*Real.log N) + ∑ i, ((A i:ℝ)-(B i:ℝ))*Real.log (p i) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hx : 0<(p i:ℝ) := by exact_mod_cast hp i
  have hn : 0<(N:ℝ) := by exact_mod_cast hN
  simp only [slot,numerator,denominator,Nat.cast_mul,Nat.cast_pow,
    Real.log_mul (pow_pos hx _).ne' (pow_pos hn _).ne',Real.log_pow]
  ring

/-- One common denominator for the complete original slot vector, even
when it has negative coordinates. No bound on the intercept is involved. -/
theorem clear_slopes {k : ℕ} (a : Fin k → ℚ) :
    ∃ D : ℕ, 0<D ∧ ∃ A B : Fin k → ℕ, ∀ i,
      (D:ℝ)*(a i:ℝ) = (A i:ℝ)-(B i:ℝ) := by
  classical
  let D := ∏ i, (a i).den
  let d (i : Fin k) := ∏ j ∈ (Finset.univ.erase i), (a j).den
  let z (i : Fin k) : ℤ := (d i:ℤ)*(a i).num
  refine ⟨D,Finset.prod_pos (fun i _ => (a i).den_pos),fun i => (z i).toNat,
    fun i => (-(z i)).toNat,?_⟩
  intro i
  have hmul : d i*(a i).den=D := Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i)
  have hnum : (z i).toNat - ((-(z i)).toNat : ℤ) = z i := by omega
  have hcast : ((z i).toNat:ℝ) - ((-(z i)).toNat:ℝ)=(z i:ℝ) := by exact_mod_cast hnum
  rw [hcast,← hmul,Rat.cast_def]
  dsimp only [z]
  push_cast
  field_simp [(show ((a i).den:ℝ) ≠ 0 by exact_mod_cast (a i).den_nz)]

theorem log_period (k S N : ℕ) (hN : 1≤N) :
    2+Real.log (period k (N^S)) ≤
      2+Real.log ((k:ℝ)+5)+(3*S:ℕ)*Real.log N := by
  have h₁ := Nat.one_le_pow S N hN
  have hp : period k (N^S) ≤ (k+5)*(N^(3*S)) := by
    have he : N^(3*S) = (N^S)^3 := by rw [Nat.mul_comm 3 S,pow_mul]
    rw [he]
    dsimp [period,scale]
    nlinarith [Nat.one_le_pow 3 (N^S) h₁]
  have hlog := Real.log_le_log (show (0:ℝ)<(period k (N^S):ℕ) by
    unfold period; positivity) (by exact_mod_cast hp : ((period k (N^S):ℕ):ℝ) ≤ ((k+5)*(N^(3*S)):ℕ))
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  push_cast at hlog
  rw [Real.log_mul (by positivity) (pow_pos hn _).ne',Real.log_pow] at hlog
  linarith

def affineSum {k : ℕ} (a : Fin k → ℚ) (N : ℕ) (p : Fin k → ℕ) : ℝ :=
  ∑ i, (a i:ℝ)*(Real.log (p i)/Real.log N)

def lowerCut (closed : Bool) (x b : ℝ) : Prop :=
  if closed then x≤b else x<b

/-- The slopes, and hence the polynomial degree and constant, are fixed
before N, every real threshold, the choice of open/closed endpoint,
and any finite slot box. The modes only act on their own integer slot. -/
theorem rational_row {k : ℕ} (a : Fin k → ℚ) :
    ∃ S : ℕ, ∀ N : ℕ, 1<N → ∀ T : Finset (Fin k → ℕ),
      (∀ p ∈ T, ∀ i, 1≤p i ∧ p i≤N) → ∀ b : ℝ, ∀ closed : Bool,
      ∃ c : ZMod (period k (N^S)) → ℂ,
        (∑ r, ‖c r‖) ≤ 2+Real.log ((k:ℝ)+5)+(3*S:ℕ)*Real.log N ∧
        ∃ g : ZMod (period k (N^S)) → Fin k → ℕ → ℂ,
        (∀ r i x, ‖g r i x‖=1) ∧ ∀ p ∈ T,
          (if lowerCut closed (affineSum a N p) b then (1:ℂ) else 0) =
            ∑ r, c r * ∏ i, g r i (p i) := by
  obtain ⟨D,hD,A,B,hAB⟩ := clear_slopes a
  let S := ∑ i, (A i+B i)
  refine ⟨S,?_⟩
  intro N hN T hT b closed
  let u := numerator N A B
  let v := denominator B
  have hp : ∀ p ∈ T, bounded u v (N^S) p :=
    fun p hp => powers_bounded hN.le A B p (hT p hp)
  have hlog : 0<Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hpos : (0:ℝ)<(D:ℝ)*Real.log N := mul_pos (by exact_mod_cast hD) hlog
  have hx (p) (ht : p ∈ T) :
      score u v p = (∑ i, (B i:ℝ)*Real.log N) + ((D:ℝ)*Real.log N)*affineSum a N p := by
    rw [powers_score (by omega : 0<N) A B p (fun i => (hT p ht i).1)]
    congr 1
    rw [affineSum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hAB i]
    field_simp [hlog.ne'] <;> ring
  obtain ⟨c,hc,g,hg,he⟩ := split_cut u v T hp
    (fun p => lowerCut closed (affineSum a N p) b) (by
      intro p hp q hq ht hf
      have hl : affineSum a N p < affineSum a N q := by
        cases closed <;> simp only [lowerCut,Bool.false_eq_true,if_false,if_true,
          not_le,not_lt] at ht hf <;> linarith
      rw [hx p hp,hx q hq]
      linarith [mul_lt_mul_of_pos_left hl hpos])
  exact ⟨c,hc.trans (log_period k S N hN.le),g,hg,he⟩

end
end ImbalancedChen.P4AModulusSlotFourierCut
