import ImbalancedChen.P5LiteralHeathBrownOccurrenceWords
import ImbalancedChen.Part3RoughSlotCharacterLift

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The derived finite HB identity is now filtered by the ACTUAL strict rough
slot z<p. Its forbidden prime product includes p=z, through Joint07's
proved coprimality identity. Each active Mobius occurrence is the actual
signed roughMoebiusSlot with the SAME REAL n<=y cutoff; one occurrences
are actual roughOneSlot, and the single log occurrence is log*roughOne.
The equality holds at the CLOSED real cube range, including n=0/1.
There is no HB chart, Mellin separation, SW or MediumAtom assertion.
-/
namespace ImbalancedChen.P5Z.ActualRoughHeathBrownWords
noncomputable section
open Classical
open scoped BigOperators ArithmeticFunction.zeta
open LiteralHeathBrownOccurrenceWords RealTruncatedMobiusSupport
open ImbalancedChen.Part3
open ImbalancedChen.Part3.RoughSlotCharacterLift20261026b

theorem roughOne_mul {z : ℝ} (hz : 0≤z) (a b : ℕ) :
    roughOneSlot z (a*b)=roughOneSlot z a*roughOneSlot z b := by
  rw [roughOneSlot_eq_coprime_indicator hz,roughOneSlot_eq_coprime_indicator hz,
    roughOneSlot_eq_coprime_indicator hz,Nat.coprime_mul_iff_left]
  by_cases ha : Nat.Coprime a (smallProduct z) <;>
    by_cases hb : Nat.Coprime b (smallProduct z) <;> simp [ha,hb]

theorem roughOne_one {z : ℝ} (hz : 0≤z) : roughOneSlot z 1=1 := by
  rw [roughOneSlot_eq_coprime_indicator hz]
  simp

theorem roughOne_list_prod {z : ℝ} (hz : 0≤z) (ps : List ℕ) :
    roughOneSlot z ps.prod=(ps.map (roughOneSlot z)).prod := by
  induction ps with
  | nil => simpa using roughOne_one hz
  | cons p ps ih => simp only [List.prod_cons,List.map_cons,roughOne_mul hz,ih]

inductive Role where
  | mobius
  | one
  | logarithm
  deriving DecidableEq

def base (y : ℝ) : Role → ArithmeticFunction ℝ
  | .mobius => muTrunc y
  | .one => (ζ : ArithmeticFunction ℝ)
  | .logarithm => ArithmeticFunction.log

def roughMuTrunc (z y : ℝ) (n : ℕ) : ℂ :=
  if (n : ℝ)≤y then roughMoebiusSlot z n else 0

def roughLog (z : ℝ) (n : ℕ) : ℂ := (Real.log (n : ℝ) : ℂ)*roughOneSlot z n

def actual (z y : ℝ) : Role → ℕ → ℂ
  | .mobius => roughMuTrunc z y
  | .one => roughOneSlot z
  | .logarithm => roughLog z

def roles (j : ℕ) : List Role :=
  List.replicate (j+1) .mobius ++ List.replicate j .one ++ [.logarithm]

def roughTupleWeight (z y : ℝ) : List Role → List ℕ → ℂ
  | [],[] => 1
  | r::rs,p::ps => actual z y r p*roughTupleWeight z y rs ps
  | _,_ => 0

theorem roles_base (y : ℝ) (j : ℕ) : (roles j).map (base y)=hbWord y j := by
  simp only [roles,hbWord,List.map_append,List.map_replicate,List.map_cons,List.map_nil,base]

theorem roles_length (j : ℕ) : (roles j).length=2*(j+1) := by
  simp only [roles,List.length_append,List.length_replicate,List.length_singleton]
  omega

/-- The zeta one-slot differs from the literal roughOne only at zero
before masking. All literal factor tuples have POSITIVE coordinates,
which is derived in22, and the whole zero coefficient is handled below. -/
theorem actual_eq_base_mask (z y : ℝ) (r : Role) {n : ℕ} (hn : 0<n) :
    actual z y r n=((base y r n : ℝ) : ℂ)*roughOneSlot z n := by
  cases r with
  | mobius =>
    by_cases hcut : (n : ℝ)≤y
    · simp only [actual,base,roughMuTrunc,if_pos hcut,muTrunc_of_le hcut,
        roughMoebiusSlot,Complex.ofReal_intCast]
    · simp only [actual,base,roughMuTrunc,if_neg hcut,
        muTrunc_of_gt (lt_of_not_ge hcut),Complex.ofReal_zero,zero_mul]
  | one =>
    simp only [actual,base,ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply_ne hn.ne',Nat.cast_one,Complex.ofReal_one,one_mul]
  | logarithm => rfl

theorem rough_tuple_weight_mask {z : ℝ} (hz : 0≤z) (y : ℝ) :
    ∀ (rs : List Role) (ps : List ℕ), (∀p∈ps,0<p) →
      roughTupleWeight z y rs ps=
        ((tupleWeight (rs.map (base y)) ps : ℝ) : ℂ)*roughOneSlot z ps.prod := by
  intro rs
  induction rs with
  | nil =>
    intro ps hpos
    cases ps with
    | nil => simp only [roughTupleWeight,List.map_nil,tupleWeight,List.prod_nil,
        Complex.ofReal_one,roughOne_one hz,one_mul]
    | cons p ps => simp only [roughTupleWeight,List.map_nil,tupleWeight,Complex.ofReal_zero,zero_mul]
  | cons r rs ih =>
    intro ps hpos
    cases ps with
    | nil => simp only [roughTupleWeight,List.map_cons,tupleWeight,Complex.ofReal_zero,zero_mul]
    | cons p ps =>
      have hp : 0<p := hpos p (by simp)
      have htail : ∀q∈ps,0<q := fun q hq => hpos q (List.mem_cons_of_mem p hq)
      rw [roughTupleWeight,actual_eq_base_mask z y r hp,ih ps htail]
      simp only [List.map_cons,tupleWeight,List.prod_cons,Complex.ofReal_mul,roughOne_mul hz]
      ring

/-- All coordinates, their product, and their real Mobius cutoffs are
derived from the ACTUAL literal factor tuple, not input as a licence. -/
theorem actual_word_mask {z : ℝ} (hz : 0≤z) (y : ℝ) (j n : ℕ) (ps : List ℕ)
    (hps : ps∈factorTuples (2*(j+1)) n) :
    roughTupleWeight z y (roles j) ps=
      ((tupleWeight (hbWord y j) ps : ℝ) : ℂ)*roughOneSlot z n := by
  have hs := factorTuples_spec (2*(j+1)) n ps hps
  simpa only [roles_base,hs.2.1] using rough_tuple_weight_mask hz y (roles j) ps hs.2.2

theorem actual_word_nonzero_cutoff {z : ℝ} (hz : 0≤z) (y : ℝ) (j n : ℕ) (ps : List ℕ)
    (hps : ps∈factorTuples (2*(j+1)) n)
    (hn : roughTupleWeight z y (roles j) ps≠0) :
    ∀p∈ps.take (j+1),(p : ℝ)≤y := by
  have hbase : tupleWeight (hbWord y j) ps≠0 := by
    intro h
    apply hn
    rw [actual_word_mask hz y j n ps hps,h]
    simp
  exact hbWord_nonzero_mobius_cutoff y j ps hbase

/-- Literal ORIGINAL rough-filtered HB source coefficient. The three
signed binomial scalars, repeated occurrences and single log-slot remain
unchanged; the zero and unit arguments are included in the identity. -/
theorem actual_rough_order_three_identity {z y : ℝ} (hz : 0≤z) (hy : 0≤y)
    {n : ℕ} (hn : (n : ℝ)≤y^3) :
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)*roughOneSlot z n=
      ∑ j∈Finset.range 3,
        (((-1 : ℝ)^j*(Nat.choose 3 (j+1) : ℝ) : ℝ) : ℂ)*
          ∑ ps∈factorTuples (2*(j+1)) n,roughTupleWeight z y (roles j) ps := by
  rw [literal_order_three_identity hy hn]
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_assoc,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro ps hps
  exact (actual_word_mask hz y j n ps hps).symm

theorem roughMuTrunc_norm_le (z y : ℝ) (n : ℕ) : ‖roughMuTrunc z y n‖≤1 := by
  unfold roughMuTrunc
  split_ifs
  · exact roughMoebiusSlot_norm_le z n
  · simp

end
end ImbalancedChen.P5Z.ActualRoughHeathBrownWords
