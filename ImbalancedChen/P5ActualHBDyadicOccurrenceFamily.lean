import ImbalancedChen.P5HBRightClosedDyadicRoles

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact finite dyadic bank of ACTUAL ordered HB occurrences. Every role
keeps its position, signed value, REAL Mobius cutoff and the single log.
The finite block-assignment bank is chosen from n BEFORE the factor tuple.
Unit/nonunit endpoint ownership is HB26, never the gamma convention.
-/
namespace ImbalancedChen.P5Z.ActualHBDyadicOccurrenceFamily
noncomputable section
open Classical
open scoped BigOperators
open LiteralHeathBrownOccurrenceWords ActualRoughHeathBrownWords HBRightClosedDyadicRoles
open ImbalancedChen.Part3

def blockWords (n : ℕ) : ℕ → Finset (List Block)
  | 0 => {[]}
  | r+1 => ((bank n).product (blockWords n r)).image (fun bc => bc.1::bc.2)

private theorem cons_pair_injective : Function.Injective (fun bc : Block×List Block => bc.1::bc.2) := by
  intro x y h
  exact Prod.ext (List.cons.inj h).1 (List.cons.inj h).2

theorem blockWords_sum_cons (n r : ℕ) (F : List Block → ℂ) :
    (∑ bs∈blockWords n (r+1),F bs)=∑ b∈bank n,∑ bs∈blockWords n r,F (b::bs) := by
  rw [blockWords,Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro x hx y hy h
    exact cons_pair_injective h

theorem blockWords_card (n r : ℕ) : (blockWords n r).card=(Nat.log2 (n-1)+2)^r := by
  induction r with
  | zero => simp [blockWords]
  | succ r ih =>
    rw [blockWords,Finset.card_image_of_injective _ cons_pair_injective,
      Finset.card_product,bank_card,ih,pow_succ]
    exact Nat.mul_comm _ _

theorem blockWords_spec (n : ℕ) : ∀r : ℕ, ∀bs∈blockWords n r,
    bs.length=r ∧ ∀b∈bs,b∈bank n := by
  intro r
  induction r with
  | zero =>
    intro bs hbs
    have hh : bs=[] := by simpa [blockWords] using hbs
    subst bs
    simp
  | succ r ih =>
    intro bs hbs
    obtain ⟨⟨b,cs⟩,hbc,rfl⟩ := Finset.mem_image.mp hbs
    obtain ⟨hb,hcs⟩ := Finset.mem_product.mp hbc
    have hc := ih cs hcs
    refine ⟨by simpa using congrArg Nat.succ hc.1,?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hb
    · exact hc.2 a ha

def assignedWeight (z y : ℝ) : List Role → List Block → List ℕ → ℂ
  | [],[],[] => 1
  | r::rs,b::bs,p::ps => blockValue z y r b p*assignedWeight z y rs bs ps
  | _,_,_ => 0

/-- Cartesian expansion of the ACTUAL role values. The factor-bound
premise here is discharged from positive product tuples in the caller. -/
theorem occurrence_reconstruct (n : ℕ) (z y : ℝ) :
    ∀rs : List Role, ∀ps : List ℕ, (∀p∈ps,0<p ∧ p≤n) →
      (∑bs∈blockWords n rs.length,assignedWeight z y rs bs ps)=roughTupleWeight z y rs ps := by
  intro rs
  induction rs with
  | nil =>
    intro ps hp
    cases ps <;> simp [blockWords,assignedWeight,roughTupleWeight]
  | cons r rs ih =>
    intro ps hp
    cases ps with
    | nil =>
      rw [show (r::rs).length=rs.length+1 from rfl,blockWords_sum_cons]
      simp [assignedWeight,roughTupleWeight]
    | cons p ps =>
      have hhead := hp p (by simp)
      have htail : ∀q∈ps,0<q ∧ q≤n := fun q hq => hp q (List.mem_cons_of_mem p hq)
      rw [show (r::rs).length=rs.length+1 from rfl,blockWords_sum_cons]
      simp only [assignedWeight]
      simp_rw [← Finset.mul_sum,ih ps htail]
      rw [← Finset.sum_mul,role_reconstruct hhead.1 hhead.2]

def blockCoefficient (z y : ℝ) (j n : ℕ) (bs : List Block) : ℂ :=
  ∑ps∈factorTuples (2*(j+1)) n,assignedWeight z y (roles j) bs ps

theorem actual_term_decomposition (z y : ℝ) (j n : ℕ) :
    (∑ps∈factorTuples (2*(j+1)) n,roughTupleWeight z y (roles j) ps)=
      ∑bs∈blockWords n (2*(j+1)),blockCoefficient z y j n bs := by
  calc
    _ = ∑ps∈factorTuples (2*(j+1)) n,
        ∑bs∈blockWords n (2*(j+1)),assignedWeight z y (roles j) bs ps := by
      apply Finset.sum_congr rfl
      intro ps hps
      have hbound : ∀p∈ps,0<p ∧ p≤n := fun p hp => actual_factor_bound hps hp
      simpa only [roles_length] using (occurrence_reconstruct n z y (roles j) ps hbound).symm
    _ = _ := Finset.sum_comm

/-- EXACT original rough Lambda source = finite actual dyadic ROLE
family. No arbitrary alpha, factorability oracle, or SW input occurs. -/
theorem actual_dyadic_rough_HB_identity {z y : ℝ} (hz : 0≤z) (hy : 0≤y)
    {n : ℕ} (hn : (n : ℝ)≤y^3) :
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)*roughOneSlot z n=
      ∑j∈Finset.range 3,(((-1 : ℝ)^j*(Nat.choose 3 (j+1) : ℝ) : ℝ) : ℂ)*
        ∑bs∈blockWords n (2*(j+1)),blockCoefficient z y j n bs := by
  rw [actual_rough_order_three_identity hz hy hn]
  apply Finset.sum_congr rfl
  intro j hj
  rw [actual_term_decomposition]

/-- Every bank, including its units and empty coefficient blocks, is
fixed before the factor tuple. At most six ACTUAL occurrence choices. -/
theorem actual_family_card_le_six (n : ℕ) {j : ℕ} (hj : j∈Finset.range 3) :
    (blockWords n (2*(j+1))).card≤(Nat.log2 (n-1)+2)^6 := by
  rw [blockWords_card]
  have he : 2*(j+1)≤6 := by have := Finset.mem_range.mp hj; omega
  exact Nat.pow_le_pow_right (by omega : 0<Nat.log2 (n-1)+2) he

end
end ImbalancedChen.P5Z.ActualHBDyadicOccurrenceFamily
