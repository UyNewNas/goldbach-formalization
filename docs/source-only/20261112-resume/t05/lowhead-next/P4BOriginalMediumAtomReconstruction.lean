import ImbalancedChen.P4BOriginalMediumSignedFibre

/-! Recover the actual three-factor modulus sum of each original word from
the signed errors of its genuine dyadic Part 3 atoms. No squarefree cut is
inserted into the independent third coefficient. -/
namespace ImbalancedChen.P4BOriginalMediumAtomReconstruction
noncomputable section
open Classical
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block owner)
open P5Z.ActualHBDyadicProductWindow (lower)
open P4BOriginalMediumAtomFamily (Index cut support support_data third_data)
open P4BOriginalMediumSignedFibre (owner_sum)
open P4BOriginalCollisionThirdFactor (thirdSupport factor gamma)
open Part3 (factorCarrier MediumAtom)

private def weighted (S : Finset ℕ) (f : ℕ→ℝ) (F : ℕ→ℂ) := ∑ n∈S,(f n:ℂ)*F n
private def box (S : Finset ℕ) (f : ℕ→ℝ) (B : Block) (F : ℕ→ℂ) :=
  ∑ n∈factorCarrier (lower B:ℝ),cut S f B n*F n

private theorem box_sum {α : Type*} (T : Finset α) (S : Finset ℕ) (f : ℕ→ℝ) (B : Block)
    (F : α→ℕ→ℂ) : (∑ v∈T,box S f B (F v))=box S f B (fun n => ∑ v∈T,F v n) := by
  unfold box
  conv_lhs => rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]

variable {order : ℕ} {zeta kap0 : ℝ} (I : Index order zeta kap0)
def withOwners (D E F : Block) : Index order zeta kap0 :=
  { I with owners := ![D,E,F] }

theorem word_errors (K : ℕ) :
    let A := support I.P I.groups.1
    let B := support I.P I.groups.2.1
    let C := thirdSupport I.P I.J I.groups.2.2
    (∑ D∈A.image owner,∑ E∈B.image owner,∑ G∈C.image owner,((withOwners I D E G).atom K).signedError)=
    ∑ a∈A,∑ b∈B,∑ c∈C,(factor I.P I.groups.1 a:ℂ)*(factor I.P I.groups.2.1 b:ℂ)*
      (gamma I.P I.J I.groups.2.2 c:ℂ)*(I.atom K).discrepancy (a*b*c) := by
  let A := support I.P I.groups.1
  let B := support I.P I.groups.2.1
  let C := thirdSupport I.P I.J I.groups.2.2
  let f := factor I.P I.groups.1
  let g := factor I.P I.groups.2.1
  let h := gamma I.P I.J I.groups.2.2
  let F (a b c : ℕ) := (I.atom K).discrepancy (a*b*c)
  have ha : ∀a∈A,0<a := fun _ ha => (support_data _ _ ha).1
  have hb : ∀b∈B,0<b := fun _ hb => (support_data _ _ hb).1
  have hc : ∀c∈C,0<c := fun _ hc => (third_data _ _ _ hc).1
  have atom (D E G : Block) :
      ((withOwners I D E G).atom K).signedError=
        box A f D (fun a => box B g E (fun b => box C h G (F a b))) := by
    unfold MediumAtom.signedError box
    change (∑ a∈factorCarrier (lower D:ℝ),∑ b∈factorCarrier (lower E:ℝ),
      ∑ c∈factorCarrier (lower G:ℝ),cut A f D a*cut B g E b*cut C h G c*F a b c)=_
    simp only [Finset.mul_sum,mul_assoc]
  have last (D E : Block) :
      (∑ G∈C.image owner,((withOwners I D E G).atom K).signedError)=
      box A f D (fun a => box B g E (fun b => weighted C h (F a b))) := by
    simp_rw [atom]
    rw [box_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [box_sum]
    apply congrArg (fun z : ℂ => cut A f D a*z)
    apply Finset.sum_congr rfl
    intro b _
    rw [show (∑ G∈C.image owner,box C h G (F a b))=weighted C h (F a b) from owner_sum C h hc (F a b)]
  have middle (D : Block) :
      (∑ E∈B.image owner,∑ G∈C.image owner,((withOwners I D E G).atom K).signedError)=
      box A f D (fun a => weighted B g (fun b => weighted C h (F a b))) := by
    simp_rw [last]
    rw [box_sum]
    exact Finset.sum_congr rfl (fun a _ => congrArg (fun z : ℂ => cut A f D a*z)
      (owner_sum B g hb (fun b => weighted C h (F a b))))
  change (∑ D∈A.image owner,∑ E∈B.image owner,∑ G∈C.image owner,
    ((withOwners I D E G).atom K).signedError)=_
  simp_rw [middle]
  rw [show (∑ D∈A.image owner,box A f D (fun a => weighted B g (fun b => weighted C h (F a b))))=
    weighted A f (fun a => weighted B g (fun b => weighted C h (F a b))) from owner_sum A f ha _]
  simp only [weighted,Finset.mul_sum,mul_assoc,F,f,g,h,A,B,C]

end
end ImbalancedChen.P4BOriginalMediumAtomReconstruction
