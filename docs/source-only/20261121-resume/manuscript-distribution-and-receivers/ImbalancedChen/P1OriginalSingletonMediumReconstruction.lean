import ImbalancedChen.P1OriginalSingletonMediumAdmissible
import all ImbalancedChen.P4BOriginalMediumSignedFibre
import all ImbalancedChen.P4BOriginalMediumAtomReconstruction

/-!
SOURCE ONLY / NOT COMPILED.

The literal singleton retained mode reaches the same native signed atoms.
Only the pair-Index binding in the old caller is removed. Complementary
separation, disjoint dyadic owners and the complete physical word tensor
are existing generic proofs, reused below without a new tensor argument.
-/
namespace ImbalancedChen.P1OriginalSingletonMediumReconstruction
noncomputable section
open Classical Filter
open scoped BigOperators
open P1OriginalSingletonMediumLowThreeAdmissible (Index size)
open P5Z.HBRightClosedDyadicRoles (Block owner)
open P5Z.ActualHBDyadicProductWindow (lower)
open P5Z.OrderedFactorTupleRectangleReindex (blockIntegers)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct hbSlots)
open P5Z.ActualAllRankOccurrenceFourierBridge (occurrenceMode)
open P5Z.ActualSelectedRoughSlotAPDictionary (intervalCarrier)
open P4BUpperPairOrderedRowGeometry (blockScales)
open P4BOriginalHighRankComplementBlocks (fibre)
open P4BOriginalMediumComplementCoefficient (beta other_mem)
open P4BOriginalMediumAtomFamily (support cut support_data third_data)
open P4BOriginalMediumSignedFibre (block_sub owner_sum)
open P4BOriginalCollisionTensor (products free)
open P4BOriginalCollisionThirdFactor (factor gamma thirdSupport)
open P4BOriginalHigherLowTensor (restore)
open P4BOriginalHigherActionGroups (rule)
open P4BOriginalCollisionKernel (row reindex)
open PrimeProducts.MellinInsertion20261028 (residueKernel exactDiscrepancy)
open Part3 (factorCarrier MediumAtom)
open private nonunit_interval from ImbalancedChen.P4BOriginalMediumSignedFibre
open private weighted box box_sum from ImbalancedChen.P4BOriginalMediumAtomReconstruction

variable {modeOrder : ℕ} {kap zeta kap0 : ℝ} (I : Index modeOrder kap zeta kap0)

def originalMode (K : ℕ) (y : Fin (size I.j)→ℕ) : ℂ :=
  hbSlots (I.Z K) I.truncations I.roles y*occurrenceMode (blockScales I.bv) y I.xi

def scalar : ℝ := ∏ a,P4BOriginalMediumHBHead.scalar (I.bv a) (I.roles a)

/-- One fixed convolution row, independent of the modulus-factor owners.
Its complete n*m is used in both the count and primitive coprime mean. -/
def convolution (K q : ℕ) : ℂ :=
  ∑ n∈intervalCarrier I.U (2*I.U),∑ m∈factorCarrier I.V,
    P4BOriginalMediumHBHead.alpha (I.bv I.i) (I.Z K) (I.truncations I.i) (I.roles I.i) (I.xi I.i) n*
      beta I.bv I.i I.C (I.Z K) I.truncations I.roles I.xi m*residueKernel q I.P.N (n*m)

theorem atom_discrepancy (K : ℕ) (D E G : Block) (q : ℕ) :
    (I.atom K D E G).discrepancy q=convolution I K q := by
  unfold MediumAtom.discrepancy convolution
  rw [I.carrier K D E G]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  have hmod : (((n*m:ℕ):ℤ)%(q:ℤ)=(I.P.N:ℤ)%(q:ℤ)) ↔
      (n*m)%q=I.P.N%q := Int.natCast_modEq_iff
  simp only [residueKernel,P1OriginalSingletonMediumLowThreeAdmissible.Index.atom,
    P1OriginalSingletonMediumLowThreeAdmissible.Index.truncations]
  rw [propext hmod]

private theorem beta_outside (K : ℕ) {m : ℕ} (hm : m∉blockIntegers I.C) :
    beta I.bv I.i I.C (I.Z K) I.truncations I.roles I.xi m=0 := by
  unfold beta
  apply Finset.sum_eq_zero
  intro z hz
  exact (hm ((Finset.mem_filter.mp hz).2 ▸ other_mem (Finset.mem_filter.mp hz).1)).elim

/-- Restore the original HB scalar on the literal finite count-minus-mean
row. The selected interval is the nonunit right-closed HB block. -/
theorem row_at_level (K : ℕ) (hu : 1<I.U) (q : ℕ) :
    row (fibre I.bv I.i I.C) completeProduct (originalMode I K) I.P.N q=
      (scalar I:ℂ)*convolution I K q := by
  have H := P4BOriginalMediumComplementCoefficient.separated I.bv I.i I.C (I.Z K)
    I.truncations I.roles I.xi (residueKernel q I.P.N)
  change row (fibre I.bv I.i I.C) completeProduct (originalMode I K) I.P.N q=_ at H
  rw [H]
  apply congrArg (fun z : ℂ => (scalar I:ℂ)*z)
  unfold convolution
  rw [show intervalCarrier I.U (2*I.U)=blockIntegers (I.bv I.i) from nonunit_interval _ hu]
  apply Finset.sum_congr rfl
  intro n _
  exact Finset.sum_subset (block_sub I.C) (fun m _ hm => by
    rw [beta_outside I K hm]
    ring)

theorem free_fibre (K : ℕ) (hu : 1<I.U) :
    exactDiscrepancy (fibre I.bv I.i I.C) (products I.P) (fun q => (free I.P q:ℂ))
      completeProduct I.P.N (originalMode I K)=
      (scalar I:ℂ)*∑ q∈products I.P,(free I.P q:ℂ)*convolution I K q := by
  rw [reindex,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun q _ => by rw [row_at_level I K hu]; ring)

def onWord (J : {J // J∈I.P.words}) : Index modeOrder kap zeta kap0 :=
  { I with J := J.val, word := J.property }

def boxedErrors (K : ℕ) : ℂ :=
  ∑ D∈I.firstOwners,∑ E∈I.secondOwners,∑ G∈I.thirdOwners,(I.atom K D E G).signedError

/-- Reuse the exact disjoint owner sum on the actual selected grouping.
The original small Rosser is still part of gamma3. -/
theorem word_errors (K : ℕ) :
    boxedErrors I K=
      ∑ a∈support I.P I.groups.1,∑ b∈support I.P I.groups.2.1,
      ∑ c∈thirdSupport I.P I.J I.groups.2.2,
        (factor I.P I.groups.1 a:ℂ)*(factor I.P I.groups.2.1 b:ℂ)*
          (gamma I.P I.J I.groups.2.2 c:ℂ)*convolution I K (a*b*c) := by
  let A := support I.P I.groups.1
  let B := support I.P I.groups.2.1
  let C := thirdSupport I.P I.J I.groups.2.2
  let f := factor I.P I.groups.1
  let g := factor I.P I.groups.2.1
  let h := gamma I.P I.J I.groups.2.2
  let F (a b c : ℕ) := convolution I K (a*b*c)
  have ha : ∀a∈A,0<a := fun _ ha => (support_data _ _ ha).1
  have hb : ∀b∈B,0<b := fun _ hb => (support_data _ _ hb).1
  have hc : ∀c∈C,0<c := fun _ hc => (third_data _ _ _ hc).1
  have atom (D E G : Block) : (I.atom K D E G).signedError=
      box A f D (fun a => box B g E (fun b => box C h G (F a b))) := by
    unfold MediumAtom.signedError box
    simp_rw [atom_discrepancy I K D E G]
    change (∑ a∈factorCarrier (lower D:ℝ),∑ b∈factorCarrier (lower E:ℝ),
      ∑ c∈factorCarrier (lower G:ℝ),cut A f D a*cut B g E b*cut C h G c*F a b c)=_
    simp only [Finset.mul_sum,mul_assoc]
  have last (D E : Block) :
      (∑ G∈C.image owner,(I.atom K D E G).signedError)=
      box A f D (fun a => box B g E (fun b => weighted C h (F a b))) := by
    simp_rw [atom]
    rw [box_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [box_sum]
    apply congrArg (fun z : ℂ => cut A f D a*z)
    exact Finset.sum_congr rfl (fun b _ => by
      rw [show (∑ G∈C.image owner,box C h G (F a b))=weighted C h (F a b) from owner_sum C h hc (F a b)])
  have middle (D : Block) :
      (∑ E∈B.image owner,∑ G∈C.image owner,(I.atom K D E G).signedError)=
      box A f D (fun a => weighted B g (fun b => weighted C h (F a b))) := by
    simp_rw [last]
    rw [box_sum]
    exact Finset.sum_congr rfl (fun a _ => congrArg (fun z : ℂ => cut A f D a*z)
      (owner_sum B g hb (fun b => weighted C h (F a b))))
  change (∑ D∈A.image owner,∑ E∈B.image owner,∑ G∈C.image owner,(I.atom K D E G).signedError)=_
  simp_rw [middle]
  rw [show (∑ D∈A.image owner,box A f D (fun a => weighted B g (fun b => weighted C h (F a b))))=
    weighted A f (fun a => weighted B g (fun b => weighted C h (F a b))) from owner_sum A f ha _]
  simp only [weighted,Finset.mul_sum,mul_assoc,F,f,g,h,A,B,C]

/-- The complete signed free coefficient is reconstructed on exactly the
same common assignment and all actual P.words. No word witness is reselected. -/
theorem all_free_words (K : ℕ) (hN : 1<I.P.N) (hu : 1<I.U) :
    exactDiscrepancy (fibre I.bv I.i I.C) (products I.P) (fun q => (free I.P q:ℂ))
      completeProduct I.P.N (originalMode I K)=
      (scalar I:ℂ)*∑ J∈I.P.words.attach,
        (restore I.P J.val (onWord I J).groups:ℂ)*boxedErrors (onWord I J) K := by
  rw [free_fibre I K hu,rule.complex_complete I.P hN I.x I.U zeta]
  apply congrArg (fun z : ℂ => (scalar I:ℂ)*z)
  rw [←Finset.sum_attach I.P.words]
  apply Finset.sum_congr rfl
  intro J _
  apply congrArg (fun z : ℂ => (restore I.P J.val (onWord I J).groups:ℂ)*z)
  exact (word_errors (onWord I J) K).symm

/-- The original singleton window removes the nonunit-head premise with
one threshold before the actual physical word, row, complement and mode. -/
theorem eventually_original_fibre (K modeOrder : ℕ) {kap zeta kappa kap0 : ℝ}
    (hkap : kap<1) (hz : 0<zeta) (hz1 : zeta≤1/400) (hk : 0<kappa)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop,∀ I : Index modeOrder kap zeta kap0,I.P.N=N →
      exactDiscrepancy (fibre I.bv I.i I.C) (products I.P) (fun q => (free I.P q:ℂ))
        completeProduct I.P.N (originalMode I K)=
        (scalar I:ℂ)*∑ J∈I.P.words.attach,
          (restore I.P J.val (onWord I J).groups:ℂ)*boxedErrors (onWord I J) K := by
  filter_upwards [P1OriginalSingletonMediumWindow.eventually_original_medium_window K 1
      hkap hz hz1 hk ht ht1,eventually_ge_atTop (2:ℕ)] with N HW hN
  intro I hIN
  rw [←hIN] at HW hN
  have hu := (HW I.cj (size I.j) I.bv I.i I.C I.live I.selected_ofFn).2.2.2.2.2.1
  exact all_free_words I K (by omega) hu

end
end ImbalancedChen.P1OriginalSingletonMediumReconstruction
