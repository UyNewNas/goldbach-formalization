import ImbalancedChen.P4BOriginalHigherLowTensor
import ImbalancedChen.P4BOriginalHigherLowEndpointBounds

namespace ImbalancedChen.P4BOriginalHigherLowNativeAtoms
noncomputable section
open Classical
open scoped BigOperators
open Part3 (MediumAtom factorCarrier)
open P4BOriginalMediumAtomFamily (Index cut support support_data third_data)
open P4BOriginalCollisionThirdFactor (factor gamma gamma_one thirdSupport)
open P4BOriginalMediumAtomReconstruction (withOwners)
open P4BOriginalMediumPhysicalAtomSum (onWord)
open P4BOriginalMediumSignedFibre (scalar originalMode free_fibre owner_sum)
open P4BOriginalHigherLowBins (split Groups)
open P4BOriginalHigherLowTensor (restore)
open P5Z.HBRightClosedDyadicRoles (Block owner)
open P5Z.ActualHBDyadicProductWindow (lower)
open P4BOriginalCollisionTensor (products free)
open P4BOriginalHighRankComplementBlocks (fibre)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open PrimeProducts.MellinInsertion20261028 (exactDiscrepancy)

variable {order : ℕ} {zeta kap0 : ℝ} (I : Index order zeta kap0)
abbrev groups := split I.P I.x I.U I.eta I.J
abbrev firstSet := support I.P (groups I).1
abbrev secondSet := support I.P (groups I).2.1
abbrev thirdSet := thirdSupport I.P I.J (groups I).2.2

def atom (K : ℕ) (D E G : Block) : MediumAtom :=
  { (withOwners I D E G).atom K with
    gamma1 := cut (firstSet I) (factor I.P (groups I).1) D
    gamma2 := cut (secondSet I) (factor I.P (groups I).2.1) E
    gamma3 := cut (thirdSet I) (gamma I.P I.J (groups I).2.2) G }

/-- Regrouping the modulus occurrences leaves the original first medium
HB slot, the auxiliary progression, and its family-uniform constants intact. -/
theorem uniform_auxiliary (K order : ℕ) {zeta kappa kap0 : ℝ}
    (hz : 0<zeta) (hz1 : zeta≤1/400) (hk : 0<kappa) (hkz : kappa≤zeta)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    Part3.UniformAuxiliarySW
      (fun p : Index order zeta kap0 × Block × Block × Block => atom p.1 K p.2.1 p.2.2.1 p.2.2.2) 1 := by
  intro A hA
  obtain ⟨C,hC,x0,hx,H⟩ := P4BOriginalMediumAtomFamily.uniform_original_auxiliary_SW
    K order hz hz1 hk hkz ht ht1 A hA
  exact ⟨C,hC,x0,hx,fun p hp k q b hk' hq hb => H p.1 hp k q b hk' hq hb⟩

theorem factors (K : ℕ) (D E G : Block) (q : ℕ) :
    let a := atom I K D E G
    (‖a.gamma1 q‖≤1 ∧ (a.gamma1 q≠0 → q.Coprime I.P.N)) ∧
    (‖a.gamma2 q‖≤1 ∧ (a.gamma2 q≠0 → q.Coprime I.P.N)) ∧
    (‖a.gamma3 q‖≤1 ∧ (a.gamma3 q≠0 → q.Coprime I.P.N)) := by
  have atCut (S : Finset ℕ) (f : ℕ→ℝ) (B : Block)
      (hf : |f q|≤1) (hc : q∈S → q.Coprime I.P.N) :
      ‖cut S f B q‖≤1 ∧ (cut S f B q≠0 → q.Coprime I.P.N) := by
    by_cases h : q∈S ∧ P5Z.HBRightClosedDyadicRoles.Owns B q
    · simpa [cut,h] using And.intro hf (fun _ : (f q:ℂ)≠0 => hc h.1)
    · simp [cut,h]
  refine ⟨atCut _ _ _ (P4AOriginalFiniteFallbackGroupedAtoms.group_unit _ _ _ _ _) (fun h => (support_data _ _ h).2),
    atCut _ _ _ (P4AOriginalFiniteFallbackGroupedAtoms.group_unit _ _ _ _ _) (fun h => (support_data _ _ h).2),
    atCut _ _ _ (gamma_one _ _ _ _) (fun h => (third_data _ _ _ h).2)⟩

def errors (K : ℕ) : ℂ :=
  ∑ D∈(firstSet I).image owner,∑ E∈(secondSet I).image owner,∑ G∈(thirdSet I).image owner,
    (atom I K D E G).signedError

private def box (S : Finset ℕ) (f : ℕ→ℝ) (D : Block) (F : ℕ→ℂ) :=
  ∑ n∈factorCarrier (lower D:ℝ),cut S f D n*F n

private theorem commute {α : Type*} (T : Finset α) (S : Finset ℕ) (f : ℕ→ℝ) (D : Block) (F : α→ℕ→ℂ) :
    (∑ v∈T,box S f D (F v))=box S f D (fun n => ∑ v∈T,F v n) := by
  unfold box
  conv_lhs => rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]

theorem word_errors (K : ℕ) :
    errors I K=∑ a∈firstSet I,∑ b∈secondSet I,∑ c∈thirdSet I,
      (factor I.P (groups I).1 a:ℂ)*(factor I.P (groups I).2.1 b:ℂ)*
        (gamma I.P I.J (groups I).2.2 c:ℂ)*(I.atom K).discrepancy (a*b*c) := by
  let A := firstSet I
  let B := secondSet I
  let C := thirdSet I
  let f := factor I.P (groups I).1
  let g := factor I.P (groups I).2.1
  let h := gamma I.P I.J (groups I).2.2
  let F (a b c : ℕ) := (I.atom K).discrepancy (a*b*c)
  have ha (n) (hn : n∈A) := (support_data _ _ hn).1
  have hb (n) (hn : n∈B) := (support_data _ _ hn).1
  have hc (n) (hn : n∈C) := (third_data _ _ _ hn).1
  have boxes (D E G : Block) : (atom I K D E G).signedError=
      box A f D (fun a => box B g E (fun b => box C h G (F a b))) := by
    change (∑ a∈factorCarrier (lower D:ℝ),∑ b∈factorCarrier (lower E:ℝ),∑ c∈factorCarrier (lower G:ℝ),
      cut A f D a*cut B g E b*cut C h G c*F a b c)=_
    simp only [box,Finset.mul_sum,mul_assoc]
  have last (D E : Block) :
      (∑ G∈C.image owner,(atom I K D E G).signedError)=
        box A f D (fun a => box B g E (fun b => ∑ c∈C,(h c:ℂ)*F a b c)) := by
    simp_rw [boxes]
    rw [commute]
    apply Finset.sum_congr rfl
    intro a _
    rw [commute]
    apply congrArg (fun v : ℂ => cut A f D a*v)
    exact Finset.sum_congr rfl (fun b _ =>
      congrArg (fun v : ℂ => cut B g E b*v) (owner_sum C h hc (F a b)))
  have middle (D : Block) :
      (∑ E∈B.image owner,∑ G∈C.image owner,(atom I K D E G).signedError)=
      box A f D (fun a => ∑ b∈B,(g b:ℂ)*∑ c∈C,(h c:ℂ)*F a b c) := by
    simp_rw [last]
    rw [commute]
    exact Finset.sum_congr rfl (fun a _ => congrArg (fun v : ℂ => cut A f D a*v)
      (owner_sum B g hb (fun b => ∑ c∈C,(h c:ℂ)*F a b c)))
  unfold errors
  simp_rw [middle]
  rw [show (∑ D∈A.image owner,box A f D (fun a => ∑ b∈B,(g b:ℂ)*∑ c∈C,(h c:ℂ)*F a b c))=
      ∑ a∈A,(f a:ℂ)*∑ b∈B,(g b:ℂ)*∑ c∈C,(h c:ℂ)*F a b c from owner_sum A f ha _]
  simp only [Finset.mul_sum,mul_assoc,F,f,g,h,A,B,C]

/-- The signed errors of the three new owner banks are evaluated on the
original HB scalar, before-HB cutoff, mode, residue and exact coprime mean. -/
theorem original_fibre (K : ℕ) (hN : 1<I.P.N) (hU : 1<I.U) :
    exactDiscrepancy (fibre I.bs I.i I.C) (products I.P) (fun q => (free I.P q:ℂ))
      completeProduct I.P.N (originalMode I K)=
      (scalar I:ℂ)*∑ j∈I.P.words.attach,let A := onWord I j
        (restore I.P j.val (groups A):ℂ)*errors A K := by
  rw [free_fibre I K hU,P4BOriginalHigherLowTensor.complex_complete I.P hN I.x I.U I.eta]
  apply congrArg (fun z : ℂ => (scalar I:ℂ)*z)
  rw [←Finset.sum_attach I.P.words]
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun z : ℂ => (restore I.P j.val (groups (onWord I j)):ℂ)*z)
  exact (word_errors (onWord I j) K).symm

end
end ImbalancedChen.P4BOriginalHigherLowNativeAtoms
