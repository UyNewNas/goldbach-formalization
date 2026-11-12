import ImbalancedChen.P4BOriginalMediumAtomFamily

/-! The native Part 3 discrepancy equals the physical AP count minus its
exact coprime mean, at the same complete level. The three coefficients
have a disjoint dyadic reconstruction even at powers of two and at one. -/
namespace ImbalancedChen.P4BOriginalMediumSignedFibre
noncomputable section
open Classical
open scoped BigOperators
open Part3 (MediumAtom factorCarrier)
open P5Z.HBRightClosedDyadicRoles (Block Owns owner owner_owns owns_unique)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos owns_bounds)
open P5Z.OrderedFactorTupleRectangleReindex (blockIntegers mem_blockIntegers)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct hbSlots)
open P5Z.ActualAllRankOccurrenceFourierBridge (occurrenceMode)
open P4BUpperPairOrderedRowGeometry (blockScales)
open P4BOriginalHighRankComplementBlocks (fibre)
open P4BOriginalMediumAtomFamily (Index cut support support_data third_data)
open P4BOriginalMediumComplementCoefficient (beta otherWords other_mem)
open P4BOriginalCollisionThirdFactor (thirdSupport factor gamma)
open P4BOriginalCollisionTensor (products free)
open P4BOriginalCollisionKernel (row reindex)
open PrimeProducts.MellinInsertion20261028 (residueKernel exactDiscrepancy)

theorem block_sub (B : Block) : blockIntegers B⊆factorCarrier (lower B:ℝ) := by
  intro n hn
  obtain ⟨h1,h2⟩ := owns_bounds ((mem_blockIntegers B n).mp hn)
  exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr (by exact_mod_cast h1),Nat.le_floor (by exact_mod_cast h2)⟩

private theorem nonunit_interval (B : Block) (hu : 1<(lower B:ℝ)) :
    Finset.Ioc ⌊(lower B:ℝ)⌋₊ ⌊2*(lower B:ℝ)⌋₊=blockIntegers B := by
  cases B with
  | unit => norm_num [lower] at hu
  | dyadic k =>
    rw [show 2*((lower (Block.dyadic k):ℝ))=((2*lower (Block.dyadic k):ℕ):ℝ) by push_cast <;> rfl]
    simp only [Nat.floor_natCast,blockIntegers,lower,pow_succ,mul_comm (2:ℕ)]

variable {order : ℕ} {zeta kap0 : ℝ} (I : Index order zeta kap0)
private theorem head_carrier (K : ℕ) (hu : 1<I.U) :
    (I.atom K).alphaCarrier=blockIntegers (I.bs I.i) :=
  (I.carrier K).trans (nonunit_interval _ hu)

def originalMode (K : ℕ) (y : Fin (P4BOriginalMediumAtomFamily.size I.j+
    P4BOriginalMediumAtomFamily.size I.l)→ℕ) :=
  hbSlots (I.Z K) I.truncations I.roles y*occurrenceMode (blockScales I.bs) y I.xi

def scalar : ℝ := ∏ j,P4BOriginalMediumHBHead.scalar (I.bs j) (I.roles j)

private theorem beta_outside (K : ℕ) {m : ℕ} (hm : m∉blockIntegers I.C) :
    (I.atom K).beta m=0 := by
  change beta I.bs I.i I.C (I.Z K) I.truncations I.roles I.xi m=0
  unfold beta
  apply Finset.sum_eq_zero
  intro z hz
  exact (hm ((Finset.mem_filter.mp hz).2 ▸ other_mem (Finset.mem_filter.mp hz).1)).elim

theorem row_at_level (K : ℕ) (hu : 1<I.U) (q : ℕ) :
    row (fibre I.bs I.i I.C) completeProduct (originalMode I K) I.P.N q =
      (scalar I:ℂ)*(I.atom K).discrepancy q := by
  have H := P4BOriginalMediumComplementCoefficient.separated I.bs I.i I.C (I.Z K)
    I.truncations I.roles I.xi (residueKernel q I.P.N)
  change row (fibre I.bs I.i I.C) completeProduct (originalMode I K) I.P.N q=_ at H
  rw [H]
  apply congrArg (fun a : ℂ => (scalar I:ℂ)*a)
  unfold MediumAtom.discrepancy
  rw [head_carrier I K hu]
  apply Finset.sum_congr rfl
  intro n _
  have hkernel (m : ℕ) :
      residueKernel q I.P.N (n*m)=
        (if (((n*m:ℕ):ℤ)%(q:ℤ)=(I.atom K).residue%(q:ℤ)) then (1:ℂ) else 0)-
        (if Nat.Coprime (n*m) q then 1 else 0)/(q.totient:ℂ) := by
    have iff : (((n*m:ℕ):ℤ)%(q:ℤ)=(I.P.N:ℤ)%(q:ℤ)) ↔ (n*m)%q=I.P.N%q :=
      Int.natCast_modEq_iff
    unfold residueKernel
    change _=(if (((n*m:ℕ):ℤ)%(q:ℤ)=(I.P.N:ℤ)%(q:ℤ)) then _ else _)-_
    rw [propext iff]
  simp_rw [←hkernel]
  exact Finset.sum_subset (block_sub I.C) (fun m _ hm => by
    change (I.atom K).alpha n*(I.atom K).beta m*residueKernel q I.P.N (n*m)=0
    rw [beta_outside I K hm]
    ring)

/-- All physical levels together, with the free arithmetic coefficient
obtained from the original same-rho collision payment. -/
theorem free_fibre (K : ℕ) (hu : 1<I.U) :
    exactDiscrepancy (fibre I.bs I.i I.C) (products I.P) (fun d => (free I.P d:ℂ))
      completeProduct I.P.N (originalMode I K)=
      (scalar I:ℂ)*∑ d∈products I.P,(free I.P d:ℂ)*(I.atom K).discrepancy d := by
  rw [reindex,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun d _ => by rw [row_at_level I K hu]; ring)

theorem owner_sum (S : Finset ℕ) (f : ℕ→ℝ) (hp : ∀n∈S,0<n) (F : ℕ→ℂ) :
    (∑ B∈S.image owner,∑ n∈factorCarrier (lower B:ℝ),cut S f B n*F n)=
      ∑ n∈S,(f n:ℂ)*F n := by
  rw [←Finset.sum_fiberwise_of_maps_to (s:=S) (t:=S.image owner) (g:=owner)
    (fun n hn => Finset.mem_image_of_mem owner hn) (fun n => (f n:ℂ)*F n)]
  apply Finset.sum_congr rfl
  intro B _
  let T := S.filter (fun n => owner n=B)
  have hs : T⊆factorCarrier (lower B:ℝ) := by
    intro n hn
    obtain ⟨hnS,hnB⟩ := Finset.mem_filter.mp hn
    exact block_sub B ((mem_blockIntegers B n).mpr (hnB ▸ owner_owns (hp n hnS)))
  calc
    _=∑ n∈T,cut S f B n*F n := by
      symm
      apply Finset.sum_subset hs
      intro n _ hn
      have hz : ¬(n∈S ∧ Owns B n) := fun h => hn (Finset.mem_filter.mpr
        ⟨h.1,(owns_unique (hp n h.1) h.2).symm⟩)
      simp [cut,hz]
    _=_ := Finset.sum_congr rfl (fun n hn => by
      obtain ⟨hs,he⟩ := Finset.mem_filter.mp hn
      rw [cut,if_pos ⟨hs,he ▸ owner_owns (hp n hs)⟩])

end
end ImbalancedChen.P4BOriginalMediumSignedFibre
