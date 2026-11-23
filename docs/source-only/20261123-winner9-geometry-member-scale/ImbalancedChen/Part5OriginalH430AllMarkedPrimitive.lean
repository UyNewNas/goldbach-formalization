import ImbalancedChen.Part5OriginalH430MemberAttachedPrimeCarrier
import ImbalancedChen.CurrentChenPairRosser
import ImbalancedChen.CoprimeRecentering

/-! Complete marked moduli are primitive on both actual signed supports,
even on an empty receiver. Reindex the literal quotient divisor sum at
its full AP modulus and its exact prime-carrier coprime mean. -/
namespace ImbalancedChen.Part5OriginalH430AllMarkedPrimitive
noncomputable section
open scoped Classical BigOperators
open P2EnhancedLowerFinitePhysicalGraph P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OwnedRootCounts Part5OriginalH430SameQHistoryCells Part5OriginalH430EnhancedPhysicalGrid
open Part5OriginalH430OriginalReceiptMemberPullback (memberCutoff)
open Part5OriginalH430MemberAttachedPrimeCarrier (memberModuli)
open Part5OriginalH430LowerRoughMember (retainEven)

def supportAt {N : ℕ} (upper : Bool) (cap : ℕ) (Q rho : ℝ) (o : Occurrence N) : Finset ℕ :=
  if upper then memberModuli cap Q rho o else
    let B := parentProduct o.current.old
    actualLowerSmallRoughModuli (retainEven (Q/(B:ℝ))) (N*B) cap ((N:ℝ)^rho) (memberCutoff Q o)

def attachedAt {N : ℕ} (upper : Bool) (cap : ℕ) (Q rho ell : ℝ) (o : Occurrence N) : ℕ→ℝ :=
  if upper then Part5OriginalH430AttachedUpperMember.coefficientAt cap Q rho ell o
  else Part5OriginalH430LowerRoughMember.coefficientAt cap Q rho ell o

/-- The primitive-residue and old/new coprimality conditions hold on
the full displayed upper or lower support of every chronological Member.
No nonzero coefficient, sifted value or populated fibre is assumed. -/
theorem whole_displayed_primitive {N n m p : ℕ} {k : Root} {t : ℝ} {key : RootKey n m} {o : Occurrence N}
    (hN : 2≤N) (hn : 111≤n) (ht : 0≤t) (hu : t≤1/12) (hp : p∈rootFibre N n m k t key)
    (ho : o∈rootHistory N n k t p) (upper : Bool) (cap : ℕ) (rho : ℝ) :
    let B := parentProduct o.current.old
    B.Coprime N ∧ ∀ h∈supportAt upper cap (cellQ N n key.1) rho o,
      (B*h).Coprime N ∧ h.Coprime B ∧ 0<B*h ∧ N%(B*h)∈finiteReducedResidues (B*h) := by
  dsimp only
  let B := parentProduct o.current.old
  let Q := cellQ N n key.1
  have hb := (Finset.mem_filter.mp hp).1
  have hco := rootHistory_coherent (by omega : 1<N) ht hu (precision_error hn)
    (original_band_prime hb) (original_band_geometry hN hb) ho
  have hB : B.Coprime N := Nat.coprime_list_prod_left_iff.mpr (fun q hq=>(hco.letters q hq).2)
  refine ⟨hB,?_⟩
  intro h hh
  have hl : h.Coprime (N*B) := by
    cases upper
    · exact actualLowerSmallRoughModuli_coprime_target _ _ _ _ _ hh
    · exact actualSmallRoughModuli_coprime_target _ _ _ _ _ hh
  have hc := Nat.coprime_mul_iff_right.mp hl
  have hprod : (B*h).Coprime N := hB.mul_left hc.1
  have hpos : 0<B*h := by
    apply Nat.pos_of_ne_zero
    intro hh0
    rw [hh0,Nat.coprime_zero_left] at hprod
    omega
  exact ⟨hprod,hc.2,hpos,(mod_mem_finiteReducedResidues_iff N _ hpos).mpr hprod.symm⟩

/-- A nonzero value of the actual attached coefficient lies in its
displayed support. Each factor of any three-way division of its full
marked modulus is therefore a primitive modulus for the same residue. -/
theorem active_group_factors {N n m p h : ℕ} {k : Root} {t : ℝ} {key : RootKey n m} {o : Occurrence N}
    (hN : 2≤N) (hn : 111≤n) (ht : 0≤t) (hu : t≤1/12) (hp : p∈rootFibre N n m k t key)
    (ho : o∈rootHistory N n k t p) (upper : Bool) (cap : ℕ) (rho ell : ℝ)
    (ha : attachedAt upper cap (cellQ N n key.1) rho ell o h≠0) :
    let B := parentProduct o.current.old
    (B*h).Coprime N ∧ h.Coprime B ∧
      ∀ q1 q2 q3 : ℕ, q1*q2*q3=B*h → q1.Coprime N ∧ q2.Coprime N ∧ q3.Coprime N := by
  have hmem : h∈supportAt upper cap (cellQ N n key.1) rho o := by
    by_contra hnot
    apply ha
    cases upper
    · exact smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hnot
    · exact smallRoughRho_eq_zero_of_not_mem _ _ _ _ _ hnot
  have H := (whole_displayed_primitive hN hn ht hu hp ho upper cap rho).2 h hmem
  refine ⟨H.1,H.2.1,?_⟩
  intro q1 q2 q3 he
  have hcop : (q1*q2*q3).Coprime N := by rw [he]; exact H.1
  obtain ⟨h12,h3⟩ := Nat.coprime_mul_iff_left.mp hcop
  exact ⟨(Nat.coprime_mul_iff_left.mp h12).1,(Nat.coprime_mul_iff_left.mp h12).2,h3⟩

/-- On the actual unsifted quotient source underlying either attached
comparison, the same signed finite divisor sum equals both the full
AP-minus-centre and its exact coprime mean plus the original primitive
discrepancy. Every identity also holds when the quotient fibre is empty. -/
theorem signed_quotient_full_AP {N : ℕ} (upper : Bool) (cap : ℕ) (Q rho ell : ℝ) (o : Occurrence N) :
    let B := parentProduct o.current.old
    let S := supportAt upper cap Q rho o
    let w := attachedAt upper cap Q rho ell o
    let source := chenAdditivePrimeCarrier N
    let total := ∑ r∈chenQuotientPrimeSource N B, supportedDivisorSum S w r
    total=∑ h∈S,w h*(chenPrimeAPCount N N (B*h)-chenCentrePrimeAPCount N N (B*h)) ∧
    total=(∑ h∈S,w h*(finiteCoprimeMass source (fun _=>1) (B*h)/(Nat.totient (B*h):ℝ)))+
          ∑ h∈S,w h*finitePrimitiveDiscrepancy source (fun _=>1) N (B*h) := by
  dsimp only
  let B := parentProduct o.current.old
  let S := supportAt upper cap Q rho o
  let w := attachedAt upper cap Q rho ell o
  have H := currentChen_quotient_sum_supportedDivisorSum N B S w
  refine ⟨H,H.trans ?_⟩
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  have hg : finiteCongruenceMass (chenAdditivePrimeCarrier N) (fun _=>1) N (B*h)=
      chenPrimeAPCount N N (B*h)-chenCentrePrimeAPCount N N (B*h) := by
    simpa only [finiteCongruenceMass,Finset.sum_const, nsmul_eq_mul,mul_one] using
      (chenAdditivePrimeCarrier_AP_count N N (B*h))
  rw [finitePrimitiveDiscrepancy,hg]
  ring

/-- The normalizer in the previous exact decomposition is a true average
on every displayed full modulus, including those with empty observed
progression. Its residue-discrepancy sum is zero individually. -/
theorem exact_mean_on_every_displayed_modulus {N n m p : ℕ} {k : Root} {t : ℝ} {key : RootKey n m}
    {o : Occurrence N} (hN : 2≤N) (hn : 111≤n) (ht : 0≤t) (hu : t≤1/12)
    (hp : p∈rootFibre N n m k t key) (ho : o∈rootHistory N n k t p) (upper : Bool) (cap : ℕ) (rho : ℝ) :
    let B := parentProduct o.current.old
    ∀ h∈supportAt upper cap (cellQ N n key.1) rho o,
      (∑ r∈finiteReducedResidues (B*h),finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N)
        (fun _=>1) r (B*h))=0 := by
  intro h hh
  exact sum_finitePrimitiveDiscrepancy_reducedResidues _ _ _
    (((whole_displayed_primitive hN hn ht hu hp ho upper cap rho).2 h hh).2.2.1)

end
end ImbalancedChen.Part5OriginalH430AllMarkedPrimitive
