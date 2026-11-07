import ImbalancedChen.P5OriginalU5MixedCover
import ImbalancedChen.P2OriginalPairRootRoughProducer
import ImbalancedChen.P2OriginalSelectedIntegerPrefixSquares

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The independently defined production U5 selector and signed rho supply
the actual first rough prime. There is no eligibility/rescue screen on
that prime. The complete native source winner, its true root/rough W
ceiling, its integer full/complement gates and its near-tie cover follow.

The supplied CapPlan remains independently given: this theorem does not
claim that its third choice is the ideal winner. That finite adoption,
all higher histories and the same-coefficient AP/table/integral estimates
are still required. This distinction prevents a source identity from
being misrepresented as an adopted-policy identity.
-/
namespace ImbalancedChen.P5OriginalU5NativeMixedPrefix

noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairRootRoughProducer P2OriginalSelectedPairNativeData
open P2OriginalSelectedIntegerPrefixSquares P2EnhancedLowerPhysicalNode
open P5OriginalU5MixedWinner P5OriginalU5MixedCover

def integerSlots (mask : Finset (Fin 5)) (p : ℕ×ℕ) (q : ℕ) : List (ℕ×Bool) :=
  [(p.2,decide (0∈mask)),(p.1,decide (1∈mask)),(q,decide (2∈mask))]

theorem actual_domain {N : ℕ} (hN : 2≤N) {p : ℕ×ℕ}
    (hp : p∈P5OriginalU5CausalFinite.pairSupport N) {enum : ℕ} {w : ℝ} {q : ℕ}
    (hq : q∈roughPrimeUniverse N enum w (P5OriginalU5CausalFinite.cutoff N)) :
    Domain (coordinate N p.2) (coordinate N p.1) (coordinate N q) := by
  have hn : 1<(N:ℝ) := by exact_mod_cast (show 1<N by omega)
  have hpdom := Part5OriginalUpsilon5CausalDictionary.mem_triangle.mp
    (P5OriginalU5CausalFinite.coordinates_mem_triangle hN hp)
  have hcoords : P5OriginalU5CausalFinite.coordinates N p =
      (![coordinate N p.1,coordinate N p.2] : Fin 2 → ℝ) := by
    funext i
    fin_cases i <;> rfl
  rw [hcoords] at hpdom
  have hprime := mem_roughPrimeUniverse_prime hq
  have hnonneg : 0≤coordinate N q :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)) (Real.log_pos hn).le
  have hpow : (N:ℝ)^(coordinate N q)<(N:ℝ)^(417/5000:ℝ) := by
    rw [coordinate_power hn hprime.pos]
    exact mem_roughPrimeUniverse_upper hq
  exact ⟨hpdom.1,hpdom.2.1.le,hpdom.2.2.le,hnonneg,
    ((Real.rpow_lt_rpow_left_iff hn).mp hpow).le⟩

def Payload (N : ℕ) (p : ℕ×ℕ) (q : ℕ) (buffer kappa : ℝ) : Prop :=
  let t := coordinate N p.2
  let u := coordinate N p.1
  let z := coordinate N q
  let s := winner t u z
  let form := nativeForm t u z s
  let slots := integerSlots form.supportMask p q
  Domain t u z ∧ sourceValue t u z s=VariableEnvelope.original t u z ∧
    form.affine.eval (sourcePoint t u z s)=VariableEnvelope.original t u z ∧
    form.supportMask=sourceMask s ∧
    (s=rootSource t u ↔ VariableEnvelope.original t u z=rootValue t u) ∧
    IntegerSquareGates N (VariableEnvelope.original t u z-2*buffer-1/32) 1
      (slots.map Prod.fst) ∧
    IntegerSquareGates N (VariableEnvelope.original t u z-2*buffer-1/32)
      (selectedPrimes slots).prod (remainingPrimes slots) ∧
    (selectedPrimes slots).prod*(remainingPrimes slots).prod=(p.2*p.1)*q ∧
    Licensed t u z buffer kappa

/-- Every actual first rough prime of the original L5 source is covered.
The source is not cropped to the earlier small rescue rectangle. -/
theorem actual_prefix_payload {N : ℕ} (hN : 2≤N) {p : ℕ×ℕ}
    (hp : p∈P5OriginalU5CausalFinite.pairSupport N) {enum : ℕ} {w : ℝ} {q : ℕ}
    (hq : q∈roughPrimeUniverse N enum w (P5OriginalU5CausalFinite.cutoff N))
    {buffer kappa : ℝ} (hb : 0<buffer) (hbhi : buffer≤1/1000) (hk : kappa≤buffer/8) :
    Payload N p q buffer kappa := by
  let t := coordinate N p.2
  let u := coordinate N p.1
  let z := coordinate N q
  let s := winner t u z
  let mask := (nativeForm t u z s).supportMask
  let slots := integerSlots mask p q
  have hd := actual_domain hN hp hq
  have hn : 1<(N:ℝ) := by exact_mod_cast (show 1<N by omega)
  have hpprimes := P2OriginalU5SmallPartnerRootPayment.pair_primes hp
  have hqprime := mem_roughPrimeUniverse_prime hq
  have hpos : ∀ x∈slots, 0<x.1 := by
    intro x hx
    simp only [slots,integerSlots,List.mem_cons,List.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hpprimes.2.pos
    · exact hpprimes.1.pos
    · exact hqprime.pos
  have hlog : logSlots N slots=prefixSlots mask t u z := rfl
  have hg := winner_full_and_complement hd hbhi
  have hi := physical_slots_to_integer hn slots hpos
    (VariableEnvelope.original t u z-2*buffer-1/32)
    (by simpa only [hlog,prefixSlots,List.map_cons,List.map_nil] using hg.1)
    (by simpa only [hlog] using hg.2)
  have hprod : (selectedPrimes slots).prod*(remainingPrimes slots).prod=(p.2*p.1)*q := by
    rw [selected_mul_remaining]
    simp [slots,integerSlots,Nat.mul_assoc]
  exact ⟨hd,winner_eq_original hd,(winner_native_source hd).1,(winner_native_source hd).2,
    winner_inherits_iff hd,hi.1,hi.2,hprod,full_original_winner_cover hd hb hbhi hk⟩

/-- The physical pair-root cap is exactly the independent variable root,
not the rational ranking floor of a candidate bank. -/
theorem native_root_identity (buffer : ℚ) (N : ℕ) (p : ℕ×ℕ) :
    rootSeed false buffer N p = rootValue (coordinate N p.2) (coordinate N p.1)-2*(buffer:ℝ) := by
  rfl

/-- Actual nonzero signed rho supplies its accepted original word and
exact beta/rough coefficient. Only then is the whole mixed-source theorem
applied to its first rough prime. The policy is not equated with winner. -/
theorem nonzero_original_rho_prefix {depth mesh : ℕ} (P : CapPlan depth mesh)
    (lo hi : ℝ) (buffer : ℚ) (hb : 0<(buffer:ℝ)) (hbhi : (buffer:ℝ)≤1/1000)
    (kappa : ℝ) (hkappa : kappa≤(buffer:ℝ)/8)
    {N : ℕ} (hN : 2≤N) {p : ℕ×ℕ} (hp : p∈P5OriginalU5CausalFinite.pairSupport N)
    (epsilon : ℝ) {k : ℕ}
    (hk : P5OriginalU5CausalFinite.rho N epsilon
      (pairPolicy P lo hi (rootSeed false buffer N p) N p) k≠0) :
    let policy := pairPolicy P lo hi (rootSeed false buffer N p) N p
    let enum := Nat.ceil (P5OriginalU5CausalFinite.cutoff N)
    let small := P5OriginalU5CausalFinite.smallCutoff N epsilon
    let cutoff := P5OriginalU5CausalFinite.cutoff N
    let L := P5OriginalU5CausalFinite.smallLevel N epsilon
    ∃ s∈actualSmallRosserSupport N enum small,
      ∃ r∈fixedEvenRoughSupport policy N enum small cutoff,
        ∃ chosen : List ℕ, chosen <+ roughPrimeUniverse N enum small cutoff ∧
          chosen.prod=r ∧ k=s*r ∧
          (run P lo hi (pairRoot N p (rootSeed false buffer N p))
            (chosen.map (coordinate N))).accepted=true ∧
          P5OriginalU5CausalFinite.rho N epsilon policy k=
            P5CausalRhoFactorization.coefficient policy N enum small cutoff L (s,r) ∧
          ∀ q tail, chosen=q::tail → Payload N p q buffer kappa := by
  obtain ⟨s,hs,r,hr,chosen,hsub,hprod,hkr,haccept,hvalue⟩ :=
    pair_rho_nonzero_rough_word P lo hi (rootSeed false buffer N p) N
      (Nat.ceil (P5OriginalU5CausalFinite.cutoff N)) p
      (P5OriginalU5CausalFinite.smallCutoff N epsilon) (P5OriginalU5CausalFinite.cutoff N)
      (P5OriginalU5CausalFinite.smallLevel N epsilon) hk
  refine ⟨s,hs,r,hr,chosen,hsub,hprod,hkr,haccept,hvalue,?_⟩
  intro q tail hshape
  have hq : q∈chosen := by rw [hshape]; exact List.mem_cons_self q tail
  exact actual_prefix_payload hN hp (hsub.subset hq) hb hbhi hkappa

end
end ImbalancedChen.P5OriginalU5NativeMixedPrefix
