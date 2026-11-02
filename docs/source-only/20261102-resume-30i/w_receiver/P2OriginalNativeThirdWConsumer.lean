import ImbalancedChen.P2OriginalThirdWReceiver

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual nonzero signed small/rough coefficient supplies its own word,
acceptance, beta sign and product. A COMPUTED third-W branch then gives
the complete full/empty-complement gates and the deterministic arithmetic
licence on (p2*p1)*k, for arbitrary inherited rough descendants and beta
slots. No accepted-word, full-support, Inherits or final-licence hypothesis.
The full adopted-bank equality and uniform common-box compiler remain open.
-/
namespace ImbalancedChen.P2OriginalNativeThirdWConsumer
noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairSourceReceiver P2OriginalPairRootRoughProducer
open P2OriginalLowerWholeBoxBranchSelect P2OriginalSelectedPairNativeData
open P2OriginalSelectedIntegerPrefixSquares P2OriginalSelectedNativeSmallExtension
open P2OriginalPairNativeWEmptyMaskSupport P2EnhancedLowerPhysicalNode
open P2OriginalFreshWArithmetic P2OriginalThirdWReceiver P5CausalRhoFactorization

def Payload (R : PairRange) (mesh : ℕ) (buffer : ℚ) (seed : ℝ)
    (N : ℕ) (p : ℕ×ℕ) (k s q : ℕ) (tail : List ℕ) : Prop :=
  let code := firstCode R mesh (coordinate N p.2) (coordinate N p.1) (coordinate N q)
  let z := endpoint R code 2
  let whole := wTagged (p.2::p.1::q::tail) ++ s.primeFactorsList.reverse.map (fun n => (n,false))
  let H := run (plan R mesh buffer seed) R.epsilon ceiling (pairRoot N p seed)
    ((q::tail).map (coordinate N))
  (SourceForm.wSlot 2).affine.eval (endpoint R code)=value z ∧
    (SourceForm.wSlot 2).affine.eval
      (![coordinate N p.2,coordinate N p.1,coordinate N q,0,0] : Fin 5 → ℝ)=
      VariableEnvelope.B (coordinate N q) ∧
    value z≤VariableEnvelope.B (coordinate N q) ∧
    VariableEnvelope.w (coordinate N p.2) (coordinate N p.1) (coordinate N q)=
      VariableEnvelope.B (coordinate N q) ∧
    value z≤VariableEnvelope.original (coordinate N p.2) (coordinate N p.1) (coordinate N q) ∧
    (SourceForm.wSlot 2).supportMask=∅ ∧ H.cap=physical z buffer ∧
    selectedPrimes whole=[] ∧ (whole.map Prod.fst).prod=(p.2*p.1)*k ∧
    IntegerSquareGates N (auxiliary z buffer) 1 (whole.map Prod.fst) ∧
    IntegerSquareGates N (auxiliary z buffer) (selectedPrimes whole).prod (remainingPrimes whole) ∧
    ∀ A : ℝ, 1≤A → A≤(N:ℝ)^(1/3:ℝ) →
      Licence N z buffer A p ((q::tail)++s.primeFactorsList.reverse)

private theorem coord_mono {N p q : ℕ} (hN : 1<(N:ℝ)) (hq : 0<q) (hqp : q≤p) :
    coordinate N q≤coordinate N p := by
  exact div_le_div_of_nonneg_right
    (Real.log_le_log (Nat.cast_pos.mpr hq) (by exact_mod_cast hqp)) (Real.log_pos hN).le

private theorem square_mono {c d T : ℝ} (xs : List ℝ) (hcd : c≤d)
    (h : SquareGates c T xs) : SquareGates d T xs := by
  induction xs generalizing T with
  | nil => trivial
  | cons x xs ih => exact ⟨h.1.trans hcd,ih h.2⟩

/-- General native pair source, with its actual seed retained as data.
The compact coordinate conditions only crop the original endpoint mesh;
eligibility is the literal primitive screen read by the computed plan. -/
theorem native_receiver (R : PairRange) (mesh : ℕ) (buffer : ℚ) (seed : ℝ)
    (N enum : ℕ) (hN : 1<(N:ℝ)) (p : ℕ×ℕ) (hp1 : p.1.Prime) (hp2 : p.2.Prime)
    (w cutoff L : ℝ) (hhead : w^2≤L) (hL : L≤(N:ℝ)^(buffer:ℝ)) {k : ℕ}
    (hk : actualLowerSmallRoughRho
      (pairPolicy (plan R mesh buffer seed) R.epsilon ceiling seed N p)
      N enum w cutoff L k≠0) :
    let P := plan R mesh buffer seed
    let policy := pairPolicy P R.epsilon ceiling seed N p
    ∃ s∈actualSmallRosserSupport N enum w,
      ∃ r∈fixedEvenRoughSupport policy N enum w cutoff,
        ∃ chosen : List ℕ, chosen <+ roughPrimeUniverse N enum w cutoff ∧
          chosen.prod=r ∧ k=s*r ∧
          (run P R.epsilon ceiling (pairRoot N p seed) (chosen.map (coordinate N))).accepted=true ∧
          actualLowerSmallRoughRho policy N enum w cutoff L k=coefficient policy N enum w cutoff L (s,r) ∧
          ∀ q tail, chosen=q::tail →
            coordinate N p.2∈Set.Icc (R.epsilon:ℝ) (ceiling:ℝ) →
            coordinate N p.1∈Set.Icc (R.epsilon:ℝ) (ceiling:ℝ) →
            coordinate N q∈Set.Icc (R.epsilon:ℝ) (ceiling:ℝ) →
            eligible R buffer seed (firstCode R mesh (coordinate N p.2) (coordinate N p.1) (coordinate N q)) →
            Payload R mesh buffer seed N p k s q tail := by
  let P := plan R mesh buffer seed
  let policy := pairPolicy P R.epsilon ceiling seed N p
  obtain ⟨s,hs,r,hr,chosen,hsub,hprod,hkprod,haccept,hvalue⟩ :=
    pair_rho_nonzero_rough_word P R.epsilon ceiling seed N enum p w cutoff L hk
  dsimp only
  refine ⟨s,hs,r,hr,chosen,hsub,hprod,hkprod,haccept,hvalue,?_⟩
  intro q tail hshape ht hu hq he
  subst chosen
  let code := firstCode R mesh (coordinate N p.2) (coordinate N p.1) (coordinate N q)
  let z := endpoint R code 2
  let word := p.2::p.1::q::tail
  let H3 := step P R.epsilon ceiling (pairRoot N p seed) (coordinate N q)
  let H := run P R.epsilon ceiling H3 (tail.map (coordinate N))
  have hupper := firstCode_upper R mesh _ _ _ ht hu hq
  have hgeom : Geometry (coordinate N p.2) (coordinate N p.1) z buffer :=
    source_geometry he hupper.1 hupper.2.1
  have hc : choice R buffer seed code=.fresh (physical z buffer) 2 := by
    simp only [choice,firstCode_prefix]
    exact if_pos he
  have hcap3 : H3.cap=physical z buffer := by
    rw [show H3.cap=(choice R buffer seed code).freeze seed from first_step R mesh buffer seed _ _ _]
    rw [hc]
    rfl
  have hword3 : H3.word=[coordinate N p.2,coordinate N p.1,coordinate N q] := rfl
  have hthree : SquareGates H3.cap 0 H3.word := by
    rw [hcap3,hword3]
    have hh := first_three_squares he.1
    simp only [SquareGates,zero_add] at hh ⊢
    exact ⟨by linarith [hupper.1],by linarith [hupper.1,hupper.2.1],
      by linarith [hupper.1,hupper.2.1,hupper.2.2],True.intro⟩
  have hprime : ∀ n∈q::tail, n.Prime :=
    fun n hn => mem_roughPrimeUniverse_prime (hsub.subset hn)
  have hsortNat : (q::tail).Pairwise (· > ·) :=
    (roughPrimeUniverse_pairwise_gt N enum w cutoff).sublist hsub
  have hsort : (tail.map (coordinate N)).Pairwise (· ≥ ·) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have hi' : i<tail.length := by simpa using hi
    have hj' : j<tail.length := by simpa using hj
    have hgt := (List.pairwise_iff_getElem.mp (List.pairwise_cons.mp hsortNat).2) i j hi' hj' hij
    simpa only [List.getElem_map] using coord_mono hN
      (hprime _ (List.mem_cons_of_mem _ (List.getElem_mem hj'))).pos hgt.le
  have hnonneg : ∀ x∈tail.map (coordinate N), 0≤x := by
    intro x hx
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hx
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast
      (hprime n (List.mem_cons_of_mem q hn)).one_lt.le)) (Real.log_pos hN).le
  have hword : H.word=word.map (coordinate N) := by
    simp [H,run_word,H3,step,pairRoot,word]
  have hreal : SquareGates (physical z buffer) 0 (word.map (coordinate N)) := by
    have hh := accepted_third_continuation R mesh buffer seed H3 rfl
      (tail.map (coordinate N)) hthree hsort hnonneg haccept
    simpa only [hcap3,hword] using hh
  have hwholeprime : ∀ n∈word, n.Prime := by
    intro n hn
    simp only [word,List.mem_cons] at hn
    rcases hn with rfl | rfl | hn
    · exact hp2
    · exact hp1
    · exact hprime n hn
  have hfull : IntegerSquareGates N (physical z buffer) 1 word :=
    squareGates_to_integer hN word (fun n hn => (hwholeprime n hn).pos) (by simp) hreal
  have hb : 0<(buffer:ℝ) := he.1.1
  have haux : physical z buffer≤auxiliary z buffer := by dsimp [physical,auxiliary]; linarith
  have hfullAux : IntegerSquareGates N (auxiliary z buffer) 1 word :=
    squareGates_to_integer hN word (fun n hn => (hwholeprime n hn).pos) (by simp)
      (square_mono _ haux hreal)
  have hprodlt : (word.prod:ℝ)<(N:ℝ)^(physical z buffer) := by
    simpa only [Nat.one_mul] using integerSquareGates_product_lt word (by omega : 0<(1:ℕ))
      (fun n hn => (hwholeprime n hn).one_lt) (by simp [word]) hfull
  have hbudget : (word.prod:ℝ)*L≤(N:ℝ)^(auxiliary z buffer) := by
    calc
      _ ≤ (word.prod:ℝ)*(N:ℝ)^(buffer:ℝ) := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg _)
      _ < (N:ℝ)^(physical z buffer)*(N:ℝ)^(buffer:ℝ) :=
        mul_lt_mul_of_pos_right hprodlt (Real.rpow_pos_of_pos (zero_lt_one.trans hN) _)
      _ = _ := by rw [←Real.rpow_add (zero_lt_one.trans hN)]; congr 1; dsimp [physical,auxiliary]; ring
  have hactive : (s,r)∈activePairs policy N enum w cutoff L := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hs,hr⟩,by rw [←hvalue]; exact hk⟩
  have hsmall := active_pair_small_word_well policy N enum w cutoff L hactive hhead
  have hempty := w_empty_mask_words (2:Fin 5) word
  have hsf := actualSmallRosserSupport_squarefree N enum w hs
  have hsprod : s.primeFactorsList.reverse.prod=s := by
    rw [List.prod_reverse,Nat.prod_primeFactorsList hsf.ne_zero]
  have hext := append_unselected_same_cap (wTagged word) s.primeFactorsList.reverse
    (by simpa only [hempty.2.2.2] using hfullAux)
    (by simpa only [hempty.2.1,hempty.2.2.1,List.prod_nil] using hfullAux)
    hsmall (by simpa only [hempty.2.2.2] using hbudget)
  have hqpow : (q:ℝ)≤(N:ℝ)^z := by
    rw [←coordinate_power hN (hprime q (by simp)).pos]
    exact Real.rpow_le_rpow_of_exponent_le hN.le hupper.2.2
  have htailBound : ∀ n∈(q::tail)++s.primeFactorsList.reverse,
      0<n ∧ (n:ℝ)≤(N:ℝ)^z := by
    intro n hn
    rcases List.mem_append.mp hn with hn | hn
    · have hnq : n≤q := by
        rcases List.mem_cons.mp hn with rfl | hn
        · exact le_refl _
        · exact ((List.pairwise_cons.mp hsortNat).1 n hn).le
      exact ⟨(hprime n hn).pos,(by exact_mod_cast hnq : (n:ℝ)≤q).trans hqpow⟩
    · have hnw := active_pair_small_word_cutoff policy N enum w cutoff L hactive n hn
      have hwq := mem_roughPrimeUniverse_lower (hsub.subset (List.mem_cons_self q tail))
      exact ⟨(Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp hn)).pos,
        hnw.le.trans (hwq.trans hqpow)⟩
  have hsource := original_point_source R mesh _ _ _ ht hu hq
  have hgeomActual : Geometry (coordinate N p.2) (coordinate N p.1) (coordinate N q) buffer := by
    rcases hgeom with ⟨hb,hbhi,hz,hzhi,htop,utop,hgap⟩
    refine ⟨hb,hbhi,?_,hupper.2.2.trans hzhi,htop,utop,?_⟩
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast (hprime q (by simp)).one_lt.le))
        (Real.log_pos hN).le
    · have hh : value z≤value (coordinate N q) := by dsimp [value]; linarith [hupper.2.2]
      exact hgap.trans hh
  have horiginal := original_W_identity hgeomActual
  have hB : value (coordinate N q)=VariableEnvelope.B (coordinate N q) := by
    dsimp [value,VariableEnvelope.B,VariableEnvelope.cap]; ring
  dsimp only [Payload]
  refine ⟨(source_identity R code).1,hsource.1,hsource.2,horiginal.1,
    hsource.2.trans (hB ▸ horiginal.2),rfl,?_,?_,?_,hext.1,hext.2.1,?_⟩
  · exact (run_cap R mesh buffer seed H3 (by simp [hword3]) _).trans hcap3
  · rw [appendUnselected_selected]
    exact hempty.2.1
  · rw [appendUnselected_values,List.prod_append,hempty.2.2.2,hsprod]
    have hwprod : word.prod=(p.2*p.1)*r := by
      change p.2*(p.1*(q::tail).prod)=(p.2*p.1)*r
      rw [hprod]
      ring
    rw [hwprod,hkprod]
    ring
  · intro A hA hAupper
    apply complete_word hN p hp1.pos hp2.pos hgeom hA hAupper _ htailBound
    simpa only [appendUnselected_values,hempty.2.2.2,List.cons_append,List.nil_append] using hext.1

/-- Literal production U5 attachment. Its small-level/head hypotheses
are proved from the original exponent 34/125; the native root is the
independent original max, and no candidate/adopted identity is assumed. -/
theorem original_U5_receiver (R : PairRange) (mesh : ℕ) (buffer : ℚ)
    {N : ℕ} (hN : 2≤N) {p : ℕ×ℕ} (hp : p∈P5OriginalU5CausalFinite.pairSupport N)
    {epsilon : ℝ} (heps : 0<epsilon) (heps8 : epsilon<1/8)
    (halloc : P5OriginalU5CausalFinite.attachmentNu*epsilon≤(buffer:ℝ)) {k : ℕ}
    (hk : P5OriginalU5CausalFinite.rho N epsilon
      (pairPolicy (plan R mesh buffer (rootSeed false buffer N p))
        R.epsilon ceiling (rootSeed false buffer N p) N p) k≠0) :
    let seed := rootSeed false buffer N p
    let P := plan R mesh buffer seed
    let policy := pairPolicy P R.epsilon ceiling seed N p
    let enum := Nat.ceil (P5OriginalU5CausalFinite.cutoff N)
    let w := P5OriginalU5CausalFinite.smallCutoff N epsilon
    let z := P5OriginalU5CausalFinite.cutoff N
    let L := P5OriginalU5CausalFinite.smallLevel N epsilon
    ∃ s∈actualSmallRosserSupport N enum w,
      ∃ r∈fixedEvenRoughSupport policy N enum w z,
        ∃ chosen : List ℕ, chosen <+ roughPrimeUniverse N enum w z ∧
          chosen.prod=r ∧ k=s*r ∧
          (run P R.epsilon ceiling (pairRoot N p seed) (chosen.map (coordinate N))).accepted=true ∧
          P5OriginalU5CausalFinite.rho N epsilon policy k=coefficient policy N enum w z L (s,r) ∧
          ∀ q tail, chosen=q::tail →
            coordinate N p.2∈Set.Icc (R.epsilon:ℝ) (ceiling:ℝ) →
            coordinate N p.1∈Set.Icc (R.epsilon:ℝ) (ceiling:ℝ) →
            coordinate N q∈Set.Icc (R.epsilon:ℝ) (ceiling:ℝ) →
            eligible R buffer seed (firstCode R mesh (coordinate N p.2) (coordinate N p.1) (coordinate N q)) →
            Payload R mesh buffer seed N p k s q tail := by
  have hn : 1<(N:ℝ) := by exact_mod_cast (show 1<N by omega)
  obtain ⟨hcarrier,_⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hcarrier
  have hhead : (P5OriginalU5CausalFinite.smallCutoff N epsilon)^2≤
      P5OriginalU5CausalFinite.smallLevel N epsilon := by
    unfold P5OriginalU5CausalFinite.smallCutoff P5OriginalU5CausalFinite.smallLevel
    rw [←Real.rpow_mul_natCast (zero_lt_one.trans hn).le]
    apply Real.rpow_le_rpow_of_exponent_le hn.le
    norm_num [P5OriginalU5CausalFinite.attachmentNu]
    nlinarith
  exact native_receiver R mesh buffer (rootSeed false buffer N p) N _ hn p
    (mem_chenAdditivePrimeCarrier.mp hp1).2.1 (mem_chenAdditivePrimeCarrier.mp hp2).2.1
    _ _ _ hhead (Real.rpow_le_rpow_of_exponent_le hn.le halloc) hk

/-- A source instance of the actual U6 LowerData interface. Original w
and L are retained literally; no equality with original.policy is claimed. -/
def sixthData (R : PairRange) (mesh : ℕ) (buffer : ℚ) (N : ℕ)
    (original : P5JointNativeSignedRegroup.LowerData) : P5JointNativeSignedRegroup.LowerData where
  policy := fun p => pairPolicy (plan R mesh buffer (rootSeed true buffer N p))
    R.epsilon ceiling (rootSeed true buffer N p) N p
  w := original.w
  L := original.L

/-- The actual retained sixth selector keeps its original complement E
and piecewise root. The arbitrary original w/L fields have explicit beta
head/allocation ports; they are not falsely discharged from interface data. -/
theorem original_U6_receiver (R : PairRange) (mesh : ℕ) (buffer : ℚ)
    {N : ℕ} (hN : 1<(N:ℝ)) (original : P5JointNativeSignedRegroup.LowerData)
    (E : ℕ×ℕ → Prop) (eta : ℝ) {p : ℕ×ℕ}
    (hp : p∈currentChenUpsilon6RetainedSelector N E eta)
    (hhead : (original.w p)^2≤original.L p)
    (hL : original.L p≤(N:ℝ)^(buffer:ℝ)) {k : ℕ}
    (hk : P5JointNativeSignedRegroup.lowerRho (sixthData R mesh buffer N original) N p k≠0) :
    let seed := rootSeed true buffer N p
    let P := plan R mesh buffer seed
    let policy := pairPolicy P R.epsilon ceiling seed N p
    let enum := Nat.ceil (P5CausalRhoQuotientBridge.cutoff N)
    let cutoff := P5CausalRhoQuotientBridge.cutoff N
    ¬E p ∧ ∃ s∈actualSmallRosserSupport N enum (original.w p),
      ∃ r∈fixedEvenRoughSupport policy N enum (original.w p) cutoff,
        ∃ chosen : List ℕ, chosen <+ roughPrimeUniverse N enum (original.w p) cutoff ∧
          chosen.prod=r ∧ k=s*r ∧
          (run P R.epsilon ceiling (pairRoot N p seed) (chosen.map (coordinate N))).accepted=true ∧
          P5JointNativeSignedRegroup.lowerRho (sixthData R mesh buffer N original) N p k=
            coefficient policy N enum (original.w p) cutoff (original.L p) (s,r) ∧
          ∀ q tail, chosen=q::tail →
            coordinate N p.2∈Set.Icc (R.epsilon:ℝ) (ceiling:ℝ) →
            coordinate N p.1∈Set.Icc (R.epsilon:ℝ) (ceiling:ℝ) →
            coordinate N q∈Set.Icc (R.epsilon:ℝ) (ceiling:ℝ) →
            eligible R buffer seed (firstCode R mesh (coordinate N p.2) (coordinate N p.1) (coordinate N q)) →
            Payload R mesh buffer seed N p k s q tail := by
  have hret := (mem_currentChenUpsilon6RetainedSelector_log_iff hN E eta p).mp hp
  exact ⟨hret.2.2.1,native_receiver R mesh buffer (rootSeed true buffer N p) N _ hN p
    (mem_chenAdditivePrimeCarrier.mp hret.1).2.1
    (mem_chenAdditivePrimeCarrier.mp hret.2.1).2.1 _ _ _ hhead hL hk⟩

end
end ImbalancedChen.P2OriginalNativeThirdWConsumer
