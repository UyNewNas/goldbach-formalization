import ImbalancedChen.P2OriginalPairRootWArithmetic
import ImbalancedChen.P2OriginalPairNativeOnceBufferedWSquares
import ImbalancedChen.P5ZU1011OriginalW16FactorMonomials

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Original U5 pairSupport and the literal signed rho supply the word.
The canonical tent continuation is only the already constructed subfamily.
For its ACTUAL inherited root-W histories, both complete gate lists,
initialization, deterministic W completion and three arithmetic monomials
are derived on the entire modulus p2*p1*k, including the actual beta word.
The empty W mask is not used as a critical selected product. Full original
adoption, fresh W entries, common endpoint partitions and PP remain open.
-/
namespace ImbalancedChen.P2OriginalNativeU5InheritedWLicence
noncomputable section
open scoped Classical
open P2LowerCapPlanIntegerRetention P2PhysicalIncomingPrefixCells
open P2OriginalPairSourceReceiver P2OriginalPairRootRoughProducer
open P2OriginalSelectedPairNativeData P2CanonicalPairTentWarmHistory
open P2OriginalPairBufferedRootProvenance P2OriginalPairRootWArithmetic
open P2OriginalSelectedIntegerPrefixSquares P2OriginalSelectedNativeSmallExtension
open P2OriginalPairNativeWEmptyMaskSupport P2OriginalPairNativeOnceBufferedWSquares
open P2OriginalLowerWholeBoxBranchSelect
open Part3.ActualWThreeCapacityRun Part3.ActualWResidualCompletion
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

/-- Only p2 and p1 are initialized. The third argument of initialBins
    is definitionally unused and is not added to the physical word. -/
def initialPair (A : ℝ) (p : ℕ×ℕ) : Bins ℕ :=
  let ac := actualTwoCapacityGreedy (fun n : ℕ => (n:ℝ)) A [p.1]
  ⟨ac.1,[p.2],ac.2⟩

def completed (N : ℕ) (buffer A : ℝ) (p : ℕ×ℕ) (tail : List ℕ) : Bins ℕ :=
  complete (fun n : ℕ => (n:ℝ)) A ((N:ℝ)^(2*theta buffer-1))
    ((N:ℝ)^(1-theta buffer-2*delta buffer)/A) (initialPair A p) tail

def ArithmeticLicence (N : ℕ) (buffer A : ℝ) (p : ℕ×ℕ) (tail : List ℕ) : Prop :=
  let out := completed N buffer A p tail
  Part3.ActualWThreeCapacityRun.Trace (initialPair A p) tail out ∧
    out.left.prod*out.middle.prod*out.right.prod=(p.2*p.1)*tail.prod ∧
    (0<out.left.prod ∧ 0<out.middle.prod ∧ 0<out.right.prod) ∧
    (out.left.prod:ℝ)≤A ∧
    A^2*(out.middle.prod:ℝ)*(out.right.prod:ℝ)^2≤(N:ℝ)^(1-4*delta buffer) ∧
    (N:ℝ)^(7/32:ℝ)*A*(out.left.prod:ℝ)*(out.middle.prod:ℝ)^5*(out.right.prod:ℝ)^2≤
      (N:ℝ)^(2-4*delta buffer) ∧
    (A*(out.right.prod:ℝ)/(out.middle.prod:ℝ))^(7/16:ℝ)*A*(out.left.prod:ℝ)*
      (out.middle.prod:ℝ)^5*(out.right.prod:ℝ)^2≤(N:ℝ)^(2-39*delta buffer/8)

theorem root_initialization {N : ℕ} (hN : 1<(N:ℝ)) (p : ℕ×ℕ)
    (hp1 : p.1.Prime) (hp2 : p.2.Prime)
    (hd : pairPoint N p∈Part5OriginalUpsilon5CausalDictionary.triangle)
    {buffer A : ℝ} (hb : 0<buffer) (hbhi : buffer≤1/1000)
    (hgap : VariableEnvelope.A (coordinate N p.2)+2*buffer≤W)
    (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) :
    let B := (N:ℝ)^(2*theta buffer-1)
    let C := (N:ℝ)^(1-theta buffer-2*delta buffer)/A
    1≤B ∧ 1≤C ∧ A*B*C=(N:ℝ)^(theta buffer-2*delta buffer) ∧
      Bounded (fun n : ℕ => (n:ℝ)) A B C (initialPair A p) ∧
      Positive (fun n : ℕ => (n:ℝ)) (initialPair A p) ∧
      total (fun n : ℕ => (n:ℝ)) (initialPair A p)=
        wp (fun n : ℕ => (n:ℝ)) [p.2,p.1] := by
  have hex := root_W_exponents hd hb hbhi hgap (show (0:ℝ)≤buffer from hb.le)
  have hNpos : 0<(N:ℝ) := zero_lt_one.trans hN
  have hApos : 0<A := zero_lt_one.trans_le hA
  let B := (N:ℝ)^(2*theta buffer-1)
  let P := (N:ℝ)^(1-theta buffer-2*delta buffer)
  let C := P/A
  have hC : 1≤C := (le_div_iff₀ hApos).mpr (by
    simpa using hAupper.trans (Real.rpow_le_rpow_of_exponent_le hN.le hex.2.2.2.2.1))
  have hAC : A*C=P := by dsimp [C]; field_simp [hApos.ne'] <;> ring
  have hsecond : (p.1:ℝ)^2≤P := by
    rw [←coordinate_power hN hp1.pos,←Real.rpow_mul_natCast hNpos.le]
    apply Real.rpow_le_rpow_of_exponent_le hN.le
    simpa only [Nat.cast_ofNat,mul_comm] using hex.2.2.2.1
  have hs : actualDwellSupport (A*C) [p.1] := by
    intro i hi
    have hi0 : i=0 := by simp only [List.length_singleton] at hi; omega
    subst i
    simpa only [hAC,List.take_zero,List.map_nil,List.prod_nil,
      List.getElem_cons_zero,one_mul] using hsecond
  obtain ⟨hprod,hleft,hright⟩ := actualTwoCapacityFactors_correct hA hC [p.1] hs
  have hfirst : (p.2:ℝ)≤B := by
    rw [←coordinate_power hN hp2.pos]
    exact Real.rpow_le_rpow_of_exponent_le hN.le (by linarith [hex.2.2.1])
  have hB : 1≤B := Real.one_le_rpow hN.le (by linarith [hex.1])
  have hbounded : Bounded (fun n : ℕ => (n:ℝ)) A B C (initialPair A p) :=
    ⟨by simpa [initialPair,wp,actualTwoCapacityFactors,actualNatList_cast_prod] using hleft,
      by simpa [initialPair,wp] using hfirst,
      by simpa [initialPair,wp,actualTwoCapacityFactors,actualNatList_cast_prod] using hright⟩
  have hp : ∀ i : Fin 3, 0<(![p.2,p.1,1] : Fin 3 → ℕ) i := by
    intro i
    fin_cases i
    · exact hp2.pos
    · exact hp1.pos
    · norm_num
  refine ⟨hB,hC,?_,hbounded,?_,?_⟩
  · calc
      A*B*C=B*P := by rw [←hAC]; ring
      _ = _ := by dsimp [B,P]; rw [←Real.rpow_add hNpos]; congr 1; ring
  · simpa [initialBins,initialPair] using initialBins_positive A ![p.2,p.1,1] hp
  · simpa [initialBins,initialPair] using initialBins_product A ![p.2,p.1,1] hA hC hs

/-- The complete W program consumes original full-prefix squares and
    the true ceiling. The first-overflow branch supplies its own critical
    middle product; the success branch uses the three actual capacities. -/
theorem complete_original_root_word {N : ℕ} (hN : 1<(N:ℝ)) (p : ℕ×ℕ)
    (hp1 : p.1.Prime) (hp2 : p.2.Prime)
    (hd : pairPoint N p∈Part5OriginalUpsilon5CausalDictionary.triangle)
    {buffer A : ℝ} (hb : 0<buffer) (hbhi : buffer≤1/1000)
    (hgap : VariableEnvelope.A (coordinate N p.2)+2*buffer≤W)
    (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ))
    (tail : List ℕ)
    (htail : ∀ q∈tail, 0<q ∧ (q:ℝ)≤(N:ℝ)^cutoff)
    (hgates : IntegerSquareGates N (theta buffer-2*delta buffer) 1
      ([p.2,p.1]++tail)) : ArithmeticLicence N buffer A p tail := by
  let B := (N:ℝ)^(2*theta buffer-1)
  let C := (N:ℝ)^(1-theta buffer-2*delta buffer)/A
  let D := (N:ℝ)^(theta buffer-2*delta buffer)
  let out := completed N buffer A p tail
  have hNpos : 0<(N:ℝ) := zero_lt_one.trans hN
  have hApos : 0<A := zero_lt_one.trans_le hA
  obtain ⟨_,_,_,hinit,hpositive,hseed⟩ :=
    root_initialization hN p hp1 hp2 hd hb hbhi hgap hA hAupper
  have hfull : PrefixSquareBound (fun n : ℕ => (n:ℝ)) D ([p.2,p.1]++tail) := by
    intro i hi
    have hh := integerSquareGates_at ([p.2,p.1]++tail) hgates i hi
    simpa only [Nat.one_mul,actualNatList_cast_prod] using hh
  have hslots : ∀ q∈tail, (0:ℝ)<q ∧ (q:ℝ)≤(N:ℝ)^cutoff := by
    intro q hq
    exact ⟨by exact_mod_cast (htail q hq).1,(htail q hq).2⟩
  obtain ⟨htrace,hprod,hcases⟩ := complete_correct (fun n : ℕ => (n:ℝ))
    (U := (N:ℝ)^cutoff) hApos hinit hpositive hslots hseed hfull
  have hpos := trace_positive (fun n : ℕ => (n:ℝ)) htrace hpositive
    (fun q hq => (hslots q hq).1)
  have hnat : out.left.prod*out.middle.prod*out.right.prod=(p.2*p.1)*tail.prod := by
    have hh : ((out.left.prod*out.middle.prod*out.right.prod:ℕ):ℝ)=
        (((p.2*p.1)*tail.prod:ℕ):ℝ) := by
      simpa [out,completed,total,wp,actualNatList_cast_prod,List.prod_append,
        Nat.cast_mul,mul_assoc] using hprod
    exact_mod_cast hh
  have hnatpos : 0<out.left.prod ∧ 0<out.middle.prod ∧ 0<out.right.prod := by
    simpa only [Positive,wp,actualNatList_cast_prod,Nat.cast_pos] using hpos
  have ha : (0:ℝ)<out.left.prod := by exact_mod_cast hnatpos.1
  have hbmid : (0:ℝ)<out.middle.prod := by exact_mod_cast hnatpos.2.1
  have hc : (0:ℝ)<out.right.prod := by exact_mod_cast hnatpos.2.2
  have hex := root_W_exponents hd hb hbhi hgap (show (0:ℝ)≤buffer from hb.le)
  change Part3.ActualWThreeCapacityRun.Trace (initialPair A p) tail out ∧ _
  refine ⟨htrace,hnat,hnatpos,?_⟩
  rcases hcases with hbounded | ⟨hlo,hhi,hleft,hright⟩
  · have hleft' : (out.left.prod:ℝ)≤A := by
      simpa only [wp,actualNatList_cast_prod] using hbounded.1
    have hmid' : (out.middle.prod:ℝ)≤B := by
      simpa only [wp,actualNatList_cast_prod] using hbounded.2.1
    have hright' : (out.right.prod:ℝ)≤C := by
      simpa only [wp,actualNatList_cast_prod] using hbounded.2.2
    exact ⟨hleft',P5Z.U1011OriginalW16FactorMonomials.W_success_monomials
      hN hApos ha hbmid hc hex.2.1 hleft' hmid' hright'⟩
  · have hleft' : (out.left.prod:ℝ)≤A := by
      simpa only [wp,actualNatList_cast_prod] using hleft
    have hlo' : B≤(out.middle.prod:ℝ) := by
      simpa only [wp,actualNatList_cast_prod] using hlo.le
    have hcritical : (out.middle.prod:ℝ)≤(N:ℝ)^(actualSelectedSubproductUpper 1 (theta buffer)) := by
      have hcrit : 2*theta buffer-1+cutoff≤actualSelectedSubproductUpper 1 (theta buffer) := by
        have hh := hex.2.2.2.2.2.1
        norm_num at hh
        linarith
      have hBU : B*(N:ℝ)^cutoff=(N:ℝ)^(2*theta buffer-1+cutoff) :=
        (Real.rpow_add hNpos _ _).symm
      have hh := hhi.trans (hBU.le.trans
        (Real.rpow_le_rpow_of_exponent_le hN.le hcrit))
      simpa only [wp,actualNatList_cast_prod] using hh
    have hcap : A*(out.middle.prod:ℝ)*(out.right.prod:ℝ)≤D := by
      have hh : (out.right.prod:ℝ)≤D/(A*(out.middle.prod:ℝ)) := by
        simpa only [wp,actualNatList_cast_prod] using hright
      have hh' := (le_div_iff₀ (mul_pos hApos hbmid)).mp hh
      nlinarith only [hh']
    exact ⟨hleft',by simpa only [mul_one] using
      selectedPair_monomials (α := (1:ℝ)) hN hApos ha hbmid hc hcap hlo' hcritical hleft'⟩

/-- Literal original U5 caller. All beta/cutoff and source/gate inputs
    are produced from actual pairSupport, actual nonzero rho and its
    primitive allocation. The remaining implication is a transparent
    historical branch: every actually read decision inherits the root.
    It is not an assumption of a final cap, support or arithmetic licence. -/
theorem native_U5_inherited_W (R : PairRange) (mesh : ℕ) (floor buffer : ℚ)
    (hb : 0<buffer) (hbhi : buffer≤1/1000)
    {N : ℕ} (hN : 2≤N) {p : ℕ×ℕ}
    (hp : p∈P5OriginalU5CausalFinite.pairSupport N)
    (hW : rootWChosen false (coordinate N p.1) (coordinate N p.2)=true)
    (hgap : VariableEnvelope.A (coordinate N p.2)+2*(buffer:ℝ)≤W)
    {epsilon : ℝ} (heps : 0<epsilon) (heps8 : epsilon<1/8)
    (halloc : P5OriginalU5CausalFinite.attachmentNu*epsilon≤(buffer:ℝ))
    {k : ℕ}
    (hk : P5OriginalU5CausalFinite.rho N epsilon
      (pairPolicy (warmPlan R mesh (2*buffer) floor (rootSeed false buffer N p))
        R.epsilon ceiling (rootSeed false buffer N p) N p) k≠0) :
    let seed := rootSeed false buffer N p
    let P := warmPlan R mesh (2*buffer) floor seed
    let policy := pairPolicy P R.epsilon ceiling seed N p
    let enum := Nat.ceil (P5OriginalU5CausalFinite.cutoff N)
    let w := P5OriginalU5CausalFinite.smallCutoff N epsilon
    let z := P5OriginalU5CausalFinite.cutoff N
    ∃ s∈actualSmallRosserSupport N enum w,
      ∃ r∈fixedEvenRoughSupport policy N enum w z,
        ∃ chosen : List ℕ, chosen <+ roughPrimeUniverse N enum w z ∧
          chosen.prod=r ∧ k=s*r ∧
          (P2LowerCapPlanIntegerRetention.run P R.epsilon ceiling
            (pairRoot N p seed) (chosen.map (coordinate N))).accepted=true ∧
          (Inherits P R.epsilon ceiling (pairRoot N p seed) (chosen.map (coordinate N)) →
            let tail := chosen++s.primeFactorsList.reverse
            let whole := appendUnselected (wTagged (p.2::p.1::chosen)) s.primeFactorsList.reverse
            (SourceForm.wSlot 2).affine.eval (sourcePoint (coordinate N p.1) (coordinate N p.2))=
              rootLevel false N p ∧
            (SourceForm.wSlot 2).supportMask=∅ ∧ selectedPrimes whole=[] ∧
            tail.prod=k ∧
            (whole.map Prod.fst).prod=(p.2*p.1)*k ∧
            IntegerSquareGates N (theta buffer-2*delta buffer) 1 (whole.map Prod.fst) ∧
            IntegerSquareGates N (theta buffer-2*delta buffer)
              (selectedPrimes whole).prod (remainingPrimes whole) ∧
            ∀ A : ℝ, 1≤A → A≤(N:ℝ)^(1/3:ℝ) → ArithmeticLicence N buffer A p tail) := by
  have hn : 1<(N:ℝ) := by exact_mod_cast (show 1<N by omega)
  have hbR : 0<(buffer:ℝ) := by exact_mod_cast hb
  have hbhiR : (buffer:ℝ)≤1/1000 := by exact_mod_cast hbhi
  have hcoord : P5OriginalU5CausalFinite.coordinates N p=pairPoint N p := by
    funext i
    fin_cases i <;> rfl
  have hd : pairPoint N p∈Part5OriginalUpsilon5CausalDictionary.triangle := by
    rw [←hcoord]
    exact P5OriginalU5CausalFinite.coordinates_mem_triangle hN hp
  obtain ⟨hcarrier,_⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp1',hp2'⟩ := Finset.mem_product.mp hcarrier
  have hp1 := (mem_chenAdditivePrimeCarrier.mp hp1').2.1
  have hp2 := (mem_chenAdditivePrimeCarrier.mp hp2').2.1
  let seed := rootSeed false buffer N p
  let P := warmPlan R mesh (2*buffer) floor seed
  let policy := pairPolicy P R.epsilon ceiling seed N p
  let enum := Nat.ceil (P5OriginalU5CausalFinite.cutoff N)
  let w := P5OriginalU5CausalFinite.smallCutoff N epsilon
  let z := P5OriginalU5CausalFinite.cutoff N
  let L := P5OriginalU5CausalFinite.smallLevel N epsilon
  have hhead : w^2≤L := by
    dsimp [w,L,P5OriginalU5CausalFinite.smallCutoff,P5OriginalU5CausalFinite.smallLevel]
    rw [←Real.rpow_mul_natCast (zero_lt_one.trans hn).le]
    apply Real.rpow_le_rpow_of_exponent_le hn.le
    norm_num [P5OriginalU5CausalFinite.attachmentNu]
    nlinarith
  have hL : L≤(N:ℝ)^(buffer:ℝ) := fifth_native_small_level_budget hn epsilon buffer halloc
  obtain ⟨s,hs,r,hr,chosen,hsub,hprod,hkprod,haccept,hselected,hwholeprod,hgates⟩ :=
    native_complete_once_buffered_W_squares R mesh buffer floor hb.le hbhi false
      (show 0≤2*(buffer:ℝ) by positivity) (le_refl _) N enum hn p hp1 hp2 hd w L hhead hL hk
  dsimp only
  refine ⟨s,hs,r,hr,chosen,hsub,hprod,hkprod,haccept,?_⟩
  intro hhistory
  have hlevel := inherited_original_W_level P R.epsilon ceiling false buffer N p
    (chosen.map (coordinate N)) hW hhistory
  have hcaple : (P2LowerCapPlanIntegerRetention.run P R.epsilon ceiling
      (pairRoot N p seed) (chosen.map (coordinate N))).cap+(buffer:ℝ)≤
        theta buffer-2*delta buffer := hlevel.le
  obtain ⟨hmask,hfull,hcomp⟩ := hgates (theta buffer-2*delta buffer) hcaple 2
  have htailprod : (chosen++s.primeFactorsList.reverse).prod=k := by
    have hsf := actualSmallRosserSupport_squarefree N enum w hs
    rw [List.prod_append,List.prod_reverse,Nat.prod_primeFactorsList hsf.ne_zero,hprod,hkprod]
    exact Nat.mul_comm _ _
  refine ⟨(source_form _ _).1.trans (chosen_original_root false N p hW).symm,
    hmask,hselected,htailprod,hwholeprod,hfull,hcomp,?_⟩
  intro A hA hAupper
  apply complete_original_root_word hn p hp1 hp2 hd hbR hbhiR hgap hA hAupper
    (chosen++s.primeFactorsList.reverse)
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · have hprime := mem_roughPrimeUniverse_prime (hsub.subset hq)
      exact ⟨hprime.pos,(mem_roughPrimeUniverse_upper (hsub.subset hq)).le⟩
    · have hsmall := actualSmallRosserSupport_smallPrimeSupportedAt N enum w hs
      have hprime := Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp hq)
      have hqw : (q:ℝ)<w := hsmall.2 q (Nat.mem_primeFactors.mpr
        ⟨hprime,Nat.dvd_of_mem_primeFactorsList (List.mem_reverse.mp hq),hsmall.1⟩)
      have hwz := (P5OriginalU5CausalFinite.attachment_gates hN heps heps8).2.2
      exact ⟨hprime.pos,hqw.le.trans hwz⟩
  · simpa only [appendUnselected_values,(w_empty_mask_words 2 (p.2::p.1::chosen)).2.2.2,
      List.cons_append,List.nil_append] using hfull

end
end ImbalancedChen.P2OriginalNativeU5InheritedWLicence
