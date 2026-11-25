import ImbalancedChen.P5ZU1011OriginalW16NearCapSupport
import ImbalancedChen.P5ZU1011OriginalW16ResidueUniform

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The SAME original W16 box parameters drive the existing P3 completion
algorithm. Primitive residual well support is at the frozen box level,
and every residual rough prime is below its frozen cutoff. The natural
factors are selected before kappa, and all three original monomials hold
uniformly for 0<=kappa<=the FIXED rational delta. No pointwise midpoint is
substituted and no W16 policy distribution licence is assumed.
-/

namespace ImbalancedChen.P5Z.U1011OriginalW16NearCapFactors
noncomputable section
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalW16NearCapNative U1011OriginalW16NearCapSupport
open U1011OriginalW16NativeInitialization (firstThree)
open U1011OriginalW16AttachedWellSupport (specified)
open U1011OriginalW16FactorMonomials (W_success_monomials)
open U1011OriginalW16ResidueUniform (critical_upper_residue_loss W_success_second_residue)
open P5U1011JointOverlap
open Part3.ActualWThreeCapacityRun Part3.ActualWResidualCompletion
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

def completedBins (B : Box) (eta : ℚ) (N : ℕ) (t : Four) (A : ℝ) (tail : List ℕ) : Bins ℕ :=
  complete (fun n:ℕ => (n:ℝ)) A (middleCapacity B eta N) (rightCapacity B eta N A)
    (initialBins A (firstThree t)) (slots t 2::slots t 3::tail)
def completedFactors (B : Box) (eta : ℚ) (N : ℕ) (t : Four) (A : ℝ) (tail : List ℕ) : ℕ×ℕ×ℕ :=
  let out := completedBins B eta N t A tail
  (out.left.prod,out.middle.prod,out.right.prod)

/-- All completion hypotheses come from the fixed box and the two
primitive residual-vector inputs. The true success/overflow split is
retained, including a middle product below the critical lower endpoint
in the success case. -/
theorem fixed_complete_factors {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈U11Adaptive.source N E) (B : Box) (eta : ℚ) (heta : 0<eta) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) (hbox : coordinates N t∈B.region)
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) (tail : List ℕ)
    (hresidual : actualDwellSupport (D B eta N) tail)
    (hrough : ∀q∈tail,Nat.Prime q ∧ (q:ℝ)<Z B eta N) :
    let out := completedBins B eta N t A tail
    Trace (initialBins A (firstThree t)) (slots t 2::slots t 3::tail) out ∧
      out.left.prod*out.middle.prod*out.right.prod=fullPrefix t*tail.prod ∧
      (0<out.left.prod ∧ 0<out.middle.prod ∧ 0<out.right.prod) ∧
      (Bounded (fun n:ℕ => (n:ℝ)) A (middleCapacity B eta N) (rightCapacity B eta N A) out ∨
        (middleCapacity B eta N<wp (fun n:ℕ => (n:ℝ)) out.middle ∧
          wp (fun n:ℕ => (n:ℝ)) out.middle≤
            (N:ℝ)^(actualSelectedSubproductUpper 1 (nu B eta:ℝ)-(delta B eta:ℝ)) ∧
          wp (fun n:ℕ => (n:ℝ)) out.left≤A ∧
          wp (fun n:ℕ => (n:ℝ)) out.right≤runLevel B eta N/(A*wp (fun n:ℕ => (n:ℝ)) out.middle))) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hp : (0:ℝ)<N := zero_lt_one.trans hn
  have hj := originalU11_mem_joint hn.le ht
  obtain ⟨hB,hC,hcapacity,hseed,hinit⟩ :=
    fixed_initialization hN hj B eta heta hvalid hpositive htest hbox A hA hAupper
  let input := slots t 2::slots t 3::tail
  let initial := initialBins A (firstThree t)
  let U := (N:ℝ)^(actualSelectedSubproductUpper 1 (nu B eta:ℝ)-(2*(nu B eta:ℝ)-1)-(delta B eta:ℝ))
  have hpositive' : Positive (fun n:ℕ => (n:ℝ)) initial :=
    initialBins_positive A (firstThree t) (by
      intro i
      fin_cases i
      · simpa [firstThree] using slots_pos hj 0
      · simpa [firstThree] using slots_pos hj 1
      · simpa [firstThree] using slots_pos hj 2)
  have hlate := (native_W_critical hN hj B eta heta hvalid hpositive htest hbox).2.2.2
  have hZ := (native_legality hN ht B eta heta hvalid hpositive htest hbox).2.2.1
  have h32 : (slots t 3:ℝ)≤slots t 2 := by
    exact_mod_cast ((slots_strictAnti hj) (by norm_num : (2:Fin 4)<3)).le
  have hslots : ∀q∈input,(0:ℝ)<q ∧ (q:ℝ)≤U := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl|hq
    · exact ⟨by exact_mod_cast slots_pos hj 2,hlate⟩
    · rcases List.mem_cons.mp hq with rfl|hq
      · exact ⟨by exact_mod_cast slots_pos hj 3,h32.trans hlate⟩
      · obtain ⟨hqprime,hqsmall⟩ := hrough q hq
        have hZ' : Z B eta N≤(slots t 3:ℝ) := by simpa [slots] using hZ
        exact ⟨by exact_mod_cast hqprime.pos,hqsmall.le.trans (hZ'.trans (h32.trans hlate))⟩
  have hs : total (fun n:ℕ => (n:ℝ)) initial=wp (fun n:ℕ => (n:ℝ)) [slots t 0,slots t 1] := by
    simpa [wp,initial] using hseed
  have hfull : PrefixSquareBound (fun n:ℕ => (n:ℝ)) (runLevel B eta N)
      ([slots t 0,slots t 1]++input) := by
    simpa [specified,input] using attached_well_support hN hj B eta heta hvalid hpositive htest hbox tail hresidual
  obtain ⟨htrace,hprod,hcases⟩ := complete_correct (fun n:ℕ => (n:ℝ)) (U:=U)
    (zero_lt_one.trans_le hA) hinit hpositive' hslots hs hfull
  have hpos := trace_positive (fun n:ℕ => (n:ℝ)) htrace hpositive'
    (fun q hq => (hslots q hq).1)
  have hnat : (completedBins B eta N t A tail).left.prod*(completedBins B eta N t A tail).middle.prod*
      (completedBins B eta N t A tail).right.prod=fullPrefix t*tail.prod := by
    have hh : (((completedBins B eta N t A tail).left.prod*(completedBins B eta N t A tail).middle.prod*
        (completedBins B eta N t A tail).right.prod:ℕ):ℝ)=((fullPrefix t*tail.prod:ℕ):ℝ) := by
      simpa [completedBins,total,wp,actualNatList_cast_prod,input,initial,fullPrefix,
        Fin.prod_univ_succ,List.prod_append,Nat.cast_mul,mul_assoc] using hprod
    exact_mod_cast hh
  have hnatpos : 0<(completedBins B eta N t A tail).left.prod ∧
      0<(completedBins B eta N t A tail).middle.prod ∧ 0<(completedBins B eta N t A tail).right.prod := by
    simpa only [Positive,wp,actualNatList_cast_prod,Nat.cast_pos] using hpos
  refine ⟨htrace,hnat,hnatpos,?_⟩
  rcases hcases with hbounded|⟨hlo,hhi,hleft,hright⟩
  · exact Or.inl hbounded
  · refine Or.inr ⟨hlo,?_,hleft,hright⟩
    have hBU : middleCapacity B eta N*U=
        (N:ℝ)^(actualSelectedSubproductUpper 1 (nu B eta:ℝ)-(delta B eta:ℝ)) := by
      dsimp [middleCapacity,U]
      rw [←Real.rpow_add hp]
      congr 1
      ring
    exact hhi.trans_eq hBU

/-- One actual natural factorization works throughout the fixed kappa
interval, for EVERY original source tuple and primitive residual atom
of the box. All N-dependent parameters were frozen before the tuple. -/
theorem fixed_factors_uniform_residue {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t∈U11Adaptive.source N E) (B : Box) (eta : ℚ) (heta : 0<eta) (hvalid : B.Valid) (hpositive : 0<B.lo 3)
    (htest : wholeBoxEligibleTest wPolicy B=true) (hbox : coordinates N t∈B.region)
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) (tail : List ℕ)
    (hresidual : actualDwellSupport (D B eta N) tail)
    (hrough : ∀q∈tail,Nat.Prime q ∧ (q:ℝ)<Z B eta N) :
    let abc := completedFactors B eta N t A tail
    abc.1*abc.2.1*abc.2.2=fullPrefix t*tail.prod ∧
      0<abc.1 ∧ 0<abc.2.1 ∧ 0<abc.2.2 ∧ (abc.1:ℝ)≤A ∧
      ∀kappa:ℝ,0≤kappa → kappa≤(delta B eta:ℝ) →
        A^2*(abc.2.1:ℝ)*(abc.2.2:ℝ)^2≤(N:ℝ)^(1-4*(delta B eta:ℝ)) ∧
        (N:ℝ)^(7*(1+3*kappa)/32)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*(abc.2.2:ℝ)^2≤
          (N:ℝ)^(2-4*(delta B eta:ℝ)) ∧
        (A*(abc.2.2:ℝ)/(abc.2.1:ℝ))^(7/16:ℝ)*A*(abc.1:ℝ)*(abc.2.1:ℝ)^5*
          (abc.2.2:ℝ)^2≤(N:ℝ)^(2-39*(delta B eta:ℝ)/8) := by
  let out := completedBins B eta N t A tail
  obtain ⟨htrace,hprod,hpositive',hcases⟩ :=
    fixed_complete_factors hN ht B eta heta hvalid hpositive htest hbox A hA hAupper tail hresidual hrough
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hj := originalU11_mem_joint hn.le ht
  have hApos : 0<A := zero_lt_one.trans_le hA
  have ha : (0:ℝ)<out.left.prod := by exact_mod_cast hpositive'.1
  have hb : (0:ℝ)<out.middle.prod := by exact_mod_cast hpositive'.2.1
  have hc : (0:ℝ)<out.right.prod := by exact_mod_cast hpositive'.2.2
  have hdQ := (rational_parameters B eta heta hvalid hpositive htest).2.2.1
  have hd : (0:ℝ)<(delta B eta:ℝ) := by exact_mod_cast hdQ
  have hmargin : (nu B eta:ℝ)+64*(delta B eta:ℝ)≤153/256 := by
    have h := (whole_box_margins B eta heta htest hbox).2.2.1
    rw [U1011OriginalW16NativeInitialization.W_cap] at h
    linarith [U1011OriginalW16NativeInitialization.coordinate_pos hN hj 2]
  have hnu : (nu B eta:ℝ)≤153/256 := by linarith
  change out.left.prod*out.middle.prod*out.right.prod=fullPrefix t*tail.prod ∧
    0<out.left.prod ∧ 0<out.middle.prod ∧ 0<out.right.prod ∧ (out.left.prod:ℝ)≤A ∧ _
  refine ⟨hprod,hpositive'.1,hpositive'.2.1,hpositive'.2.2,?_⟩
  rcases hcases with hbounded|⟨hlower,hupper,hleft,hright⟩
  · have hleft : (out.left.prod:ℝ)≤A := by simpa only [wp,actualNatList_cast_prod] using hbounded.1
    have hmiddle : (out.middle.prod:ℝ)≤(N:ℝ)^(2*(nu B eta:ℝ)-1) := by
      simpa only [middleCapacity,wp,actualNatList_cast_prod] using hbounded.2.1
    have hright : (out.right.prod:ℝ)≤(N:ℝ)^(1-(nu B eta:ℝ)-2*(delta B eta:ℝ))/A := by
      simpa only [rightCapacity,wp,actualNatList_cast_prod] using hbounded.2.2
    have hbase := W_success_monomials hn hApos ha hb hc hnu hleft hmiddle hright
    refine ⟨hleft,?_⟩
    intro kappa hk0 hk
    exact ⟨hbase.1,W_success_second_residue hn hd.le hk hApos ha hb hc hmargin hleft hmiddle hright,hbase.2.2⟩
  · have hleft' : (out.left.prod:ℝ)≤A := by simpa only [wp,actualNatList_cast_prod] using hleft
    have hlower' : (N:ℝ)^(2*(nu B eta:ℝ)-1)≤(out.middle.prod:ℝ) := by
      simpa only [middleCapacity,wp,actualNatList_cast_prod] using hlower.le
    have hcap : A*(out.middle.prod:ℝ)*(out.right.prod:ℝ)≤(N:ℝ)^((nu B eta:ℝ)-2*(delta B eta:ℝ)) := by
      have hh : (out.right.prod:ℝ)≤(N:ℝ)^((nu B eta:ℝ)-2*(delta B eta:ℝ))/(A*(out.middle.prod:ℝ)) := by
        simpa only [runLevel,wp,actualNatList_cast_prod] using hright
      have h := (le_div_iff₀ (mul_pos hApos hb)).1 hh
      nlinarith only [h]
    refine ⟨hleft',?_⟩
    intro kappa hk0 hk
    have hupper' : (out.middle.prod:ℝ)≤(N:ℝ)^actualSelectedSubproductUpper (1+3*kappa) (nu B eta:ℝ) := by
      have hloss := critical_upper_residue_loss (nu B eta:ℝ) kappa hk0
      have he : actualSelectedSubproductUpper 1 (nu B eta:ℝ)-(delta B eta:ℝ)≤
          actualSelectedSubproductUpper (1+3*kappa) (nu B eta:ℝ) := by linarith
      have h := hupper.trans (Real.rpow_le_rpow_of_exponent_le hn.le he)
      simpa only [wp,actualNatList_cast_prod] using h
    exact selectedPair_monomials (α:=1+3*kappa) hn hApos ha hb hc hcap hlower' hupper' hleft'

end
end ImbalancedChen.P5Z.U1011OriginalW16NearCapFactors

