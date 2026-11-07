import ImbalancedChen.P2OriginalNativeU5InheritedWLicence

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original W(z)=153/256-3z/8 source with its actual retained ceiling.
Primitive first-two-slot geometry implies initialization, BOTH critical
upper bounds, and the deterministic success/first-overflow monomials.
The physical level remains W(z)-2b; only support uses W(z)-b.
-/
namespace ImbalancedChen.P2OriginalFreshWArithmetic
noncomputable section
open scoped Classical
open P2LowerCapPlanIntegerRetention P2OriginalSelectedIntegerPrefixSquares
open Part3.ActualWThreeCapacityRun Part3.ActualWResidualCompletion
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

def value (z : ℝ) : ℝ := 153/256-3*z/8
def physical (z b : ℝ) : ℝ := value z-2*b
def auxiliary (z b : ℝ) : ℝ := value z-b
def parameter (z b : ℝ) : ℝ := value z-b/2
def reserve (b : ℝ) : ℝ := b/4

/-- Original enhanced-pair endpoint restrictions and a literal W/tent
gap. These are geometry, not a factorization or final-gate hypothesis. -/
def Geometry (t u z b : ℝ) : Prop :=
  0<b ∧ b≤1/1000 ∧ 0≤z ∧ z≤417/5000 ∧
    t≤25/128 ∧ u≤19/125 ∧ (1+t)/2+2*b≤value z

/-- The two other ORIGINAL wInner minima and its psi gate are discharged.
Thus this is a genuine original eight-branch W candidate, not merely the
affine expression B with its historical gate silently removed. -/
theorem original_W_identity {t u z b : ℝ} (h : Geometry t u z b) :
    VariableEnvelope.w t u z=VariableEnvelope.B z ∧
      value z≤VariableEnvelope.original t u z := by
  rcases h with ⟨hb,hbhi,hz,hzhi,ht,hu,hgap⟩
  have hv : value z=VariableEnvelope.B z := by
    dsimp [value,VariableEnvelope.B,VariableEnvelope.cap]; ring
  have hfirst : VariableEnvelope.B z≤(66-34*z)/107 := by
    dsimp [VariableEnvelope.B,VariableEnvelope.cap]; linarith
  have hsecond : VariableEnvelope.B z≤1-2*u := by
    dsimp [VariableEnvelope.B,VariableEnvelope.cap]; linarith
  have hgate : VariableEnvelope.A t≤VariableEnvelope.B z := by
    rw [←hv]
    dsimp [VariableEnvelope.A]
    linarith
  have hw : VariableEnvelope.w t u z=VariableEnvelope.B z := by
    rw [VariableEnvelope.w,VariableEnvelope.wInner,min_eq_left hsecond,
      min_eq_right hfirst,VariableEnvelope.psi,if_pos hgate]
  refine ⟨hw,?_⟩
  rw [hv,←hw]
  unfold VariableEnvelope.original
  apply le_max_of_le_right
  apply le_max_of_le_right
  apply le_max_of_le_right
  apply le_max_of_le_right
  exact le_max_left _ _

/-- A full-dimensional original L5 source band really admits this W
rescue. This is symbolic interval algebra, not an evaluated finite witness
or an assertion that the complete adopted winner bank has been covered. -/
theorem original_U5_rescue_band {t u z b : ℝ}
    (ht : t∈Set.Icc (13/100:ℝ) (7/50:ℝ))
    (hu : u∈Set.Icc (9/100:ℝ) (1/10:ℝ))
    (hz : z∈Set.Icc (0:ℝ) (1/25:ℝ)) (hb : 0<b) (hbhi : b≤1/1000) :
    (![u,t] : Fin 2 → ℝ)∈Part5OriginalUpsilon5CausalDictionary.triangle ∧
      Geometry t u z b ∧
      Part5OriginalUpsilon5CausalDictionary.level u t-2*b<physical z b := by
  have hroot : Part5OriginalUpsilon5CausalDictionary.level u t≤(57/100:ℝ) := by
    unfold Part5OriginalUpsilon5CausalDictionary.level
    apply max_le
    · rw [VariableEnvelope.v_eq_min]
      exact (min_le_left _ _).trans (by dsimp [VariableEnvelope.A]; linarith [ht.2])
    · apply max_le
      · rw [VariableEnvelope.v_eq_min]
        exact (min_le_right _ _).trans (by dsimp [VariableEnvelope.C]; linarith [ht.1,hu.1])
      · norm_num [VariableEnvelope.B,VariableEnvelope.cap,Part5OriginalUpsilon5CausalDictionary.a]
  refine ⟨?_,?_,?_⟩
  · apply Part5OriginalUpsilon5CausalDictionary.mem_triangle.mpr
    norm_num [Part5OriginalUpsilon5CausalDictionary.a,Part5OriginalUpsilon5CausalDictionary.h]
    exact ⟨by linarith [hu.1],by linarith [hu.2,ht.1],by linarith [ht.2]⟩
  · unfold Geometry value
    exact ⟨hb,hbhi,hz.1,by linarith [hz.2],by linarith [ht.2],
      by linarith [hu.2],by linarith [ht.2,hz.2]⟩
  · dsimp [physical,value]
    linarith [hz.2]

theorem exponents {t u z b : ℝ} (h : Geometry t u z b) :
    (1/2:ℝ)<parameter z b ∧ parameter z b≤153/256 ∧
    t≤2*parameter z b-1 ∧ 2*u≤1-parameter z b-2*reserve b ∧
    (1/3:ℝ)≤1-parameter z b-2*reserve b ∧
    z+(2*parameter z b-1)≤actualSelectedSubproductUpper 1 (parameter z b) ∧
    parameter z b-2*reserve b=auxiliary z b ∧
    physical z b+b=auxiliary z b := by
  rcases h with ⟨hb,hbhi,hz,hzhi,ht,hu,hgap⟩
  dsimp [parameter,reserve,auxiliary,physical,value] at hgap ⊢
  refine ⟨by linarith,by linarith,by linarith,by linarith,by linarith,?_,by ring,by ring⟩
  unfold actualSelectedSubproductUpper
  apply le_min <;> linarith

/-- Every own prefix square, including the empty-W complement, is paid
at the actual DOUBLE-buffer physical cap. No selected-product surrogate. -/
theorem first_three_squares {t u z b : ℝ} (h : Geometry t u z b) :
    P2EnhancedLowerPhysicalNode.SquareGates (physical z b) 0 [t,u,z] := by
  rcases h with ⟨hb,hbhi,hz,hzhi,ht,hu,hgap⟩
  dsimp [physical,value] at hgap ⊢
  simp only [P2EnhancedLowerPhysicalNode.SquareGates,zero_add]
  exact ⟨by linarith,by linarith,by linarith,True.intro⟩

def initial (A : ℝ) (p : ℕ×ℕ) : Bins ℕ :=
  P2OriginalNativeU5InheritedWLicence.initialPair A p

def factors (N : ℕ) (z b A : ℝ) (p : ℕ×ℕ) (tail : List ℕ) : Bins ℕ :=
  complete (fun q : ℕ => (q:ℝ)) A ((N:ℝ)^(2*parameter z b-1))
    ((N:ℝ)^(1-parameter z b-2*reserve b)/A) (initial A p) tail

def Licence (N : ℕ) (z b A : ℝ) (p : ℕ×ℕ) (tail : List ℕ) : Prop :=
  let out := factors N z b A p tail
  Part3.ActualWThreeCapacityRun.Trace (initial A p) tail out ∧
    out.left.prod*out.middle.prod*out.right.prod=(p.2*p.1)*tail.prod ∧
    (0<out.left.prod ∧ 0<out.middle.prod ∧ 0<out.right.prod) ∧
    (out.left.prod:ℝ)≤A ∧
    A^2*(out.middle.prod:ℝ)*(out.right.prod:ℝ)^2≤(N:ℝ)^(1-4*reserve b) ∧
    (N:ℝ)^(7/32:ℝ)*A*(out.left.prod:ℝ)*(out.middle.prod:ℝ)^5*(out.right.prod:ℝ)^2≤
      (N:ℝ)^(2-4*reserve b) ∧
    (A*(out.right.prod:ℝ)/(out.middle.prod:ℝ))^(7/16:ℝ)*A*(out.left.prod:ℝ)*
      (out.middle.prod:ℝ)^5*(out.right.prod:ℝ)^2≤(N:ℝ)^(2-39*reserve b/8)

theorem initialization {N : ℕ} (hN : 1<(N:ℝ)) (p : ℕ×ℕ)
    (hp1 : 0<p.1) (hp2 : 0<p.2) {z b A : ℝ}
    (h : Geometry (coordinate N p.2) (coordinate N p.1) z b)
    (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) :
    let B := (N:ℝ)^(2*parameter z b-1)
    let C := (N:ℝ)^(1-parameter z b-2*reserve b)/A
    Bounded (fun q : ℕ => (q:ℝ)) A B C (initial A p) ∧
      Positive (fun q : ℕ => (q:ℝ)) (initial A p) ∧
      total (fun q : ℕ => (q:ℝ)) (initial A p)=wp (fun q : ℕ => (q:ℝ)) [p.2,p.1] := by
  have he := exponents h
  have hn : 0<(N:ℝ) := zero_lt_one.trans hN
  have ha : 0<A := zero_lt_one.trans_le hA
  let C := (N:ℝ)^(1-parameter z b-2*reserve b)/A
  have hC : 1≤C := (le_div_iff₀ ha).mpr
    (by simpa using hAupper.trans (Real.rpow_le_rpow_of_exponent_le hN.le he.2.2.2.2.1))
  have hAC : A*C=(N:ℝ)^(1-parameter z b-2*reserve b) := by
    dsimp [C]; field_simp [ha.ne'] <;> ring
  have hsecond : (p.1:ℝ)^2≤A*C := by
    rw [hAC,←coordinate_power hN hp1,←Real.rpow_mul_natCast hn.le]
    apply Real.rpow_le_rpow_of_exponent_le hN.le
    simpa only [Nat.cast_ofNat,mul_comm] using he.2.2.2.1
  have hs : actualDwellSupport (A*C) [p.1] := by
    intro i hi
    have hi0 : i=0 := by simp only [List.length_singleton] at hi; omega
    subst i
    simpa only [List.take_zero,List.map_nil,List.prod_nil,List.getElem_cons_zero,one_mul] using hsecond
  obtain ⟨hprod,hleft,hright⟩ := actualTwoCapacityFactors_correct hA hC [p.1] hs
  have hfirst : (p.2:ℝ)≤(N:ℝ)^(2*parameter z b-1) := by
    rw [←coordinate_power hN hp2]
    exact Real.rpow_le_rpow_of_exponent_le hN.le he.2.2.1
  have hp : ∀ i : Fin 3, 0<(![p.2,p.1,1] : Fin 3 → ℕ) i := by
    intro i; fin_cases i
    · exact hp2
    · exact hp1
    · norm_num
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · simpa [initial,P2OriginalNativeU5InheritedWLicence.initialPair,wp,
      actualTwoCapacityFactors,actualNatList_cast_prod] using hleft
  · simpa [initial,P2OriginalNativeU5InheritedWLicence.initialPair,wp] using hfirst
  · simpa [initial,P2OriginalNativeU5InheritedWLicence.initialPair,wp,
      actualTwoCapacityFactors,actualNatList_cast_prod] using hright
  · simpa [initialBins,initial,P2OriginalNativeU5InheritedWLicence.initialPair] using
      initialBins_positive A ![p.2,p.1,1] hp
  · simpa [initialBins,initial,P2OriginalNativeU5InheritedWLicence.initialPair] using
      initialBins_product A ![p.2,p.1,1] hA hC hs

/-- Original full-prefix support and true W ceiling feed the existing
deterministic complete allocator, including genuine first-overflow repair. -/
theorem complete_word {N : ℕ} (hN : 1<(N:ℝ)) (p : ℕ×ℕ)
    (hp1 : 0<p.1) (hp2 : 0<p.2) {z b A : ℝ}
    (h : Geometry (coordinate N p.2) (coordinate N p.1) z b)
    (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) (tail : List ℕ)
    (htail : ∀ q∈tail, 0<q ∧ (q:ℝ)≤(N:ℝ)^z)
    (hgates : IntegerSquareGates N (auxiliary z b) 1 ([p.2,p.1]++tail)) :
    Licence N z b A p tail := by
  let B := (N:ℝ)^(2*parameter z b-1)
  let C := (N:ℝ)^(1-parameter z b-2*reserve b)/A
  let D := (N:ℝ)^(auxiliary z b)
  let out := factors N z b A p tail
  have hn : 0<(N:ℝ) := zero_lt_one.trans hN
  have ha : 0<A := zero_lt_one.trans_le hA
  have he := exponents h
  obtain ⟨hinit,hpos,hseed⟩ := initialization hN p hp1 hp2 h hA hAupper
  have hfull : PrefixSquareBound (fun q : ℕ => (q:ℝ)) D ([p.2,p.1]++tail) := by
    intro i hi
    simpa only [Nat.one_mul,actualNatList_cast_prod] using
      integerSquareGates_at ([p.2,p.1]++tail) hgates i hi
  have hslots : ∀ q∈tail, (0:ℝ)<q ∧ (q:ℝ)≤(N:ℝ)^z := by
    intro q hq
    exact ⟨by exact_mod_cast (htail q hq).1,(htail q hq).2⟩
  obtain ⟨htrace,hprod,hcases⟩ := complete_correct (fun q : ℕ => (q:ℝ))
    (U := (N:ℝ)^z) ha hinit hpos hslots hseed hfull
  have hposout := trace_positive (fun q : ℕ => (q:ℝ)) htrace hpos (fun q hq => (hslots q hq).1)
  have hnat : out.left.prod*out.middle.prod*out.right.prod=(p.2*p.1)*tail.prod := by
    have hh : ((out.left.prod*out.middle.prod*out.right.prod:ℕ):ℝ)=
        (((p.2*p.1)*tail.prod:ℕ):ℝ) := by
      simpa [out,factors,total,wp,actualNatList_cast_prod,List.prod_append,Nat.cast_mul,mul_assoc] using hprod
    exact_mod_cast hh
  have hnp : 0<out.left.prod ∧ 0<out.middle.prod ∧ 0<out.right.prod := by
    simpa only [Positive,wp,actualNatList_cast_prod,Nat.cast_pos] using hposout
  have hl : (0:ℝ)<out.left.prod := by exact_mod_cast hnp.1
  have hm : (0:ℝ)<out.middle.prod := by exact_mod_cast hnp.2.1
  have hr : (0:ℝ)<out.right.prod := by exact_mod_cast hnp.2.2
  change Part3.ActualWThreeCapacityRun.Trace (initial A p) tail out ∧ _
  refine ⟨htrace,hnat,hnp,?_⟩
  rcases hcases with hs | ⟨hlo,hhi,hleft,hright⟩
  · have hlA : (out.left.prod:ℝ)≤A := by simpa only [wp,actualNatList_cast_prod] using hs.1
    have hmB : (out.middle.prod:ℝ)≤B := by simpa only [wp,actualNatList_cast_prod] using hs.2.1
    have hrC : (out.right.prod:ℝ)≤C := by simpa only [wp,actualNatList_cast_prod] using hs.2.2
    exact ⟨hlA,P5Z.U1011OriginalW16FactorMonomials.W_success_monomials
      hN ha hl hm hr he.2.1 hlA hmB hrC⟩
  · have hlA : (out.left.prod:ℝ)≤A := by simpa only [wp,actualNatList_cast_prod] using hleft
    have hmB : B≤(out.middle.prod:ℝ) := by simpa only [wp,actualNatList_cast_prod] using hlo.le
    have hmU : (out.middle.prod:ℝ)≤(N:ℝ)^(actualSelectedSubproductUpper 1 (parameter z b)) := by
      have hBU : B*(N:ℝ)^z=(N:ℝ)^(z+(2*parameter z b-1)) := by
        rw [Real.rpow_add hn]; exact mul_comm _ _
      have hh := hhi.trans (hBU.le.trans (Real.rpow_le_rpow_of_exponent_le hN.le he.2.2.2.2.2.1))
      simpa only [wp,actualNatList_cast_prod] using hh
    have hcap : A*(out.middle.prod:ℝ)*(out.right.prod:ℝ)≤(N:ℝ)^(parameter z b-2*reserve b) := by
      rw [he.2.2.2.2.2.2.1]
      have hh : (out.right.prod:ℝ)≤D/(A*(out.middle.prod:ℝ)) := by
        simpa only [wp,actualNatList_cast_prod] using hright
      have hh' := (le_div_iff₀ (mul_pos ha hm)).mp hh
      nlinarith only [hh']
    exact ⟨hlA,by simpa only [mul_one] using selectedPair_monomials
      (α := (1:ℝ)) hN ha hl hm hr hcap hmB hmU hlA⟩

end
end ImbalancedChen.P2OriginalFreshWArithmetic
