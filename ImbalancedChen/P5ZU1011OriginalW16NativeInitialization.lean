import ImbalancedChen.P5ZU1011OriginalSixteenInteriorArithmetic
import ImbalancedChen.Part3ActualWThreeCapacityRun
import ImbalancedChen.P5ZU11LoweredCutoffFiniteRosser

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Actual original W16 arithmetic caller. The source is the genuine fourth
policy cap153/256-3*z/8, its A(x) gate and x<25/128, on the ORIGINAL
decreasing four-prime slots ![p4,p3,p2,p1]. W's empty selected product is
never used as a selected-subproduct critical factor.

The interior, positive buffer, reduced cutoff and all starting capacity
inequalities are constructed from the actual TypedEligible W point.
The existing original-order two/three-bin algorithms are then called on
the actual first two slots and original unread suffix p2,p1,tail.
There is no density, AP estimate, H248 correctness, completed W analytic
factorization or final count theorem among the hypotheses or conclusions.
-/

namespace ImbalancedChen.P5Z.U1011OriginalW16NativeInitialization
noncomputable section
open Set MeasureTheory
open Classical
open U11Integral U1011OriginalSixteenPolicyBank U1011OriginalSixteenArithmeticProducts
open U1011OriginalSixteenInteriorArithmetic
open P5U1011JointOverlap
open Part3.ActualWThreeCapacityRun
open scoped BigOperators

def theta (v : LogFour) : ℝ := interior wPolicy v
def buffer (v : LogFour) : ℝ := min (3/4096:ℝ)
  (min ((theta v-gate wPolicy v)/64) ((cap wPolicy v-theta v)/64))

theorem W_cap (v : LogFour) : cap wPolicy v=153/256-(3/8:ℝ)*v 2 :=
  (w_policy_dictionary v).1

theorem fullSquare_le_gate (v : LogFour) (j : Fin 4) : fullSquare j v≤gate wPolicy v := by
  apply Finset.le_max'
  apply Finset.mem_insert.mpr
  apply Or.inr
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩

theorem firstGate_le_gate (v : LogFour) : (1+v 0)/2≤gate wPolicy v := by
  apply Finset.le_max'
  apply Finset.mem_insert.mpr
  apply Or.inr
  apply Finset.mem_union_right
  simp only [wPolicy,show ¬(15:ℕ)<15 by omega,if_false,Finset.mem_singleton]

/-- One positive canonical buffer pays the actual lower and upper source
surpluses, with room for the original20delta residual-level loss. -/
theorem buffer_bounds (v : LogFour) (he : TypedEligible wPolicy v) :
    0<buffer v ∧ buffer v≤3/4096 ∧
      gate wPolicy v+64*buffer v≤theta v ∧ theta v+64*buffer v≤cap wPolicy v := by
  have hgc := gate_lt_cap wPolicy v he
  have hgi : gate wPolicy v<theta v := by dsimp [theta,interior]; linarith
  have hic : theta v<cap wPolicy v := by dsimp [theta,interior]; linarith
  have hb : 0<buffer v := by
    apply lt_min (by norm_num)
    exact lt_min (div_pos (sub_pos.mpr hgi) (by norm_num))
      (div_pos (sub_pos.mpr hic) (by norm_num))
  have hlo : buffer v≤(theta v-gate wPolicy v)/64 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hhi : buffer v≤(cap wPolicy v-theta v)/64 :=
    (min_le_right _ _).trans (min_le_right _ _)
  exact ⟨hb,min_le_left _ _,by linarith,by linarith⟩

theorem coordinate_pos {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (i : Fin 4) : 0<coordinates N t i := by
  have hp : (1:ℝ)<slots t i := by exact_mod_cast (slots_prime ht i).one_lt
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  exact div_pos (Real.log_pos hp) (Real.log_pos hn)

/-- Both ORIGINAL upper critical constraints are retained. The explicit
second one is exactly z<51/32-(8/3)*nu; it is not the whole min by itself. -/
theorem W_logarithmic_critical (v : LogFour) (he : TypedEligible wPolicy v)
    (hz : 0≤v 2) :
    (1/2:ℝ)<theta v ∧ theta v<(5/8:ℝ) ∧ v 0<(25/128:ℝ) ∧
      v 0≤2*theta v-1-buffer v ∧
      v 2<(51/32:ℝ)-(8/3:ℝ)*theta v ∧
      v 2+(2*theta v-1)+buffer v≤actualSelectedSubproductUpper 1 (theta v) := by
  have hi := interior_admissible wPolicy v he
  have hW : (1+v 0)/2<theta v ∧ v 0<(25/128:ℝ) := by
    simpa only [wPolicy,show ¬(15:ℕ)<15 by omega,if_false,theta] using hi.2.2.1
  have hb := buffer_bounds v he
  have hcap := hb.2.2.2
  rw [W_cap] at hcap
  have hfirst := firstGate_le_gate v
  have hB : 153/256-(3/8:ℝ)*v 2≤(66-34*v 2)/107 := by linarith
  refine ⟨hi.1,?_,hW.2,?_,?_,?_⟩
  · have hupper := hi.2.2.2
    change theta v<cap wPolicy v at hupper
    rw [W_cap] at hupper
    linarith
  · linarith [hb.2.2.1,hb.1]
  · linarith [hb.1]
  · unfold actualSelectedSubproductUpper
    apply le_min <;> linarith [hb.1]

/-- The first two specified primes satisfy the buffered small-square
hypothesis of the repaired W initialization. The3/256 source margin
comes from Lambda+2mu=253/256, before any arithmetic transfer. -/
theorem W_second_square_exponent (v : LogFour) (he : TypedEligible wPolicy v)
    (hz : 0≤v 2) (hyx : v 1≤v 0) :
    2*v 1≤1-theta v-2*buffer v := by
  have hw := W_logarithmic_critical v he hz
  have hb := buffer_bounds v he
  have hcap : theta v≤(153/256:ℝ) := by
    have hi := (interior_admissible wPolicy v he).2.2.2
    change theta v<cap wPolicy v at hi
    rw [W_cap] at hi
    linarith
  linarith [hw.2.2.1,hb.2.1]

/-- Actual W third-prime intervals, with the complete spectral7/32 min
and the manuscript's literal51/32 endpoint both displayed. -/
theorem actual_W_critical_intervals {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (he : TypedEligible wPolicy (coordinates N t)) :
    (slots t 0 : ℝ)≤(N:ℝ)^(2*theta (coordinates N t)-1-buffer (coordinates N t)) ∧
      (slots t 1 : ℝ)^2≤(N:ℝ)^(1-theta (coordinates N t)-2*buffer (coordinates N t)) ∧
      (slots t 2 : ℝ)<(N:ℝ)^((51/32:ℝ)-(8/3:ℝ)*theta (coordinates N t)) ∧
      (slots t 2 : ℝ)≤(N:ℝ)^(actualSelectedSubproductUpper 1 (theta (coordinates N t))-
        (2*theta (coordinates N t)-1)-buffer (coordinates N t)) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hp : (0:ℝ)<N := zero_lt_one.trans hn
  have hz := (coordinate_pos hN ht 2).le
  have hc := W_logarithmic_critical (coordinates N t) he hz
  have hyx : coordinates N t 1≤coordinates N t 0 :=
    (coordinates_strictAnti hN ht).antitone (by norm_num : (0:Fin 4)≤1)
  have hs := W_second_square_exponent (coordinates N t) he hz hyx
  have hr := actualPrimeTupleLog_rpow hN (slots t) (slots_pos ht)
  refine ⟨?_,?_,?_,?_⟩
  · rw [←hr 0]
    exact Real.rpow_le_rpow_of_exponent_le hn.le hc.2.2.2.1
  · rw [←hr 1,←Real.rpow_mul_natCast hp.le]
    apply Real.rpow_le_rpow_of_exponent_le hn.le
    simpa only [Nat.cast_ofNat] using hs
  · rw [←hr 2]
    exact Real.rpow_lt_rpow_of_exponent_lt hn hc.2.2.2.2.1
  · rw [←hr 2]
    exact Real.rpow_le_rpow_of_exponent_le hn.le (by linarith [hc.2.2.2.2.2])

def firstThree (t : Four) : Fin 3 → ℕ := ![slots t 0,slots t 1,slots t 2]

/-- This uses the ORIGINAL first two slots only. The unread fourth
specified prime is kept in the suffix before every residual rough slot. -/
theorem actual_W_first_two_and_run {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (he : TypedEligible wPolicy (coordinates N t))
    (A : ℝ) (hA : 1≤A) (hAupper : A≤(N:ℝ)^(1/3:ℝ)) (tail : List ℕ) :
    let v := coordinates N t
    let B := (N:ℝ)^(2*theta v-1)
    let C := (N:ℝ)^(1-theta v-2*buffer v)/A
    let initial := initialBins A (firstThree t)
    let suffix := slots t 2 :: slots t 3 :: tail
    1≤B ∧ 1≤C ∧ A*B*C=(N:ℝ)^(theta v-2*buffer v) ∧
      total (fun n : ℕ => (n:ℝ)) initial=(slots t 0:ℝ)*slots t 1 ∧
      RunSpec (fun n : ℕ => (n:ℝ)) A B C initial suffix
        (run (fun n : ℕ => (n:ℝ)) A B C initial suffix) := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hp : (0:ℝ)<N := zero_lt_one.trans hn
  let v := coordinates N t
  let B := (N:ℝ)^(2*theta v-1)
  let P := (N:ℝ)^(1-theta v-2*buffer v)
  let C := P/A
  have hApos : 0<A := zero_lt_one.trans_le hA
  have hw := W_logarithmic_critical v he (coordinate_pos hN ht 2).le
  have hb := buffer_bounds v he
  have htheta : theta v≤(153/256:ℝ) := by
    have h := (interior_admissible wPolicy v he).2.2.2
    change theta v<cap wPolicy v at h
    rw [W_cap] at h
    linarith [coordinate_pos hN ht 2]
  have hP : A≤P := hAupper.trans
    (Real.rpow_le_rpow_of_exponent_le hn.le (by dsimp [P]; linarith [hb.2.1]))
  have hC : 1≤C := (le_div_iff₀ hApos).2 (by simpa using hP)
  have hAC : A*C=P := by dsimp [C]; field_simp [hApos.ne'] <;> ring
  have hcrit := actual_W_critical_intervals hN ht he
  have hsupport : actualDwellSupport (A*C) [slots t 1] := by
    intro i hi
    have hi0 : i=0 := by simp only [List.length_singleton] at hi; omega
    subst i
    simpa only [hAC,List.take_zero,List.map_nil,List.prod_nil,List.getElem_cons_zero,one_mul,P]
      using hcrit.2.1
  obtain ⟨hprod,hleft,hright⟩ := actualTwoCapacityFactors_correct hA hC [slots t 1] hsupport
  have hB : 1≤B := by
    exact Real.one_le_rpow hn.le (by dsimp [B]; linarith [hw.1])
  have hfirst : (slots t 0:ℝ)≤B := hcrit.1.trans
    (Real.rpow_le_rpow_of_exponent_le hn.le (by dsimp [B]; linarith [hb.1]))
  have hinit : Bounded (fun n : ℕ => (n:ℝ)) A B C (initialBins A (firstThree t)) := by
    refine ⟨?_,?_,?_⟩
    · simpa [initialBins,firstThree,wp,actualTwoCapacityFactors,actualNatList_cast_prod] using hleft
    · simpa [initialBins,firstThree,wp] using hfirst
    · simpa [initialBins,firstThree,wp,actualTwoCapacityFactors,actualNatList_cast_prod] using hright
  refine ⟨hB,hC,?_,?_,run_spec _ _ _ _ _ _ hinit⟩
  · change A*B*C=(N:ℝ)^(theta v-2*buffer v)
    calc
      A*B*C=B*P := by rw [←hAC]; ring
      _ = _ := by dsimp [B,P]; rw [←Real.rpow_add hp]; congr 1; ring
  · have hh := initialBins_product A (firstThree t) hA hC
      (by simpa [firstThree] using hsupport)
    simpa [wp,firstThree] using hh

def cutoffMargin (v : LogFour) : ℝ := min (v 3/2) (buffer v)
def residualExponent (v : LogFour) : ℝ := theta v-U11SelectedLargest.prefixSum v-20*buffer v
def cutoffExponent (v : LogFour) : ℝ :=
  U11SelectedLargest.reducedCutoff v v (theta v) (buffer v) (cutoffMargin v) (buffer v)

/-- The canonical W point supplies the ORIGINAL20delta loss, xi and rho
conditions. None of these legality conditions is an assumed row bound. -/
theorem W_cutoff_margins (v : LogFour) (he : TypedEligible wPolicy v) (hw : 0<v 3) :
    0<cutoffMargin v ∧ 0<v 3-cutoffMargin v ∧
      20*buffer v<theta v-U11SelectedLargest.prefixSum v ∧ 0<buffer v := by
  have hb := buffer_bounds v he
  have hx : 0<cutoffMargin v := lt_min (half_pos hw) hb.1
  have hxi : cutoffMargin v≤v 3/2 := min_le_left _ _
  have hg := fullSquare_le_gate v 3
  rw [fullSquare_last] at hg
  exact ⟨hx,by linarith,by linarith [hb.2.2.1],hb.1⟩

/-- The actual reduced W cutoff is below p1, and its actual residual
Rosser level is >1 and >=Z. The original p2 sieve is not substituted. -/
theorem native_W_cutoff_legal {N : ℕ} (hN : 1<N) {E : ℕ×ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (he : TypedEligible wPolicy (coordinates N t)) :
    let v := coordinates N t
    1<(N:ℝ)^residualExponent v ∧
      (N:ℝ)^cutoffExponent v≤(slots t 3:ℝ) ∧
      (N:ℝ)^cutoffExponent v≤(N:ℝ)^residualExponent v := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  let v := coordinates N t
  have hm := W_cutoff_margins v he (coordinate_pos hN ht 3)
  have hr := U11LoweredRosser.reduced_physical_level_legal N hn v v
    (theta v) (buffer v) (cutoffMargin v) (buffer v) hm.2.1 hm.2.2.1 hm.2.2.2
  have hfirst : (N:ℝ)^v 3≤(t.1.1:ℝ) := by
    have hh := actualPrimeTupleLog_rpow hN (slots t) (slots_pos ht) 3
    simpa [v,coordinates,slots] using hh.le
  have hz := U11LoweredRosser.reduced_physical_cutoff_le_first N hn.le v v
    (theta v) (buffer v) (cutoffMargin v) (buffer v) hm.1.le t hfirst
  exact ⟨hr.1,by simpa [cutoffExponent,slots] using hz,hr.2⟩

/-- Original finite U11 W row at its actually CONSTRUCTED native
interior/cutoff/level. All physical Rosser hypotheses are proved above.
The signed AP and centre terms remain the original explicit arithmetic
terms, rather than being asserted small or replaced by a density target. -/
theorem native_W_original_row_upper {N : ℕ} (hN : 1<N) (E : ℕ×ℕ → Prop) (t : Four)
    (ht : t ∈ U11Adaptive.source N E) (he : TypedEligible wPolicy (coordinates N t)) :
    let v := coordinates N t
    let Z := (N:ℝ)^cutoffExponent v
    let R := (N:ℝ)^residualExponent v
    U11Adaptive.weight N t≤U11LoweredRosser.mainTerm N t Z R+
      U11LoweredRosser.signedAP N t Z R-U11LoweredRosser.signedCentre N t Z R := by
  have hn : (1:ℝ)<N := by exact_mod_cast hN
  have hj := originalU11_mem_joint hn.le ht
  have hl := native_W_cutoff_legal hN hj he
  exact U11LoweredRosser.row_upper hn.le ht _ _
    (by simpa [slots] using hl.2.1) hl.1 hl.2.2

end
end ImbalancedChen.P5Z.U1011OriginalW16NativeInitialization
