import ImbalancedChen.P4BOriginalHighRankMotherModes
import ImbalancedChen.P4BOriginalRankTwoChartScales
import ImbalancedChen.P4BArbitraryWidthUpperBlockGeometry
import ImbalancedChen.P5OriginalHBCompleteProductScale

/-! The selected HB coordinate and its entire complementary integer have
right-closed dyadic owners.  The same integer tuple meets both original
mother windows and the complete-product trim. -/
namespace ImbalancedChen.P4BOriginalHighRankMotherScale
noncomputable section
open Classical Filter
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block Owns owner owner_owns)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos owns_bounds)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle mem_rectangle owns_pos)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct)
open P5Z.ActualAllRankOccurrenceFourierBridge
open P5Z.ActualOccurrencePlateauWordBudget
open P5Z.GroupedOccurrenceLogShift
open P5Z.ActualEtaPsiOccurrenceBudget (eta eta_zero psi)
open P5Z.ExactOriginalSmoothDyadicPartition (R R_pos beforeHBCutoff)
open P5Z.ActualHBMediumBranchPartition (firstMedium firstMedium_some Medium)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P4BOriginalRankTwoChartScales (psi_window eventually_power)
open P4BUpperPairOrderedRowGeometry (pairOwner integerProfile)
open P4BOuterRampRoughness (baseline)
open P4BArbitraryWidthUpperPairProfile (legal_width_le_one)

def completeScale {t : ℕ} (bs : Fin t→Block) (v : Fin t→ℕ) (i : Fin t) : ℝ :=
  (lower (bs i):ℝ)*(lower (owner (completeProduct v / v i)):ℝ)

theorem tuple_scale {t : ℕ} (bs : Fin t→Block) (v : Fin t→ℕ) (i : Fin t)
    (hv : v∈rectangle bs) :
    completeScale bs v i≤(completeProduct v:ℝ) ∧ (completeProduct v:ℝ)≤4*completeScale bs v i := by
  have hown := (mem_rectangle bs v).mp hv
  have hy : 0<completeProduct v := Finset.prod_pos (fun j _ => owns_pos (hown j))
  have hdiv : v i∣completeProduct v := Finset.dvd_prod_of_mem v (Finset.mem_univ i)
  have hc := owner_owns (Nat.div_pos (Nat.le_of_dvd hy hdiv) (owns_pos (hown i)))
  have hp := Nat.mul_div_cancel' hdiv
  have hlow := Nat.mul_le_mul (owns_bounds (hown i)).1 (owns_bounds hc).1
  have hupper := Nat.mul_le_mul (owns_bounds (hown i)).2 (owns_bounds hc).2
  rw [hp] at hlow hupper
  have hupper' : completeProduct v≤4*(lower (bs i)*lower (owner (completeProduct v/v i))) := by
    calc
      _≤_ := hupper
      _=_ := by ring
  exact ⟨by unfold completeScale; exact_mod_cast hlow,by unfold completeScale; exact_mod_cast hupper'⟩

/-- No restriction is placed on the other integers of a live rectangle.
Support is read from a genuine nonzero source point on its full mother. -/
theorem live_geometry {u v N : ℕ} {b kap s kap0 : ℝ}
    (hN : 0<N) (hb : 0<b) (hk : 0<kap) (hs : 0<s) (hg : 2*s≤baseline b kap-19/96)
    (cj ck : ℕ) (bs : Fin (u+v)→Block) (n : Fin (u+v)→ℕ) (i : Fin (u+v))
    (hn : n∈rectangle bs) (hw : integerProfile (a:=u) (d:=v) b kap s N kap0 cj ck n≠0) :
    let x := completeScale bs n i
    let X := R cj * R ck
    (1/4:ℝ)*(N:ℝ)^(1-kap0)≤x ∧ x≤Real.exp 1*N ∧ X≤16*x ∧ x≤4*X := by
  let p : Fin 2→ℝ := fun j => (integerGroupProduct (pairOwner u v) n j:ℝ)
  have htotal : p 0*p 1=(completeProduct n:ℝ) := by
    have h := congrArg (fun t : ℕ => (t:ℝ)) (complete_product_grouped (pairOwner u v) n)
    simpa only [p,Fin.prod_univ_two,Nat.cast_prod,Nat.cast_mul,completeProduct] using h
  have hEta : eta ((∏ j,p j)/(N:ℝ)^(1-kap0))≠0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1).2
  have hp : (∏ j,psi (p j/(![R cj,R ck] : Fin 2→ℝ) j))≠0 := (mul_ne_zero_iff.mp hw).2
  have h0 : psi (p 0/R cj)≠0 := Finset.prod_ne_zero_iff.mp hp 0 (Finset.mem_univ _)
  have h1 : psi (p 1/R ck)≠0 := Finset.prod_ne_zero_iff.mp hp 1 (Finset.mem_univ _)
  have hden := Real.rpow_pos_of_pos (show (0:ℝ)<N by exact_mod_cast hN) (1-kap0)
  have htrim : (N:ℝ)^(1-kap0)<(completeProduct n:ℝ) := by
    by_contra! bad
    apply hEta
    apply eta_zero
    rw [Fin.prod_univ_two,htotal]
    exact (div_le_one hden).mpr bad
  have hG : 2*s≤baseline b kap-1*(19/96:ℝ) := by simpa only [one_mul] using hg
  have he := P4BArbitraryWidthUpperBlockGeometry.integerProfile_support hb
    (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96) hs hG
    (pairOwner u v) (![R cj,R ck]) kap0 hw
  have hwidth := legal_width_le_one hb hk (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<19/96) hG
  have htop := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hwidth) (Nat.cast_nonneg N)
  have w0 := psi_window (R_pos cj) h0
  have w1 := psi_window (R_pos ck) h1
  have hLo := mul_le_mul w0.1.le w1.1.le (by positivity : 0≤R ck/2) (by dsimp [p]; positivity)
  have hHi := mul_le_mul w0.2.le w1.2.le (by dsimp [p]; positivity) (by positivity : 0≤2*R cj)
  rw [htotal] at hLo hHi
  obtain ⟨hl,hh⟩ := tuple_scale bs n i hn
  exact ⟨by linarith,hl.trans (he.le.trans htop),by nlinarith only [hLo,hh],by nlinarith only [hHi,hl]⟩

/-- The original first-medium comparison picks a labelled occurrence before
its integer tuple or its whole-complement block is read. -/
theorem selected_window {t : ℕ} (bs : Fin t→Block) (i : Fin t) (cj ck : ℕ) (zeta : ℝ)
    (hp : firstMedium (originalMediumLow zeta [cj,ck]) (originalMediumHigh zeta [cj,ck])
      (List.ofFn bs)=some i.val) :
    (R cj*R ck)^(3*zeta)≤(lower (bs i):ℝ) ∧
      (lower (bs i):ℝ)≤(R cj*R ck)^(1/3+zeta/4:ℝ) := by
  obtain ⟨hi,hm,_⟩ := firstMedium_some hp
  simpa [Medium,originalMediumLow,originalMediumHigh,P5Z.ExactOriginalSmoothDyadicPartition.scales] using hm

end
end ImbalancedChen.P4BOriginalHighRankMotherScale
