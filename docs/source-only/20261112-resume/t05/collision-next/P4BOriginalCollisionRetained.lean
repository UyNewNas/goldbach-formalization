import ImbalancedChen.P4BOriginalCollisionModes

/-! Integration on the true retained band on each fixed complement, with
zero on a dead fibre for both sides. Restoration uses the actual mother
mass and the single original complement bank. -/
namespace ImbalancedChen.P4BOriginalCollisionRetained
noncomputable section
open Classical Filter MeasureTheory
open scoped BigOperators
open ImbalancedChen.PrimeProducts
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionTensor (products free)
open P4BOriginalCollisionModes (live_products exists_mode_cost)
open P4BOriginalHighRankPostModulusRow (retained truncated truncated_eq_band H)
open P4BOriginalHighRankPostModulusFibres (split first)
open P4BOriginalHighRankMotherMass (rowMass exists_row_mass)
open P4BOriginalHighRankComplementBlocks (cap fibre complement_count)
open P4BOriginalHighRankPostModulusCount (band retainedMother)
open P4BUpperPairOrderedRowModes (amplitude amplitude_integrable amplitude_mode_integrable)
open P4BUpperPairOrderedRowGeometry (integerProfile blockScales rowRoles)
open P5Z.ActualRoughHeathBrownWords (Role)
open P5Z.HBRightClosedDyadicRoles (Block bank)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct hbSlots)
open P5Z.ActualAllRankOccurrenceFourierBridge (occurrenceMode)
open P5Z.AllRankCauchyCubeTail (outsideCube)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle blockVector)
open P5Z.ExactOriginalSmoothDyadicPartition (chartBank beforeHBCutoff)
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCutoff)
open P5Z.CompleteProductTailDivisorBudgets (logScale logScale_one_le)
open P4BArbitraryWidthUpperBlockGeometry (countingScale countingScale_one_le)
open P4BOriginalHighRankScheduledCount (outerWidth resolution eventually_width)
open P4BOriginalUpperFourierTailPaid (groupEval groupEval_sub_le groupScalarMass sourceScalarMass
  sourceScalarMass_le dyadicConstant dyadicConstant_pos)
open P4AHeldTaggedCompilerSupport (J0)
open P4BOuterRampRoughness (baseline)

private theorem integrate {u v N : ℕ} {b kap s : ℝ} (hb : 0<b) (hs : 0<s)
    (hg : 2*s≤baseline b kap-19/96) (kap0 : ℝ) (cj ck : ℕ) (bs : Fin (u+v)→Block)
    (I : Finset (Fin (u+v)→ℕ)) (Z : ℝ) (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role)
    (Q1 Q2 : Finset ℕ) (c1 c2 : ℕ→ℝ) (A : ℕ) {E : ℝ} (hE : 0≤E)
    (hmode : ∀ xi : Fin (u+v)→ℝ,
      let w := fun y => hbSlots Z ys rs y*occurrenceMode (blockScales bs) y xi
      ‖MellinInsertion20261028.exactDiscrepancy I Q1 (fun t => (c1 t:ℂ)) completeProduct N w-
        MellinInsertion20261028.exactDiscrepancy I Q2 (fun t => (c2 t:ℂ)) completeProduct N w‖≤E) :
    ‖truncated (u:=u) (v:=v) b kap s N kap0 cj ck bs I Z ys rs Q1 c1 (H N A)-
      truncated (u:=u) (v:=v) b kap s N kap0 cj ck bs I Z ys rs Q2 c2 (H N A)‖≤
      rowMass (u:=u) (v:=v) b kap s N kap0 cj ck bs*E := by
  let M := amplitude (a:=u) (d:=v) b kap s N kap0 cj ck bs
  let F := fun Q (c : ℕ→ℝ) (xi : Fin (u+v)→ℝ) => MellinInsertion20261028.exactDiscrepancy I Q
    (fun t => (c t:ℂ)) completeProduct N (fun y => hbSlots Z ys rs y*occurrenceMode (blockScales bs) y xi)
  have hg' : 2*s≤baseline b kap-1*(19/96:ℝ) := by simpa only [one_mul] using hg
  have hM : Integrable M := amplitude_integrable hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96)
    hs hg' N kap0 cj ck bs
  have hi (Q c) : Integrable (fun xi => M xi*F Q c xi) := by
    let C := fun y => ∑ q∈Q,(c q:ℂ)*MellinInsertion20261028.residueKernel q N (completeProduct y)
    have terms (y : Fin (u+v)→ℕ) : Integrable (fun xi =>
        M xi*(hbSlots Z ys rs y*occurrenceMode (blockScales bs) y xi)) := by
      have hi' := (amplitude_mode_integrable hb (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<19/96)
        hs hg' N kap0 cj ck bs y).const_mul (hbSlots Z ys rs y)
      apply hi'.congr
      exact Eventually.of_forall (fun xi => by dsimp [M]; ring)
    have hh := MellinInsertion20261028.functional_integrable I C
      (fun xi y => M xi*(hbSlots Z ys rs y*occurrenceMode (blockScales bs) y xi)) (fun y _ => terms y)
    simpa only [MellinInsertion20261028.functional_mul] using hh
  let R := (outsideCube (u+v) (H N A))ᶜ
  rw [truncated_eq_band hb hs hg,truncated_eq_band hb hs hg]
  change ‖(∫ xi in R,M xi*F Q1 c1 xi)-(∫ xi in R,M xi*F Q2 c2 xi)‖≤_
  rw [←integral_sub (hi Q1 c1).integrableOn (hi Q2 c2).integrableOn]
  calc
    _≤∫ xi in R,‖M xi*F Q1 c1 xi-M xi*F Q2 c2 xi‖ := norm_integral_le_integral_norm _
    _≤∫ xi in R,‖M xi‖*E := by
      apply integral_mono_ae ((hi Q1 c1).sub (hi Q2 c2)).norm.integrableOn (hM.norm.mul_const E).integrableOn
      exact Eventually.of_forall (fun xi => by rw [←mul_sub,norm_mul]; exact mul_le_mul_of_nonneg_left (hmode xi) (norm_nonneg _))
    _=(∫ xi in R,‖M xi‖)*E := by rw [integral_mul_const]
    _≤_ := mul_le_mul_of_nonneg_right (setIntegral_le_integral hM.norm
      (Eventually.of_forall (fun xi => norm_nonneg _))) hE

/-- Uniform over every original medium fibre or full no-medium rectangle,
all actual roles and every retained frequency bound. -/
theorem exists_row_cost (omega loss : ℝ) (ho : 0<omega) (hloss : 0<loss) :
    ∃ C : ℝ,0≤C ∧ ∀ {b kap : ℝ},0<b → b≤1 → 0<kap → 19/96<baseline b kap →
    ∀ᶠ N : ℕ in atTop,∀ P : Params,P.N=N → P.omega=omega → 0≤P.e →
    P.ell+P.T*(J0 P.omega:ℝ)<1/1000 →
    ∀ {u v : ℕ},u+v≤12 → ∀ (kap0 : ℝ) (A cj ck : ℕ) (bs : Fin (u+v)→Block)
      (I : Finset (Fin (u+v)→ℕ)),I⊆rectangle bs →
    ∀ (Z : ℝ) (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role),
    ‖retained (u:=u) (v:=v) b kap (outerWidth N) N kap0 cj ck bs I Z ys rs (products P) (free P) A-
      retained (u:=u) (v:=v) b kap (outerWidth N) N kap0 cj ck bs I Z ys rs P.S P.rho A‖≤
      C*(N:ℝ)^(1-omega+loss)*logScale (countingScale N)^36 := by
  obtain ⟨D,hD,hm⟩ := exists_mode_cost omega loss ho hloss
  obtain ⟨G,hG,hg⟩ := exists_row_mass
  refine ⟨G*D,mul_nonneg hG hD.le,?_⟩
  intro b kap hb hb1 hk hgap
  filter_upwards [hm,eventually_width _ (half_pos (sub_pos.mpr hgap))] with N hM hw
  obtain ⟨hN,hs,hs1,hres,hscale⟩ := hw
  have hN0 : 0<N := by omega
  have hgate : 2*outerWidth N≤baseline b kap-19/96 := by linarith
  let L := logScale (countingScale N)
  have hL : 1≤L := logScale_one_le (countingScale_one_le hN0)
  intro P hp ho' he ht u v hd kap0 A cj ck bs I hI Z ys rs
  by_cases live : ∃ y∈I,integerProfile (a:=u) (d:=v) b kap (outerWidth N) N kap0 cj ck y≠0
  · simp only [retained,if_pos live]
    let E := D*(N:ℝ)^(1-omega+loss)*L^12
    have epos : 0≤E := by dsimp [E]; positivity
    have H := (integrate hb hs hgate kap0 cj ck bs I Z ys rs (products P) P.S (free P) P.rho A epos
      (hM P hp ho' he ht hd I (live_products hb hk hs hgate hd cj ck bs I hI live) Z ys rs (blockScales bs)))
    have hA := hg b kap (outerWidth N) hb hb1 hk hs hgate N hN0 kap0 cj ck u v hd bs
    have hgL : G/(outerWidth N)^24≤G*L^24 := by
      unfold outerWidth
      rw [one_div,inv_pow,div_inv_eq_mul]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hres _) hG
    apply H.trans ((mul_le_mul_of_nonneg_right (hA.trans hgL) epos).trans_eq ?_)
    dsimp only [E,L]; ring
  · simp only [retained,if_neg live,sub_self,norm_zero]
    positivity

/-- Fourteen powers for original scalar/chart/role owners and one power
for the real complement bank. Earlier source factor 24 and the native HB
slot factor 12 are both retained. -/
theorem exists_band_power (omega loss : ℝ) (ho : 0<omega) (hloss : 0<loss) :
    ∃ C : ℝ,0≤C ∧ ∀ {b kap : ℝ},0<b → b≤1 → 0<kap → 19/96<baseline b kap →
    ∀ᶠ N : ℕ in atTop,∀ P : Params,P.N=N → P.omega=omega → 0≤P.e →
    P.ell+P.T*(J0 P.omega:ℝ)<1/1000 → ∀ (K A : ℕ) (kap0 zeta : ℝ),
      ‖band b kap N K A kap0 zeta (products P) (free P)-band b kap N K A kap0 zeta P.S P.rho‖≤
        C*(N:ℝ)^(1-omega+loss)*logScale (countingScale N)^51 := by
  obtain ⟨D,hD,H⟩ := exists_row_cost omega loss ho hloss
  let dc := dyadicConstant
  have hc : 0<dc := dyadicConstant_pos
  refine ⟨49*dc^14*dc*D,by positivity,?_⟩
  intro b kap hb hb1 hk hgap
  filter_upwards [H hb hb1 hk hgap,eventually_ge_atTop (2:ℕ)] with N hrows hN
  intro P hp how he ht K A kap0 zeta
  let L := logScale (countingScale N)
  have hL : 1≤L := logScale_one_le (countingScale_one_le (by omega : 0<N))
  let E := D*(N:ℝ)^(1-omega+loss)*L^36
  have hE : 0≤E := by dsimp [E]; positivity
  let S := products P
  have hbnd {u v : ℕ} (hm : u+v≤12) (cj ck : ℕ) (bs : Fin (u+v)→Block)
      (Z : ℝ) (ys : Fin (u+v)→ℝ) (rs : Fin (u+v)→Role) :
      ‖split (u:=u) (v:=v) b kap (outerWidth N) N kap0 cj ck zeta bs Z ys rs S (free P) A-
        split (u:=u) (v:=v) b kap (outerWidth N) N kap0 cj ck zeta bs Z ys rs P.S P.rho A‖≤(dc*L)*E := by
    have one (I) (hi : I⊆rectangle bs) := hrows P hp how he ht hm kap0 A cj ck bs I hi Z ys rs
    have card := complement_count (N:=N) (by omega)
    have nonempty : 1≤((bank (cap N)).card:ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (show (bank (cap N)).Nonempty from ⟨.unit,Finset.mem_insert_self _ _⟩)
    cases h : first cj ck zeta bs with
    | none =>
      simp only [split,h]
      exact (one _ (fun _ hi => hi)).trans (le_mul_of_one_le_left hE (nonempty.trans card))
    | some i =>
      simp only [split,h]
      rw [←Finset.sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      apply le_trans _ (mul_le_mul_of_nonneg_right card hE)
      simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum
        (s:=bank (cap N)) (fun C _ => one (fibre bs i C) (fun _ hh => (Finset.mem_filter.mp hh).1))
  have hmo (cj ck : ℕ) :
      ‖retainedMother b kap N K A cj ck kap0 zeta S (free P)-
        retainedMother b kap N K A cj ck kap0 zeta P.S P.rho‖≤
        (groupScalarMass cj*groupScalarMass ck)*((dc*L)*E) := by
    change ‖groupEval cj _-groupEval cj _‖≤_
    rw [mul_assoc]
    apply groupEval_sub_le
    intro i hi bs hbs
    apply groupEval_sub_le
    intro j hj cs hcs
    apply hbnd (u:=2*(i+1)) (v:=2*(j+1))
    have H1 := Finset.mem_range.mp hi
    have H2 := Finset.mem_range.mp hj
    omega
  unfold band
  rw [←Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun js _ => hmo (js.getD 0 0) (js.getD 1 0))).trans ?_)
  rw [←Finset.sum_mul]
  change sourceScalarMass N*((dc*L)*E)≤_
  apply (mul_le_mul_of_nonneg_right (sourceScalarMass_le (by omega : 0<N))
    (by positivity : 0≤dc*L*E)).trans_eq
  dsimp only [E,L,dc]; ring

end
end ImbalancedChen.P4BOriginalCollisionRetained
