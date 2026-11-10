import ImbalancedChen.P4AFull87HistoricalCompilerRate

namespace ImbalancedChen.P4AFull87PhysicalReserveFromRate
noncomputable section
open scoped Classical BigOperators Topology
open Filter P4AUpperTaggedParityCompiler
open P4AFull87CompilerChangedPartition P4AFull87HistoricalChangedSupport

abbrev Keep := ℕ → List ℕ → Bool
abbrev Tags := ℕ → ℕ → List Bool

def WallRate (M : ℕ) (keep : Keep) (tags : Tags) : Prop :=
  ∃ K E : ℝ, 1 < K ∧ 1 < E ∧ ∀ B : ℝ, 0 ≤ B →
    ∀ N cap : ℕ, 2 ≤ N → Even N → ∀ omega v tau : ℝ, 0 < omega → omega ≤ v → v ≤ 1 →
    0 < tau → 3 ≤ (N:ℝ)^omega → E ≤ omega*Real.log (N:ℝ) →
    (B/omega)*changedMass (keep N) (tags N) N cap ((N:ℝ)^omega) ((N:ℝ)^v) tau ≤
      ((M : ℝ)*150*B*tau+(M : ℝ)*10*B*K/Real.log (N:ℝ))/omega^5

private theorem choose_width {M : ℕ} {keep : Keep} {tags : Tags} (h : WallRate M keep tags)
    (B omega v eta : ℝ) (hB : 0 < B) (hw : 0 < omega) (hv : omega ≤ v) (h1 : v ≤ 1)
    (heta : 0 < eta) :
    ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
    ∀ cap : ℕ, ∀ tau : ℝ, 0 < tau → tau ≤ tau0 →
    (B/omega)*changedMass (keep N) (tags N) N cap ((N:ℝ)^omega) ((N:ℝ)^v) tau < eta := by
  obtain ⟨K,E,hK,hE,hh⟩ := h
  let A := (M:ℝ)*150*B
  let D := (M:ℝ)*10*B*K
  let G := eta*omega^5/4
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hG : 0 < G := by dsimp only [G]; positivity
  let t := G/(A+1)
  have htp : 0 < t := div_pos hG (by positivity)
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpow := (tendsto_rpow_atTop hw).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge : ∀ᶠ N : ℕ in atTop, 2 ≤ N ∧ 3 ≤ (N:ℝ)^omega ∧
      E/omega ≤ Real.log (N:ℝ) ∧ D/G ≤ Real.log (N:ℝ) := by
    filter_upwards [eventually_ge_atTop 2,hpow.eventually (eventually_ge_atTop 3),
      hlog.eventually (eventually_ge_atTop (E/omega)),
      hlog.eventually (eventually_ge_atTop (D/G))] with N h1 h2 h3 h4 using ⟨h1,h2,h3,h4⟩
  obtain ⟨N0,hN0⟩ := eventually_atTop.1 hlarge
  refine ⟨t,htp,N0,(hN0 _ le_rfl).1,?_⟩
  intro N hN hEven cap tau ht hsmall
  obtain ⟨hn,h3,he,hd⟩ := hN0 N hN
  have hl : 0 < Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hwlog : E ≤ omega*Real.log (N:ℝ) := by simpa only [mul_comm] using (div_le_iff₀ hw).mp he
  apply (hh B hB.le N cap hn hEven omega v tau hw hv h1 ht h3 hwlog).trans_lt
  apply (div_lt_iff₀ (pow_pos hw 5)).mpr
  have h1' : A*tau ≤ G := by
    have hx := (le_div_iff₀ (by positivity : 0 < A+1)).mp hsmall
    nlinarith
  have h2' : D/Real.log (N:ℝ) ≤ G := by
    apply (div_le_iff₀ hl).mpr
    simpa only [mul_comm] using (div_le_iff₀ hG).mp hd
  change A*tau+D/Real.log (N:ℝ) < _
  dsimp only [G] at h1' h2'
  linarith [mul_pos heta (pow_pos hw 5)]

def Paid (keep : Keep) (tags : Tags) (nu r u_c epsilonMax : ℝ) : Prop :=
  ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1/8 ∧ epsilon < epsilonMax ∧
    epsilon^2 < r ∧ nu*epsilon < 1/1000 ∧
    ∃ tau0 : ℝ, 0 < tau0 ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
    ∀ cap : ℕ, (N:ℝ)^(nu*r) ≤ (cap:ℝ) → ∀ tau : ℝ, 0 < tau → tau ≤ tau0 →
      let w := (N:ℝ)^(nu*epsilon^2)
      let z := (N:ℝ)^(nu*r)
      let L := (N:ℝ)^(nu*epsilon)
      let rho := P4AUpperTaggedBetaAttachment.rho (keep N) (tags N) N cap w z tau L
      let spend := P4AFiniteCapTaggedConstructor.compilerExpense (keep N) (tags N) N cap w z tau L
      spend < u_c*(singularSeries N / Real.log (N:ℝ)) ∧
      ((N:ℝ)/Real.log (N:ℝ))*spend < u_c*singularNormalization N ∧
      physicalDensitySum (P4AUpperTaggedBetaAttachment.support N cap w z) rho <
        p4aReserveRawDensity (keep N) N cap 0 z - p4aActualPresieveCorrection (keep N) N cap w z +
        u_c*(singularSeries N / Real.log (N:ℝ))

theorem of_wallRate {M : ℕ} {keep : Keep} {tags : Tags} (hh : WallRate M keep tags)
    (nu r u_c epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r) (hv1 : nu*r ≤ 1)
    (hu : 0 < u_c) (hmax : 0 < epsilonMax) : Paid keep tags nu r u_c epsilonMax := by
  obtain ⟨B,hB,hbox⟩ := P4AUpperTaggedBetaAttachment.exists_density_difference_le_changedMass
  let em := min epsilonMax (min 1 (min r (1/(2000*nu))))
  have hem : 0 < em := lt_min hmax (lt_min zero_lt_one (lt_min hr (by positivity)))
  obtain ⟨eps,he,h8,hemax,_,Nb,hNb,hbeta⟩ :=
    exists_actualSmallRoughRho_density_error_le_target_reserve nu r (u_c/2) em hnu hr (by positivity) hem
  have hrest := hemax.trans_le (min_le_right epsilonMax _)
  have h1 : eps < 1 := hrest.trans_le (min_le_left _ _)
  have hr' : eps < r := hrest.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hlev := (lt_div_iff₀ (by positivity : 0 < 2000*nu)).mp
    (hrest.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hsq : eps^2 < r := by nlinarith
  let omega := nu*eps^2
  have hw : 0<omega := mul_pos hnu (sq_pos_of_pos he)
  have hv : omega ≤ nu*r := mul_le_mul_of_nonneg_left hsq.le hnu.le
  obtain ⟨Nf,hNf,hphys⟩ := hbox nu hnu eps he h8
  obtain ⟨t,ht,Nm,hNm,hcost⟩ := choose_width hh B omega (nu*r) (u_c/2) hB hw hv hv1 (by positivity)
  refine ⟨eps,he,h8,hemax.trans_le (min_le_left _ _),hsq,by nlinarith,t,ht,max Nb (max Nf Nm),
    hNb.trans (le_max_left _ _),?_⟩
  intro N hN hEven cap hcap tau htp hsmall
  have hbN := (le_max_left _ _).trans hN
  have hfN := (le_max_left Nf Nm).trans ((le_max_right _ _).trans hN)
  have hmN := (le_max_right Nf Nm).trans ((le_max_right _ _).trans hN)
  have hn2 := hNb.trans hbN
  have hn : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  let w := (N:ℝ)^omega
  let z := (N:ℝ)^(nu*r)
  let L := (N:ℝ)^(nu*eps)
  let scale := singularSeries N/Real.log (N:ℝ)
  let A := P4AFiniteCapTaggedConstructor.compilerExpense (keep N) (tags N) N cap w z tau L
  have hwz : w ≤ z := Real.rpow_le_rpow_of_exponent_le hn.le hv
  have hS : 0 < scale := densityScale_pos hn2
  have hb := (hbeta N hbN hEven cap hcap (keep N)).2
  change p4aReservePhysicalDensity (keep N) N cap w z L -
    actualSmallEulerProduct N cap w * p4aReserveRawDensity (keep N) N cap w z ≤
    (u_c/2)*singularSeries N/Real.log (N:ℝ) at hb
  rw [mul_div_assoc] at hb
  have hh := (hphys N hfN hEven cap (hwz.trans hcap) (keep N) (tags N) z tau).trans_lt
    (mul_lt_mul_of_pos_right (hcost N hmN hEven cap tau htp hsmall) hS)
  have hsp : A < u_c*scale := by
    change _ ≤ (u_c/2)*scale at hb
    dsimp only [A,P4AFiniteCapTaggedConstructor.compilerExpense]
    linarith only [add_lt_add_of_le_of_lt hb hh]
  refine ⟨hsp,?_,?_⟩
  · have hsrc : 0 < (N:ℝ)/Real.log (N:ℝ) := div_pos (zero_lt_one.trans hn) (Real.log_pos hn)
    calc
      _ < ((N:ℝ)/Real.log (N:ℝ))*(u_c*scale) := mul_lt_mul_of_pos_left hsp hsrc
      _ = _ := by rw [← sourceMassScale_mul_densityScale N]; dsimp only [scale]; ring
  · have hproj := p4a_fullRaw_eq_euler_presieved_add_correction (keep N) N cap w z hwz
    have hone := le_abs_self
      (physicalDensitySum (P4AUpperTaggedBetaAttachment.support N cap w z)
      (P4AUpperTaggedBetaAttachment.rho (keep N) (tags N) N cap w z tau L) -
      p4aReservePhysicalDensity (keep N) N cap w z L)
    dsimp only [A,P4AFiniteCapTaggedConstructor.compilerExpense] at hsp
    change _ < p4aReserveRawDensity (keep N) N cap 0 z-p4aActualPresieveCorrection (keep N) N cap w z+u_c*scale
    linarith only [hone,hsp,hproj]

theorem historical_paid (P : Parameters) (he : 0 ≤ P.e) (hd : 0 < P.delta)
    (nu r u_c epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r) (hv : nu*r ≤ 1)
    (hu : 0 < u_c) (hmax : 0 < epsilonMax) :
    Paid P.keep (fun N => P.tags N (suffix P N)) nu r u_c epsilonMax :=
  of_wallRate (P4AFull87HistoricalCompilerRate.exists_actual_rate P he hd)
    nu r u_c epsilonMax hnu hr hv hu hmax

end
end ImbalancedChen.P4AFull87PhysicalReserveFromRate
