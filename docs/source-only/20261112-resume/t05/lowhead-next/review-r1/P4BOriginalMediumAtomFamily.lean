import ImbalancedChen.P4BOriginalMediumAuxiliaryBound
import ImbalancedChen.P4BOriginalMediumComplementCoefficient
import ImbalancedChen.P4BOriginalCollisionThirdFactor
import ImbalancedChen.Part3DistributionTargets

/-! A retained first-medium fibre on the actual finite upper tree, with
the original small Rosser incorporated into the third arithmetic factor.
The residue, HB roles, real cutoffs and both interval endpoints are fixed
before evaluating either arithmetic sum. -/
namespace ImbalancedChen.P4BOriginalMediumAtomFamily
noncomputable section
open Classical Filter
open scoped BigOperators
open Part3 (MediumAtom factorCarrier UniformAuxiliarySW auxiliarySWError)
open P5Z.HBRightClosedDyadicRoles (Block Owns)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos owns_bounds)
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCutoff)
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff)
open P5Z.AllRankCauchyCubeTail (outsideCube)
open P5Z.ActualSelectedRoughSlotAPDictionary (intervalCarrier)
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionThirdFactor (splitAt factor gamma thirdSupport)
open P4BOriginalHighRankComplementBlocks (fibre same_scale)
open P4BOriginalHighRankPostModulusFibres (first)
open P4BOriginalHighRankPostModulusRow (H)
open P4BUpperPairOrderedRowGeometry (integerProfile rowRoles)
open P4BOuterRampRoughness (baseline)

abbrev size (j : Fin 3) := 2*(j.val+1)
def support (P : Params) (labels : List ℕ) := (P.bins labels).image List.prod

def cut (S : Finset ℕ) (f : ℕ→ℝ) (B : Block) (n : ℕ) : ℂ :=
  if n∈S ∧ Owns B n then (f n:ℂ) else 0

structure Index (order : ℕ) (zeta kap0 : ℝ) where
  P : Params
  N_pos : 0<P.N
  b : ℝ
  kap : ℝ
  s : ℝ
  b_pos : 0<b
  kap_pos : 0<kap
  s_pos : 0<s
  gate : 2*s≤baseline b kap-19/96
  j : Fin 3
  l : Fin 3
  cj : ℕ
  ck : ℕ
  bs : Fin (size j+size l)→Block
  i : Fin (size j+size l)
  C : Block
  live : ∃ y∈fibre bs i C,integerProfile (a:=size j) (d:=size l) b kap s P.N kap0 cj ck y≠0
  selected : first cj ck zeta bs=some i
  xi : Fin (size j+size l)→ℝ
  band : xi∈(outsideCube (size j+size l) (H P.N order))ᶜ
  eta : ℝ
  J : List ℕ
  word : J∈P.words
  owners : Fin 3→Block

namespace Index
variable {order : ℕ} {zeta kap0 : ℝ} (I : Index order zeta kap0)
abbrev U : ℝ := (lower (I.bs I.i):ℝ)
abbrev V : ℝ := (lower I.C:ℝ)
abbrev x : ℝ := I.U*I.V
abbrev groups := splitAt I.P I.x I.U I.eta I.J
abbrev truncations : Fin (size I.j+size I.l)→ℝ :=
  Fin.append (fun _ : Fin (size I.j) => hbCutoff I.cj) (fun _ : Fin (size I.l) => hbCutoff I.ck)
abbrev roles := Fin.append (rowRoles I.j.val) (rowRoles I.l.val)
abbrev Z (K : ℕ) := beforeHBCutoff K [I.cj,I.ck]

def atom (K : ℕ) : MediumAtom where
  U := I.U
  V := I.V
  Q1 := lower (I.owners 0)
  Q2 := lower (I.owners 1)
  Q3 := lower (I.owners 2)
  residue := (I.P.N:ℤ)
  intervalLo := I.U
  intervalHi := 2*I.U
  alpha := P4BOriginalMediumHBHead.alpha (I.bs I.i) (I.Z K) (I.truncations I.i) (I.roles I.i) (I.xi I.i)
  beta := P4BOriginalMediumComplementCoefficient.beta I.bs I.i I.C (I.Z K) I.truncations I.roles I.xi
  gamma1 := cut (support I.P I.groups.1) (factor I.P I.groups.1) (I.owners 0)
  gamma2 := cut (support I.P I.groups.2.1) (factor I.P I.groups.2.1) (I.owners 1)
  gamma3 := cut (thirdSupport I.P I.J I.groups.2.2) (gamma I.P I.J I.groups.2.2) (I.owners 2)

theorem carrier (K : ℕ) : (I.atom K).alphaCarrier=intervalCarrier I.U (2*I.U) := by
  have hp : 0≤I.U := Nat.cast_nonneg _
  have h2 : 0≤2*I.U := by positivity
  ext n
  simp only [MediumAtom.alphaCarrier,atom,intervalCarrier,Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc,
    Nat.ceil_le,Nat.le_floor_iff h2,Nat.floor_lt hp]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨⟨h.1.le,h.2⟩,h⟩

theorem scale_upper : I.x≤Real.exp 1*I.P.N := by
  obtain ⟨y,hy,hw⟩ := I.live
  have h := (P4BOriginalHighRankMotherScale.live_geometry I.N_pos I.b_pos I.kap_pos I.s_pos I.gate
      I.cj I.ck I.bs y I.i (Finset.mem_filter.mp hy).1 hw).2.1
  rwa [same_scale hy] at h

theorem atom_beta_bound (K : ℕ) {m : ℕ} (hm : m∈(I.atom K).betaCarrier) :
    ‖(I.atom K).beta m‖≤(m.divisors.card:ℝ)^12 := by
  have hm' : (lower I.C:ℝ)≤m := Nat.ceil_le.mp (Finset.mem_Icc.mp hm).1
  have hp : 0<m := (lower_pos I.C).trans_le (by exact_mod_cast hm')
  have ht : size I.j+size I.l≤12 := by dsimp [size]; omega
  have htau : 1≤(m.divisors.card:ℝ) := by
    have h : 0<m.divisors.card := Finset.card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr hp.ne'⟩
    exact_mod_cast Nat.succ_le_of_lt h
  exact (P4BOriginalMediumComplementCoefficient.beta_norm I.bs I.i I.C (I.Z K)
    I.truncations I.roles I.xi hp).trans (pow_le_pow_right₀ htau ht)

end Index

private theorem factor_data (P : Params) (G : List ℕ) {q : ℕ} (hq : q∈support P G) :
    0<q ∧ q.Coprime P.N := by
  obtain ⟨ps,hps,rfl⟩ := Finset.mem_image.mp hq
  have crop := (P4AOrderedThirdClippedFactorial.crop _ _ _ _).mp hps
  refine ⟨Nat.pos_of_ne_zero (P.rough hps).1,Nat.coprime_list_prod_left_iff.mpr ?_⟩
  intro p hp
  have h := mem_roughPrimeFinset.mp (crop.2 p hp)
  exact h.2.1.coprime_iff_not_dvd.mpr h.2.2.1

theorem third_data (P : Params) (J G : List ℕ) {q : ℕ} (hq : q∈thirdSupport P J G) :
    0<q ∧ q.Coprime P.N := by
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
  have hs := (Finset.mem_filter.mp ha).1
  have hpos := (actualSmallRosserSupport_smallPrimeSupportedAt _ _ _ hs).1
  have hr := factor_data P G hb
  exact ⟨Nat.mul_pos (Nat.pos_of_ne_zero hpos) hr.1,
    (actualSmallRosserSupport_coprime_target _ _ _ hs).mul_left hr.2⟩

theorem support_data (P : Params) (G : List ℕ) {q : ℕ} (hq : q∈support P G) :
    0<q ∧ q.Coprime P.N := factor_data P G hq

private theorem cut_data (S : Finset ℕ) (f : ℕ→ℝ) (B : Block) (N : ℕ)
    (h : ∀q∈S,|f q|≤1 ∧ q.Coprime N) (q : ℕ) :
    ‖cut S f B q‖≤1 ∧ (cut S f B q≠0 → q.Coprime N) := by
  by_cases hm : q∈S ∧ Owns B q
  · simpa [cut,hm] using And.intro (h q hm.1).1 (fun _ : (f q:ℂ)≠0 => (h q hm.1).2)
  · simp [cut,hm]

theorem factor_bounds {order : ℕ} {zeta kap0 : ℝ} (I : Index order zeta kap0) (K : ℕ) (q : ℕ) :
    (‖(I.atom K).gamma1 q‖≤1 ∧ ((I.atom K).gamma1 q≠0 → q.Coprime I.P.N)) ∧
    (‖(I.atom K).gamma2 q‖≤1 ∧ ((I.atom K).gamma2 q≠0 → q.Coprime I.P.N)) ∧
    (‖(I.atom K).gamma3 q‖≤1 ∧ ((I.atom K).gamma3 q≠0 → q.Coprime I.P.N)) := by
  have fg (G : List ℕ) (B : Block) := cut_data (support I.P G) (factor I.P G) B I.P.N
    (fun n hn => ⟨P4AOriginalFiniteFallbackGroupedAtoms.group_unit _ _ _ G n,(factor_data I.P G hn).2⟩) q
  exact ⟨fg _ _,fg _ _,cut_data _ _ _ _ (fun n hn =>
    ⟨P4BOriginalCollisionThirdFactor.gamma_one I.P I.J I.groups.2.2 n,(third_data I.P I.J I.groups.2.2 hn).2⟩) q⟩

/-- The literal quantified SW premise, for the family with the actual N,
three complete-level factors, complementary HB product and first selected
slot. The scale threshold precedes every policy and every permitted width. -/
theorem uniform_original_auxiliary_SW (K order : ℕ) {zeta kappa kap0 : ℝ}
    (hz : 0<zeta) (hz1 : zeta≤1/400) (hk : 0<kappa) (hkz : kappa≤zeta)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    UniformAuxiliarySW (fun I : Index order zeta kap0 => I.atom K) 1 := by
  intro A hA
  obtain ⟨C,hC,HN⟩ := P4BOriginalMediumAuxiliaryBound.eventually_original_selected K order A hA.le
    hz hz1 hk hkz ht ht1
  obtain ⟨N0,h0⟩ := eventually_atTop.mp HN
  let x0 : ℝ := max 2 (Real.exp 1*(N0:ℝ))
  refine ⟨C,hC,x0,(by dsimp [x0]; exact (by norm_num : (1:ℝ)<2).trans_le (le_max_left _ _)),?_⟩
  intro I hx k q b hk' hq hb
  have hn : N0≤I.P.N := by
    have he := (le_max_right (2:ℝ) (Real.exp 1*(N0:ℝ))).trans (hx.trans I.scale_upper)
    exact_mod_cast (mul_le_mul_iff_right₀ (Real.exp_pos 1)).mp he
  obtain ⟨_,_,H⟩ := h0 I.P.N hn I.b_pos I.kap_pos I.s_pos I.gate _ _ I.cj I.ck I.bs I.i I.C
    I.live I.selected (I.roles I.i) (I.truncations I.i) I.xi I.band
  change ‖auxiliarySWError (I.atom K).alphaCarrier (I.atom K).alpha k q b‖≤_
  rw [I.carrier K]
  have hu : 0≤I.U := Nat.cast_nonneg _
  simpa only [pow_one] using H I.U (2*I.U) (le_refl _) (by linarith only [hu])
    (le_refl _) k q b hk' hq hb

end
end ImbalancedChen.P4BOriginalMediumAtomFamily
