import ImbalancedChen.P1OriginalSingletonMediumAuxiliarySW
import ImbalancedChen.P4BOriginalMediumTripleOccupiedBridge
import ImbalancedChen.P4BOriginalHigherActionFamily
import all ImbalancedChen.P4BOriginalMediumAtomFamily

/-!
SOURCE ONLY / NOT COMPILED.

Literal singleton HB rows, rather than a pair-mother Index. The modulus
grouping is the selected raised-action Rule on the same final Params.
This file supplies the low-first rough-rank-three subfamily and the actual
family-uniform auxiliary SW. It does not claim the whole medium word bank,
signed M, Fourier restoration, total Atlas, or the final prime target.
-/
namespace ImbalancedChen.P1OriginalSingletonMediumLowThreeAdmissible
noncomputable section
open Classical Filter
open Part3 (MediumAtom MediumAdmissible UniformAuxiliarySW auxiliarySWError)
open P4BOriginalCollisionWords (Params)
open P4BOriginalCollisionTensor (ownerHead)
open P4BOriginalCollisionThirdFactor (splitAt factor gamma thirdSupport)
open P4BOriginalMediumAtomFamily (support cut support_data third_data)
open P5Z.HBRightClosedDyadicRoles (Block owner)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos)
open P5Z.ActualHBDyadicOccurrenceFamily (blockWords blockWords_spec)
open P5Z.OrderedFactorTupleRectangleReindex (blockVector ofFn_blockVector)
open P5Z.PerGroupIntegerHBAtlasPushforward (hbCap hbCutoff)
open P5Z.ExactOriginalSmoothDyadicPartition (beforeHBCutoff)
open P5Z.OriginalPrimeAtlasReserveBranches (originalMediumLow originalMediumHigh)
open P5Z.ActualHBMediumBranchPartition (firstMedium)
open P5Z.ActualLowerNormalizedAtlasOccurrence (integerProfile rowRoles)
open P5Z.ActualSelectedRoughSlotAPDictionary (intervalCarrier)
open P5Z.AllRankCauchyCubeTail (outsideCube)
open P4BOriginalHighRankComplementBlocks (fibre same_scale)
open P4BOriginalHighRankPostModulusRow (H)
open P4BOriginalMediumHBHead (alpha)
open P1OriginalSingletonMediumWindow (live_geometry eventually_original_medium_window)
open P1OriginalSingletonMediumAuxiliarySW (eventually_actual_singleton_row)
open private cut_data from ImbalancedChen.P4BOriginalMediumAtomFamily

abbrev size (j : Fin 3) := 2*(j.val+1)

/-- The same row bank used by source64, including every unit slot,
rowRoles, real hbCutoff, firstMedium position and the original H cube. -/
structure Index (modeOrder : ℕ) (kap zeta kap0 : ℝ) where
  P : Params
  N_pos : 0<P.N
  cj : ℕ
  j : Fin 3
  bs : List Block
  row : bs∈blockWords (hbCap cj) (size j)
  i : Fin (size j)
  C : Block
  live : ∃ n∈fibre (blockVector (size j) bs) i C,
    integerProfile kap 6 P.N cj kap0 n≠0
  selected : firstMedium (originalMediumLow zeta [cj])
    (originalMediumHigh zeta [cj]) bs=some i.val
  xi : Fin (size j)→ℝ
  band : xi∈(outsideCube (size j) (H P.N modeOrder))ᶜ
  J : List ℕ
  word : J∈P.words

namespace Index
variable {modeOrder : ℕ} {kap zeta kap0 : ℝ} (I : Index modeOrder kap zeta kap0)
abbrev bv := blockVector (size I.j) I.bs
abbrev U : ℝ := lower (I.bv I.i)
abbrev V : ℝ := lower I.C
abbrev x : ℝ := I.U*I.V
abbrev Z (K : ℕ) := beforeHBCutoff K [I.cj]
abbrev truncations : Fin (size I.j)→ℝ := fun _ => hbCutoff I.cj
abbrev roles := rowRoles I.j.val
abbrev groups := P4BOriginalHigherActionGroups.split I.P I.x I.U zeta I.J
abbrev firstOwners := (support I.P I.groups.1).image owner
abbrev secondOwners := (support I.P I.groups.2.1).image owner
abbrev thirdOwners := (thirdSupport I.P I.J I.groups.2.2).image owner

theorem selected_ofFn : firstMedium (originalMediumLow zeta [I.cj])
    (originalMediumHigh zeta [I.cj]) (List.ofFn I.bv)=some I.i.val := by
  dsimp only [bv]
  rw [ofFn_blockVector (blockWords_spec _ _ _ I.row).1]
  exact I.selected

def atom (K : ℕ) (D E G : Block) : MediumAtom where
  U := I.U
  V := I.V
  Q1 := lower D
  Q2 := lower E
  Q3 := lower G
  residue := (I.P.N:ℤ)
  intervalLo := I.U
  intervalHi := 2*I.U
  alpha := alpha (I.bv I.i) (I.Z K) (hbCutoff I.cj) (I.roles I.i) (I.xi I.i)
  beta := P4BOriginalMediumComplementCoefficient.beta I.bv I.i I.C (I.Z K)
    I.truncations I.roles I.xi
  gamma1 := cut (support I.P I.groups.1) (factor I.P I.groups.1) D
  gamma2 := cut (support I.P I.groups.2.1) (factor I.P I.groups.2.1) E
  gamma3 := cut (thirdSupport I.P I.J I.groups.2.2) (gamma I.P I.J I.groups.2.2) G

theorem carrier (K : ℕ) (D E G : Block) :
    (I.atom K D E G).alphaCarrier=intervalCarrier I.U (2*I.U) := by
  have hp : 0≤I.U := Nat.cast_nonneg _
  have h2 : 0≤2*I.U := by positivity
  ext n
  simp only [MediumAtom.alphaCarrier,atom,intervalCarrier,Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc,
    Nat.ceil_le,Nat.le_floor_iff h2,Nat.floor_lt hp]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨⟨h.1.le,h.2⟩,h⟩

/-- The singleton cap is 2*N; this read does not use the pair-mother cap. -/
theorem scale_upper (hkap : kap<1) : I.x≤2*(I.P.N:ℝ) := by
  obtain ⟨n,hn,hw⟩ := I.live
  obtain ⟨_,hcap,_,_⟩ := live_geometry kap hkap I.N_pos I.cj kap0 I.bv n I.i
    (Finset.mem_filter.mp hn).1 hw
  rwa [same_scale hn] at hcap

theorem beta_bound (K : ℕ) (D E G : Block) {m : ℕ}
    (hm : m∈(I.atom K D E G).betaCarrier) :
    ‖(I.atom K D E G).beta m‖≤(m.divisors.card:ℝ)^6 := by
  have hm' : (lower I.C:ℝ)≤m := Nat.ceil_le.mp (Finset.mem_Icc.mp hm).1
  have hp : 0<m := (lower_pos I.C).trans_le (by exact_mod_cast hm')
  have ht : size I.j≤6 := by dsimp [size]; omega
  have htau : 1≤(m.divisors.card:ℝ) := by
    have h : 0<m.divisors.card := Finset.card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr hp.ne'⟩
    exact_mod_cast Nat.succ_le_of_lt h
  exact (P4BOriginalMediumComplementCoefficient.beta_norm I.bv I.i I.C (I.Z K)
    I.truncations I.roles I.xi hp).trans (pow_le_pow_right₀ htau ht)

theorem factor_bounds (K : ℕ) (D E G : Block) (q : ℕ) :
    (‖(I.atom K D E G).gamma1 q‖≤1 ∧ ((I.atom K D E G).gamma1 q≠0 → q.Coprime I.P.N)) ∧
    (‖(I.atom K D E G).gamma2 q‖≤1 ∧ ((I.atom K D E G).gamma2 q≠0 → q.Coprime I.P.N)) ∧
    (‖(I.atom K D E G).gamma3 q‖≤1 ∧ ((I.atom K D E G).gamma3 q≠0 → q.Coprime I.P.N)) := by
  have fg (S : List ℕ) (B : Block) := cut_data (support I.P S) (factor I.P S) B I.P.N
    (fun n hn => ⟨P4AOriginalFiniteFallbackGroupedAtoms.group_unit _ _ _ S n,(support_data I.P S hn).2⟩) q
  exact ⟨fg _ _,fg _ _,cut_data _ _ _ _ (fun n hn =>
    ⟨P4BOriginalCollisionThirdFactor.gamma_one I.P I.J I.groups.2.2 n,
      (third_data I.P I.J I.groups.2.2 hn).2⟩) q⟩

end Index

/-- A common scale threshold for the literal singleton atoms. The scalar
from the logarithm role is not incorporated into alpha or its coprime mean. -/
theorem uniform_auxiliary (K modeOrder : ℕ) {kap zeta kappa kap0 : ℝ}
    (hkap : kap<1) (hz : 0<zeta) (hz1 : zeta≤1/400)
    (hk : 0<kappa) (hk1 : kappa≤1)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    UniformAuxiliarySW
      (fun p : Index modeOrder kap zeta kap0 × Block × Block × Block =>
        p.1.atom K p.2.1 p.2.2.1 p.2.2.2) 1 := by
  intro A hA
  obtain ⟨C,hC,HN⟩ := eventually_actual_singleton_row K modeOrder A hA.le
    hkap hz hz1 hk hk1 ht ht1
  obtain ⟨N0,h0⟩ := eventually_atTop.mp HN
  let x0 : ℝ := max (Real.exp 1+1) (2*(N0:ℝ))
  refine ⟨C,hC,x0,(by dsimp [x0]; linarith [Real.exp_pos 1,le_max_left (Real.exp 1+1) (2*(N0:ℝ))]),?_⟩
  intro p hx k q b hk' hq hb
  let I := p.1
  have hn : N0≤I.P.N := by
    have he := (le_max_right (Real.exp 1+1) (2*(N0:ℝ))).trans (hx.trans (I.scale_upper hkap))
    exact_mod_cast (show (N0:ℝ)≤I.P.N by linarith only [he])
  obtain ⟨_,_,HS⟩ := h0 I.P.N hn I.cj I.j.val I.bs I.row I.i I.C
    I.live I.selected I.xi I.band
  change ‖auxiliarySWError (I.atom K p.2.1 p.2.2.1 p.2.2.2).alphaCarrier
    (I.atom K p.2.1 p.2.2.1 p.2.2.2).alpha k q b‖≤_
  rw [I.carrier K p.2.1 p.2.2.1 p.2.2.2]
  have hu : 0≤I.U := Nat.cast_nonneg _
  have Hstrong := (HS I.U (2*I.U) (le_refl _) (by linarith only [hu])
    (le_refl _) k q b (by omega) (by omega) hb).1
  have hxExp : Real.exp 1≤I.x :=
    (show Real.exp 1≤x0 by dsimp [x0]; linarith [le_max_left (Real.exp 1+1) (2*(N0:ℝ))]).trans hx
  have hxPos : 0<I.x := (Real.exp_pos 1).trans_le hxExp
  have hlog : 1≤Real.log I.x := (Real.le_log_iff_exp_le hxPos).mpr hxExp
  have hden := Real.rpow_le_rpow_of_exponent_le hlog (show A≤A+1 by linarith)
  apply Hstrong.trans
  simpa only [pow_one] using div_le_div_of_nonneg_left
    (show 0≤C*I.U*(k.divisors.card:ℝ) by positivity)
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hlog) A) hden

/-- All four actual M lengths and the actual coefficient gates on the
occupied low-first rough-rank-three subfamily. No desired error estimate
or target length condition is a hypothesis. One physical threshold precedes
the singleton chart, row, first position, complement, mode, word and owners. -/
theorem eventually_low_three (K modeOrder : ℕ) {kap zeta kappa kap0 : ℝ}
    (hkap : kap<1) (hz : 0<zeta) (hz0 : zeta≤1/20000)
    (hk : 0<kappa) (hkz : kappa≤zeta/200000)
    (ht : kap0<kappa/(4*(1+kappa))) (ht1 : kap0<1) :
    ∀ᶠ N : ℕ in atTop,∀ I : Index modeOrder kap zeta kap0,I.P.N=N →
      0≤I.P.e → (I.P.e:ℝ)≤1/2048 → 0<I.P.q → I.P.T≤zeta →
      0≤I.P.ell → 2*I.P.ell≤zeta/16 → I.J.length=3 →
      actualPrimeTupleLog I.P.N (ownerHead I.P I.J) 0≤VariableEnvelope.mu →
      ∀ D∈I.firstOwners,∀ E∈I.secondOwners,∀ G∈I.thirdOwners,
        MediumAdmissible 6 (zeta/2000) kappa (1/2) (I.atom K D E G) := by
  have hz1 : zeta≤1/400 := by linarith
  have hk1 : kappa≤1 := by linarith
  have hke : kappa≤zeta := by linarith
  filter_upwards [eventually_original_medium_window K (Real.exp (Real.exp 1)+1)
      hkap hz hz1 hk ht ht1,
    (eventually_actual_singleton_row K modeOrder 0 (le_refl (0:ℝ))
      hkap hz hz1 hk hk1 ht ht1).choose_spec.2,
    eventually_ge_atTop (2:ℕ)] with N HW HS hNN
  intro I hN he he' hq hT hell hell' h3 hl D hD E hE G hG
  rw [←hN] at HW HS hNN
  obtain ⟨hLarge,hx,hRes,hNx,_,hU,hUlo,hUhi,_,_,_,_,_⟩ :=
    HW I.cj (size I.j) I.bv I.i I.C I.live I.selected_ofFn
  obtain ⟨hAlpha,hRough,_⟩ := HS I.cj I.j.val I.bs I.row I.i I.C
    I.live I.selected I.xi I.band
  have hgroups : I.groups=splitAt I.P I.x I.U zeta I.J :=
    P4BOriginalHigherActionFamily.off_low I.P I.x I.U zeta I.J (Or.inl (by omega))
  change D∈(support I.P I.groups.1).image owner at hD
  change E∈(support I.P I.groups.2.1).image owner at hE
  change G∈(thirdSupport I.P I.J I.groups.2.2).image owner at hG
  rw [hgroups] at hD hE hG
  obtain ⟨h1,h2,h3',h4⟩ := P4BOriginalMediumTripleOccupiedBridge.original_three I.P
    (by omega) he he' hq hx hz hz0 hke hNx hUlo hUhi hT hell hell' I.word h3 hl D E G hD hE hG
  have hp (B : Block) : (1:ℝ)≤lower B := by exact_mod_cast lower_pos B
  refine ⟨hU.le,hp I.C,hp D,hp E,hp G,?_,?_,hNx,h1,h2,h3',?_,?_,?_,?_,?_,?_,?_⟩
  · change Real.exp (Real.exp 1)<I.x
    linarith only [hLarge]
  · simpa only [one_div] using hRes
  · change I.U^(1+2*(7/32:ℝ))*(lower D:ℝ)*(lower E:ℝ)^(5-2*(7/32:ℝ))*
      (lower G:ℝ)^(2+2*(7/32:ℝ))<_
    simpa only [show 1+2*(7/32:ℝ)=23/16 by norm_num,
      show 5-2*(7/32:ℝ)=73/16 by norm_num,show 2+2*(7/32:ℝ)=39/16 by norm_num] using h4
  · exact fun n _ => hAlpha n
  · exact fun n _ hn p hp hd => hRough n hn p hp hd
  · exact fun m hm => I.beta_bound K D E G hm
  · exact fun q _ => (I.factor_bounds K D E G q).1
  · exact fun q _ => (I.factor_bounds K D E G q).2.1
  · exact fun q _ => (I.factor_bounds K D E G q).2.2

end
end ImbalancedChen.P1OriginalSingletonMediumLowThreeAdmissible
