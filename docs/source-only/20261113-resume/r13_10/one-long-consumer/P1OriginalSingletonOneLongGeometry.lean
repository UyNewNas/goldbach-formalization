import ImbalancedChen.P1OriginalSingletonOneLongRestoration
import ImbalancedChen.P5OriginalOneLongMertensChartHarmonic

/-! SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.
All eventual quantifiers precede the actual chart and the ordered HB
rectangle. The rough cutoff is still the original one; the canonical
envelope is used only to majorize the finite Brun divisor support. -/
namespace ImbalancedChen.P1OriginalSingletonOneLongGeometry
noncomputable section
open Classical Filter Set
open scoped BigOperators Topology
open P5Z.ActualRoughHeathBrownWords P5Z.HBRightClosedDyadicRoles
open P5Z.ActualHBDyadicProductWindow P5Z.ActualHBMediumBranchPartition
open P5Z.OrderedFactorTupleRectangleReindex P5Z.ActualLowerNormalizedAtlasOccurrence
open P5Z.ActualLowerNormalizedHBSource
open P5Z.PerGroupIntegerHBAtlasPushforward P5Z.ExactOriginalSmoothDyadicPartition
open P5Z.OriginalPrimeAtlasReserveBranches P5Z.OriginalChartRoughCutoff
open P1OriginalSingletonOneLongRectangle P1OriginalSingletonOneLongFibres
open P1OriginalSingletonOneLongProfile P1OriginalSingletonOneLongRestoration
open OriginalOneLongExplicitBrunRates OriginalOneLongMertensChartHarmonic

theorem unique_filter_index {α : Type*} (p : α→Bool) (bs : List α)
    (hone : (bs.filter p).length=1) (i j : ℕ) (hi : i<bs.length) (hj : j<bs.length)
    (hpi : p bs[i]=true) (hpj : p bs[j]=true) : i=j := by
  induction bs generalizing i j with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        have hb : p b=true := by simpa using hpi
        have ht : bs.filter p=[] := List.length_eq_zero.mp (by simpa [hb] using hone)
        have hm : bs[j]∈bs.filter p := List.mem_filter.mpr
          ⟨List.getElem_mem (by simpa using hj),by simpa using hpj⟩
        exact False.elim (by simpa [ht] using hm)
    | succ i =>
      cases j with
      | zero =>
        have hb : p b=true := by simpa using hpj
        have ht : bs.filter p=[] := List.length_eq_zero.mp (by simpa [hb] using hone)
        have hm : bs[i]∈bs.filter p := List.mem_filter.mpr
          ⟨List.getElem_mem (by simpa using hi),by simpa using hpi⟩
        exact False.elim (by simpa [ht] using hm)
      | succ j =>
        by_cases hb : p b=true
        · have ht : bs.filter p=[] := List.length_eq_zero.mp (by simpa [hb] using hone)
          have hm : bs[i]∈bs.filter p := List.mem_filter.mpr
            ⟨List.getElem_mem (by simpa using hi),by simpa using hpi⟩
          exact False.elim (by simpa [ht] using hm)
        · have hh : (bs.filter p).length=1 := by simpa [hb] using hone
          exact congrArg Nat.succ (ih hh i j (by simpa using hi) (by simpa using hj)
            (by simpa using hpi) (by simpa using hpj))

theorem blockVector_mem {r : ℕ} {bs : List Block} (hlen : bs.length=r) (i : Fin r) :
    blockVector r bs i∈bs := by
  have hi : i.val<bs.length := by simpa only [hlen] using i.isLt
  simpa only [blockVector,List.getD_eq_getElem _ _ hi] using List.getElem_mem hi

theorem selected_long_position {r : ℕ} (bs : List Block) (hlen : bs.length=r)
    (lo hi : ℝ) (h : OneLong lo hi bs) :
    ∃ a : Fin r,hi<(lower (blockVector r bs a) : ℝ) ∧
      ∀ i : ShortIndex a,(lower (blockVector r bs i.val) : ℝ)<lo := by
  have hne : longBlocks hi bs≠[] := by
    intro hz
    have hh := h.2
    simp only [hz,List.length_nil] at hh
    omega
  obtain ⟨b,hb⟩ := List.exists_mem_of_ne_nil (longBlocks hi bs) hne
  obtain ⟨hbmem,hblong⟩ := List.mem_filter.mp hb
  obtain ⟨i,hiLen,hget⟩ := List.mem_iff_getElem.mp hbmem
  let a : Fin r := ⟨i,by simpa only [←hlen] using hiLen⟩
  have ha : hi<(lower (blockVector r bs a) : ℝ) := by
    simpa only [blockVector,a,List.getD_eq_getElem _ _ hiLen,hget,decide_eq_true_eq] using hblong
  refine ⟨a,ha,?_⟩
  intro q
  rcases noMedium_short_or_long h.1 (blockVector_mem hlen q.val) with hs | hl
  · exact hs
  · have hqLen : q.val.val<bs.length := by simpa only [hlen] using q.val.isLt
    have hai : (fun b : Block=>decide (hi<(lower b : ℝ))) bs[i]=true := by
      simpa only [blockVector,a,List.getD_eq_getElem _ _ hiLen,decide_eq_true_eq] using ha
    have hqi : (fun b : Block=>decide (hi<(lower b : ℝ))) bs[q.val.val]=true := by
      simpa only [blockVector,List.getD_eq_getElem _ _ hqLen,decide_eq_true_eq] using hl
    have eqi := unique_filter_index (fun b : Block=>decide (hi<(lower b : ℝ))) bs h.2
      i q.val.val hiLen hqLen hai hqi
    exact False.elim (q.property (Fin.ext eqi.symm))

theorem active_chart_geometry (kap : ℝ) (hk : kap<1) (B N cj : ℕ) (kap0 : ℝ)
    {r : ℕ} (bs : Fin r→Block)
    (hactive : ∃ n∈rectangle bs,integerProfile kap B N cj kap0 n≠0) :
    (N : ℝ)^(1-kap)/2≤R cj ∧ R cj≤4*(N : ℝ) := by
  obtain ⟨n,hn,hp⟩ := hactive
  have hR := R_pos cj
  have hs : scalarProfile kap B N cj kap0 (completeProduct n)≠0 := hp
  rw [scalarProfile_eq_ambient] at hs
  have hamb := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hs).1).1
  have hpsi := (mul_ne_zero_iff.mp hs).2
  have hsupport := ambient_support kap hk B N
    (fun _ : Fin 1=>(completeProduct n : ℝ)) hamb
  have hlow : (N : ℝ)^(1-kap)≤completeProduct n := hsupport.1 0
  have hhigh : (completeProduct n : ℝ)≤2*(N : ℝ) := by
    simpa only [Fin.prod_univ_one] using hsupport.2
  have hratio : (completeProduct n : ℝ)/R cj∈Icc (1/2 : ℝ) 2 := by
    constructor
    · by_contra h
      have hl : (completeProduct n : ℝ)/R cj<1/2 := lt_of_not_ge h
      apply hpsi
      rw [P5Z.ActualEtaPsiOccurrenceBudget.psi_eq_eta_difference,
        P5Z.ActualEtaPsiOccurrenceBudget.eta_zero (by linarith :
          2*((completeProduct n : ℝ)/R cj)≤1),
        P5Z.ActualEtaPsiOccurrenceBudget.eta_zero (by linarith :
          (completeProduct n : ℝ)/R cj≤1)]
      ring
    · by_contra h
      have hr : 2<(completeProduct n : ℝ)/R cj := lt_of_not_ge h
      apply hpsi
      rw [P5Z.ActualEtaPsiOccurrenceBudget.psi_eq_eta_difference,
        P5Z.ActualEtaPsiOccurrenceBudget.eta_one (by linarith :
          2≤2*((completeProduct n : ℝ)/R cj)),
        P5Z.ActualEtaPsiOccurrenceBudget.eta_one hr.le]
      ring
  have hh := (div_le_iff₀ hR).mp hratio.2
  have hl := (le_div_iff₀ hR).mp hratio.1
  constructor <;> nlinarith

theorem original_singleton_thresholds (zeta : ℝ) (cj : ℕ) :
    originalMediumLow zeta [cj]=(R cj)^(3*zeta) ∧
      originalMediumHigh zeta [cj]=(R cj)^(1/3+zeta/4 : ℝ) := by
  simp [originalMediumLow,originalMediumHigh,scales]

/-- A POSITION count, hence exactly five short factors at most. No
distinct-product quotient or factorial division is used here. -/
theorem actual_short_size_bound (kap : ℝ) (hk : kap<1) (N cj : ℕ) (kap0 zeta : ℝ)
    (hzeta : 0<zeta) (j : ℕ) (hj : j<3) (bs : List Block)
    (hlen : bs.length=2*(j+1))
    (hactive : ∃ n∈rectangle (blockVector (2*(j+1)) bs),integerProfile kap 6 N cj kap0 n≠0)
    (a : Fin (2*(j+1)))
    (hshort : ∀ i : ShortIndex a,
      (lower (blockVector (2*(j+1)) bs i.val) : ℝ)<originalMediumLow zeta [cj]) :
    (shortSize (blockVector (2*(j+1)) bs) a : ℝ)≤(4*(N : ℝ))^(15*zeta) := by
  have hR1 : 1≤R cj := by dsimp [R]; exact one_le_pow₀ (by norm_num) _
  have hRp : 0<R cj := R_pos cj
  have hA : 1≤(R cj)^(3*zeta) := Real.one_le_rpow hR1 (by positivity)
  have hcard : Fintype.card (ShortIndex a)≤5 := by rw [short_index_card]; omega
  have hp : (shortSize (blockVector (2*(j+1)) bs) a : ℝ)≤((R cj)^(3*zeta))^5 := by
    rw [shortSize,Nat.cast_prod]
    apply (Finset.prod_le_prod (fun i hi=>Nat.cast_nonneg _)
      (fun i hi=>((hshort i).trans_eq (original_singleton_thresholds zeta cj).1).le)).trans
    simpa only [Finset.prod_const,Finset.card_univ] using pow_le_pow_right₀ hA hcard
  have he : ((R cj)^(3*zeta))^5=(R cj)^(15*zeta) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hRp.le]
    congr 1
    ring
  rw [he] at hp
  exact hp.trans (Real.rpow_le_rpow hRp.le
    (active_chart_geometry kap hk 6 N cj kap0 _ hactive).2 (by positivity))

theorem original_cutoff_singleton (K cj : ℕ) :
    beforeHBCutoff K [cj]=roughF ((2 : ℝ)^(6*K+3)*R cj) := by
  unfold beforeHBCutoff chartCutoff argument scales
  simp only [List.map_cons,List.map_nil,List.length_cons,List.length_nil,
    List.prod_cons,List.prod_nil,mul_one,pow_one]
  congr 1
  rw [show 6*K+3=(6*K+2)+1 by omega,pow_succ]
  ring

theorem original_cutoff_nonneg (K cj : ℕ) : 0≤beforeHBCutoff K [cj] := by
  rw [original_cutoff_singleton]
  exact (Real.rpow_pos_of_pos (mul_pos (by positivity) (R_pos cj)) _).le

/-- There is ONE N threshold before cj, all block words, the selected
position and every short vector. It supplies the actual cutoff majorant
and the exclusion of a long real-truncated Mobius occurrence. -/
theorem eventually_original_cutoff_and_long_role
    (kap zeta : ℝ) (hk : kap<1) (hzeta : 0<zeta) (K : ℕ) :
    ∀ᶠ N : ℕ in atTop,∀ cj : ℕ,∀ (r : ℕ) (bs : Fin r→Block),
      (∃ n∈rectangle bs,integerProfile kap 6 N cj kap n≠0) →
      beforeHBCutoff K [cj]≤canonicalEnvelope N ∧
        hbCutoff cj<(R cj)^(1/3+zeta/4 : ℝ) := by
  have hlong : ∀ᶠ X : ℝ in atTop,
      0<X ∧ (2*X)^(1/3 : ℝ)<X^(1/3+zeta/4 : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      (_root_.tendsto_rpow_atTop (by positivity : 0<zeta/4)).eventually
        (eventually_gt_atTop ((2 : ℝ)^(1/3 : ℝ)))] with X hX hgap
    refine ⟨hX,?_⟩
    rw [Real.mul_rpow (by norm_num : (0 : ℝ)≤2) hX.le,Real.rpow_add hX]
    simpa only [mul_comm] using mul_lt_mul_of_pos_left hgap
      (Real.rpow_pos_of_pos hX (1/3 : ℝ))
  obtain ⟨X0,hX0⟩ := eventually_atTop.mp hlong
  let T : ℝ := max (max 1 X0) (Real.exp (Real.exp 3))
  let C : ℝ := (2 : ℝ)^(6*K+3)
  have hC : 1≤C := one_le_pow₀ (by norm_num) _
  have hCp : 0<C := zero_lt_one.trans_le hC
  have hgrowth : Tendsto (fun N : ℕ=>(N : ℝ)^(1-kap)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by linarith : 0<1-kap)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hgrowth.eventually (eventually_ge_atTop (2*T)),
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (max 2 (4*C))),
    tendsto_L2.eventually (eventually_ge_atTop (3 : ℝ))]
    with N hpow hN hL cj r bs hactive
  have hN2 : (2 : ℝ)≤N := (le_max_left _ _).trans hN
  have hN4 : 4*C≤(N : ℝ) := (le_max_right _ _).trans hN
  have hNp : (0 : ℝ)<N := by linarith
  have hgeometry := active_chart_geometry kap hk 6 N cj kap bs hactive
  have hRT : T≤R cj := by nlinarith [hgeometry.1]
  have hRX0 : X0≤R cj := (le_max_right 1 X0).trans ((le_max_left _ _).trans hRT)
  have hR := R_pos cj
  have hCR : R cj≤C*R cj := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hR.le
  have harg : Real.exp (Real.exp 3)≤C*R cj :=
    (le_max_right _ _).trans (hRT.trans hCR)
  have hargp : 0<C*R cj := mul_pos hCp hR
  have hargone : 1<C*R cj :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 3)).trans_le harg
  have hlogarg : Real.exp 3≤Real.log (C*R cj) :=
    (Real.le_log_iff_exp_le hargp).mpr harg
  have hLarg : 3≤Real.log (Real.log (C*R cj)) :=
    (Real.le_log_iff_exp_le (Real.log_pos hargone)).mpr hlogarg
  have hupper : C*R cj≤4*C*(N : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hgeometry.2 hCp.le]
  have hNupper : (N : ℝ)≤4*C*(N : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hC hNp.le]
  have hupperN2 : 4*C*(N : ℝ)≤(N : ℝ)^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hN4 hNp.le]
  constructor
  · rw [original_cutoff_singleton]
    apply (roughF_mono hargone hLarg hupper).trans
    simpa only [canonicalEnvelope,L2] using roughF_upper (by linarith : (1 : ℝ)<N)
      hL hNupper hupperN2
  · exact (hX0 (R cj) hRX0).2

end
end ImbalancedChen.P1OriginalSingletonOneLongGeometry
