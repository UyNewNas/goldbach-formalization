import ImbalancedChen.P5ActualLabelledPrimeSmoothCharts

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT.
-- Original prime chart -> actual nonzero rough HB group witnesses.
-- The strict prime>Z input is explicit: selected-W source bands and
-- the proved subpower envelope supply it in the selected-W bridge.
namespace ImbalancedChen.P5Z.OriginalPrimeChartHBWitnesses
noncomputable section
open Classical Filter
open scoped BigOperators
open ImbalancedChen.Part3
open LiteralHeathBrownOccurrenceWords ActualRoughHeathBrownWords
open HBRightClosedDyadicRoles ActualHBDyadicOccurrenceFamily
open ActualHBDyadicProductWindow ActualHBMediumBranchPartition
open SmoothChartHBDyadicPartition SmoothChartPhysicalHBBranch
open ActualMultiGroupHBChartScale OriginalChartRoughCutoff
open ExactOriginalSmoothDyadicPartition ActualLabelledPrimeSmoothCharts

theorem eventually_subpower_envelope (delta : ℝ) (hd : 0 < delta) :
    ∀ᶠ x : ℝ in atTop, 1 < x ∧
      x^(2/(Real.log (Real.log x))^3) ≤ x^delta := by
  have hell := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (max 1 (2/delta)))
  filter_upwards [hell,eventually_gt_atTop (1 : ℝ)] with x hl hx
  have h1 : 1 ≤ Real.log (Real.log x) := (le_max_left _ _).trans hl
  have hdell : 2/delta ≤ Real.log (Real.log x) := (le_max_right _ _).trans hl
  have hp : 0 < Real.log (Real.log x) := by linarith
  have hcubic : Real.log (Real.log x) ≤ (Real.log (Real.log x))^3 := by
    have hpow : (1 : ℝ) ≤ (Real.log (Real.log x))^2 := one_le_pow₀ h1
    have hh := mul_le_mul_of_nonneg_right hpow hp.le
    nlinarith
  have hlarge : 2 ≤ delta*(Real.log (Real.log x))^3 := by
    have hh := (div_le_iff₀ hd).mp (hdell.trans hcubic)
    nlinarith
  have he : 2/(Real.log (Real.log x))^3 ≤ delta :=
    (div_le_iff₀ (pow_pos hp 3)).mpr hlarge
  exact ⟨hx,Real.rpow_le_rpow_of_exponent_le hx.le he⟩

theorem prime_rough_one {z : ℝ} {p : ℕ} (hp : p.Prime) (hzp : z < (p : ℝ)) :
    roughOneSlot z p = 1 := by
  unfold roughOneSlot
  apply if_pos
  intro ell hell hdiv
  have he : ell = p := (Nat.dvd_prime_two_le hp hell.two_le).mp hdiv
  simpa only [he] using hzp

-- The cap 2^(chartj+1), rough z and real cube are fixed from the chart,
-- before the HB order and any factor tuple. No nonzero HB term is input.
theorem prime_active_HB_group (chi : ℝ → ℝ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (chartj p : ℕ) (hp : p.Prime) {z : ℝ} (hz : 0 ≤ z)
    (hzp : z < (p : ℝ)) (hpsi : psi chi ((p : ℝ)/R chartj) ≠ 0) :
    ∃ g : Group, g.R = R chartj ∧ g.n = p ∧ g.z = z := by
  let y : ℝ := (2*R chartj)^(1/3 : ℝ)
  let N : ℕ := 2^(chartj+1)
  have hR := R_pos chartj
  have hbase : 0 < 2*R chartj := by positivity
  have hy : 0 ≤ y := (Real.rpow_pos_of_pos hbase (1/3 : ℝ)).le
  have hcube : y^3 = 2*R chartj := by
    dsimp [y]
    rw [← Real.rpow_natCast,← Real.rpow_mul hbase.le]
    norm_num
  have hquot : (p : ℝ)/R chartj ≤ 2 := by
    apply le_of_not_gt
    intro h
    exact hpsi (psi_right chi hzero _ h)
  have hpcube : (p : ℝ) ≤ y^3 := by
    rw [hcube]
    exact (div_le_iff₀ hR).mp hquot
  have hNcast : (N : ℝ) = 2*R chartj := by
    dsimp [N,R]
    push_cast
    rw [pow_succ]
    ring
  have hpN : p ≤ N := by
    have hh : (p : ℝ) ≤ (N : ℝ) := by rw [hNcast]; exact (div_le_iff₀ hR).mp hquot
    exact_mod_cast hh
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hsource : ((ArithmeticFunction.vonMangoldt p : ℝ) : ℂ)*roughOneSlot z p ≠ 0 := by
    rw [prime_rough_one hp hzp,mul_one,ArithmeticFunction.vonMangoldt_apply_prime hp]
    exact_mod_cast hlog.ne'
  have hex : ∃ j ∈ Finset.range 3, ∃ bs ∈ blockWords N (2*(j+1)),
      blockCoefficient z y j p bs ≠ 0 := by
    by_contra hnot
    apply hsource
    rw [fixed_bank_HB hz hy N hpN hpcube]
    apply Finset.sum_eq_zero
    intro j hj
    have hblocks : (∑ bs ∈ blockWords N (2*(j+1)), blockCoefficient z y j p bs) = 0 := by
      apply Finset.sum_eq_zero
      intro bs hbs
      by_contra hne
      exact hnot ⟨j,hj,bs,hbs,hne⟩
    rw [hblocks,mul_zero]
  obtain ⟨j,hj,bs,hbs,hbc⟩ := hex
  let g : Group := {
    psi := psi chi, R := R chartj, z := z, y := y, j := j, n := p, bs := bs,
    w := fun _ => 1, positive := hR, rough_nonneg := hz,
    hb_nonneg := hy, hb_cube := hcube,
    lower_support := psi_left chi hone, upper_support := psi_right chi hzero,
    order := hj,
    active := by simpa only [chartWeight,mul_one] using mul_ne_zero hpsi hbc }
  exact ⟨g,rfl,rfl,rfl⟩

theorem profile_to_HB_groups (chi : ℝ → ℝ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0) {z : ℝ} (hz : 0 ≤ z) :
    ∀ js ps : List ℕ, tupleProfile chi js ps ≠ 0 →
      (∀ p ∈ ps, p.Prime) → (∀ p ∈ ps, z < (p : ℝ)) →
      ∃ gs : List Group, gs.map Group.R = scales js ∧ gs.map Group.n = ps ∧
        ∀ g ∈ gs, g.z = z := by
  intro js
  induction js with
  | nil =>
    intro ps hn hp hr
    cases ps with
    | nil => exact ⟨[],rfl,rfl,by simp⟩
    | cons p ps => simp [tupleProfile] at hn
  | cons chartj js ih =>
    intro ps hn hp hr
    cases ps with
    | nil => simp [tupleProfile] at hn
    | cons p ps =>
      have hh := mul_ne_zero_iff.mp hn
      obtain ⟨g,hR,hnp,hz⟩ := prime_active_HB_group chi hone hzero chartj p
        (hp p (by simp)) hz (hr p (by simp)) hh.1
      obtain ⟨gs,hRs,hns,hzs⟩ := ih ps hh.2
        (fun q hq => hp q (List.mem_cons_of_mem p hq))
        (fun q hq => hr q (List.mem_cons_of_mem p hq))
      refine ⟨g::gs,?_,?_,?_⟩
      · simp only [List.map_cons,hR,hRs,scales,List.map_cons]
      · simp only [List.map_cons,hnp,hns]
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hz
        · exact hzs b hb

theorem chartN_eq_product (gs : List Group) : chartN gs = ((gs.map Group.n).prod : ℝ) := by
  induction gs with
  | nil => simp [chartN]
  | cons g gs ih => simp only [chartN,List.map_cons,List.prod_cons,Nat.cast_mul,ih]

-- The external W mark is kept ONCE, on the same original ps. Actual HB
-- groups only factor the Lambda sources. eta's nonzero value and trim
-- transfer by exact equality chartN(gs)=prod(ps), never by a new gate.
theorem active_prime_chart_to_HB
    (chi eta : ℝ → ℝ) (W : List ℕ → ℂ)
    (hone : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hzero : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (heta : ∀ t : ℝ, t ≤ 1 → eta t = 0)
    (cap k K : ℕ) {T kappa0 c astar C : ℝ} (hT : 0 < T)
    (hW : ∀ ps ∈ primeTuples cap k, W ps ≠ 0 →
      (∀ p ∈ ps, c*T^astar ≤ (p : ℝ)) ∧ (ps.prod : ℝ) ≤ C*T)
    {js ps : List ℕ} (hjs : js ∈ chartBank cap k) (hps : ps ∈ primeTuples cap k)
    (hactive : chartTerm chi eta W T kappa0 js ps ≠ 0)
    (hz : 0 ≤ beforeHBCutoff K js)
    (hprimeRough : ∀ p ∈ ps, beforeHBCutoff K js < (p : ℝ)) :
    ∃ gs : List Group, gs.map Group.R = scales js ∧ gs.map Group.n = ps ∧
      (∀ g ∈ gs, g.z = beforeHBCutoff K js ∧ g.j ∈ Finset.range 3 ∧
        blockCoefficient g.z g.y g.j g.n g.bs ≠ 0) ∧
      eta ((ps.prod : ℝ)/T^(1-kappa0)) ≠ 0 ∧ W ps ≠ 0 ∧
      T^(1-kappa0) < chartN gs ∧ chartN gs ≤ C*T ∧
      (∀ g ∈ gs, c*T^astar ≤ (g.n : ℝ)) ∧
      (∀ (left right : List Block) (b : Block), blocks gs = left++b::right →
        ∃ pl p pr, integers gs = pl++p::pr ∧
          List.Forall₂ Owns left pl ∧ Owns b p ∧ List.Forall₂ Owns right pr ∧
          let x : ℝ := (lower b : ℝ)*(lower (owner (pl++pr).prod) : ℝ)
          rawProduct (blocks gs)/2 ≤ x) := by
  obtain ⟨hjlen,hplen,hsupport,hetaNe,hWne,htrim,hindividual,hupper⟩ :=
    active_original_chart_support chi eta W hone hzero heta cap k hT hW hjs hps hactive
  have hprofile := (mul_ne_zero_iff.mp hactive).1
  have hprimes := (primeTuples_spec cap k hps).2
  obtain ⟨gs,hRs,hns,hzs⟩ := profile_to_HB_groups chi hone hzero hz js ps hprofile
    (fun p hp => (hprimes p hp).1) hprimeRough
  have hN : chartN gs = (ps.prod : ℝ) := by rw [chartN_eq_product,hns]
  refine ⟨gs,hRs,hns,?_,hetaNe,hWne,by simpa only [hN] using htrim,
    by simpa only [hN] using hupper,?_,?_⟩
  · intro g hg
    exact ⟨hzs g hg,g.order,(mul_ne_zero_iff.mp g.active).2⟩
  · intro g hg
    apply hindividual g.n
    rw [← hns]
    exact List.mem_map.mpr ⟨g,hg,rfl⟩
  · exact grouped_scale_half_raw gs

end
end ImbalancedChen.P5Z.OriginalPrimeChartHBWitnesses
