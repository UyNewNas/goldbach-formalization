import ImbalancedChen.P2GammaU5PlateauGeometry

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
An actual positive reciprocal-mass witness for the original U5 constant
root fibre. The target-deleted prime box theorem supplies its mass limit;
no nonempty-family, prime-count or mass lower bound is a caller input.
The conservative 1/4 comparison is between p*q and (p-1)*(q-1), NOT a
replacement of the physical singular-series normalizer.
-/
namespace ImbalancedChen.P2GammaU5PlateauMass
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2GammaU5PlateauGeometry P2GammaSelectedPhysicalTheta
open P2GammaSelectedRelativeLogSaving P2GammaRootFiberRelative
open P5OriginalU5CausalFinite (pairSupport)
open MathlibNt.SieveTheory.SingularSeries

/-- Positive limit of the EXISTING target-deleted reciprocal-(p-1) box. -/
def boxLimit : ℝ := Real.log (11/10 : ℝ)*Real.log (13/12 : ℝ)

/-- Half of the limiting box mass, followed by the finite factor 1/4. -/
def massFloor : ℝ := boxLimit/8

theorem boxLimit_pos : 0 < boxLimit :=
  mul_pos (Real.log_pos (by norm_num : (1 : ℝ) < 11/10))
    (Real.log_pos (by norm_num : (1 : ℝ) < 13/12))

theorem massFloor_pos : 0 < massFloor := div_pos boxLimit_pos (by norm_num)

theorem tendsto_plateau_box_mass :
    Tendsto (fun N : ℕ => actualPrimeBoxMass N boxLo boxHi) atTop (𝓝 boxLimit) := by
  have h := tendsto_actualPrimeBoxMass boxLo boxHi
    (by intro i; fin_cases i <;> norm_num [boxLo])
    (by intro i; fin_cases i <;> norm_num [boxLo,boxHi])
  simpa only [Fin.prod_univ_two,boxLo,boxHi,Matrix.cons_val_zero,
    Matrix.cons_val_one,show (11/100 : ℝ)/(1/10)=11/10 by norm_num,
    show (13/100 : ℝ)/(3/25)=13/12 by norm_num,boxLimit] using h

/-- A finite pointwise bound, valid for every pair of primes, including 2.
No asymptotic replacement of reciprocal weights is needed. -/
private theorem reciprocal_product_lower (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    (1/4 : ℝ)*(1/((p : ℝ)-1)* (1/((q : ℝ)-1))) ≤
      1/((p*q : ℕ) : ℝ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ)-1 := by linarith
  have hq1 : (0 : ℝ) < (q : ℝ)-1 := by linarith
  have hden : (p : ℝ)*(q : ℝ) ≤ 4*((p : ℝ)-1)*((q : ℝ)-1) := by
    have h := mul_le_mul (show (p : ℝ) ≤ 2*((p : ℝ)-1) by linarith)
      (show (q : ℝ) ≤ 2*((q : ℝ)-1) by linarith) hq0.le (by positivity)
    nlinarith
  calc
    _ = 1/(4*((p : ℝ)-1)*((q : ℝ)-1)) := by
      field_simp [hp1.ne',hq1.ne'] <;> ring
    _ ≤ 1/((p : ℝ)*(q : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) (mul_pos hp0 hq0) hden
    _ = _ := by rw [Nat.cast_mul]

/-- Injectivity is only the TWO-COORDINATE encoding, not the product map. -/
theorem rectangle_mass_ge_quarter_box (N : ℕ) :
    (1/4 : ℝ)*actualPrimeBoxMass N boxLo boxHi ≤
      reciprocalMass (rectangle N) (fun _ => 1) := by
  have hinj : Set.InjOn (fun p : Fin 2 → ℕ => (p 0,p 1))
      (actualPrimeBoxTuples N boxLo boxHi) := by
    intro p hp q hq heq
    funext i
    fin_cases i
    · exact congrArg Prod.fst heq
    · exact congrArg Prod.snd heq
  rw [reciprocalMass,rectangle,Finset.sum_image hinj]
  unfold actualPrimeBoxMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  simp only [Fin.prod_univ_two]
  exact reciprocal_product_lower (p 0) (p 1)
    (mem_actualPrimeBoxTuples_iff.mp hp 0).1
    (mem_actualPrimeBoxTuples_iff.mp hp 1).1

/-- The positive constant and the arithmetic family are both supplied.
No caller harmonic-mass input, enumeration or finite proof guard is used. -/
theorem eventually_rectangle_mass_floor :
    ∀ᶠ N : ℕ in atTop,massFloor ≤ reciprocalMass (rectangle N) (fun _ => 1) := by
  have hlarge := tendsto_plateau_box_mass.eventually
    (gt_mem_nhds (show boxLimit/2 < boxLimit by linarith [boxLimit_pos]))
  filter_upwards [hlarge] with N hN
  calc
    massFloor = (1/4 : ℝ)*(boxLimit/2) := by unfold massFloor; ring
    _ ≤ (1/4 : ℝ)*actualPrimeBoxMass N boxLo boxHi :=
      mul_le_mul_of_nonneg_left hN.le (by norm_num)
    _ ≤ _ := rectangle_mass_ge_quarter_box N

/-- The whole same-root fibre is genuinely nondegenerate. The witness
rectangle retains target exclusion and is contained in the original U5. -/
theorem eventually_plateau_mass_floor :
    ∀ᶠ N : ℕ in atTop,massFloor ≤ reciprocalMass (plateauFiber N) (fun _ => 1) := by
  filter_upwards [eventually_rectangle_mass_floor,eventually_ge_atTop (2 : ℕ)]
    with N hm hN
  exact hm.trans (Finset.sum_le_sum_of_subset_of_nonneg
    (rectangle_subset_plateauFiber hN) (fun t ht hnot => by positivity))

theorem eventually_plateau_nonempty :
    ∀ᶠ N : ℕ in atTop,(plateauFiber N).Nonempty := by
  filter_upwards [eventually_plateau_mass_floor] with N hm
  by_contra hn
  have he : plateauFiber N = ∅ :=
    Finset.eq_empty_iff_forall_not_mem.mpr (fun t ht => hn ⟨t,ht⟩)
  have hm0 : massFloor ≤ 0 := by simpa only [he,reciprocalMass,Finset.sum_empty] using hm
  exact (not_le_of_gt massFloor_pos) hm0

/-- A stable extension to genuine selected weights. This premise is only
pointwise domination of a CONCRETE arithmetic rectangle, not an analytic
mass licence. The next corollary supplies it for constant weight. -/
theorem eventually_plateau_dominated_mass (fraction : ℝ) (hf : 0 ≤ fraction) :
    ∀ᶠ N : ℕ in atTop,∀ height : ℝ,0 ≤ height → ∀ sigma : Pair → ℝ,
      (∀ t ∈ plateauFiber N,0 ≤ sigma t) →
      (∀ t ∈ rectangle N,fraction*height ≤ sigma t) →
      (fraction*massFloor)*height ≤ reciprocalMass (plateauFiber N) sigma := by
  filter_upwards [eventually_rectangle_mass_floor,eventually_ge_atTop (2 : ℕ)]
    with N hm hN
  intro height hh sigma hs hrect
  calc
    _ = fraction*height*massFloor := by ring
    _ ≤ fraction*height*reciprocalMass (rectangle N) (fun _ => 1) :=
      mul_le_mul_of_nonneg_left hm (mul_nonneg hf hh)
    _ ≤ _ := reciprocalMass_of_subfamily (rectangle_subset_plateauFiber hN)
      sigma hs fraction height hrect

/-- ALL later amplitudes, including arbitrarily small positive values.
There is no family mass hypothesis and no fixed-before-N amplitude. -/
theorem eventually_plateau_constant_mass :
    ∀ᶠ N : ℕ in atTop,∀ height : ℝ,0 ≤ height →
      massFloor*height ≤ reciprocalMass (plateauFiber N) (fun _ => height) := by
  filter_upwards [eventually_plateau_dominated_mass 1 (by norm_num)] with N hN
  intro height hh
  simpa only [one_mul] using hN height hh (fun _ => height)
    (fun _ _ => hh) (fun _ _ => by simp)

/-- A true lower bound for the existing physical Theta, not a new
normalizer and not mere positivity. The original singular factor stays. -/
theorem eventually_plateau_Theta_lower :
    ∀ᶠ N : ℕ in atTop,∀ height : ℝ,0 ≤ height →
      (2*liuUniversalProduct*massFloor)*height*(N : ℝ)/(Real.log (N : ℝ))^2 ≤
        selectedTheta N (plateauQ N) (plateauFiber N) (fun _ => height) := by
  filter_upwards [eventually_plateau_constant_mass,eventually_ge_atTop (4 : ℕ)]
    with N hm hN
  intro height hh
  have hU := liuUniversalProduct_pos
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  calc
    _ = (2*liuUniversalProduct*(N : ℝ)/(Real.log (N : ℝ))^2)*(massFloor*height) := by ring
    _ ≤ (2*liuUniversalProduct*(N : ℝ)/(Real.log (N : ℝ))^2)*
        reciprocalMass (plateauFiber N) (fun _ => height) :=
      mul_le_mul_of_nonneg_left (hm height hh) (by positivity)
    _ ≤ _ := selectedTheta_lower hN (plateauQ N) (plateauFiber N) (fun _ => height)
      (rootFiber_subset N (plateauQ N) (fun _ => True)) (fun _ _ => hh)
      (fun _ ht => (rootFiber_data ht).2.2.2)

theorem eventually_plateau_Theta_pos :
    ∀ᶠ N : ℕ in atTop,∀ height : ℝ,0 < height →
      0 < selectedTheta N (plateauQ N) (plateauFiber N) (fun _ => height) := by
  filter_upwards [eventually_plateau_Theta_lower,eventually_ge_atTop (4 : ℕ)]
    with N hlow hN
  intro height hh
  have hU := liuUniversalProduct_pos
  have hmass := massFloor_pos
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  exact (by positivity : 0 < (2*liuUniversalProduct*massFloor)*height*
    (N : ℝ)/(Real.log (N : ℝ))^2).trans_le (hlow height hh.le)

end
end ImbalancedChen.P2GammaU5PlateauMass
