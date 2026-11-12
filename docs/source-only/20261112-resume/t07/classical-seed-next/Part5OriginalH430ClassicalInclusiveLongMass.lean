import ImbalancedChen.Part5OriginalH430ClassicalSwitchedSmallPayment

/-! The full positive untested Γ9--21 price on every classical history
uses only the twenty existing nonunit integrals at the actual alpha.
This includes the two five/six-prime unit counts on the old source. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalInclusiveLongMass
noncomputable section
open Finset Real Wu2008DoubleSieve LiLiuPrereqBuchstab
open P2EnhancedSwitchedUnsiftedSource (labels unitWordMass unitWordMass_eq_product_count)
open P2EnhancedNonunitLabelGeometry (ordinaryNonunitWord label_prod_pos)
open P2EnhancedNonunitMarkedMass
open P2EnhancedSwitchedTrueNormalization (thetaConversion thetaPayload trueAlpha)
open P2EnhancedUnitSourceMass (thetaConversion_nonneg)
open P2OriginalChildPhysicalNormalization (thetaAtom Theta_eq_sum_atoms)
open P2SeedOmegaLiteralFibre (K)
open Part5OriginalH430FrozenRootRefinement Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430FrozenClassicalRootModuli Part5OriginalH430RequestedHistory
open Part5OriginalH430SeedHistoryMass Part5OriginalH430SeedPurifiedPrimeFibres (wordFibre)
open Part5OriginalH430OriginalRootQBound (original_root_Q_le_target)
open Part5OriginalH430ClassicalCausalSeedScale
open Part5OriginalH430ClassicalSmallSwitchedIntegers
open Part5OriginalH430ClassicalSwitchedSmallPayment
open scoped Classical BigOperators

def longFibre (tested : Bool) (N : ℕ) (Q : ℝ) (d : ℕ) : ℝ :=
  ∑ j : Fin 13,((secondFunctionalMotherGammaWords (9+j.val)).map (wordFibre tested N Q d)).sum

def longNonunitIntegral (α : ℝ) : ℝ :=
  ∑ j : Fin 13,((secondFunctionalMotherGammaWords (9+j.val)).map (fun cs => nonunitIntegral cs α)).sum

private theorem source_units {N n p dep : ℕ} {τ κ : ℝ} (hN : 2≤N)
    (ht : 0≤τ) (ht' : τ≤1/12) (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈classicalBand N)
    (l : LevelIndex N n .U3 τ p dep) (j : Fin 13) {cs qs : List ℕ}
    (hc : cs∈secondFunctionalMotherGammaWords (9+j.val))
    (hqs : qs∈labels N (rootQ N n .U3 τ p) (wordProduct l) cs) (hk : κ≤1/112) :
    let D := wordProduct l*qs.prod; let z := (qs.getD (qs.length-2) 0:ℝ)
    (1∈smallIntegers N D z (smallProduct N κ) ↔ D≤N) ∧
    largeIntegers N D z (smallProduct N κ) ⊆ (roughNumbers ((N:ℝ)/D) z).erase 1 := by
  let D := wordProduct l*qs.prod
  have hd := (actual_cubic_residual hN ht ht' hn hp l).1
  have hD : (0:ℝ)<D := Nat.cast_pos.mpr (Nat.mul_pos hd (label_prod_pos hqs))
  have hlo := every_original_unit_low hN ht ht' hn hp l j hc hqs hk
  dsimp only
  constructor
  · simp only [smallIntegers,mem_filter,one_mem_roughNumbers,Nat.mul_one,
      le_div_iff₀ hD,one_mul,Nat.cast_le]
    exact ⟨And.left,fun h => ⟨h,hlo⟩⟩
  · intro m hm
    obtain ⟨hr,hh⟩ := mem_filter.mp hm
    refine mem_erase.mpr ⟨?_,hr⟩
    rintro rfl
    rw [Nat.mul_one] at hh
    exact (not_lt_of_ge hlo) hh

/-- Direct comparison with the native original unit counter, including
its exact complete-product test. The prime-restricted unit is dominated
on the identical singleton by the separately paid tested small source. -/
theorem native_unit_le_small {N n p dep : ℕ} {τ κ : ℝ} (hN : 2≤N)
    (ht : 0≤τ) (ht' : τ≤1/12) (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈classicalBand N)
    (l : LevelIndex N n .U3 τ p dep) (j : Fin 13) {cs : List ℕ}
    (hc : cs∈secondFunctionalMotherGammaWords (9+j.val)) (hk : κ≤1/112) :
    let d := wordProduct l; let Q := rootQ N n .U3 τ p
    unitWordMass N Q d cs≤smallWord false N Q d cs (smallProduct N κ) := by
  let Q := rootQ N n .U3 τ p
  let d := wordProduct l
  have hd := (actual_cubic_residual hN ht ht' hn hp l).1
  dsimp only
  rw [unitWordMass_eq_product_count hd]
  have hcard : (((labels N Q d cs).filter (fun qs => d*qs.prod≤N)).card:ℝ)=
      ∑ qs∈labels N Q d cs,if d*qs.prod≤N then (1:ℝ) else 0 := by
    rw [←sum_filter]; simp
  rw [hcard]
  unfold smallWord
  apply sum_le_sum
  intro qs hqs
  simp only [testWeight,Bool.false_eq_true,if_false,sum_const,nsmul_eq_mul,mul_one]
  by_cases hcap : d*qs.prod≤N
  · rw [if_pos hcap]
    have hone := (source_units hN ht ht' hn hp l j hc hqs hk).1.mpr hcap
    exact_mod_cast (Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨1,hone⟩))
  · rw [if_neg hcap]
    positivity

theorem classical_large_le_nonunit {N n p dep : ℕ} {τ κ : ℝ} (hN : 2≤N)
    (ht : 0≤τ) (ht' : τ≤1/12) (hn : 1/((n:ℝ)+1)≤11/384) (hp : p∈classicalBand N)
    (l : LevelIndex N n .U3 τ p dep) (j : Fin 13) {cs : List ℕ}
    (hc : cs∈secondFunctionalMotherGammaWords (9+j.val)) (hk : κ≤1/112) :
    largeWord false N (rootQ N n .U3 τ p) (wordProduct l) cs (smallProduct N κ)≤
      ordinaryNonunitWord N (rootQ N n .U3 τ p) (wordProduct l) cs := by
  apply sum_le_sum
  intro qs hqs
  have hs := (source_units hN ht ht' hn hp l j hc hqs hk).2
  have hh := (Nat.cast_le (α:=ℝ)).mpr (card_le_card hs)
  simpa [testWeight] using hh

/-- One threshold for all original source primes, causal generations
and selections, including the positive clamp subfamily. The multiplier
on BOTH integrals and integer masses is the unchanged K/4. -/
theorem classical_inclusive_long_cost {ε : ℝ} (he : 0<ε) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → ∀ (n : ℕ) (τ : ℝ) (p dep : ℕ),
      0≤τ → τ≤1/12 → 1/((n:ℝ)+1)≤11/384 → p∈classicalBand N →
      ∀ B : Finset (LevelIndex N n .U3 τ p dep),
      let Q := rootQ N n .U3 τ p
      (∑ l∈B,levelMark l*((K/4)*thetaConversion N (wordProduct l)*longFibre false N Q (wordProduct l)))≤
        (∑ l∈B,levelMark l*((K/4)*thetaAtom N Q (wordProduct l)*longNonunitIntegral (trueAlpha N Q (wordProduct l))))+
          ε*markedTheta B := by
  have hK : 0<K/4 := by norm_num [K]
  let δ := (ε/2)/(K/4)
  have hδ : 0<δ := div_pos (half_pos he) hK
  obtain ⟨Ta,h4,ha⟩ := small_both_atoms (κ:=1/112) (by norm_num) (half_pos he)
  obtain ⟨Tb,_,hb⟩ := original_Gamma9_to_21_theta_upper frozenResidualFloor_pos hδ
  refine ⟨max Ta Tb,h4.trans (le_max_left _ _),?_⟩
  intro N hN n τ p dep ht ht' hn hp B
  let Q := rootQ N n .U3 τ p
  let X := smallProduct N (1/112)
  have haN := (le_max_left Ta Tb).trans hN
  have hbN := (le_max_right Ta Tb).trans hN
  have hN4 := h4.trans haN
  have h2 : 2≤N := by omega
  have hQ := original_root_Q_le_target N n .U3 τ p h2 ht ht' (mem_filter.mp hp).1
  have hrow (l : LevelIndex N n .U3 τ p dep) :
      (K/4)*thetaConversion N (wordProduct l)*longFibre false N Q (wordProduct l)≤
        (K/4)*thetaAtom N Q (wordProduct l)*longNonunitIntegral (trueAlpha N Q (wordProduct l))+
        ε*thetaAtom N Q (wordProduct l) := by
    let d := wordProduct l
    obtain ⟨hd,hR,hscale,hα,_⟩ := actual_cubic_residual h2 ht ht' hn hp l
    have hconv := thetaConversion_nonneg hN4 hd hR
    have hsmall := (ha N haN Q d hd hQ hscale).2
    let J := ∑ j : Fin 13,((secondFunctionalMotherGammaWords (9+j.val)).map (ordinaryNonunitWord N Q d)).sum
    have hnon : allLarge false N Q d X≤J :=
      sum_le_sum (fun j _ => secondFunctionalMother_list_sum_mono _ _ _
        (fun cs hc => classical_large_le_nonunit h2 ht ht' hn hp l j hc le_rfl))
    have hcost := hb N hbN Q ({d}:Finset ℕ) (fun _ => (1:ℝ))
      (fun x hx => (mem_singleton.mp hx).symm ▸ hd) (fun _ _ => zero_le_one)
      (fun x hx => (mem_singleton.mp hx).symm ▸ hscale)
      (fun x hx => (mem_singleton.mp hx).symm ▸ (show (2:ℝ)≤trueAlpha N Q d by linarith only [hα]))
    simp only [convertedOriginalSwitches,originalIntegralSwitches,convertedWord,thetaPayload,
      Theta_eq_sum_atoms,sum_singleton,one_mul,List.sum_map_mul_left,←mul_sum] at hcost
    change thetaConversion N d*J≤thetaAtom N Q d*longNonunitIntegral (trueAlpha N Q d)+δ*thetaAtom N Q d at hcost
    have hlarge := (mul_le_mul_of_nonneg_left hnon hconv).trans hcost
    have hlarge' := mul_le_mul_of_nonneg_left hlarge hK.le
    have hδK : (K/4)*δ=ε/2 := by dsimp [δ]; field_simp [hK.ne']
    have hparts := all_parts false N Q d X
    change longFibre false N Q d=allSmall false N Q d X+allLarge false N Q d X at hparts
    change (K/4)*thetaConversion N d*longFibre false N Q d≤_
    rw [hparts,mul_add]
    calc
      _ ≤ (ε/2)*thetaAtom N Q d+(K/4)*(thetaAtom N Q d*longNonunitIntegral (trueAlpha N Q d)+δ*thetaAtom N Q d) :=
        add_le_add hsmall (by simpa only [mul_assoc] using hlarge')
      _ = _ := by rw [mul_add,←mul_assoc (K/4) δ,hδK]; ring
  dsimp only
  unfold markedTheta
  rw [mul_sum,←sum_add_distrib]
  apply sum_le_sum
  intro l _
  convert mul_le_mul_of_nonneg_left (hrow l) (mark_pos (levelOccurrence l)).le using 1 <;> ring

end
end ImbalancedChen.Part5OriginalH430ClassicalInclusiveLongMass
