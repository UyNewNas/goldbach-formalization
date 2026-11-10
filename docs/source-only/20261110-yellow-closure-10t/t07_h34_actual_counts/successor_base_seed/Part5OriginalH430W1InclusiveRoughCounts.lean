import ImbalancedChen.Part5OriginalH430W1ConvertedPrimeQuadrature
import MathlibNt.Wu2008DoubleSieve.InclusiveRoughUniform

/-! The actual unsifted W1 integer family, including quotient one, at the
real same-Q height N/(B q1 q2 q3) and middle-prime cutoff. -/
namespace ImbalancedChen.Part5OriginalH430W1InclusiveRoughCounts
noncomputable section
open Set MeasureTheory Filter Real Finset Wu2008DoubleSieve LiLiuPrereqBuchstab
open P5OriginalActionMassBound (W1Target W1Anchor)
open P2OriginalBankChildPrimeMass P2OriginalHalfOpenProfileCarrier
open P2OriginalPositiveSameQMassLift P2OriginalChildPhysicalNormalization
open P2EnhancedSwitchedTrueNormalization (trueAlpha thetaConversion rawMainAtom rawMainAtom_to_thetaAtom)
open P2EnhancedNonunitWordMass (rawScale)
open P2SeedOmegaLiteralFibre (omegaCap)
open P2N48TiedMomentPrimitives (moment11)
open Part5OriginalH430W1ConvertedPrimeQuadrature
open Part5OriginalH430W1SwitchedBuchstabIntegral (argument argument_lower cap_on_cube envelope)
open scoped Classical BigOperators Topology

def height (N d : ℕ) (q : Fin 3 → ℕ) : ℝ := (N:ℝ)/((d*q 0*q 1*q 2:ℕ):ℝ)

def mass (N : ℕ) (L : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10) : ℝ :=
  ∑ q∈actualPrimeBoxTuples N (fun _ : Fin 3 => L/10) (fun _ => 3*L/5),
    if normalizedLog N L q∈chamber (1/W1Anchor j) (1/W1Target i) ∧ ∀ a,(q a).Coprime (d*N)
    then ((roughNumbers (height N d q) (q 1:ℝ)).card:ℝ) else 0

private theorem log_height {N d : ℕ} {Q L : ℝ} (hN : 1<N) (hd : 0<d) (hL : 0<L)
    (hQ : Q=(d:ℝ)*(N:ℝ)^L) (q : Fin 3 → ℕ) (hp : ∀ a,0<q a) (hv : 1<q 1) :
    log (height N d q)/log (q 1:ℝ) =
      argument (trueAlpha N Q d) (normalizedLog N L q 0,(normalizedLog N L q 1,normalizedLog N L q 2)) := by
  have hR := sameQ_residual_gt_one hN hd hL hQ
  have ht : ∀ a,normalizedLog N L q a=log (q a:ℝ)/log (Q/d) := by
    intro a; rw [hQ]; exact (physical_log_ratio hN hd hL q a).symm
  have hN' : (N:ℝ)≠0 := (Nat.cast_pos.mpr (show 0<N by omega)).ne'
  have hd' := (Nat.cast_pos.mpr hd : (0:ℝ)<d).ne'
  have hp' (a : Fin 3) := (Nat.cast_pos.mpr (hp a) : (0:ℝ)<q a).ne'
  have hR' := (log_pos hR).ne'
  have hv' := (log_pos (show (1:ℝ)<q 1 by exact_mod_cast hv)).ne'
  unfold argument trueAlpha height
  push_cast
  simp only [ht,log_div hN' hd',log_div hN' (mul_ne_zero (mul_ne_zero (mul_ne_zero hd' (hp' 0))
    (hp' 1)) (hp' 2)),log_mul (mul_ne_zero (mul_ne_zero hd' (hp' 0)) (hp' 1)) (hp' 2),
    log_mul (mul_ne_zero hd' (hp' 0)) (hp' 1),log_mul hd' (hp' 0)]
  field_simp [hR',hv']; ring

private theorem eventual_units {η τ : ℝ} (hη : 0<η) (hτ : 0<τ) :
    ∃ T : ℕ,∀ N : ℕ,T≤N → ∀ y : ℝ,(N:ℝ)^η≤y → log y/y≤τ := by
  have hh := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero
  have ev : ∀ᶠ y : ℝ in atTop,log y/y<τ := by simpa using hh.eventually (gt_mem_nhds hτ)
  obtain ⟨A,hA⟩ := eventually_atTop.mp ev
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop A)
  exact ⟨T,fun N hN y hy => (hA _ ((hT N hN).trans hy)).le⟩

theorem mass_to_prime_sum {η τ : ℝ} (hη : 0<η) (hτ : 0<τ) :
    ∃ T : ℕ,4≤T ∧ ∀ N : ℕ,T≤N → ∀ (Q L : ℝ) (d : ℕ) (i : Fin 7) (j : Fin 10),
      η≤L → 0<d → Q=(d:ℝ)*(N:ℝ)^L → 2≤trueAlpha N Q d →
      mass N L d i j ≤ rawScale N Q d*(omegaCap+2*τ)*
        scaledPrimeSum N L (chamber (1/W1Anchor j) (1/W1Target i)) test := by
  have hη' : 0<η/10 := by positivity
  obtain ⟨Ta,hTa,ha⟩ := InclusiveRoughUniform.uniform_upper hη' hτ
  obtain ⟨Tb,hb⟩ := eventual_units hη' hτ
  refine ⟨max Ta Tb,hTa.trans (le_max_left _ _),?_⟩
  intro N hN Q L d i j hL hd hQ hα
  have hNa := (le_max_left _ _).trans hN
  have hNb := (le_max_right _ _).trans hN
  have h4 := hTa.trans hNa
  have hN' : 1<N := by omega
  have hNr : (1:ℝ)<N := by exact_mod_cast hN'
  have hL' := hη.trans_le hL
  have hR := sameQ_residual_gt_one hN' hd hL' hQ
  have hscale : 0≤rawScale N Q d := div_nonneg (Nat.cast_nonneg N)
    (mul_nonneg (Nat.cast_nonneg d) (log_pos hR).le)
  have hconst := P2SeedOmegaGlobalEnvelope.omegaCap_positive
  have hC : 0≤rawScale N Q d*(omegaCap+2*τ) := mul_nonneg hscale (by positivity)
  unfold mass scaledPrimeSum actualPrimeBoxTestSum
  rw [mul_sum]
  apply sum_le_sum
  intro q hq
  let u := normalizedLog N L q
  let x := height N d q
  let y : ℝ := q 1
  have hp (a : Fin 3) := mem_actualPrimeBoxTuples_iff.mp hq a
  have hpos (a : Fin 3) := (hp a).1.pos
  have hge (a : Fin 3) : (2:ℝ)≤q a := by exact_mod_cast (hp a).1.two_le
  have hw := actualPrimeBoxWeight_nonneg hq
  have ht0 : 0≤test u := one_div_nonneg.mpr ((by norm_num : (0:ℝ)≤1/10).trans (le_max_left _ _))
  by_cases hm : u∈chamber (1/W1Anchor j) (1/W1Target i)
  · rw [indicator_of_mem hm]
    by_cases hcop : ∀ a,(q a).Coprime (d*N)
    · rw [if_pos ⟨hm,hcop⟩]
      have ha0 := P2AllW1FrozenReceiverFiniteAction.original_W1_parameters i j
      have hs : 12/5≤W1Target i := le_add_of_nonneg_right (by positivity)
      have hs0 : 0<W1Anchor j := (show 0<W1Target i by linarith).trans_le ha0.2.1
      have hlR := log_pos hR
      have hv : 1<y := by dsimp [y]; linarith [hge 1]
      have hly := log_pos hv
      have hfloor : (N:ℝ)^(η/10)≤y := (rpow_le_rpow_of_exponent_le hNr.le (by linarith : η/10≤L/10)).trans
        (hp 1).2.2.1
      have hD : 0<d*q 0*q 1*q 2 := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hd (hpos 0)) (hpos 1)) (hpos 2)
      have hx : 0<x := div_pos (zero_lt_one.trans hNr) (Nat.cast_pos.mpr hD)
      have hcap : x≤N := div_le_self (Nat.cast_nonneg N) (by exact_mod_cast hD)
      have hold := chamber_bounds hm
      have hcube : (u 0,(u 1,u 2))∈P2N48GenericTwoThreeTieVolumes.tripleCube
          (1/W1Anchor j) (1/W1Target i) := ⟨hold 0,hold 1,hold 2⟩
      have hh := log_height hN' hd hL' hQ q hpos (hp 1).1.one_lt
      change log x/log y=argument (trueAlpha N Q d) (u 0,(u 1,u 2)) at hh
      have hratio : 1≤log x/log y := by rw [hh]; linarith only [argument_lower hs hs0 hα hcube,hs]
      have hyx : y≤x := (log_le_log_iff (zero_lt_one.trans hv) hx).mp (by linarith [(le_div_iff₀ hly).mp hratio])
      have hrough := ha N hNa x y hcap hfloor
      rw [if_pos (hv.le.trans hyx),if_pos hyx] at hrough
      have hunit : 1≤τ*x/log y := (le_div_iff₀ hly).mpr (by
        have hu := (div_le_iff₀ (zero_lt_one.trans hv)).mp (hb N hNb y hfloor)
        linarith only [hu,mul_le_mul_of_nonneg_left hyx hτ.le])
      have hω := cap_on_cube hs hs0 hα hcube
      rw [←hh] at hω
      have hweighted := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (add_le_add_right hω τ) hx.le) hly.le
      have hfamily : ((roughNumbers x y).card:ℝ) ≤ (omegaCap+2*τ)*x/log y := by
        linarith only [hrough,hunit,hweighted]
      have hy : u 1=log y/log (Q/d) := by rw [hQ]; exact (physical_log_ratio hN' hd hL' q 1).symm
      have hl : 1/5≤1/W1Anchor j := (one_div_le_one_div_of_le hs0 ha0.2.2)
      have huu : 1/10≤u 1 := by linarith [(hold 1).1]
      have hprod : (∏ k,1/(q k:ℝ))≤∏ k,1/((q k:ℝ)-1) := by
        apply prod_le_prod
        · exact fun k _ => (one_div_pos.mpr (Nat.cast_pos.mpr (hpos k))).le
        · intro k _; exact one_div_le_one_div_of_le (by linarith [hge k]) (by linarith)
      have heq : (omegaCap+2*τ)*x/log y =
          (rawScale N Q d*(omegaCap+2*τ))*((∏ k,1/(q k:ℝ))*test u) := by
        rw [test,max_eq_right huu,hy,Fin.prod_univ_three]
        dsimp only [x,height,rawScale]
        push_cast
        field_simp [(Nat.cast_pos.mpr hd : (0:ℝ)<d).ne',hlR.ne',hly.ne',
          (Nat.cast_pos.mpr (hpos 0) : (0:ℝ)<q 0).ne',(Nat.cast_pos.mpr (hpos 1) : (0:ℝ)<q 1).ne',
          (Nat.cast_pos.mpr (hpos 2) : (0:ℝ)<q 2).ne'] <;> ring
      exact hfamily.trans (heq.le.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hprod ht0) hC))
    · simp only [if_neg (fun h => hcop h.2)]
      exact mul_nonneg hC (mul_nonneg hw ht0)
  · simp only [if_neg (fun h => hm h.1),indicator_of_notMem hm,mul_zero]

end
end ImbalancedChen.Part5OriginalH430W1InclusiveRoughCounts
