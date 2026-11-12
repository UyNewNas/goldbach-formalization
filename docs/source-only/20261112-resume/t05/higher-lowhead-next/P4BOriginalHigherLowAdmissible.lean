import ImbalancedChen.P4BOriginalHigherLowRestoration

namespace ImbalancedChen.P4BOriginalHigherLowAdmissible
noncomputable section
open Classical Filter
open Part3 (MediumAdmissible)
open P4BOriginalMediumAtomFamily (Index support third_data)
open P4BOriginalHigherLowBins (useRoot four_used)
open P4BOriginalHigherLowRepresentative (d t)
open P4BOriginalHigherLowNativeAtoms (groups firstSet secondSet thirdSet atom factors)
open P4BOriginalMediumOccupiedLengths (factor_owner)
open P4BOriginalMediumTriplePowers (power upper_iff strict_iff power_mul power_pow power_rpow)
open P4BUpperSelectedBoxCapacity (endpoint)
open P5Z.HBRightClosedDyadicRoles (Block owner owner_owns)
open P5Z.ActualHBDyadicProductWindow (lower lower_pos owns_bounds)
open P4AHeldTaggedCompilerSupport (J0)

theorem coarse_step {e : ℚ} (he : 0<e) :
    ∃ q0 : ℕ,∀ q≥q0,∀ a : ℝ,
      logPrimeMeshStep 0 (19/96) (P4AOriginalNewFifthUnion.data e q a).m≤(e:ℝ)/20 := by
  have heR : 0<(e:ℝ) := by exact_mod_cast he
  obtain ⟨q0,hq⟩ := exists_nat_gt (20/(2400*(e:ℝ)))
  refine ⟨q0+1,?_⟩
  intro q hq0 a
  have hp : 0<q := by omega
  have H := (div_lt_iff₀ (by positivity : 0<2400*(e:ℝ))).mp
    (hq.trans_le (by exact_mod_cast (show q0≤q by omega)))
  change logPrimeMeshStep 0 (19/96) (P1OriginalFifthGrid400RefinedFullBoxCover.refinedMesh q)≤_
  rw [P1OriginalFifthGrid400RefinedFullBoxCover.refined_step q hp]
  apply (div_le_iff₀ (by positivity : 0<2400*(q:ℝ))).mpr
  linarith only [H]

theorem eventually_root_words (K order : ℕ) {z k k0 : ℝ}
    (hz : 0<z) (hz' : z≤1/20000) (hk : 0<k) (hk' : k≤z/200000)
    (hk0 : k0<k/(4*(1+k))) (hk1 : k0<1) :
    ∀ᶠ N : ℕ in atTop,∀ (I : Index order z k0),I.P.N=N → I.eta=z →
      0<I.P.e → (I.P.e:ℝ)≤1/2048 → z≤(I.P.e:ℝ)/512 →
      logPrimeMeshStep 0 (19/96) (d I.P).m≤(I.P.e:ℝ)/20 →
      0<I.P.omega → I.P.T*((J0 I.P.omega:ℝ)+1)≤z → 0≤I.P.ell → 2*I.P.ell≤z/16 →
      useRoot I.P I.J →
      ∀ D∈(firstSet I).image owner,∀ E∈(secondSet I).image owner,∀ G∈(thirdSet I).image owner,
        MediumAdmissible 12 (z/2000) k (1/Real.exp 1) (atom I K D E G) := by
  have hz0 : z≤1/400 := by linarith
  have hkz : k≤z := by linarith
  filter_upwards [P4BOriginalHighRankLiveFibreModes.eventually_fixed_live_window K hz hz0 hk hkz hk0 hk1,
    P4BOriginalMediumFibreSWWindow.eventually_window K order (Real.exp (Real.exp 1)+1) hz hz0 hk hkz hk0 hk1,
    eventually_ge_atTop (2:ℕ)] with N HL HW hNP
  intro I hn heta he he' hzE step ho ht hell hell' huse D hD E hE G hG
  rw [←hn] at HL HW hNP
  have hsel := P4BOriginalMediumFibreSWWindow.first_spec I.selected
  obtain ⟨hx,hlo,hhi,hU,hUmax,hZ,_⟩ := HL I.b_pos I.kap_pos I.s_pos I.gate _ _ I.cj I.ck I.bs I.i I.C I.live hsel
  obtain ⟨hLarge,_,_,_,hU1,_,_,_,_⟩ := HW I.b_pos I.kap_pos I.s_pos I.gate _ _ I.cj I.ck I.bs I.i I.C I.live hsel
  have hx0 := zero_lt_one.trans hx
  have hnR : 0<(I.P.N:ℝ) := by exact_mod_cast I.N_pos
  have hu := zero_lt_one.trans hU1
  have hi := hhi.trans (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith only [hkz] : 1+k≤1+z))
  obtain ⟨h1,h2,h3,h4⟩ := P4BOriginalHigherLowEndpointBounds.original I.P (by omega) he he' step ho
    I.word huse hx hz hzE ht hlo hi hU hUmax hell'
  let S := groups I
  let H := actualPrimeFineLabelIntegerUpper I.P.N I.P.T
  let A := endpoint H S.1
  let B := endpoint H S.2.1
  let C := endpoint H S.2.2*I.x^(2*I.P.ell)
  have a1 : (lower D:ℝ)≤A := factor_owner I hD
  have a2 : (lower E:ℝ)≤B := factor_owner I hE
  have a3 : (lower G:ℝ)≤C := by
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hG
    have h := (owns_bounds (owner_owns (third_data _ _ _ hq).1)).1
    apply (by exact_mod_cast h : (lower (owner q):ℝ)≤q).trans
    apply (P4BOriginalCollisionThirdFactor.gamma_range I.P hq).trans
    have hb : I.P.L≤I.x^(2*I.P.ell) := by
      apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hi hell).trans
      rw [←Real.rpow_mul hx0.le]
      apply Real.rpow_le_rpow_of_exponent_le hx.le
      nlinarith only [mul_nonneg hell (show 0≤1-z by linarith)]
    change I.P.L*endpoint H S.2.2≤endpoint H S.2.2*_
    rw [mul_comm I.P.L]
    exact mul_le_mul_of_nonneg_left hb (by rw [P4BUpperSelectedBoxCapacity.endpoint_eq_cast]; positivity)
  have f1 : A<I.U*I.x^(-z/100) := by simpa only [A,S,groups,heta] using h1
  have f2 : I.U^2*B*C^2<I.x^(1-8*(z/100)) := by simpa only [B,C,S,groups,heta] using h2
  have f3 : I.x^(7/32:ℝ)*I.U*A*B^5*C^2<I.x^(2-15*(z/100)) := by simpa only [A,B,C,S,groups,heta] using h3
  have f4 : I.U^(23/16:ℝ)*A*B^(73/16:ℝ)*C^(39/16:ℝ)<I.x^(2-15*(z/100)) := by
    simpa only [A,B,C,S,groups,heta] using h4
  have hDP : (0:ℝ)<lower D := by exact_mod_cast lower_pos D
  have hEP : (0:ℝ)<lower E := by exact_mod_cast lower_pos E
  have hGP : (0:ℝ)<lower G := by exact_mod_cast lower_pos G
  have mov : (I.P.N:ℝ)^(7/32:ℝ)≤I.x^(7*k/32)*I.x^(7/32:ℝ) := by
    apply (Real.rpow_le_rpow hnR.le hhi (by norm_num : (0:ℝ)≤7/32)).trans_eq
    rw [←Real.rpow_mul hx0.le,←Real.rpow_add hx0]; congr 1 <;> ring
  have mon3 : (I.P.N:ℝ)^(7/32:ℝ)*I.U*(lower D:ℝ)*(lower E:ℝ)^5*(lower G:ℝ)^2<I.x^(2-15*(z/2000)) := by
    calc
      _≤(I.x^(7*k/32)*I.x^(7/32:ℝ))*I.U*A*B^5*C^2 := by gcongr
      _=I.x^(7*k/32)*(I.x^(7/32:ℝ)*I.U*A*B^5*C^2) := by ring
      _<I.x^(7*k/32)*I.x^(2-15*(z/100)) := mul_lt_mul_of_pos_left f3 (Real.rpow_pos_of_pos hx0 _)
      _≤_ := by rw [←Real.rpow_add hx0]; apply Real.rpow_le_rpow_of_exponent_le hx.le; linarith only [hk',hz]
  have residue : (1/Real.exp 1)*I.x≤I.P.N := by
    calc
      _≤(1/Real.exp 1)*(Real.exp 1*I.P.N) := mul_le_mul_of_nonneg_left I.scale_upper (by positivity)
      _=(I.P.N:ℝ) := by rw [←mul_assoc,div_mul_cancel₀ _ (Real.exp_pos 1).ne',one_mul]
  have hp (b : Block) : (1:ℝ)≤lower b := by exact_mod_cast lower_pos b
  refine ⟨hU1.le,hp I.C,hp D,hp E,hp G,by change Real.exp (Real.exp 1)<I.x; linarith only [hLarge],
    residue,hhi,?_,?_,mon3,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (a1.trans_lt f1).trans_le (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith)) hu.le)
  · change I.U^2*(lower E:ℝ)*(lower G:ℝ)^2<_
    apply lt_of_le_of_lt (show _≤I.U^2*B*C^2 by gcongr)
    exact f2.trans_le (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))
  · change I.U^(1+2*(7/32:ℝ))*(lower D:ℝ)*(lower E:ℝ)^(5-2*(7/32:ℝ))*(lower G:ℝ)^(2+2*(7/32:ℝ))<_
    rw [show 1+2*(7/32:ℝ)=23/16 by norm_num,show 5-2*(7/32:ℝ)=73/16 by norm_num,
      show 2+2*(7/32:ℝ)=39/16 by norm_num]
    apply lt_of_le_of_lt (show _≤I.U^(23/16:ℝ)*A*B^(73/16:ℝ)*C^(39/16:ℝ) by gcongr <;> norm_num)
    exact f4.trans_le (Real.rpow_le_rpow_of_exponent_le hx.le (by linarith))
  · intro n _; exact P4BOriginalMediumHBHead.alpha_one _ _ _ _ _ n
  · intro n _ h p hp hd; exact hZ.trans_lt (P4BOriginalMediumHBHead.alpha_rough h p hp hd)
  · exact fun _ h => I.atom_beta_bound K h
  · exact fun q _ => (factors I K D E G q).1
  · exact fun q _ => (factors I K D E G q).2.1
  · exact fun q _ => (factors I K D E G q).2.2

/-- Every rank-four low-first word, with no inherited-cap test left as a
premise. All original smoothing widths and occupied dyadic HB fibres
come after the target threshold. -/
theorem eventually_four (K order : ℕ) {z k k0 : ℝ}
    (hz : 0<z) (hz' : z≤1/20000) (hk : 0<k) (hk' : k≤z/200000)
    (hk0 : k0<k/(4*(1+k))) (hk1 : k0<1) :
    ∀ᶠ N : ℕ in atTop,∀ (I : Index order z k0),I.P.N=N → I.eta=z →
      0<I.P.e → (I.P.e:ℝ)≤1/2048 → z≤(I.P.e:ℝ)/512 →
      logPrimeMeshStep 0 (19/96) (d I.P).m≤(I.P.e:ℝ)/20 →
      0<I.P.omega → I.P.T*((J0 I.P.omega:ℝ)+1)≤z → 0≤I.P.ell → 2*I.P.ell≤z/16 →
      I.J.length=4 → t I.P I.J 0≤VariableEnvelope.mu →
      ∀ D∈(firstSet I).image owner,∀ E∈(secondSet I).image owner,∀ G∈(thirdSet I).image owner,
        MediumAdmissible 12 (z/2000) k (1/Real.exp 1) (atom I K D E G) := by
  filter_upwards [eventually_root_words K order hz hz' hk hk' hk0 hk1,eventually_ge_atTop (2:ℕ)] with N HW hN
  intro I hn hη he he' hzE step ho ht hell hell' h4 hl
  exact HW I hn hη he he' hzE step ho ht hell hell' (four_used I.P (by omega) he.le ho.le I.word h4 hl)

end
end ImbalancedChen.P4BOriginalHigherLowAdmissible
