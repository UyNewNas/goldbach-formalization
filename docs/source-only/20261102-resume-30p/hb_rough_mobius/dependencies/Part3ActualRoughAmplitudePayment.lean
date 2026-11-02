import ImbalancedChen.Part3ActualMovingRoughHeight

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Actual contourAmplitude <= K(1+log x)^(R+82), uniformly before original
q and moving frequency. All L/inverseL, Euler, Smooth1 and epsilon costs
come from their actual definitions. No hAmplitude/leftnorm/SW premise.
-/
namespace ImbalancedChen.Part3.ActualRoughAmplitudePayment20261026b
noncomputable section
open Filter Topology
open ActualMovingRoughHeight20261026b ActualRoughContourParameters20261026b
open ActualRoughContourIntegrandBounds20261026b ActualOriginalLContourBounds20261026b
open RoughQuadraticLowRectangle20261026b RoughThinEulerUniformComparison20261026b

def amplitudeConstant (E Cnu B C d kappa:ℝ):ℝ:=
  (32*heightConstant B (C+1)+(4/d)*(128*heightConstant B (C+1)/d)^40)*
    (thinComparison kappa*E)*Cnu

theorem amplitudeConstant_pos {E Cnu B C d kappa:ℝ}
    (hE:0<E) (hCnu:0<Cnu) (hB:0≤B) (hC:0≤C) (hd:0<d) :
    0<amplitudeConstant E Cnu B C d kappa:=by
  have hK:0<heightConstant B (C+1):=by
    unfold heightConstant
    nlinarith [abs_nonneg (Real.log 3)]
  unfold amplitudeConstant
  exact mul_pos (mul_pos (by positivity) (mul_pos (thinComparison_pos kappa) hE)) hCnu

theorem actual_contour_amplitude_le {E Cnu B C L R d kappa x:ℝ}
    (hE:0<E) (hCnu:0<Cnu) (hB:0≤B) (hC:0≤C) (hL:0≤L) (hLC:L≤C)
    (hR:0≤R) (hd:0<d) (hx:2≤x) (hlog:2≤Real.log x)
    (hll:1≤Real.log (Real.log x)) (q:ℕ) [NeZero q]
    (hq:(q:ℝ)≤(Real.log x)^B) (tau:ℝ) (htau:|tau|≤(Real.log x)^L) :
    contourAmplitude E Cnu q (contourT C x+|tau|) (roughDelta d x) kappa
      (roughZ x) ((Real.log x)^(-R))≤
      amplitudeConstant E Cnu B C d kappa*(1+Real.log x)^(R+82):=by
  let K:=heightConstant B (C+1)
  let W:=1+Real.log x
  let D:=rectangleLog q (contourT C x+|tau|)
  let delta:=roughDelta d x
  let Krec:=(4/d)*(128*K/d)^40
  let Ksum:=32*K+Krec
  have hell:0<Real.log x:=by linarith
  have hx1:1<x:=by linarith
  have hW:1≤W:=by dsimp [W];linarith
  have hW0:0<W:=zero_lt_one.trans_le hW
  have hK:0<K:=by dsimp [K,heightConstant];nlinarith [abs_nonneg (Real.log 3)]
  have hD0:0<D:=lt_of_lt_of_le zero_lt_one (one_le_rectangleLog q _)
  have hD:D≤K*W:=
    (moving_rectangleLog_bound hB hC hL hLC hlog hll q hq tau htau).trans
      (mul_le_mul_of_nonneg_left (by dsimp [W];linarith) hK.le)
  have hdelta:=actual_delta_inverse_bound hd hx1 hll
  have hd0:0<delta:=hdelta.1
  have hInv:1/delta≤W/d:=hdelta.2.trans
    (div_le_div_of_nonneg_right (by dsimp [W];linarith) hd.le)
  have hFour:4/delta≤(4/d)*W:=by
    calc
      _=4*(1/delta):=by ring
      _≤4*(W/d):=mul_le_mul_of_nonneg_left hInv (by norm_num)
      _=_:=by ring
  have hRatio:128*D/delta≤(128*K/d)*W^2:=by
    have hh:=mul_le_mul hD hInv (one_div_nonneg.mpr hd0.le) (mul_nonneg hK.le hW0.le)
    calc
      _=128*(D*(1/delta)):=by ring
      _≤128*((K*W)*(W/d)):=mul_le_mul_of_nonneg_left hh (by norm_num)
      _=_:=by ring
  have hPow:(128*D/delta)^40≤((128*K/d)*W^2)^40:=pow_le_pow_left₀ (by positivity) hRatio
  have hRec:originalReciprocalCost q (contourT C x+|tau|) delta≤Krec*W^81:=by
    rw [originalReciprocalCost_eq_power q _ hd0]
    calc
      _≤((4/d)*W)*(((128*K/d)*W^2)^40):=mul_le_mul hFour hPow (by positivity) (by positivity)
      _=_:=by dsimp [Krec];ring
  have hLift:W≤W^81:=by
    have hh:1≤W^80:=one_le_pow₀ hW
    calc
      _=W*1:=by ring
      _≤W*W^80:=mul_le_mul_of_nonneg_left hh hW0.le
      _=_:=by ring
  have hLinear:32*D≤32*K*W^81:=by
    calc
      _≤32*(K*W):=mul_le_mul_of_nonneg_left hD (by norm_num)
      _=(32*K)*W:=by ring
      _≤(32*K)*W^81:=mul_le_mul_of_nonneg_left hLift (by positivity)
  have hSum:32*D+originalReciprocalCost q (contourT C x+|tau|) delta≤Ksum*W^81:=by
    dsimp [Ksum]
    nlinarith [hRec,hLinear]
  have hKsum:0≤Ksum:=by dsimp [Ksum,Krec];positivity
  have htz:0≤1+Real.log (max 2 (roughZ x)):=by
    have hh:0≤Real.log (max 2 (roughZ x)):=Real.log_nonneg
      (le_trans (by norm_num : (1:ℝ)≤2) (le_max_left _ _))
    linarith
  have hz:1+Real.log (max 2 (roughZ x))≤W:=actual_rough_log_ceiling hx hll
  have hThin:0<thinComparison kappa*E:=mul_pos (thinComparison_pos kappa) hE
  have hEuler:(thinComparison kappa*E)*(1+Real.log (max 2 (roughZ x)))≤
      (thinComparison kappa*E)*W:=mul_le_mul_of_nonneg_left hz hThin.le
  have hEps:Cnu/((Real.log x)^(-R))=Cnu*(Real.log x)^R:=by
    rw [Real.rpow_neg hell.le]
    simp only [div_eq_mul_inv,inv_inv]
  have hEpsBound:Cnu*(Real.log x)^R≤Cnu*W^R:=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hell.le (by dsimp [W];linarith) hR) hCnu.le
  have hTwo:(32*D+originalReciprocalCost q (contourT C x+|tau|) delta)*
      ((thinComparison kappa*E)*(1+Real.log (max 2 (roughZ x))))≤
      (Ksum*W^81)*((thinComparison kappa*E)*W):=
    mul_le_mul hSum hEuler (mul_nonneg hThin.le htz) (mul_nonneg hKsum (pow_nonneg hW0.le _))
  have hFinal:=mul_le_mul hTwo hEpsBound (mul_nonneg hCnu.le (Real.rpow_nonneg hell.le _))
    (mul_nonneg (mul_nonneg hKsum (pow_nonneg hW0.le _)) (mul_nonneg hThin.le hW0.le))
  have hcombine:W^81*W*W^R=W^(R+82):=by
    rw [Real.rpow_add hW0]
    norm_num [Real.rpow_natCast] <;> ring
  calc
    _=(32*D+originalReciprocalCost q (contourT C x+|tau|) delta)*
        ((thinComparison kappa*E)*(1+Real.log (max 2 (roughZ x))))*(Cnu*(Real.log x)^R):=by
      unfold contourAmplitude
      rw [hEps]
      ring
    _≤(Ksum*W^81)*((thinComparison kappa*E)*W)*(Cnu*W^R):=hFinal
    _=(Ksum*(thinComparison kappa*E)*Cnu)*(W^81*W*W^R):=by ring
    _=_:=by rw [hcombine];rfl

theorem exists_actual_contour_amplitude_threshold (E Cnu B C L R d kappa:ℝ)
    (hE:0<E) (hCnu:0<Cnu) (hB:0≤B) (hC:0≤C) (hL:0≤L) (hLC:L≤C)
    (hR:0≤R) (hd:0<d) :
    ∃K:ℝ,0<K ∧ ∃x0:ℝ,2≤x0 ∧ ∀x:ℝ,x0≤x→∀q:ℕ,∀_:NeZero q,
      (q:ℝ)≤(Real.log x)^B→∀tau:ℝ,|tau|≤(Real.log x)^L→
      contourAmplitude E Cnu q (contourT C x+|tau|) (roughDelta d x) kappa
        (roughZ x) ((Real.log x)^(-R))≤K*(1+Real.log x)^(R+82):=by
  have hlarge:∀ᶠ x:ℝ in atTop,2≤x ∧ 2≤Real.log x ∧ 1≤Real.log (Real.log x):=by
    filter_upwards [eventually_ge_atTop (2:ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2:ℝ)),
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop (1:ℝ))]
      with x hx hl hll
    exact ⟨hx,hl,hll⟩
  obtain ⟨x0,hx0⟩:=eventually_atTop.mp hlarge
  refine ⟨amplitudeConstant E Cnu B C d kappa,
    amplitudeConstant_pos hE hCnu hB hC hd,max 2 x0,le_max_left _ _,?_⟩
  intro x hx q hqInstance hq tau htau
  letI:NeZero q:=hqInstance
  have hg:=hx0 x ((le_max_right _ _).trans hx)
  exact actual_contour_amplitude_le hE hCnu hB hC hL hLC hR hd hg.1 hg.2.1 hg.2.2 q hq tau htau

end
end ImbalancedChen.Part3.ActualRoughAmplitudePayment20261026b
