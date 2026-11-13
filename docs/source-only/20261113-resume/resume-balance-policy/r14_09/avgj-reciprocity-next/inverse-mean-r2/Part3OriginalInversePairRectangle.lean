import ImbalancedChen.Part3OriginalInversePairBallCount

/-! Count the physical pairs (positive modulus, unit representative) for
the two oppositely shifted frequencies in the initial exceptional estimate. -/
namespace ImbalancedChen.Part3.OriginalInversePairRectangle20261113
noncomputable section
open Finset Matrix
open scoped MatrixGroups UpperHalfPlane
open OriginalSmoothPoissonTail ActualCompactBruhatKernel20261025a
open OriginalInversePairMatrix20261113 OriginalInversePairDisplacement20261113
open OriginalInversePairBallCount20261113 ModularFundamentalFiniteMeasure20261024z

private theorem scaled_rectangle (S : Finset (ℕ+ × ℕ)) {K α β : ℝ} (hK : 1≤K)
    (hα : 0<α) (hβ : 0<β) (A : α≤1) (B : β≤1) (scale : 1≤K^2*α*β)
    (ω : ℝ) (l r : ℕ+ × ℕ → ℤ)
    (level : ∀ p ∈ S, K ≤ (p.1.val:ℝ) ∧ (p.1.val:ℝ) ≤ 2*K)
    (unit : ∀ p ∈ S, p.2<p.1.val ∧ Nat.Coprime p.2 p.1.val)
    (left : ∀ p ∈ S, |(inverseResidue p.1.val p.2:ℝ)/(p.1.val:ℝ)-ω-(l p:ℝ)|≤α)
    (right : ∀ p ∈ S, |(p.2:ℝ)/(p.1.val:ℝ)+ω-(r p:ℝ)|≤β) :
    (S.card:ℝ) ≤ 1500*(1+Real.log (1+12*K))*(K+K^2*α*β) := by
  classical
  let z := horizontalPoint β hβ ω
  let w := horizontalPoint α hα ω
  obtain ⟨a,b,za,wb,zaCap,wbCap,inj,iso⟩ := reduce_both z w B A
  let g (p : ↥S) := lift p.val.1 p.val.2 (unit p.val p.property).2 (l p.val) (r p.val)
  let f (p : ↥S) := b*g p*a⁻¹
  have inject : Function.Injective f := by
    intro x y h
    have e : g x=g y := inj h
    obtain ⟨ec,ed⟩ := recover_pair (unit x.val x.property).1 (unit y.val y.property).1
      (unit x.val x.property).2 (unit y.val y.property).2 _ _ _ _ e
    exact Subtype.ext (Prod.ext ec ed)
  let P := Real.sqrt (α*β)
  let R := 6*K*P
  have posK : 0<K := lt_of_lt_of_le zero_lt_one hK
  have posP : 0<P := Real.sqrt_pos.mpr (mul_pos hα hβ)
  have p2 : P^2=α*β := Real.sq_sqrt (mul_pos hα hβ).le
  have p1 : P≤1 := by
    apply (sq_le_sq₀ posP.le zero_le_one).mp
    rw [p2,one_pow]
    exact (mul_le_mul A B hβ.le zero_le_one).trans_eq (one_mul 1)
  have posR : 0<R := by dsimp [R]; positivity
  have r2 : R^2=36*(K^2*α*β) := by dsimp [R]; rw [mul_pow,p2]; ring
  have r1 : 1≤R := by
    apply (sq_le_sq₀ zero_le_one posR.le).mp
    rw [r2,one_pow]
    linarith
  have rcap : R ≤ 6*K := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left p1 (by positivity : 0≤6*K)
  let T := univ.image f
  have metric (m) (hm : m∈T) : 2*Real.cosh (dist (m • (a • z)) (b • w))≤R^2 := by
    obtain ⟨p,_,rfl⟩ := mem_image.mp hm
    rcases level p.val p.property with ⟨lo,hi⟩
    let k := p.val.1
    have kp : (0:ℝ)<k.val := by exact_mod_cast k.property
    have kscale : 1≤(k.val:ℝ)^2*α*β := scale.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ posK.le lo 2) hα.le) hβ.le)
    have Ku := pow_le_pow_left₀ kp.le hi 2
    have ru := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right Ku hα.le) hβ.le
    change 2*Real.cosh (dist ((b*g p*a⁻¹) • (a • z)) (b • w))≤R^2
    rw [iso,r2]
    exact (physical_displacement k (unit p.val p.property).1 (unit p.val p.property).2
      ω _ _ hα hβ kscale (left _ p.property) (right _ p.property)).trans
        (by nlinarith only [ru,scale])
  have count := ball_card T (a • z) (b • w) (modularFD_half_lt_im za).le
    (modularFD_half_lt_im wb).le r1 metric
  have card : T.card=S.card := by
    simp only [T,card_image_of_injective univ inject,card_univ,Fintype.card_coe]
  rw [card,r2] at count
  let H := Real.sqrt ((a • z).im*(b • w).im)
  have hH : 0<H := Real.sqrt_pos.mpr (mul_pos (a • z).im_pos (b • w).im_pos)
  have h2 : H^2=(a • z).im*(b • w).im :=
    Real.sq_sqrt (mul_pos (a • z).im_pos (b • w).im_pos).le
  have height : P*H≤1 := by
    apply (sq_le_sq₀ (mul_pos posP hH).le zero_le_one).mp
    rw [mul_pow,p2,h2,one_pow]
    change (a • z).im ≤ 1/β at zaCap
    change (b • w).im ≤ 1/α at wbCap
    have ea := (le_div_iff₀ hβ).mp zaCap
    have eb := (le_div_iff₀ hα).mp wbCap
    nlinarith only [mul_le_mul ea eb (mul_pos (b • w).im_pos hα).le zero_le_one]
  have rh : R*H≤6*K := by
    dsimp [R]
    nlinarith only [mul_le_mul_of_nonneg_left height (by positivity : 0≤6*K)]
  have logCap := Real.log_le_log (by linarith only [posR] : 0<1+2*R)
    (by linarith only [rcap] : 1+2*R≤1+12*K)
  have log0 := Real.log_nonneg (by linarith only [hK] : 1≤1+12*K)
  change (S.card:ℝ) ≤ 40*(36*(K^2*α*β))*(1+Real.log (1+2*R))+2+4*R*H at count
  nlinarith only [count,rh,hK,scale,
    mul_le_mul_of_nonneg_left logCap (by positivity : 0≤K^2*α*β),
    mul_nonneg posK.le log0,mul_nonneg (zero_le_one.trans scale) log0]

/-- The dyadically localized inverse-pair box bound, including arcs narrower
than one residue spacing. The two nearest-integer representatives can be
chosen independently, also for exact resonance or ties. -/
theorem rectangle_card (S : Finset (ℕ+ × ℕ)) {K α β : ℝ} (hK : 1≤K)
    (hα : 0≤α) (hβ : 0≤β) (A : α≤1) (B : β≤1) (ω : ℝ) (l r : ℕ+ × ℕ → ℤ)
    (level : ∀ p ∈ S, K ≤ (p.1.val:ℝ) ∧ (p.1.val:ℝ) ≤ 2*K)
    (unit : ∀ p ∈ S, p.2<p.1.val ∧ Nat.Coprime p.2 p.1.val)
    (left : ∀ p ∈ S, |(inverseResidue p.1.val p.2:ℝ)/(p.1.val:ℝ)-ω-(l p:ℝ)|≤α)
    (right : ∀ p ∈ S, |(p.2:ℝ)/(p.1.val:ℝ)+ω-(r p:ℝ)|≤β) :
    (S.card:ℝ) ≤ 6000*(1+Real.log (1+12*K))*(K+K^2*α*β) := by
  have k : 0<K := zero_lt_one.trans_le hK
  have q : 0<1/K := one_div_pos.mpr k
  have q1 : 1/K≤1 := (div_le_iff₀ k).mpr (by simpa only [one_mul] using hK)
  let a := max α (1/K)
  let b := max β (1/K)
  have ap : 0<a := q.trans_le (le_max_right _ _)
  have bp : 0<b := q.trans_le (le_max_right _ _)
  have m0 := mul_le_mul (le_max_right α (1/K)) (le_max_right β (1/K)) q.le ap.le
  have m1 : 1≤K^2*a*b := by
    have H := mul_le_mul_of_nonneg_left m0 (sq_nonneg K)
    have E : K^2*(1/K*(1/K))=1 := by field_simp [k.ne'] <;> ring
    rw [E] at H
    nlinarith only [H]
  have c := scaled_rectangle S hK ap bp (max_le A q1) (max_le B q1) m1 ω l r level unit
    (fun p hp => (left p hp).trans (le_max_left _ _))
    (fun p hp => (right p hp).trans (le_max_left _ _))
  have am : a≤α+1/K := max_le (by linarith) (by linarith)
  have bm : b≤β+1/K := max_le (by linarith) (by linarith)
  have hi := mul_le_mul_of_nonneg_left (mul_le_mul am bm bp.le (by positivity)) (sq_nonneg K)
  have E : K^2*((α+1/K)*(β+1/K))=K^2*α*β+K*α+K*β+1 := by field_simp [k.ne'] <;> ring
  rw [E] at hi
  have H : K+K^2*a*b ≤ 4*(K+K^2*α*β) := by
    nlinarith only [hi,hK,mul_le_mul_of_nonneg_left A k.le,mul_le_mul_of_nonneg_left B k.le,
      mul_nonneg (mul_nonneg (sq_nonneg K) hα) hβ]
  have log0 := Real.log_nonneg (by linarith : 1≤1+12*K)
  calc
    _ ≤ _ := c
    _ ≤ 1500*(1+Real.log (1+12*K))*(4*(K+K^2*α*β)) :=
      mul_le_mul_of_nonneg_left H (by positivity)
    _ = _ := by ring

end
end ImbalancedChen.Part3.OriginalInversePairRectangle20261113
