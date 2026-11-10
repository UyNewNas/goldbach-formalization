import ImbalancedChen.Part3ActualCharacterCuspExpansion
import Mathlib.Data.ZMod.Units

/-! The denominator and unit argument in Young's finite change of basis,
on the original projective cusp quotient at an arbitrary positive level.
The inverse-index arithmetic uses the actual lower-left entry of
h T^(-k) g^(-1), not a postulated list of inequivalent cusps. -/
namespace ImbalancedChen.Part3.ActualCuspDenominatorClasses20261110

noncomputable section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularGroup
open ActualCharacterCuspExpansion20261110 Gamma0ActualCuspsSourceOnly

def frameDenominator (N : ℕ) (g : SL(2,ℤ)) : ℕ := (g 1 0).gcd (N : ℤ)

def youngFrame (f : ℕ) (u : ℤ) : SL(2,ℤ) :=
  ⟨!![1,0;u*(f : ℤ),1],by simp⟩

theorem actual_frame_test (N : ℕ) [NeZero N] (g h : SL(2,ℤ)) :
    nativeFrameOrbit N g = nativeFrameOrbit N h ↔
      ∃ k : ℤ, (N : ℤ) ∣ h 1 0*g 1 1-h 1 1*g 1 0+k*h 1 0*g 1 0 := by
  rw [nativeFrameOrbit_eq_iff,frames_same_class_iff]
  have hlower (k : ℤ) :
      (h*ModularGroup.T^(-k)*g⁻¹) 1 0 =
      h 1 0*g 1 1-h 1 1*g 1 0+k*h 1 0*g 1 0 := by
    simp [coe_mul,Matrix.mul_fin_two,ModularGroup.coe_T_zpow,SL2_inv_expl] <;> ring
  constructor
  · rintro ⟨γ,k,hk⟩
    have hγ : (γ : SL(2,ℤ)) = h*ModularGroup.T^(-k)*g⁻¹ := by rw [hk,zpow_neg]; group
    refine ⟨k,?_⟩
    rw [← hlower,← hγ]
    exact (gamma0_mem_iff_level_dvd_c N _).mp γ.property
  · rintro ⟨k,hk⟩
    let γ : CongruenceSubgroup.Gamma0 N := ⟨h*ModularGroup.T^(-k)*g⁻¹,
      (gamma0_mem_iff_level_dvd_c N _).mpr ((hlower k).symm ▸ hk)⟩
    refine ⟨γ,k,?_⟩
    change h = (h*ModularGroup.T^(-k)*g⁻¹)*g*ModularGroup.T^k
    rw [zpow_neg]
    group

private theorem denominator_dvd_of_equiv (N : ℕ) [NeZero N] (g h : SL(2,ℤ))
    (he : nativeFrameOrbit N g = nativeFrameOrbit N h) :
    frameDenominator N g ∣ frameDenominator N h := by
  obtain ⟨γ,k,rfl⟩ := (frames_same_class_iff N _ _).mp ((nativeFrameOrbit_eq_iff N _ _).mp he)
  apply Int.natCast_dvd_natCast.mp
  apply Int.dvd_coe_gcd _ (Int.gcd_dvd_right (g 1 0) (N : ℤ))
  have h₀ := (Int.gcd_dvd_right (g 1 0) (N : ℤ)).trans
    ((gamma0_mem_iff_level_dvd_c N _).mp γ.property)
  have h₁ := Int.gcd_dvd_left (g 1 0) (N : ℤ)
  simpa [frameDenominator,coe_mul,Matrix.mul_fin_two,ModularGroup.coe_T_zpow] using
    dvd_add (dvd_mul_of_dvd_left h₀ (g 0 0)) (dvd_mul_of_dvd_right h₁ ((γ : SL(2,ℤ)) 1 1))

theorem denominator_of_equiv (N : ℕ) [NeZero N] (g h : SL(2,ℤ))
    (he : nativeFrameOrbit N g = nativeFrameOrbit N h) :
    frameDenominator N g = frameDenominator N h :=
  Nat.dvd_antisymm (denominator_dvd_of_equiv N g h he) (denominator_dvd_of_equiv N h g he.symm)

theorem gcd_mul_unit (x u M : ℤ) (hu : IsCoprime u M) :
    (u*x).gcd M = x.gcd M := by
  apply Nat.dvd_antisymm
  · let h := (u*x).gcd M
    have hM : (h : ℤ) ∣ M := Int.gcd_dvd_right _ _
    have hx : (h : ℤ) ∣ u*x := Int.gcd_dvd_left _ _
    obtain ⟨a,b,H⟩ := hu
    obtain ⟨k,hk⟩ := hM
    have hcop : IsCoprime (h : ℤ) u := ⟨b*k,a,by rw [hk] at H; linear_combination H⟩
    exact Int.natCast_dvd_natCast.mp (Int.dvd_coe_gcd (hcop.dvd_of_dvd_mul_left hx) hM)
  · exact Int.natCast_dvd_natCast.mp (Int.dvd_coe_gcd
      (dvd_mul_of_dvd_right (Int.gcd_dvd_left x M) u) (Int.gcd_dvd_right x M))

theorem youngFrame_denominator {N f : ℕ} (hf : f ∣ N) (u : ℤ) (hu : IsCoprime u (N : ℤ)) :
    frameDenominator N (youngFrame f u) = f := by
  change (u*(f : ℤ)).gcd (N : ℤ) = f
  rw [gcd_mul_unit _ _ _ hu,Int.gcd_natCast_natCast,Nat.gcd_eq_left hf]

private theorem linear_congruence (f M : ℕ) (t A : ℤ) (ht : IsCoprime t (M : ℤ)) :
    (∃ k : ℤ, (M : ℤ) ∣ A+(f : ℤ)*t*k) ↔ ((f.gcd M : ℕ) : ℤ) ∣ A := by
  let h : ℤ := f.gcd M
  have hf : h ∣ (f : ℤ) := by exact_mod_cast Nat.gcd_dvd_left f M
  have hM : h ∣ (M : ℤ) := by exact_mod_cast Nat.gcd_dvd_right f M
  constructor
  · rintro ⟨k,hk⟩
    have h₂ : h ∣ (f : ℤ)*t*k := dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hf t) k
    exact (dvd_add_left h₂).mp (hM.trans hk)
  · rintro ⟨v,hv⟩
    obtain ⟨a,b,hab⟩ := ht
    let U : ℤ := Nat.gcdA f M
    let V : ℤ := Nat.gcdB f M
    have H : h = (f : ℤ)*U+(M : ℤ)*V := Nat.gcd_eq_gcd_ab f M
    refine ⟨-U*v*a,V*v+(f : ℤ)*U*v*b,?_⟩
    change A = h*v at hv
    rw [hv,H]
    linear_combination -((f : ℤ)*U*v)*hab

def band (N f : ℕ) : ℕ := f.gcd (N/f)

/-- Raw pair comparison for an arbitrary integral frame versus Young's
actual 1/(uf) frame. On the denominator-f component the only surviving
unit is (c/f)a mod gcd(f,N/f), with a the genuine upper-left entry. -/
theorem youngFrame_test {N f : ℕ} [NeZero N] (hf : 0 < f) (hdiv : f ∣ N)
    (g : SL(2,ℤ)) (c u : ℤ) (hc : g 1 0 = (f : ℤ)*c)
    (hcop : IsCoprime c ((N/f : ℕ) : ℤ)) (hu : IsCoprime u (N : ℤ)) :
    nativeFrameOrbit N g = nativeFrameOrbit N (youngFrame f u) ↔
      (u : ZMod (band N f)) = ((c*g 0 0 : ℤ) : ZMod (band N f)) := by
  let M := N/f
  let H := band N f
  have hN : (N : ℤ) = (f : ℤ)*(M : ℤ) := by
    exact_mod_cast (Nat.mul_div_cancel' hdiv).symm
  have hfZ : (f : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hf.ne'
  have huM : IsCoprime u (M : ℤ) := by
    obtain ⟨a,b,hab⟩ := hu
    exact ⟨a,b*f,by rw [hN] at hab; linear_combination hab⟩
  have hdivH : (H : ℤ) ∣ (f : ℤ) := by exact_mod_cast Nat.gcd_dvd_left f M
  have hCzero : (g 1 0 : ZMod H) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ H).mpr
    (hc ▸ dvd_mul_of_dvd_left hdivH c)
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0 = 1 := by simpa only [Matrix.det_fin_two] using g.det_coe
  have hunit : (g 0 0 : ZMod H)*(g 1 1 : ZMod H) = 1 := by
    simpa only [Int.cast_sub,Int.cast_mul,Int.cast_one,hCzero,mul_zero,sub_zero] using
      congrArg (fun x : ℤ => (x : ZMod H)) hdet
  have hstep : (∃ k : ℤ, (N : ℤ) ∣ (u*(f : ℤ))*g 1 1-1*g 1 0+k*(u*(f : ℤ))*g 1 0) ↔
      ∃ k : ℤ, (M : ℤ) ∣ u*g 1 1-c+(f : ℤ)*(u*c)*k := by
    apply exists_congr
    intro k
    rw [hN,hc]
    constructor
    · rintro ⟨j,hj⟩
      refine ⟨j,mul_left_cancel₀ hfZ ?_⟩
      linear_combination hj
    · rintro ⟨j,hj⟩
      refine ⟨j,?_⟩
      linear_combination (f : ℤ)*hj
  rw [actual_frame_test]
  change (∃ k : ℤ, (N : ℤ) ∣ (u*(f : ℤ))*g 1 1-1*g 1 0+k*(u*(f : ℤ))*g 1 0) ↔ _
  rw [hstep,linear_congruence f M _ _ (huM.mul_left hcop)]
  change (H : ℤ) ∣ u*g 1 1-c ↔ (u : ZMod H) = ((c*g 0 0 : ℤ) : ZMod H)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,Int.cast_mul,sub_eq_zero,Int.cast_mul]
  constructor
  · intro he
    calc
      (u : ZMod H) = (u : ZMod H)*((g 0 0 : ZMod H)*(g 1 1 : ZMod H)) := by rw [hunit,mul_one]
      _ = ((u : ZMod H)*(g 1 1 : ZMod H))*(g 0 0 : ZMod H) := by ring
      _ = _ := by rw [he]
  · intro he
    rw [he,mul_assoc,hunit,mul_one]

private theorem raw_data (N : ℕ) [NeZero N] (g : SL(2,ℤ)) :
    0 < frameDenominator N g ∧ frameDenominator N g ∣ N ∧
    g 1 0 = (frameDenominator N g : ℤ)*(g 1 0/(frameDenominator N g : ℤ)) ∧
    IsCoprime (g 1 0/(frameDenominator N g : ℤ)) ((N/frameDenominator N g : ℕ) : ℤ) := by
  let f := frameDenominator N g
  have hf : 0 < f := by
    apply Nat.pos_of_ne_zero
    intro hz
    have h := (Int.gcd_eq_zero_iff.mp hz).2
    exact (Nat.cast_ne_zero.mpr (NeZero.ne N) : (N : ℤ) ≠ 0) h
  have hd : f ∣ N := Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right _ _)
  have hc : g 1 0 = (f : ℤ)*(g 1 0/(f : ℤ)) := by
    rw [mul_comm,Int.ediv_mul_cancel (Int.gcd_dvd_left _ _)]
  refine ⟨hf,hd,hc,?_⟩
  apply Int.isCoprime_iff_gcd_eq_one.mpr
  change Int.gcd _ ((N/f : ℕ) : ℤ) = 1
  rw [Int.natCast_ediv]
  exact Int.gcd_ediv_gcd_ediv_gcd hf

abbrev Parameters (N : ℕ) := (f : {f : ℕ // f ∈ N.divisors}) × (ZMod (band N f.1))ˣ

private theorem band_dvd {N f : ℕ} (hf : f ∣ N) : band N f ∣ N := (Nat.gcd_dvd_left f _).trans hf

def unitLift {N f : ℕ} [NeZero N] (hf : f ∣ N) (u : (ZMod (band N f))ˣ) : (ZMod N)ˣ :=
  Classical.choose (ZMod.unitsMap_surjective (band_dvd hf) u)

def unitInteger {N f : ℕ} [NeZero N] (hf : f ∣ N) (u : (ZMod (band N f))ˣ) : ℤ :=
  ((unitLift hf u : (ZMod N)ˣ) : ZMod N).val

theorem unitInteger_coprime {N f : ℕ} [NeZero N] (hf : f ∣ N) (u : (ZMod (band N f))ˣ) :
    IsCoprime (unitInteger hf u) (N : ℤ) := by
  apply IsCoprime.symm
  apply (ZMod.coe_int_isUnit_iff_isCoprime _ N).mp
  simpa [unitInteger] using (unitLift hf u).isUnit

theorem unitInteger_cast {N f : ℕ} [NeZero N] (hf : f ∣ N) (u : (ZMod (band N f))ˣ) :
    (unitInteger hf u : ZMod (band N f)) = u := by
  have hu := congrArg (fun w : (ZMod (band N f))ˣ => (w : ZMod (band N f)))
    (Classical.choose_spec (ZMod.unitsMap_surjective (band_dvd hf) u))
  change ((ZMod.unitsMap (band_dvd hf) (unitLift hf u) : (ZMod (band N f))ˣ) : ZMod (band N f)) = u at hu
  simpa only [unitInteger,Int.cast_natCast,ZMod.unitsMap_val,← ZMod.natCast_val] using hu

def parameterFrame {N : ℕ} [NeZero N] (a : Parameters N) : SL(2,ℤ) :=
  youngFrame a.1.1 (unitInteger (Nat.mem_divisors.mp a.1.2).1 a.2)

private theorem parameter_injective (N : ℕ) [NeZero N] :
    Function.Injective (fun a : Parameters N => nativeFrameOrbit N (parameterFrame a)) := by
  rintro ⟨⟨f,hf⟩,u⟩ ⟨⟨f',hf'⟩,u'⟩ he
  have hfd := (Nat.mem_divisors.mp hf).1
  have hfd' := (Nat.mem_divisors.mp hf').1
  have heq := denominator_of_equiv N _ _ he
  change frameDenominator N (youngFrame f (unitInteger hfd u)) =
    frameDenominator N (youngFrame f' (unitInteger hfd' u')) at heq
  rw [youngFrame_denominator hfd _ (unitInteger_coprime hfd u),
    youngFrame_denominator hfd' _ (unitInteger_coprime hfd' u')] at heq
  subst f'
  have hpos : 0 < f := Nat.pos_of_dvd_of_pos hfd (Nat.pos_of_ne_zero (NeZero.ne N))
  let U := unitInteger hfd u
  have huM : IsCoprime U ((N/f : ℕ) : ℤ) := by
    obtain ⟨a,b,hab⟩ := unitInteger_coprime hfd u
    have H : (N : ℤ) = (f : ℤ)*(N/f : ℕ) := by exact_mod_cast (Nat.mul_div_cancel' hfd).symm
    exact ⟨a,b*f,by rw [H] at hab; linear_combination hab⟩
  have hu := (youngFrame_test hpos hfd (youngFrame f U) U (unitInteger hfd u')
    (by change U*f=(f : ℤ)*U; ring) huM (unitInteger_coprime hfd u')).mp he
  have hU : u' = u := Units.ext (by simpa [youngFrame,U,unitInteger_cast] using hu)
  subst u'
  rfl

private theorem parameter_surjective (N : ℕ) [NeZero N] :
    Function.Surjective (fun a : Parameters N => nativeFrameOrbit N (parameterFrame a)) := by
  intro x
  let a := (nativeCuspEquiv N).symm x
  let g := classFrame a
  have hx : nativeFrameOrbit N g = x := (nativeCuspEquiv N).apply_symm_apply x
  obtain ⟨hpos,hdiv,hc,hcop⟩ := raw_data N g
  let f := frameDenominator N g
  let c := g 1 0/(f : ℤ)
  let H := band N f
  have h₁ : (H : ℤ) ∣ (f : ℤ) := by exact_mod_cast Nat.gcd_dvd_left f (N/f)
  have h₂ : (H : ℤ) ∣ ((N/f : ℕ) : ℤ) := by exact_mod_cast Nat.gcd_dvd_right f (N/f)
  have hcg : IsCoprime c (H : ℤ) := hcop.of_isCoprime_of_dvd_right h₂
  have hag : IsCoprime (g 0 0) (H : ℤ) := (g.isCoprime_col 0).of_isCoprime_of_dvd_right
    (hc ▸ dvd_mul_of_dvd_left h₁ c)
  let tag := c*g 0 0
  have htag : IsUnit (tag : ZMod H) := (ZMod.coe_int_isUnit_iff_isCoprime _ H).mpr (hcg.mul_left hag).symm
  let u := htag.unit
  let P : Parameters N := ⟨⟨f,Nat.mem_divisors.mpr ⟨hdiv,NeZero.ne N⟩⟩,u⟩
  refine ⟨P,Eq.trans ?_ hx⟩
  apply Eq.symm
  apply (youngFrame_test hpos hdiv g c (unitInteger hdiv u) hc hcop (unitInteger_coprime hdiv u)).mpr
  rw [unitInteger_cast]
  exact htag.unit_spec

/-- Young's full finite divisor/unit indexing is bijective on the original
projective cusp classes, including the two axes and every composite level. -/
def youngCuspEquiv (N : ℕ) [NeZero N] : Parameters N ≃ NativeCusps N :=
  Equiv.ofBijective _ ⟨parameter_injective N,parameter_surjective N⟩

end
end ImbalancedChen.Part3.ActualCuspDenominatorClasses20261110
