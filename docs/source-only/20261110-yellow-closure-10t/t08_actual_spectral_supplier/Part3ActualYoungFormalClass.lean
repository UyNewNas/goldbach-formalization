import ImbalancedChen.Part3ActualCriticalCuspEvaluation
import Mathlib.LinearAlgebra.Basis.Basic

/-! Young (7.2), (8.1) and the orthogonal character basis on the span
of the continued original cusp functions. Young's product is linear
in its first argument. All point evaluations refer to the genuine
oldforms obtained by inversion of the divisor matrix. -/
namespace ImbalancedChen.Part3.ActualYoungFormalClass20261110

noncomputable section
attribute [local instance] Classical.propDecidable
open Complex Set UpperHalfPlane MeasureTheory Module
open scoped BigOperators UpperHalfPlane MatrixGroups
open ActualCriticalCuspEvaluation20261110 ActualYoungCriticalCusps20261110
open ActualCuspDenominatorClasses20261110 ActualYoungDilationInverse20261110
open ActualCharacterCuspExpansion20261110

local instance bandNe (N : ℕ) [NeZero N] (f : Div N) : NeZero (band N f.1) :=
  ⟨(Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp f.2).1 (NeZero.pos N))).ne'⟩

abbrev CharacterSlots (N : ℕ) := (f : Div N) × DirichletCharacter ℂ (band N f.1)

private theorem shifted_sum {H : ℕ} [NeZero H] (χ : DirichletCharacter ℂ H) :
    (∑ u : (ZMod H)ˣ, χ (-(u : ZMod H))) = if χ = 1 then (H.totient : ℂ) else 0 := by
  classical
  split_ifs with h
  · subst χ
    simp only [MulChar.one_apply (Units.isUnit _).neg,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,mul_one,ZMod.card_units_eq_totient]
  · obtain ⟨b,hb⟩ := MulChar.ne_one_iff.mp h
    apply eq_zero_of_mul_eq_self_left hb
    calc
      χ (b : ZMod H) * (∑ u : (ZMod H)ˣ, χ (-(u : ZMod H))) =
          ∑ u : (ZMod H)ˣ, χ (-((b*u : (ZMod H)ˣ) : ZMod H)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        rw [← map_mul,Units.val_mul,mul_neg]
      _ = _ := (Group.mulLeft_bijective b).sum_comp (fun u : (ZMod H)ˣ => χ (-(u : ZMod H)))

theorem unit_orthogonality {H : ℕ} [NeZero H] (χ η : DirichletCharacter ℂ H) :
    (∑ u : (ZMod H)ˣ, χ (-(u : ZMod H))*star (η (-(u : ZMod H)))) =
      if χ = η then (H.totient : ℂ) else 0 := by
  simpa only [MulChar.mul_apply,← MulChar.star_apply',mul_inv_eq_one] using shifted_sum (χ*η⁻¹)

private theorem inverse_value {H : ℕ} [NeZero H] (ξ : DirichletCharacter ℂ H) (a : ZMod H)
    (ha : IsUnit a) : ξ a⁻¹ = star (ξ a) := by
  have h : ξ a⁻¹ * ξ a = 1 := by rw [← map_mul,ZMod.inv_mul_of_unit a ha,map_one]
  have hξ : ξ a ≠ 0 := (ha.map ξ).ne_zero
  rw [MulChar.star_apply',MulChar.inv_apply_eq_inv']
  field_simp [hξ]
  exact h

/-- Actual Cramer combination at the primitive conductor, using every
permitted dilation at this denominator. -/
def channelFunction {N : ℕ} [NeZero N] (f : Div N) (ξ : DirichletCharacter ℂ (band N f.1))
    (s : ℂ) (z : ℍ) : ℂ := by
  letI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
  exact continuedDAt ξ.primitiveCharacter f ξ.conductor_dvd_level s z

theorem inverse_cusp {N : ℕ} [NeZero N] (f : Div N) (u : (ZMod (band N f.1))ˣ) (s : ℂ) (z : ℍ) :
    parameterFamily ⟨f,u⟩ s z = ((band N f.1).totient : ℂ)⁻¹ *
      ∑ ξ : DirichletCharacter ℂ (band N f.1), star (ξ (-(u : ZMod (band N f.1))))*channelFunction f ξ s z := by
  unfold parameterFamily
  apply congrArg (fun c : ℂ => ((band N f.1).totient : ℂ)⁻¹*c)
  apply Finset.sum_congr rfl
  intro ξ _
  rw [inverse_value ξ _ u.isUnit.neg]
  rfl

/-- Both finite character directions hold on the actual continued
functions, even at an individual parameter where the span may lose rank. -/
theorem direct_channel {N : ℕ} [NeZero N] (f : Div N) (χ : DirichletCharacter ℂ (band N f.1))
    (s : ℂ) (z : ℍ) :
    (∑ u : (ZMod (band N f.1))ˣ, χ (-(u : ZMod (band N f.1)))*parameterFamily ⟨f,u⟩ s z) =
      channelFunction f χ s z := by
  classical
  let H := band N f.1
  let F := fun η : DirichletCharacter ℂ H => channelFunction f η s z
  let V := fun (η : DirichletCharacter ℂ H) (u : (ZMod H)ˣ) => η (-(u : ZMod H))
  have hc : (H.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne H))).ne'
  have hu (u : (ZMod H)ˣ) : V χ u * parameterFamily ⟨f,u⟩ s z =
      (H.totient : ℂ)⁻¹*∑ η : DirichletCharacter ℂ H,(V χ u*star (V η u))*F η := by
    rw [inverse_cusp]
    change V χ u*((H.totient : ℂ)⁻¹*∑ η : DirichletCharacter ℂ H,star (V η u)*F η) = _
    rw [mul_left_comm (V χ u),Finset.mul_sum (V χ u)]
    simp only [mul_assoc]
  change (∑ u : (ZMod H)ˣ,V χ u * parameterFamily ⟨f,u⟩ s z) = F χ
  simp_rw [hu]
  rw [← Finset.mul_sum,Finset.sum_comm]
  simp_rw [← Finset.sum_mul,show ∀ η : DirichletCharacter ℂ H,
    (∑ u : (ZMod H)ˣ,V χ u*star (V η u)) = if χ = η then (H.totient : ℂ) else 0 from unit_orthogonality χ,
    ite_mul,zero_mul]
  simp [hc]

abbrev physicalFamily (N : ℕ) [NeZero N] (t : ℝ) : Parameters N → (ℍ → ℂ) :=
  fun a => parameterFamily a (criticalPoint t)

abbrev Independent (N : ℕ) [NeZero N] (t : ℝ) := LinearIndependent ℂ (physicalFamily N t)

theorem ae_independent (N : ℕ) [NeZero N] : ∀ᵐ t : ℝ ∂volume, Independent N t := by
  filter_upwards [ae_native_cusps_independent N] with t ht
  simpa only [Function.comp_def,cuspFamily,Equiv.symm_apply_apply] using
    (linearIndependent_equiv (youngCuspEquiv N)).mpr ht

abbrev EisSpace (N : ℕ) [NeZero N] (t : ℝ) := Submodule.span ℂ (range (physicalFamily N t))

def cuspBasis {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t) :
    Module.Basis (Parameters N) ℂ (EisSpace N t) := Module.Basis.span h

/-- Formal product in Young's printed convention, with unique coordinates
of genuine functions in the actual physical span. -/
def formalProduct {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t) (v w : EisSpace N t) : ℂ :=
  (4*(Real.pi : ℂ))*∑ a : Parameters N, (cuspBasis h).repr v a * star ((cuspBasis h).repr w a)

theorem formal_add_left {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t) (v w u : EisSpace N t) :
    formalProduct h (v+w) u = formalProduct h v u + formalProduct h w u := by
  simp [formalProduct,map_add,Finsupp.add_apply,add_mul,Finset.sum_add_distrib,mul_add]

theorem formal_smul_left {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t)
    (c : ℂ) (v w : EisSpace N t) : formalProduct h (c • v) w = c*formalProduct h v w := by
  simp only [formalProduct,map_smul,Finsupp.smul_apply,smul_eq_mul,mul_assoc,← Finset.mul_sum]
  ring

theorem formal_symm {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t) (v w : EisSpace N t) :
    star (formalProduct h v w) = formalProduct h w v := by
  simp [formalProduct,star_mul,star_sum,mul_comm]

theorem formal_self {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t) (v : EisSpace N t) :
    formalProduct h v v = ((4*Real.pi*∑ a : Parameters N, Complex.normSq ((cuspBasis h).repr v a) : ℝ) : ℂ) := by
  simp only [formalProduct,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_sum,
    Complex.star_def,Complex.mul_conj]

theorem formal_positive {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t)
    (v : EisSpace N t) (hv : v ≠ 0) : 0 < (formalProduct h v v).re := by
  rw [formal_self,Complex.ofReal_re]
  apply mul_pos (mul_pos (by norm_num) Real.pi_pos)
  have hex : ∃ i, (cuspBasis h).repr v i ≠ 0 := by
    by_contra! he
    apply hv
    apply (cuspBasis h).repr.injective
    ext i
    simp [he]
  obtain ⟨i,hi⟩ := hex
  exact (Finset.sum_pos_iff_of_nonneg (fun j _ => Complex.normSq_nonneg _)).mpr
    ⟨i,Finset.mem_univ i,Complex.normSq_pos.mpr hi⟩

theorem cusp_gram {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t) (a b : Parameters N) :
    formalProduct h (cuspBasis h a) (cuspBasis h b) = if a = b then 4*(Real.pi : ℂ) else 0 := by
  classical
  simp only [formalProduct,Module.Basis.repr_self_apply]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a) (fun j _ hj => by simp [Ne.symm hj])]
  by_cases he : a = b <;> simp [he,eq_comm]

def classVector {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t) (f : Div N)
    (ξ : DirichletCharacter ℂ (band N f.1)) : EisSpace N t :=
  ∑ u : (ZMod (band N f.1))ˣ, ξ (-(u : ZMod (band N f.1))) • cuspBasis h ⟨f,u⟩

theorem classVector_value {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t) (f : Div N)
    (ξ : DirichletCharacter ℂ (band N f.1)) (z : ℍ) :
    (classVector h f ξ : ℍ → ℂ) z = channelFunction f ξ (criticalPoint t) z := by
  simpa only [classVector,Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,cuspBasis,Module.Basis.coe_span_apply,physicalFamily] using direct_channel f ξ (criticalPoint t) z

private theorem coordinate_on {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t) (f : Div N)
    (ξ : DirichletCharacter ℂ (band N f.1)) (u : (ZMod (band N f.1))ˣ) :
    (cuspBasis h).repr (classVector h f ξ) ⟨f,u⟩ = ξ (-(u : ZMod (band N f.1))) := by
  classical
  have he (v : (ZMod (band N f.1))ˣ) : ((⟨f,v⟩ : Parameters N) = ⟨f,u⟩) ↔ v = u :=
    sigma_mk_injective.eq_iff
  simp [classVector,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,
    Module.Basis.repr_self_apply,he,smul_eq_mul,mul_ite]

private theorem coordinate_off {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t)
    {f g : Div N} (hfg : f ≠ g) (ξ : DirichletCharacter ℂ (band N f.1))
    (u : (ZMod (band N g.1))ˣ) : (cuspBasis h).repr (classVector h f ξ) ⟨g,u⟩ = 0 := by
  classical
  have he (v : (ZMod (band N f.1))ˣ) : (⟨f,v⟩ : Parameters N) ≠ ⟨g,u⟩ :=
    fun e => hfg (congrArg Sigma.fst e)
  simp [classVector,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,Module.Basis.repr_self_apply,he]

theorem class_gram_same {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t) (f : Div N)
    (χ η : DirichletCharacter ℂ (band N f.1)) :
    formalProduct h (classVector h f χ) (classVector h f η) =
      if χ = η then 4*(Real.pi : ℂ)*((band N f.1).totient : ℂ) else 0 := by
  classical
  rw [formalProduct,Fintype.sum_sigma]
  rw [Finset.sum_eq_single_of_mem f (Finset.mem_univ f) (fun g _ hg => by
    simp only [coordinate_off h (Ne.symm hg),zero_mul,Finset.sum_const_zero])]
  simp_rw [coordinate_on]
  rw [unit_orthogonality]
  split_ifs <;> ring

theorem class_gram_different {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t) {f g : Div N}
    (hfg : f ≠ g) (χ : DirichletCharacter ℂ (band N f.1)) (η : DirichletCharacter ℂ (band N g.1)) :
    formalProduct h (classVector h f χ) (classVector h g η) = 0 := by
  classical
  rw [formalProduct,Fintype.sum_sigma]
  suffices (∑ j : Div N, ∑ u : (ZMod (band N j.1))ˣ,
    (cuspBasis h).repr (classVector h f χ) ⟨j,u⟩*star ((cuspBasis h).repr (classVector h g η) ⟨j,u⟩)) = 0 by
    rw [this,mul_zero]
  apply Finset.sum_eq_zero
  intro j _
  by_cases he : f = j
  · subst j
    simp [coordinate_off h (Ne.symm hfg)]
  · simp [coordinate_off h he]

theorem inverse_vector {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t)
    (f : Div N) (u : (ZMod (band N f.1))ˣ) :
    cuspBasis h ⟨f,u⟩ = ((band N f.1).totient : ℂ)⁻¹ •
      ∑ ξ : DirichletCharacter ℂ (band N f.1), star (ξ (-(u : ZMod (band N f.1)))) • classVector h f ξ := by
  apply Subtype.ext
  funext z
  simpa only [cuspBasis,Module.Basis.coe_span_apply,Submodule.coe_sum,Submodule.coe_smul,
    Pi.smul_apply,smul_eq_mul,Finset.sum_apply,classVector_value,physicalFamily] using
      inverse_cusp f u (criticalPoint t) z

/-- The denominators and primitive character pairs exhaust the actual
finite critical space on the very same full-measure set. -/
theorem class_spans {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t) :
    Submodule.span ℂ (range (fun i : CharacterSlots N => classVector h i.1 i.2)) = ⊤ := by
  let W := Submodule.span ℂ (range (fun i : CharacterSlots N => classVector h i.1 i.2))
  apply top_unique
  rw [← (cuspBasis h).span_eq]
  apply Submodule.span_le.mpr
  rintro v ⟨⟨f,u⟩,rfl⟩
  rw [inverse_vector h f u]
  apply W.smul_mem
  apply W.sum_mem
  intro ξ _
  exact W.smul_mem _ (Submodule.subset_span ⟨(⟨f,ξ⟩ : CharacterSlots N),rfl⟩)

private def leftPairing {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t) (w : EisSpace N t) :
    EisSpace N t →ₗ[ℂ] ℂ where
  toFun v := formalProduct h v w
  map_add' v u := formal_add_left h v u w
  map_smul' c v := formal_smul_left h c v w

theorem class_gram {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t) (i j : CharacterSlots N) :
    formalProduct h (classVector h i.1 i.2) (classVector h j.1 j.2) =
      if i = j then 4*(Real.pi : ℂ)*((band N i.1.1).totient : ℂ) else 0 := by
  classical
  obtain ⟨f,χ⟩ := i
  obtain ⟨g,η⟩ := j
  by_cases he : f = g
  · subst g
    have heq : ((⟨f,χ⟩ : CharacterSlots N) = ⟨f,η⟩) ↔ χ = η := sigma_mk_injective.eq_iff
    simpa only [heq] using class_gram_same h f χ η
  · have hne : (⟨f,χ⟩ : CharacterSlots N) ≠ ⟨g,η⟩ := fun e => he (congrArg Sigma.fst e)
    simpa only [if_neg hne] using class_gram_different h he χ η

theorem class_independent {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t) :
    LinearIndependent ℂ (fun i : CharacterSlots N => classVector h i.1 i.2) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  let L := leftPairing h (classVector h i.1 i.2)
  have hz := congrArg L hc
  simp only [map_sum,map_smul,smul_eq_mul,map_zero] at hz
  change (∑ j : CharacterSlots N,c j*formalProduct h (classVector h j.1 j.2) (classVector h i.1 i.2)) = 0 at hz
  simp_rw [class_gram,mul_ite,mul_zero] at hz
  have hci : c i*(4*(Real.pi : ℂ)*((band N i.1.1).totient : ℂ)) = 0 := by simpa using hz
  have hφ : ((band N i.1.1).totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne (band N i.1.1)))).ne'
  exact (mul_eq_zero.mp hci).resolve_right
    (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) hφ)

def orthogonalClassBasis {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t) :
    Module.Basis (CharacterSlots N) ℂ (EisSpace N t) :=
  Module.Basis.mk (class_independent h) (by rw [class_spans])

theorem orthogonalClassBasis_value {N : ℕ} [NeZero N] {t : ℝ} (h : Independent N t)
    (i : CharacterSlots N) (z : ℍ) :
    (orthogonalClassBasis h i : ℍ → ℂ) z = channelFunction i.1 i.2 (criticalPoint t) z := by
  rw [orthogonalClassBasis,Module.Basis.mk_apply]
  exact classVector_value h _ _ z

end
end ImbalancedChen.Part3.ActualYoungFormalClass20261110

