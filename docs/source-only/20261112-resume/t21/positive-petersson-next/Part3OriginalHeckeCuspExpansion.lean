import ImbalancedChen.Part3OriginalHeckePhysicalRow

namespace ImbalancedChen.Part3.OriginalHeckeCuspExpansion20261112

noncomputable section
open Set Complex UpperHalfPlane Matrix
open scoped MatrixGroups UpperHalfPlane ModularForm
open OriginalHeckeCosetRows20261112 OriginalHeckeRowSlash20261112
open OriginalHeckeStripPairing20261112 OriginalHolomorphicPoincare20261112
open OriginalHolomorphicCuspFilter20261112 OriginalHeckeFourierKernel20261112
open OriginalHeckeCuspSeries20261112 OriginalHeckePoisson20261112 OriginalHeckePhysicalRow20261112

def gateD (N : ℕ) (g : SL(2,ℤ)) (C : ℕ+) (D : ℤ) : Prop :=
  IsCoprime (C:ℤ) D ∧ (N:ℤ)∣(C:ℤ)*g 1 1-D*g 1 0

private def zeros (N : ℕ) (g : SL(2,ℤ)) : Set (Row N g) := {v | v.val 0=0}
private abbrev PosRow (N : ℕ) (g : SL(2,ℤ)) := ↥((zeros N g)ᶜ)

private theorem pos {N : ℕ} {g : SL(2,ℤ)} (v : PosRow N g) : 0<v.val.val 0 := by
  rcases v.val.property.2.2 with h|⟨h,_⟩
  · exact h
  · exact (v.property h).elim

private def index {N : ℕ} {g : SL(2,ℤ)} (v : PosRow N g) : ℕ+ :=
  ⟨(v.val.val 0).toNat,by have := pos v;omega⟩

private theorem c_index {N : ℕ} {g : SL(2,ℤ)} (v : PosRow N g) : (index v:ℤ)=v.val.val 0 :=
  Int.toNat_of_nonneg (pos v).le

private abbrev Fiber (N : ℕ) (g : SL(2,ℤ)) (C : ℕ+) :=
  ↥((index (N:=N) (g:=g)) ⁻¹' {C})

private theorem c_fiber {N : ℕ} {g : SL(2,ℤ)} {C : ℕ+} (v : Fiber N g C) :
    v.val.val.val 0=(C:ℤ) := by
  rw [← c_index v.val,show index v.val=C from v.property]

private def fiberEquiv (N : ℕ) (g : SL(2,ℤ)) (C : ℕ+) :
    Fiber N g C ≃ {D : ℤ // gateD N g C D} where
  toFun v := ⟨v.val.val.val 1,by
    change IsCoprime (C:ℤ) _ ∧ _
    rw [← c_fiber v]
    exact ⟨v.val.val.property.1,v.val.val.property.2.1⟩⟩
  invFun D := by
    have h : 0<(C:ℤ) := by exact_mod_cast C.property
    let v : Row N g := ⟨![(C:ℤ),D.val],D.property.1,D.property.2,Or.inl h⟩
    let v' : PosRow N g := ⟨v,h.ne'⟩
    exact ⟨v',by apply Subtype.ext;change ((C:ℤ).toNat)=(C:ℕ);simp⟩
  left_inv v := by apply Subtype.ext;apply Subtype.ext;apply Subtype.ext
                   funext j;fin_cases j
                   · exact (c_fiber v).symm
                   · rfl
  right_inv D := by apply Subtype.ext;rfl

private theorem lift_test {N : ℕ} [NeZero N] {g : SL(2,ℤ)} {C : ℕ+}
    (t : ZMod (C:ℕ)×ZMod N×ℤ) : gateD N g C (liftedD t) ↔
    IsUnit t.1 ∧ (N:ℤ)∣(C:ℤ)*g 1 1-Dval C t.1 t.2.1*g 1 0 := by
  rw [gateD,← ZMod.coe_int_isUnit_iff_isCoprime,(residues t).1,lift_gate]

theorem denominator_integer (N k m : ℕ) [NeZero N] (g : SL(2,ℤ)) (C : ℕ+)
    (p : Params) (ht : Summable (fun D : {D : ℤ // gateD N g C D} => term k m C D.val p)) :
    (∑' D : {D : ℤ // gateD N g C D},term k m C D.val p)=denominator N k m g C p := by
  classical
  let T := term k m C · p
  let S := {D : ℤ | gateD N g C D}
  let U := fun t : ZMod (C:ℕ)×ZMod N×ℤ => S.indicator T (liftedD t)
  have hu : Summable U := (liftEquiv C N).summable_iff.mpr (summable_subtype_iff_indicator.mp ht)
  calc
    _ = ∑' t : ZMod (C:ℕ)×ZMod N×ℤ,U t := by
      rw [tsum_subtype S T];exact ((liftEquiv C N).tsum_eq _).symm
    _ = ∑ u : ZMod (C:ℕ),∑ j : ZMod N,∑' l : ℤ,U (u,j,l) := by
      rw [hu.tsum_prod,tsum_fintype]
      apply Finset.sum_congr rfl;intro u _
      rw [(hu.prod_factor u).tsum_prod,tsum_fintype]
    _ = _ := by
      unfold denominator
      change _=factor k C p*_
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl;intro u _
      by_cases h : IsUnit u
      · simp only [if_pos h,Finset.mul_sum]
        apply Finset.sum_congr rfl;intro j _
        by_cases hj : (N:ℤ)∣(C:ℤ)*g 1 1-Dval C u j*g 1 0
        · simp only [if_pos hj]
          simp only [U,Set.indicator_apply,S,Set.mem_setOf_eq,lift_test,h,hj,and_self,if_true,T,
            term_lift,tsum_mul_left,mul_assoc]
        · simp [U,Set.indicator_apply,S,lift_test,h,hj]
      · simp [U,Set.indicator_apply,S,lift_test,h]

private theorem fixed_sum (N r m : ℕ) [NeZero N] (hr : 0<r) (g : SL(2,ℤ)) (C : ℕ+)
    (p : Params) (hs : 0<p.1.val) :
    (∑' v : Fiber N g C, (heckeSeed m p.1.val ∣[2*(r:ℤ)] matrix v.val.val) p.2) =
      denominator N (2*r) m g C p := by
  classical
  let f := fun v : Row N g => (heckeSeed m p.1.val ∣[2*(r:ℤ)] matrix v) p.2
  let T := term (2*r) m C · p
  let S := {D : ℤ | gateD N g C D}
  let E := fiberEquiv N g C
  have hv (v : Fiber N g C) : f v.val.val=T (E v).val := by
    have a := congrFun (row_matrix v.val.val) 0
    have d := congrFun (row_matrix v.val.val) 1
    change matrix v.val.val 1 0=v.val.val.val 0 at a
    change matrix v.val.val 1 1=v.val.val.val 1 at d
    exact (physical_row r m _ C (a.trans (c_fiber v)) p).trans (by rw [d];rfl)
  have hb := (((rows_norm_summable N r m hr hs g p.2).of_norm.subtype _).subtype
    (fun v : PosRow N g => index v∈({C}:Set ℕ+)))
  have ht : Summable (fun D : S => T D.val) := E.summable_iff.mp
    (hb.congr (fun v => hv v))
  exact (tsum_congr hv).trans ((E.tsum_eq _).trans (denominator_integer N (2*r) m g C p ht))

def diagonal (N m : ℕ) (g : SL(2,ℤ)) (p : Params) : ℂ :=
  if (N:ℤ)∣g 1 0 then heckeSeed m p.1.val p.2 else 0

private theorem zero_sum (N r m : ℕ) (g : SL(2,ℤ)) (p : Params) :
    (∑' v : zeros N g, (heckeSeed m p.1.val ∣[2*(r:ℤ)] matrix v.val) p.2) =
      diagonal N m g p := by
  classical
  by_cases h : (N:ℤ)∣g 1 0
  · obtain ⟨v,hv⟩ := (exists_zero_iff g).mpr h
    let z : zeros N g := ⟨v,hv⟩
    have hu (v' : zeros N g) : v'=z := Subtype.ext (zero_row_unique _ _ v'.property hv)
    rw [tsum_eq_single z (fun v' hn => (hn (hu v')).elim),diagonal,if_pos h]
    exact congrFun (zero_seed (r:=r) (m:=m) p.1.val v hv) p.2
  · letI : IsEmpty (zeros N g) := ⟨fun v => h (zero_row v.val v.property).2⟩
    simp [diagonal,h]

def expansion (N r m : ℕ) [NeZero N] (g : SL(2,ℤ)) (p : Params) : ℂ :=
  diagonal N m g p+series N (2*r) m g p

/-- Every positive-s Hecke family in every integral cusp equals the SAME jointly controlled
Fourier series, with its unique possible zero denominator explicitly restored. -/
theorem heckeP_expansion (N r m : ℕ) [NeZero N] (hr : 0<r) (hm : 0<m) (g : SL(2,ℤ))
    (p : Params) (hs : 0<p.1.val) :
    (heckeP N r m p.1.val ∣[2*(r:ℤ)] g) p.2=expansion N r m g p := by
  let f := fun v : Row N g => (heckeSeed m p.1.val ∣[2*(r:ℤ)] matrix v) p.2
  have hf : Summable f := (rows_norm_summable N r m hr hs g p.2).of_norm
  have H := (hf.subtype (·∈(zeros N g)ᶜ)).hasSum.tsum_fiberwise (index (N:=N) (g:=g))
  have Hp : HasSum (fun C : ℕ+ => denominator N (2*r) m g C p) (∑' v : PosRow N g,f v.val) :=
    H.congr_fun (fun C => (fixed_sum N r m hr g C p hs).symm)
  have V := Hp.unique (denominators_sum N (2*r) m (by omega) hm g p)
  rw [heckeP_rows,← hf.tsum_subtype_add_tsum_subtype_compl (zeros N g),expansion,← V]
  exact congrArg (fun a : ℂ => a+_) (zero_sum N r m g p)

end
end ImbalancedChen.Part3.OriginalHeckeCuspExpansion20261112
