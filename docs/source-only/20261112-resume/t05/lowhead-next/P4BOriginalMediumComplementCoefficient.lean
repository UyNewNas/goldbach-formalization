import ImbalancedChen.P4BOriginalMediumHBHead

/-! Group the other HB integers by their original product on a fixed
complementary dyadic fibre. The distinguished coordinate is set to one
only in the indexing word used to store the other coordinates. -/
namespace ImbalancedChen.P4BOriginalMediumComplementCoefficient
noncomputable section
open Classical
open scoped BigOperators
open P5Z.HBRightClosedDyadicRoles (Block Owns owner owner_owns)
open P5Z.OrderedFactorTupleRectangleReindex (rectangle mem_rectangle owns_pos blockIntegers mem_blockIntegers)
open P5Z.ActualHBPostModulusLogCutoff (completeProduct hbSlots hb_fibre_card_le)
open P5Z.ActualAllRankOccurrenceFourierBridge (occurrenceMode)
open P5Z.ActualRoughHeathBrownWords (Role)
open P4BUpperPairOrderedRowGeometry (blockScales)
open P4BOriginalHighRankComplementBlocks (fibre complement independent)
open P4BOriginalMediumHBHead (alpha alpha_one scalar normalized_product)

variable {t : ℕ}
def pin (i : Fin t) (y : Fin t→ℕ) : Fin t→ℕ := Function.update y i 1

def otherWords (bs : Fin t→Block) (i : Fin t) (B : Block) :=
  (fibre bs i B).image (pin i)

def otherWeight (bs : Fin t→Block) (i : Fin t) (Z : ℝ) (ys : Fin t→ℝ)
    (rs : Fin t→Role) (ξ : Fin t→ℝ) (y : Fin t→ℕ) : ℂ :=
  ∏ j∈Finset.univ.erase i,alpha (bs j) Z (ys j) (rs j) (ξ j) (y j)

def beta (bs : Fin t→Block) (i : Fin t) (B : Block) (Z : ℝ) (ys : Fin t→ℝ)
    (rs : Fin t→Role) (ξ : Fin t→ℝ) (m : ℕ) : ℂ :=
  ∑ y∈(otherWords bs i B).filter (fun y => completeProduct y=m),otherWeight bs i Z ys rs ξ y

private theorem product_split (i : Fin t) (y : Fin t→ℕ) :
    completeProduct y=y i*complement i y :=
  (Finset.mul_prod_erase Finset.univ y (Finset.mem_univ i)).symm

theorem pinned_product (i : Fin t) (y : Fin t→ℕ) : completeProduct (pin i y)=complement i y := by
  rw [product_split]
  simp only [pin,Function.update_self,one_mul]
  exact independent i (fun j hj => Function.update_of_ne hj _ _)

private theorem pinned_weight (bs : Fin t→Block) (i : Fin t) (Z : ℝ) (ys : Fin t→ℝ)
    (rs : Fin t→Role) (ξ : Fin t→ℝ) (y : Fin t→ℕ) :
    otherWeight bs i Z ys rs ξ (pin i y)=otherWeight bs i Z ys rs ξ y := by
  apply Finset.prod_congr rfl
  intro j hj
  simp only [pin,Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem other_mem {bs : Fin t→Block} {i : Fin t} {B : Block} {z : Fin t→ℕ}
    (hz : z∈otherWords bs i B) : completeProduct z∈blockIntegers B := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hyr,hw⟩ := Finset.mem_filter.mp hy
  rw [pinned_product]
  have hp : 0<complement i y :=
    Finset.prod_pos (fun j _ => owns_pos ((mem_rectangle bs y).mp hyr j))
  exact (mem_blockIntegers _ _).mpr (hw ▸ owner_owns hp)

private theorem words_image (bs : Fin t→Block) (i : Fin t) (B : Block) :
    (fibre bs i B).image (fun y => (y i,pin i y)) =
      (blockIntegers (bs i)).product (otherWords bs i B) := by
  ext p
  rcases p with ⟨a,z⟩
  constructor
  · intro h
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp h
    rw [←he]
    exact Finset.mem_product.mpr ⟨(mem_blockIntegers _ _).mpr
      ((mem_rectangle bs y).mp (Finset.mem_filter.mp hy).1 i),Finset.mem_image.mpr ⟨y,hy,rfl⟩⟩
  · intro h
    obtain ⟨ha,hz⟩ := Finset.mem_product.mp h
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
    let w := Function.update y i a
    have hw : w∈fibre bs i B := by
      obtain ⟨hyr,hown⟩ := Finset.mem_filter.mp hy
      apply Finset.mem_filter.mpr
      constructor
      · apply (mem_rectangle bs w).mpr
        intro j
        by_cases hji : j=i
        · subst j
          simpa only [w,Function.update_self] using (mem_blockIntegers _ _).mp ha
        · simpa only [w,Function.update_of_ne hji] using (mem_rectangle bs y).mp hyr j
      · exact (congrArg owner (independent i (u:=w) (v:=y)
          (fun j hj => Function.update_of_ne hj _ _))).trans hown
    apply Finset.mem_image.mpr
    refine ⟨w,hw,Prod.ext (by simp [w]) ?_⟩
    funext j
    by_cases hji : j=i <;> simp [pin,w,hji,Function.update_of_ne]

private theorem word_sum (bs : Fin t→Block) (i : Fin t) (B : Block) (F : ℕ→(Fin t→ℕ)→ℂ) :
    (∑ y∈fibre bs i B,F (y i) (pin i y)) =
      ∑ n∈blockIntegers (bs i),∑ z∈otherWords bs i B,F n z := by
  have hinj : Function.Injective (fun y : Fin t→ℕ => (y i,pin i y)) := by
    intro a b h
    funext j
    by_cases hj : j=i
    · subst j; exact congrArg Prod.fst h
    · simpa only [pin,Function.update_of_ne hj] using congrFun (congrArg Prod.snd h) j
  rw [←Finset.sum_product,←words_image]
  exact (Finset.sum_image (g:=fun y : Fin t→ℕ => (y i,pin i y))
    (f:=fun p => F p.1 p.2) (fun _ _ _ _ he => hinj he)).symm

theorem beta_apply (bs : Fin t→Block) (i : Fin t) (B : Block) (Z : ℝ) (ys : Fin t→ℝ)
    (rs : Fin t→Role) (ξ : Fin t→ℝ) (F : ℕ→ℂ) :
    (∑ m∈blockIntegers B,beta bs i B Z ys rs ξ m*F m)=
      ∑ z∈otherWords bs i B,otherWeight bs i Z ys rs ξ z*F (completeProduct z) := by
  rw [←Finset.sum_fiberwise_of_maps_to (s:=otherWords bs i B) (t:=blockIntegers B)
    (g:=completeProduct) (fun _ hz => other_mem hz) (fun z => otherWeight bs i Z ys rs ξ z*F (completeProduct z))]
  apply Finset.sum_congr rfl
  intro m _
  unfold beta
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun z hz => by rw [(Finset.mem_filter.mp hz).2])

theorem beta_norm (bs : Fin t→Block) (i : Fin t) (B : Block) (Z : ℝ)
    (ys : Fin t→ℝ) (rs : Fin t→Role) (ξ : Fin t→ℝ) {m : ℕ} (hm : 0<m) :
    ‖beta bs i B Z ys rs ξ m‖≤(m.divisors.card:ℝ)^t := by
  unfold beta
  apply (norm_sum_le _ _).trans
  have h z : ‖otherWeight bs i Z ys rs ξ z‖≤1 := by
    unfold otherWeight
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun j _ => alpha_one _ _ _ _ _ _)
  have H := Finset.sum_le_sum (s:=(otherWords bs i B).filter (fun y => completeProduct y=m)) (fun z _ => h z)
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at H
  exact H.trans (by exact_mod_cast hb_fibre_card_le (otherWords bs i B) m hm)

theorem separated (bs : Fin t→Block) (i : Fin t) (B : Block) (Z : ℝ)
    (ys : Fin t→ℝ) (rs : Fin t→Role) (ξ : Fin t→ℝ) (F : ℕ→ℂ) :
    (∑ y∈fibre bs i B,hbSlots Z ys rs y*occurrenceMode (blockScales bs) y ξ*F (completeProduct y)) =
      ((∏ j,scalar (bs j) (rs j):ℝ):ℂ) *
      ∑ n∈blockIntegers (bs i),∑ m∈blockIntegers B,
        alpha (bs i) Z (ys i) (rs i) (ξ i) n*beta bs i B Z ys rs ξ m*F (n*m) := by
  let D : ℂ := ((∏ j,scalar (bs j) (rs j):ℝ):ℂ)
  let a := alpha (bs i) Z (ys i) (rs i) (ξ i)
  let W := otherWeight bs i Z ys rs ξ
  let f (n : ℕ) (z : Fin t→ℕ) := a n*W z*F (n*completeProduct z)
  calc
    _ = D*∑ y∈fibre bs i B,f (y i) (pin i y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      rw [normalized_product bs Z ys rs ξ (Finset.mem_filter.mp hy).1,
        ←Finset.mul_prod_erase Finset.univ (fun j => alpha (bs j) Z (ys j) (rs j) (ξ j) (y j)) (Finset.mem_univ i)]
      dsimp only [f,a,W,D]
      rw [pinned_weight,pinned_product,product_split i y]
      dsimp only [otherWeight]
      ring
    _ = D*∑ n∈blockIntegers (bs i),∑ z∈otherWords bs i B,f n z := by rw [word_sum]
    _ = _ := by
      apply congrArg (fun v : ℂ => D*v)
      apply Finset.sum_congr rfl
      intro n _
      have hb := beta_apply bs i B Z ys rs ξ (fun m => F (n*m))
      calc
        _ = a n*∑ z∈otherWords bs i B,W z*F (n*completeProduct z) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by dsimp [f]; ring)
        _ = a n*∑ m∈blockIntegers B,beta bs i B Z ys rs ξ m*F (n*m) := by rw [←hb]
        _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by dsimp [a]; ring)

end
end ImbalancedChen.P4BOriginalMediumComplementCoefficient
