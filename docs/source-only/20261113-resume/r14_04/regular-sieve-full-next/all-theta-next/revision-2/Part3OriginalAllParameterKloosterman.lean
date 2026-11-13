import ImbalancedChen.Part3OriginalTwistedRectangle
import ImbalancedChen.Part3OriginalTwistedKloosterman
import ImbalancedChen.Part3KloostermanConjugation

/-! Summation of the actual two-dimensional dyadic Kloosterman form over
the physical rectangles with independently chosen input vectors. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalAllParameterKloosterman20261113
open Complex Finset
open OriginalTwistedKloosterman20261113 (twistedForm)
open OriginalIntervalFoldedKloosterman20261113 (intervalEnergy)
open OriginalTwistedRectangle20261113 (rect rectangular_twisted_bound)
open OriginalTwistedSqrtTaylor20261113 (fullFactor)
open OriginalSmoothPoissonTail (kloosterman)

def P (M H : ℕ) := M/H+1
def low (M H s : ℕ) := M+s*H
def high (M H s : ℕ) := min (M+(s+1)*H) (2*M+1)
def slice (M H s : ℕ) := Ico (low M H s) (high M H s)

private theorem bounds {M H s : ℕ} (hH : 0<H) (hs : s<P M H) :
    low M H s≤high M H s ∧ high M H s-low M H s≤H ∧ M≤low M H s := by
  have cut := (Nat.le_div_iff_mul_le hH).mp (show s≤M/H by unfold P at hs;omega)
  simp only [low,high,Nat.add_mul,one_mul]
  omega

private theorem partition {V : Type*} [AddCommMonoid V] {M H : ℕ} (hH : 0<H) (f : ℕ → V) :
    (∑ s∈range (P M H),∑ n∈slice M H s,f n)=∑ n∈Ico M (2*M+1),f n := by
  let key := fun n : ℕ => (n-M)/H
  have ix {n : ℕ} (hn : n∈Ico M (2*M+1)) : key n∈range (P M H) := by
    have dn : n-M≤M := by obtain ⟨a,b⟩ := mem_Ico.mp hn;omega
    unfold key P
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right dn))
  have cut (s : ℕ) : slice M H s=(Ico M (2*M+1)).filter (fun n => key n=s) := by
    ext n
    simp only [slice,low,high,mem_Ico,lt_min_iff,mem_filter,key]
    constructor
    · rintro ⟨ha,hb,hc⟩
      have L : s*H≤n-M := by omega
      have U : n-M<(s+1)*H := by omega
      exact ⟨⟨by omega,hc⟩,le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hH).mpr U))
        ((Nat.le_div_iff_mul_le hH).mpr L)⟩
    · rintro ⟨⟨hm,hn⟩,he⟩
      have L := (Nat.le_div_iff_mul_le hH).mp he.ge
      have U := (Nat.div_lt_iff_lt_mul hH).mp (show (n-M)/H<s+1 by omega)
      exact ⟨by omega,by omega,hn⟩
  simp_rw [cut]
  exact sum_fiberwise_of_maps_to (s:=Ico M (2*M+1)) (t:=range (P M H)) (g:=key)
    (fun n hn => ix hn) f

private theorem shifted {V : Type*} [AddCommMonoid V] (M : ℕ) (f : ℕ → V) :
    (∑ n∈Ico M (2*M+1),f n)=∑ i∈range (M+1),f (M+i) := by
  rw [sum_Ico_eq_sum_range,show 2*M+1-M=M+1 by omega] <;>
    exact sum_congr rfl (fun i _ => congrArg f (by omega))

def dyadEnergy (M : ℕ) (a : ℕ → ℂ) := ∑ i∈range (M+1),‖a (M+i)‖^2

private theorem energy_partition {M H : ℕ} (hH : 0<H) (a : ℕ → ℂ) :
    (∑ s∈range (P M H),intervalEnergy (low M H s) (high M H s) a)=dyadEnergy M a :=
  (partition hH (fun n => ‖a n‖^2)).trans (shifted M _)

private theorem sum_root_energy {M H : ℕ} (hH : 0<H) (a : ℕ → ℂ) :
    (∑ s∈range (P M H),Real.sqrt (intervalEnergy (low M H s) (high M H s) a))≤
      Real.sqrt (P M H)*Real.sqrt (dyadEnergy M a) := by
  let E := fun s => intervalEnergy (low M H s) (high M H s) a
  have pos (s : ℕ) : 0≤E s := sum_nonneg (fun _ _ => sq_nonneg _)
  have hc := sum_mul_sq_le_sq_mul_sq (range (P M H)) (fun _ => (1:ℝ)) (fun s => Real.sqrt (E s))
  simp only [one_mul,one_pow,sum_const,card_range,nsmul_eq_mul,mul_one,Real.sq_sqrt (pos _)] at hc
  have R := Real.sqrt_le_sqrt hc
  rw [Real.sqrt_sq (sum_nonneg (fun _ _ => Real.sqrt_nonneg _)),Real.sqrt_mul (Nat.cast_nonneg _)] at R
  simpa only [E,energy_partition hH] using R

theorem size_H_bound {M c H : ℕ} [NeZero c] (hM : 0<M) (hH : 0<H) (hHM : H≤M)
    {lam θ : ℝ} (hlam : 0≤lam) (hθ : 0≤θ) (cross : θ*(H:ℝ)^2≤c*(M:ℝ)) (a b : ℕ → ℂ) :
    ‖twistedForm M c lam θ a b‖≤Real.exp (4*Real.pi)*
      (((P M H:ℕ):ℝ)*((c:ℝ)+H))*Real.sqrt (dyadEnergy M a)*Real.sqrt (dyadEnergy M b) := by
  let T := fun m n : ℕ => (a m*b n*kloosterman c (m:ℤ) (n:ℤ))*
    fullFactor lam θ c (Real.sqrt m) (Real.sqrt n)
  let R := range (P M H)
  let A := fun s => Real.sqrt (intervalEnergy (low M H s) (high M H s) a)
  let B := fun s => Real.sqrt (intervalEnergy (low M H s) (high M H s) b)
  let W := Real.exp (4*Real.pi)*((c:ℝ)+H)
  have W0 : 0≤W := by dsimp [W];positivity
  have part (s : ℕ) (hs : s∈R) (t : ℕ) (ht : t∈R) :
      ‖∑ m∈slice M H s,∑ n∈slice M H t,T m n‖≤W*A s*B t := by
    obtain ⟨ab,sl,sa⟩ := bounds hH (mem_range.mp hs)
    obtain ⟨cd,tl,ta⟩ := bounds hH (mem_range.mp ht)
    apply (rectangular_twisted_bound hM hH hHM ab cd sa ta sl tl hlam hθ cross a b).trans_eq
    dsimp only [W,A,B];ring
  have flat : (∑ s∈R,∑ t∈R,∑ m∈slice M H s,∑ n∈slice M H t,T m n)=twistedForm M c lam θ a b := by
    calc
      _=∑ s∈R,∑ m∈slice M H s,∑ t∈R,∑ n∈slice M H t,T m n :=
        sum_congr rfl (fun s hs => sum_comm)
      _=∑ s∈R,∑ m∈slice M H s,∑ n∈Ico M (2*M+1),T m n := by
        exact sum_congr rfl (fun s hs => sum_congr rfl (fun m hm => partition hH (T m)))
      _=∑ m∈Ico M (2*M+1),∑ n∈Ico M (2*M+1),T m n := partition hH _
      _=_ := by
        rw [shifted M]
        apply sum_congr rfl
        intro i hi
        exact shifted M (T (M+i))
  rw [←flat]
  calc
    _≤∑ s∈R,‖∑ t∈R,∑ m∈slice M H s,∑ n∈slice M H t,T m n‖ := norm_sum_le _ _
    _≤∑ s∈R,∑ t∈R,W*A s*B t := sum_le_sum (fun s hs =>
      (norm_sum_le _ _).trans (sum_le_sum (fun t ht => part s hs t ht)))
    _=W*(∑ s∈R,A s)*(∑ t∈R,B t) := by
      rw [mul_sum R A W,sum_mul]
      exact sum_congr rfl (fun s _ => (mul_sum _ _ _).symm)
    _≤W*(Real.sqrt (P M H)*Real.sqrt (dyadEnergy M a))*
        (Real.sqrt (P M H)*Real.sqrt (dyadEnergy M b)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (sum_root_energy hH a) W0)
        (sum_root_energy hH b) (sum_nonneg (fun _ _ => Real.sqrt_nonneg _)) (by positivity)
    _=_ := by
      dsimp only [W]
      have e := Real.sq_sqrt (show 0≤(P M H:ℝ) by positivity)
      linear_combination Real.exp (4*Real.pi)*((c:ℝ)+H)*Real.sqrt (dyadEnergy M a)*Real.sqrt (dyadEnergy M b)*e

private theorem singleton_cost (c : ℕ) [NeZero c] (m n : ℕ) :
    ‖kloosterman c (m:ℤ) (n:ℤ)‖≤c := by
  rw [OriginalSmoothPoissonTail.Physical.kloosterman_eq_zmod]
  calc
    _≤_ := norm_sum_le _ _
    _≤∑ _ : ZMod c,(1:ℝ) := by
      apply sum_le_sum
      intro r hr
      split_ifs <;> simp [ZMod.stdAddChar_apply,Circle.norm_coe]
    _=_ := by simp [ZMod.card]

private theorem trivial_bound (M c : ℕ) [NeZero c] {lam : ℝ} (hlam : 0≤lam) (θ : ℝ)
    (a b : ℕ → ℂ) :
    ‖twistedForm M c lam θ a b‖≤(c:ℝ)*(M+1)*
      Real.sqrt (dyadEnergy M a)*Real.sqrt (dyadEnergy M b) := by
  let S := range (M+1)
  have one (i j : ℕ) :
      ‖(a (M+i)*b (M+j)*kloosterman c (M+i:ℕ) (M+j:ℕ))*
        fullFactor lam θ c (Real.sqrt (M+i:ℕ)) (Real.sqrt (M+j:ℕ))‖≤
        c*‖a (M+i)‖*‖b (M+j)‖ := by
    have ed : Real.exp (-lam*Real.sqrt (M+i:ℕ)*Real.sqrt (M+j:ℕ))≤1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlam) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    simp only [fullFactor,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
      OAI.Problem337.ExponentialSum.phase_norm,mul_one]
    apply (mul_le_of_le_one_right (by positivity) ed).trans
    have z := mul_le_mul_of_nonneg_left (singleton_cost c (M+i) (M+j))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    convert z using 1 <;>ring
  have cauchy (a : ℕ → ℂ) : (∑ i∈S,‖a (M+i)‖)≤Real.sqrt (M+1:ℕ)*Real.sqrt (dyadEnergy M a) := by
    have H := sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun i => ‖a (M+i)‖)
    have T := Real.sqrt_le_sqrt H
    simpa only [S,one_mul,one_pow,sum_const,card_range,nsmul_eq_mul,mul_one,
      Real.sqrt_sq (sum_nonneg (fun _ _ => norm_nonneg _)),Real.sqrt_mul (Nat.cast_nonneg _),
      dyadEnergy] using T
  calc
    _≤∑ i∈S,∑ j∈S,c*‖a (M+i)‖*‖b (M+j)‖ := (norm_sum_le _ _).trans
      (sum_le_sum (fun i hi => (norm_sum_le _ _).trans (sum_le_sum (fun j hj => one i j))))
    _=(c:ℝ)*(∑ i∈S,‖a (M+i)‖)*(∑ j∈S,‖b (M+j)‖) := by
      rw [mul_sum S (fun i => ‖a (M+i)‖) (c:ℝ),sum_mul]
      exact sum_congr rfl (fun i _ => (mul_sum _ _ _).symm)
    _≤(c:ℝ)*(Real.sqrt (M+1:ℕ)*Real.sqrt (dyadEnergy M a))*
        (Real.sqrt (M+1:ℕ)*Real.sqrt (dyadEnergy M b)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (cauchy a) (Nat.cast_nonneg _)) (cauchy b)
        (sum_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
    _=_ := by
      have E := Real.sq_sqrt (show 0≤((M+1:ℕ):ℝ) by positivity)
      simp only [Nat.cast_add,Nat.cast_one] at E ⊢
      linear_combination (c:ℝ)*Real.sqrt (dyadEnergy M a)*Real.sqrt (dyadEnergy M b)*E

def allCost (M c : ℕ) (θ : ℝ) : ℝ := c+(M:ℝ)+Real.sqrt (θ*c*M)

/-- Unrestricted nonnegative oscillation, all positive moduli including
the long-modulus tail, and arbitrary damping. The coefficient of
c+M+sqrt(θ c M) is absolute. -/
theorem all_parameter_bound (M c : ℕ) [NeZero c] (hM : 0<M) {lam θ : ℝ}
    (hlam : 0≤lam) (hθ : 0≤θ) (a b : ℕ → ℂ) :
    ‖twistedForm M c lam θ a b‖≤4*Real.exp (4*Real.pi)*allCost M c θ*
      Real.sqrt (dyadEnergy M a)*Real.sqrt (dyadEnergy M b) := by
  have cp : 0<(c:ℝ) := by exact_mod_cast NeZero.pos c
  have mp : 0<(M:ℝ) := by exact_mod_cast hM
  have M1 : 1≤(M:ℝ) := by exact_mod_cast (show 1≤M by omega)
  have K0 := Real.sqrt_nonneg (θ*c*M)
  have e1 : 1≤Real.exp (4*Real.pi) := Real.one_le_exp_iff.mpr (by positivity)
  have pay {H : ℕ} (hp : 0<H) (hH : H≤M) (cross : θ*(H:ℝ)^2≤c*(M:ℝ))
      (bill : (P M H:ℝ)*(c+(H:ℝ))≤4*allCost M c θ) :
      ‖twistedForm M c lam θ a b‖≤4*Real.exp (4*Real.pi)*allCost M c θ*
        Real.sqrt (dyadEnergy M a)*Real.sqrt (dyadEnergy M b) := by
    apply (size_H_bound hM hp hH hlam hθ cross a b).trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    have := mul_le_mul_of_nonneg_left bill (Real.exp_pos (4*Real.pi)).le
    linarith only [this]
  by_cases small : θ*(M:ℝ)≤c
  · apply pay hM le_rfl
    · have := mul_le_mul_of_nonneg_right small mp.le
      linarith only [this]
    · simp only [P,Nat.div_self hM,Nat.reduceAdd,Nat.cast_ofNat,allCost]
      nlinarith only [mp,cp,K0]
  by_cases big : c*(M:ℝ)≤θ
  · have size : (c:ℝ)*M≤Real.sqrt (θ*c*M) := by
      apply (Real.le_sqrt (mul_nonneg cp.le mp.le) (by positivity)).2
      have := mul_le_mul_of_nonneg_right big (mul_nonneg cp.le mp.le)
      nlinarith only [this]
    have mult := mul_le_mul_of_nonneg_left M1 cp.le
    have bill : (c:ℝ)*(M+1)≤2*allCost M c θ := by
      dsimp [allCost]
      nlinarith only [mult,size,mp,cp,K0]
    have T := trivial_bound M c hlam θ a b
    apply T.trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    have V := mul_le_mul_of_nonneg_right e1 (show 0≤allCost M c θ by dsimp [allCost];positivity)
    nlinarith only [bill,V,mul_nonneg (Real.exp_pos (4*Real.pi)).le
      (show 0≤allCost M c θ by dsimp [allCost];positivity)]
  have tp : 0<θ := by
    rcases hθ.eq_or_lt with e|e
    · subst θ;simp [cp.le] at small
    · exact e
  let x := Real.sqrt ((c:ℝ)*M/θ)
  have xp : 0<x := Real.sqrt_pos.mpr (div_pos (mul_pos cp mp) tp)
  have x2 : x^2=(c:ℝ)*M/θ := Real.sq_sqrt (by positivity)
  have eqx : θ*x^2=c*M := by rw [x2];field_simp [tp.ne']
  have x1 : 1≤x := by
    dsimp only [x]
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by rw [one_pow];exact (le_div_iff₀ tp).mpr (by linarith only [lt_of_not_ge big]))
  have xM : x≤M := by
    apply Real.sqrt_le_iff.mpr ⟨mp.le,?_⟩
    apply (div_le_iff₀ tp).mpr
    have := mul_le_mul_of_nonneg_right (lt_of_not_ge small).le mp.le
    nlinarith only [this]
  let H := Nat.floor x
  have HL : (H:ℝ)≤x := Nat.floor_le xp.le
  have H1 : 0<H := Nat.floor_pos.mpr x1
  have HH := Nat.lt_floor_add_one x
  have HL2 : x≤2*(H:ℝ) := by
    have hi : 1≤(H:ℝ) := by exact_mod_cast (show 1≤H by omega)
    dsimp only [H] at hi
    dsimp only [H];linarith only [HH,hi]
  have HM : H≤M := by exact_mod_cast HL.trans xM
  have hp : 0<(H:ℝ) := by exact_mod_cast H1
  apply pay H1 HM
  · have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp.le HL 2) tp.le
    linarith only [eqx,this]
  · have sqK := Real.sq_sqrt (show 0≤θ*c*M by positivity)
    have Kx : Real.sqrt (θ*c*M)*x=(c:ℝ)*M := by
      apply (sq_eq_sq₀ (mul_nonneg K0 xp.le) (mul_nonneg cp.le mp.le)).mp
      rw [mul_pow,sqK,x2]
      field_simp [tp.ne'] <;>ring
    have Pcap : (P M H:ℝ)≤(M:ℝ)/H+1 := by
      simp only [P,Nat.cast_add,Nat.cast_one]
      exact add_le_add_left Nat.cast_div_le _
    have J : (c:ℝ)*M/H≤2*Real.sqrt (θ*c*M) := (div_le_iff₀ hp).mpr (by
      have := mul_le_mul_of_nonneg_left HL2 K0
      nlinarith only [this,Kx])
    have C := mul_le_mul_of_nonneg_right Pcap (show 0≤(c:ℝ)+H by positivity)
    have E : ((M:ℝ)/H+1)*((c:ℝ)+H)=(c:ℝ)*M/H+M+c+H := by field_simp [hp.ne'] <;>ring
    rw [E] at C
    have hi : (H:ℝ)≤M := by exact_mod_cast HM
    dsimp [allCost]
    linarith only [C,J,hi,cp,mp,K0]

private theorem factor_star (lam θ c y n : ℝ) :
    star (fullFactor lam θ c y n)=fullFactor lam (-θ) c y n := by
  have E : 2*(-θ)/c*y*n=-(2*θ/c*y*n) := by ring
  simp only [fullFactor,E,star_mul,OAI.Problem337.ExponentialSum.phase_neg,
    Complex.star_def,Complex.conj_ofReal,mul_comm]

/-- The negative exponential in the sine/cosine windows is obtained by
conjugating the actual complete sum and the two physical coefficient rows. -/
theorem twistedForm_conj (M c : ℕ) [NeZero c] (lam θ : ℝ) (a b : ℕ → ℂ) :
    twistedForm M c lam (-θ) a b =
      star (twistedForm M c lam θ (fun m => star (a m)) (fun n => star (b n))) := by
  simp only [twistedForm,star_sum,star_mul,star_star,factor_star,KloostermanConjugation.star_kloosterman_eq]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

end ImbalancedChen.Part3.OriginalAllParameterKloosterman20261113
end
