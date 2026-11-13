import ImbalancedChen.Part3OriginalSmoothedInitialMean
import ImbalancedChen.Part3PolynomialResidueDivisorBound

/-! Reinsert the actual factorizations k=qd and the 1/k weight on the
geometric side of the first same-infinity trace in (4.30). -/
namespace ImbalancedChen.Part3.OriginalFactoredInitialMean20261113
noncomputable section
open Finset
open scoped BigOperators
open OriginalSmoothedInitialMean20261113 MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open CommonSmoothCutoff

private def modulus (p : ℕ+ × ℕ+) := p.1*p.2

/-- On the common dyadic input N₀≤m,n≤2N₀ the actual smooth block
vanishes outside these absolute full-modulus endpoints. The range also
allows a nonintegral N₀, as in the native dyadic window. -/
theorem smooth_modulus_support (k : ℕ+) (a b c d : ℕ) (ω : ℝ) {N₀ Y : ℝ}
    (hn : 0<N₀) (hy : 0<Y)
    (mpos : ∀ m ∈ Ico a b, N₀≤(m:ℝ) ∧ (m:ℝ)≤2*N₀)
    (npos : ∀ n ∈ Ico c d, N₀≤(n:ℝ) ∧ (n:ℝ)≤2*N₀)
    (used : smoothSum k a b c d ω Y ≠ 0) :
    (8/5)*Real.pi*N₀*Y ≤ (k.val:ℝ) ∧ (k.val:ℝ) ≤ 16*Real.pi*N₀*Y := by
  classical
  by_contra bad
  apply used
  apply sum_eq_zero
  intro m hm
  apply sum_eq_zero
  intro n hh
  have mp := mpos _ hm
  have np := npos _ hh
  let z := Y*(4*Real.pi*Real.sqrt ((m:ℝ)*n)/(k.val:ℝ))
  have zero : dyadicCutoff z=0 := by
    by_contra active
    have hs : z∈tsupport dyadicCutoff := subset_closure (show z∈Function.support dyadicCutoff from active)
    rw [dyadicCutoff_tsupport_eq_tight] at hs
    have kp : (0:ℝ)<k.val := by exact_mod_cast k.property
    have sq := Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg m (α := ℝ)) (Nat.cast_nonneg n))
    have rootlo : N₀≤Real.sqrt ((m:ℝ)*n) := by
      apply (sq_le_sq₀ hn.le (Real.sqrt_nonneg _)).mp
      rw [sq,pow_two]
      exact mul_le_mul mp.1 np.1 hn.le (Nat.cast_nonneg m)
    have roothi : Real.sqrt ((m:ℝ)*n)≤2*N₀ := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      rw [sq,pow_two]
      exact mul_le_mul mp.2 np.2 (Nat.cast_nonneg n) (by positivity)
    have zh : z*(k.val:ℝ)=Y*(4*Real.pi*Real.sqrt ((m:ℝ)*n)) := by
      dsimp [z]
      field_simp [kp.ne'] <;> ring
    apply bad
    have C0 : 0≤Y*(4*Real.pi) := by positivity
    constructor
    · nlinarith only [mul_le_mul_of_nonneg_left rootlo C0,
        mul_le_mul_of_nonneg_right hs.2 kp.le,zh]
    · nlinarith only [mul_le_mul_of_nonneg_left roothi C0,
        mul_le_mul_of_nonneg_right hs.1 kp.le,zh]
  change _*(dyadicCutoff z:ℂ)=0
  rw [zero,Complex.ofReal_zero,mul_zero]

private theorem multiplicity (S : Finset (ℕ+ × ℕ+)) (k : ℕ+) :
    (S.filter (fun p => modulus p=k)).card ≤ k.val.divisors.card := by
  classical
  let H := S.filter (fun p => modulus p=k)
  let f (p : ℕ+ × ℕ+) := (p.1.val,p.2.val)
  have inj : Function.Injective f := by
    intro p q h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  have subset : H.image f ⊆ k.val.divisorsAntidiagonal := by
    intro a ha
    obtain ⟨p,hp,rfl⟩ := mem_image.mp ha
    apply Nat.mem_divisorsAntidiagonal.mpr
    exact ⟨congrArg Subtype.val (mem_filter.mp hp).2,k.property.ne'⟩
  have C := card_le_card subset
  rw [card_image_of_injective H inj,←Nat.map_div_right_divisors,card_map] at C
  exact C

/-- A full-modulus block K≤qd≤X≤2K pays the divisor multiplicity and
the original 1/(qd). K may be any positive real. -/
theorem factored_initial_mean {ε : ℝ} (he : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (S : Finset (ℕ+ × ℕ+)) (K : ℝ) (X M N : ℕ), 0<K → (X:ℝ)≤2*K →
      1≤X → 1≤M → 1≤N → (∀ p ∈ S, K≤((p.1*p.2).val:ℝ) ∧ (p.1*p.2).val≤X) →
      ∀ a b c d : ℕ, 0<a → a≤b → b≤2*a → b-a≤M → 0<c → c≤d → d≤2*c → d-c≤N →
      ∀ ω Y : ℝ, 0<Y →
        (∑ p ∈ S, ‖smoothSum (p.1*p.2) a b c d ω Y‖/((p.1*p.2).val:ℝ)) ≤
          C*((X:ℝ)*M*N)^ε*((X:ℝ)+(M:ℝ)*N) := by
  classical
  let δ := ε/2
  have dp : 0<δ := half_pos he
  obtain ⟨A,ap,arith⟩ := smooth_initial_mean dp
  obtain ⟨D,dp',tau⟩ := PolynomialResidueDivisorBound.fouvryTau_le_const_rpow (k := 2) (by norm_num) dp
  refine ⟨2*D*A,by positivity,?_⟩
  intro S K X M N kp XK x m n level a b c d ha hab bc hm hc hcd dc hn ω Y yp
  let L := S.image modulus
  let V (k : ℕ+) := ‖smoothSum k a b c d ω Y‖
  let Z := (X:ℝ)*M*N
  have xp : (0:ℝ)<X := by exact_mod_cast x
  have m1 : (1:ℝ)≤M := by exact_mod_cast m
  have n1 : (1:ℝ)≤N := by exact_mod_cast n
  have lx (k) (hk : k∈L) : K≤(k.val:ℝ) ∧ k.val≤X := by
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hk
    exact level _ hp
  have XZ : (X:ℝ)≤Z := by
    have ma := le_mul_of_one_le_right xp.le m1
    exact ma.trans (le_mul_of_one_le_right (by positivity) n1)
  have z0 : 0<Z := xp.trans_le XZ
  have norm (k) (hk : k∈L) : ((S.filter (fun p => modulus p=k)).card:ℝ) ≤ D*Z^δ := by
    have raw : (k.val.divisors.card:ℝ)≤D*(k.val:ℝ)^δ := by
      simpa only [fouvryTau_two] using tau k.val k.property
    apply (show ((S.filter (fun p => modulus p=k)).card:ℝ)≤(k.val.divisors.card:ℝ) by
      exact_mod_cast multiplicity S k).trans
    apply raw.trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) ((show (k.val:ℝ)≤X by
      exact_mod_cast (lx k hk).2).trans XZ) dp.le) dp'.le
  have fiber (k) (hk : k∈L) :
      (∑ p ∈ S.filter (fun p => modulus p=k), V (modulus p)/((modulus p).val:ℝ)) ≤
        (D*Z^δ/K)*V k := by
    have h : (∑ p ∈ S.filter (fun p => modulus p=k), V (modulus p)/((modulus p).val:ℝ)) =
        ∑ _p ∈ S.filter (fun p => modulus p=k), V k/(k.val:ℝ) := by
      exact sum_congr rfl (fun p hp => congrArg (fun r : ℕ+ => V r/(r.val:ℝ)) (mem_filter.mp hp).2)
    rw [h,sum_const,nsmul_eq_mul]
    have bq := div_le_div_of_nonneg_left (norm_nonneg _) kp (lx k hk).1
    calc
      _ ≤ (D*Z^δ)*(V k/K) := mul_le_mul (norm k hk) bq (by dsimp [V]; positivity) (by positivity)
      _ = _ := by ring
  have ar := arith L X M N x m n (fun k hk => (lx k hk).2) a b c d ha hab bc hm hc hcd dc hn ω Y yp
  have re := sum_fiberwise_of_maps_to (s := S) (t := L) (g := modulus)
    (fun p hp => mem_image_of_mem _ hp) (fun p => V (modulus p)/((modulus p).val:ℝ))
  change (∑ p ∈ S, V (modulus p)/((modulus p).val:ℝ)) ≤ _
  have scale : (X:ℝ)/K≤2 := (div_le_iff₀ kp).mpr XK
  have zpow : Z^δ*Z^δ=Z^ε := by rw [←Real.rpow_add z0]; congr 1; dsimp [δ]; ring
  calc
    _ = _ := re.symm
    _ ≤ ∑ k ∈ L, (D*Z^δ/K)*V k := sum_le_sum fiber
    _ = (D*Z^δ/K)*∑ k ∈ L, V k := (mul_sum _ _ _).symm
    _ ≤ (D*Z^δ/K)*(A*Z^δ*(X:ℝ)*((X:ℝ)+(M:ℝ)*N)) := mul_le_mul_of_nonneg_left ar (by positivity)
    _ = ((X:ℝ)/K)*(D*A*Z^ε*((X:ℝ)+(M:ℝ)*N)) := by rw [←zpow]; ring
    _ ≤ 2*(D*A*Z^ε*((X:ℝ)+(M:ℝ)*N)) := mul_le_mul_of_nonneg_right scale (by positivity)
    _ = _ := by dsimp [Z]; ring

/-- The positive-frequency block used by fullM and pascadiJ. The integer
length is the exact cardinal of [2^j,2^(j+1)), for both variables. -/
theorem native_block_initial {ε : ℝ} (he : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (j : ℕ) (S : Finset (ℕ+ × ℕ+)) (K : ℝ) (X : ℕ),
      0<K → (X:ℝ)≤2*K → 1≤X →
      (∀ p ∈ S, K≤((p.1*p.2).val:ℝ) ∧ (p.1*p.2).val≤X) → ∀ ω Y : ℝ, 0<Y →
      (∑ p ∈ S, ‖smoothSum (p.1*p.2) (2^j) (2^(j+1)) (2^j) (2^(j+1)) ω Y‖/((p.1*p.2).val:ℝ)) ≤
        C*((X:ℝ)*(2^j:ℕ)*(2^j:ℕ))^ε*((X:ℝ)+((2^j:ℕ):ℝ)*(2^j:ℕ)) := by
  obtain ⟨C,hC,H⟩ := factored_initial_mean he
  refine ⟨C,hC,?_⟩
  intro j S K X kp hi xp levels ω Y yp
  have pos : 0<2^j := Nat.pow_pos (by decide)
  have lo : 2^j ≤ 2^(j+1) := by rw [pow_succ]; omega
  have dy : 2^(j+1) ≤ 2*2^j := by rw [pow_succ,mul_comm]
  have len : 2^(j+1)-2^j ≤ 2^j := by rw [pow_succ]; omega
  exact H S K X (2^j) (2^j) kp hi xp pos pos levels _ _ _ _ pos lo dy len pos lo dy len ω Y yp

end
end ImbalancedChen.Part3.OriginalFactoredInitialMean20261113
