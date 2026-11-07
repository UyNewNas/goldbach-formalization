# 恢复的上轮 591 项完整编译器类型

固定集成 `28fd630ef7cc38eba86beb6c0ba123336b5d05f2`；586 项实际 pp.all，5 项完整默认 Meta.ppExpr。原始格式与逐声明来源在 JSON 中明确记录。

## ImbalancedChen.actualSelectedPrefixLowerOwnCubeSum_eq_cells

模块 `ImbalancedChen.ActualSelectedPrefixLowerCellSum`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N cap : Nat) (I : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) (old nu a b : Rat)
  (hab : @LT.lt.{0} Rat Rat.instLT a b)
  (hN : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N)
  (hcap :
    @LE.le.{0} Real Real.instLE
      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
        (@Nat.cast.{0} Real Real.instNatCast N) (@Rat.cast.{0} Real Real.instRatCast b))
      (@Nat.cast.{0} Real Real.instNatCast cap))
  (m : Nat)
  (J :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))),
  @Eq.{1} Real
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@ImbalancedChen.actualSelectedPrefixOwnCubeSum (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          Bool.true N cap
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N) (@Rat.cast.{0} Real Real.instRatCast b))
          I old nu a b m J)
        (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))
      (ImbalancedChen.singularSeries N))
    (@Finset.sum.{0, 0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      Real Real.instAddCommMonoid J
      fun
        (j :
          Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
      @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (ImbalancedChen.actualPrimeBoxOwnCubeMinusSum (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N
          cap (@Rat.cast.{0} Real Real.instRatCast a) (@Rat.cast.{0} Real Real.instRatCast b)
          (@Rat.cast.{0} Real Real.instRatCast
            (@ImbalancedChen.selectedPrefixCellCap (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) I old
              nu a b m j))
          (@Inter.inter.{0}
            (Set.{0}
              (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                Real))
            (@Set.instInter.{0}
              (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                Real))
            (@ImbalancedChen.logPrimeMeshCell
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Rat.cast.{0} Real Real.instRatCast a) (@Rat.cast.{0} Real Real.instRatCast b) m j)
            (@ImbalancedChen.primeAffineGateRegion
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) ImbalancedChen.ordinaryLowerFourGateForms
              (ImbalancedChen.ordinaryLowerFourGateBounds (@Rat.cast.{0} Real Real.instRatCast old)))))
        (ImbalancedChen.actualPrimeBoxOwnCubeMinusSum (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N
          cap (@Rat.cast.{0} Real Real.instRatCast a) (@Rat.cast.{0} Real Real.instRatCast b)
          (@Rat.cast.{0} Real Real.instRatCast old)
          (@Inter.inter.{0}
            (Set.{0}
              (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                Real))
            (@Set.instInter.{0}
              (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                Real))
            (@ImbalancedChen.logPrimeMeshCell
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Rat.cast.{0} Real Real.instRatCast a) (@Rat.cast.{0} Real Real.instRatCast b) m j)
            (@ImbalancedChen.primeAffineGateRegion
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) ImbalancedChen.ordinaryLowerFourGateForms
              (ImbalancedChen.ordinaryLowerFourGateBounds (@Rat.cast.{0} Real Real.instRatCast old))))))
```

## ImbalancedChen.ordinaryLowerFourFrontierTuples_cell_filter

模块 `ImbalancedChen.ActualSelectedPrefixLowerCellSum`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N cap : Nat) (a b old : Real) (hab : @LT.lt.{0} Real Real.instLT a b)
  (hN : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N)
  (hcap :
    @LE.le.{0} Real Real.instLE
      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
        (@Nat.cast.{0} Real Real.instNatCast N) b)
      (@Nat.cast.{0} Real Real.instNatCast cap))
  (m : Nat)
  (j :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
  @Eq.{1} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat))
    (@Finset.filter.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat)
      (fun (p : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat) =>
        @Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
          (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
          (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
          (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a b m j)
          (@ImbalancedChen.actualPrimeTupleLog (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N p))
      (fun (a_1 : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat) =>
        Classical.propDecidable
          (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
            (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a b m j)
            (@ImbalancedChen.actualPrimeTupleLog (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N a_1)))
      (ImbalancedChen.firstExitFrontierTuples (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (ImbalancedChen.ordinaryParityRosserPolicy Bool.true
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N) old))
        (ImbalancedChen.roughPrimeUniverse N cap
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N) b))))
    (@Finset.filter.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat)
      (fun (p : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat) =>
        @Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
          (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
          (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
          (@Inter.inter.{0} (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@Set.instInter.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a b m j)
            (@ImbalancedChen.primeAffineGateRegion (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) ImbalancedChen.ordinaryLowerFourGateForms
              (ImbalancedChen.ordinaryLowerFourGateBounds old)))
          (@ImbalancedChen.actualPrimeTupleLog (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N p))
      (fun (a_1 : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat) =>
        @Set.decidableInter.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
          (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a b m j)
          (@ImbalancedChen.primeAffineGateRegion (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) ImbalancedChen.ordinaryLowerFourGateForms
            (ImbalancedChen.ordinaryLowerFourGateBounds old))
          (@ImbalancedChen.actualPrimeTupleLog (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N a_1)
          (Classical.propDecidable
            (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
              (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
              (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
              (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a b m j)
              (@ImbalancedChen.actualPrimeTupleLog (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N
                a_1)))
          (Classical.propDecidable
            (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
              (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
              (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
              (@ImbalancedChen.primeAffineGateRegion (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) ImbalancedChen.ordinaryLowerFourGateForms
                (ImbalancedChen.ordinaryLowerFourGateBounds old))
              (@ImbalancedChen.actualPrimeTupleLog (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N
                a_1))))
      (@ImbalancedChen.actualPrimeBoxTuples N (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => a)
        fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => b))
```

## ImbalancedChen.ordinaryLowerFourFrontierTuples_cell_filter._simp_1_1

模块 `ImbalancedChen.ActualSelectedPrefixLowerCellSum`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : @DecidablePred.{u_1 + 1} α p] {s : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.filter.{u_1} α p inst s) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (p a))
```

## ImbalancedChen.ordinaryLowerFourFrontierTuples_cell_filter._simp_1_2

模块 `ImbalancedChen.ActualSelectedPrefixLowerCellSum`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u} (x : α) (a b : Set.{u} α),
  @Eq.{1} Prop
    (@Membership.mem.{u, u} α (Set.{u} α) (@Set.instMembership.{u} α)
      (@Inter.inter.{u} (Set.{u} α) (@Set.instInter.{u} α) a b) x)
    (And (@Membership.mem.{u, u} α (Set.{u} α) (@Set.instMembership.{u} α) a x)
      (@Membership.mem.{u, u} α (Set.{u} α) (@Set.instMembership.{u} α) b x))
```

## ImbalancedChen.ordinaryLowerFourFrontierTuples_cube_filter

模块 `ImbalancedChen.ActualSelectedPrefixLowerCellSum`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N cap : Nat) (a b old : Real)
  (hN : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N)
  (hcap :
    @LE.le.{0} Real Real.instLE
      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
        (@Nat.cast.{0} Real Real.instNatCast N) b)
      (@Nat.cast.{0} Real Real.instNatCast cap)),
  @Eq.{1} (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat))
    (@Finset.filter.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat)
      (fun (p : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat) =>
        @Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat)
          (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat)
            (@Finset.instSetLike.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat)))
          (@ImbalancedChen.actualPrimeBoxTuples N (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => a)
            fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => b)
          p)
      (fun (a_1 : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat) =>
        @Finset.decidableMem.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat)
          (fun (a b : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat) =>
            @Fintype.decidablePiFintype.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Nat)
              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => instDecidableEqNat)
              (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) a b)
          a_1
          (@ImbalancedChen.actualPrimeBoxTuples N (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => a)
            fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => b))
      (ImbalancedChen.firstExitFrontierTuples (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (ImbalancedChen.ordinaryParityRosserPolicy Bool.true
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N) old))
        (ImbalancedChen.roughPrimeUniverse N cap
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N) b))))
    (@Finset.filter.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat)
      (fun (p : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat) =>
        @Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
          (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
          (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
          (@ImbalancedChen.primeAffineGateRegion (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) ImbalancedChen.ordinaryLowerFourGateForms
            (ImbalancedChen.ordinaryLowerFourGateBounds old))
          (@ImbalancedChen.actualPrimeTupleLog (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N p))
      (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat) =>
        Classical.propDecidable
          (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
            (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@ImbalancedChen.primeAffineGateRegion (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) ImbalancedChen.ordinaryLowerFourGateForms
              (ImbalancedChen.ordinaryLowerFourGateBounds old))
            (@ImbalancedChen.actualPrimeTupleLog (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N a)))
      (@ImbalancedChen.actualPrimeBoxTuples N (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => a)
        fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => b))
```

## ImbalancedChen.ordinaryLowerFourFrontierTuples_cube_filter._simp_1_1

模块 `ImbalancedChen.ActualSelectedPrefixLowerCellSum`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : @DecidablePred.{u_1 + 1} α p] {s : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.filter.{u_1} α p inst s) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (p a))
```

## ImbalancedChen.ordinaryLowerFourFrontier_cell_ownCube_difference

模块 `ImbalancedChen.ActualSelectedPrefixLowerCellSum`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N cap : Nat) (a b old lambda : Real) (hab : @LT.lt.{0} Real Real.instLT a b)
  (hN : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N)
  (hcap :
    @LE.le.{0} Real Real.instLE
      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
        (@Nat.cast.{0} Real Real.instNatCast N) b)
      (@Nat.cast.{0} Real Real.instNatCast cap))
  (m : Nat)
  (j :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
  @Eq.{1} Real
    (@Finset.sum.{0, 0}
      (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Nat)
      Real Real.instAddCommMonoid
      (ImbalancedChen.firstExitFrontierTuples (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (ImbalancedChen.ordinaryParityRosserPolicy Bool.true
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N) old))
        (ImbalancedChen.roughPrimeUniverse N cap
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N) b)))
      fun
        (p :
          Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            Nat) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Finset.prod.{0, 0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          Real Real.instCommMonoid
          (@Finset.univ.{0}
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          fun
            (i :
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
          @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@Nat.cast.{0} Real Real.instNatCast (p i))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
        (@ite.{1} Real
          (@Membership.mem.{0, 0}
            (Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
              Real)
            (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a b m j)
            (@ImbalancedChen.actualPrimeTupleLog
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              N p))
          (Classical.propDecidable
            (@Membership.mem.{0, 0}
              (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                Real)
              (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
              (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
              (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a b m j)
              (@ImbalancedChen.actualPrimeTupleLog
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                N p)))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@ImbalancedChen.actualPrimeTupleOwnCubeMinus (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              N cap lambda p)
            (@ImbalancedChen.actualPrimeTupleOwnCubeMinus (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              N cap old p))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (ImbalancedChen.actualPrimeBoxOwnCubeMinusSum (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N cap
        a b lambda
        (@Inter.inter.{0}
          (Set.{0}
            (Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
              Real))
          (@Set.instInter.{0}
            (Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
              Real))
          (@ImbalancedChen.logPrimeMeshCell
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            a b m j)
          (@ImbalancedChen.primeAffineGateRegion
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) ImbalancedChen.ordinaryLowerFourGateForms
            (ImbalancedChen.ordinaryLowerFourGateBounds old))))
      (ImbalancedChen.actualPrimeBoxOwnCubeMinusSum (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N cap
        a b old
        (@Inter.inter.{0}
          (Set.{0}
            (Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
              Real))
          (@Set.instInter.{0}
            (Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
              Real))
          (@ImbalancedChen.logPrimeMeshCell
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            a b m j)
          (@ImbalancedChen.primeAffineGateRegion
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) ImbalancedChen.ordinaryLowerFourGateForms
            (ImbalancedChen.ordinaryLowerFourGateBounds old)))))
```

## ImbalancedChen.ordinaryLowerFourFrontier_cell_ownCube_difference._simp_1_1

模块 `ImbalancedChen.ActualSelectedPrefixLowerCellSum`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {ι : Type u_1} {G : Type u_5} {s : Finset.{u_1} ι} [inst : SubtractionCommMonoid.{u_5} G] (f g : ι → G),
  @Eq.{u_5 + 1} G
    (@HSub.hSub.{u_5, u_5, u_5} G G G
      (@instHSub.{u_5} G
        (@SubNegMonoid.toSub.{u_5} G
          (@SubtractionMonoid.toSubNegMonoid.{u_5} G (@SubtractionCommMonoid.toSubtractionMonoid.{u_5} G inst))))
      (@Finset.sum.{u_1, u_5} ι G (@SubtractionCommMonoid.toAddCommMonoid.{u_5} G inst) s fun (x : ι) => f x)
      (@Finset.sum.{u_1, u_5} ι G (@SubtractionCommMonoid.toAddCommMonoid.{u_5} G inst) s fun (x : ι) => g x))
    (@Finset.sum.{u_1, u_5} ι G (@SubtractionCommMonoid.toAddCommMonoid.{u_5} G inst) s fun (x : ι) =>
      @HSub.hSub.{u_5, u_5, u_5} G G G
        (@instHSub.{u_5} G
          (@SubNegMonoid.toSub.{u_5} G
            (@SubtractionMonoid.toSubNegMonoid.{u_5} G (@SubtractionCommMonoid.toSubtractionMonoid.{u_5} G inst))))
        (f x) (g x))
```

## ImbalancedChen.ordinaryLowerFourFrontier_cell_weighted_sum

模块 `ImbalancedChen.ActualSelectedPrefixLowerCellSum`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N cap : Nat) (a b old : Real) (hab : @LT.lt.{0} Real Real.instLT a b)
  (hN : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N)
  (hcap :
    @LE.le.{0} Real Real.instLE
      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
        (@Nat.cast.{0} Real Real.instNatCast N) b)
      (@Nat.cast.{0} Real Real.instNatCast cap))
  (m : Nat)
  (j :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (f : (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat) → Real),
  @Eq.{1} Real
    (@Finset.sum.{0, 0}
      (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        Nat)
      Real Real.instAddCommMonoid
      (ImbalancedChen.firstExitFrontierTuples (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (ImbalancedChen.ordinaryParityRosserPolicy Bool.true
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N) old))
        (ImbalancedChen.roughPrimeUniverse N cap
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N) b)))
      fun
        (p :
          Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            Nat) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Finset.prod.{0, 0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          Real Real.instCommMonoid
          (@Finset.univ.{0}
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (Fin.fintype
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          fun
            (i :
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
          @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@Nat.cast.{0} Real Real.instNatCast (p i))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
        (@ite.{1} Real
          (@Membership.mem.{0, 0}
            (Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
              Real)
            (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a b m j)
            (@ImbalancedChen.actualPrimeTupleLog
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              N p))
          (Classical.propDecidable
            (@Membership.mem.{0, 0}
              (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                Real)
              (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
              (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
              (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a b m j)
              (@ImbalancedChen.actualPrimeTupleLog
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                N p)))
          (f p) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
    (@Finset.sum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat) Real
      Real.instAddCommMonoid
      (@ImbalancedChen.actualPrimeBoxTuples N (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => a)
        fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => b)
      fun (p : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Finset.prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real
          Real.instCommMonoid
          (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
          @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@Nat.cast.{0} Real Real.instNatCast (p i))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
        (@ite.{1} Real
          (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
            (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@Inter.inter.{0} (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
              (@Set.instInter.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
              (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a b m j)
              (@ImbalancedChen.primeAffineGateRegion (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) ImbalancedChen.ordinaryLowerFourGateForms
                (ImbalancedChen.ordinaryLowerFourGateBounds old)))
            (@ImbalancedChen.actualPrimeTupleLog (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N p))
          (@Set.decidableInter.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
            (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a b m j)
            (@ImbalancedChen.primeAffineGateRegion (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) ImbalancedChen.ordinaryLowerFourGateForms
              (ImbalancedChen.ordinaryLowerFourGateBounds old))
            (@ImbalancedChen.actualPrimeTupleLog (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N p)
            (Classical.propDecidable
              (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
                (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
                (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
                (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a b m j)
                (@ImbalancedChen.actualPrimeTupleLog (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N
                  p)))
            (Classical.propDecidable
              (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
                (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
                (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
                (@ImbalancedChen.primeAffineGateRegion (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  ImbalancedChen.ordinaryLowerFourGateForms (ImbalancedChen.ordinaryLowerFourGateBounds old))
                (@ImbalancedChen.actualPrimeTupleLog (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N
                  p))))
          (f p) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
```

## ImbalancedChen.actualSelectedPrefixLowerDensity

模块 `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
(N cap : Nat) →
  (I : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) →
    (old nu a b : Rat) →
      (m : Nat) →
        (J :
            Finset.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
          Real
```

## ImbalancedChen.actualSelectedPrefixLowerDensity.eq_1

模块 `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N cap : Nat) (I : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) (old nu a b : Rat)
  (m : Nat)
  (J :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))),
  @Eq.{1} Real (ImbalancedChen.actualSelectedPrefixLowerDensity N cap I old nu a b m J)
    (@ImbalancedChen.firstExitRetainedPolynomial.{0} Nat
      (@ImbalancedChen.actualSelectedPrefixSplicePolicy (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        Bool.true (@Nat.cast.{0} Real Real.instNatCast N) I old nu a b m J)
      (fun (p : Nat) =>
        @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (@Nat.cast.{0} Real Real.instNatCast p)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
      (@List.nil.{0} Nat) Bool.true (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (ImbalancedChen.roughPrimeUniverse N cap
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N) (@Rat.cast.{0} Real Real.instRatCast b))))
```

## ImbalancedChen.selectedPrefixLowerRestorationIntegral

模块 `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
(I : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) →
  (old nu a b : Rat) →
    (m : Nat) →
      (J :
          Finset.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        Real
```

## ImbalancedChen.selectedPrefixLowerRestorationIntegral_eq_integrals

模块 `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (I : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) (old nu a b : Rat)
  (ha : @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) a)
  (hab : @LT.lt.{0} Rat Rat.instLT a b) (m : Nat)
  (J :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))),
  @Eq.{1} Real (ImbalancedChen.selectedPrefixLowerRestorationIntegral I old nu a b m J)
    (@Finset.sum.{0, 0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      Real Real.instAddCommMonoid J
      fun
        (j :
          Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
      @MeasureTheory.integral.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real) Real
        Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
          (@MeasureTheory.MeasureSpace.pi.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.measureSpace))
        (@MeasureTheory.Measure.restrict.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
          (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
            (@MeasureTheory.MeasureSpace.pi.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.measureSpace))
          (@MeasureTheory.MeasureSpace.volume.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
            (@MeasureTheory.MeasureSpace.pi.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.measureSpace))
          (@Inter.inter.{0} (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@Set.instInter.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@Rat.cast.{0} Real Real.instRatCast a) (@Rat.cast.{0} Real Real.instRatCast b) m j)
            (@ImbalancedChen.primeAffineGateRegion (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) ImbalancedChen.ordinaryLowerFourGateForms
              (ImbalancedChen.ordinaryLowerFourGateBounds (@Rat.cast.{0} Real Real.instRatCast old)))))
        fun (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real) =>
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@ImbalancedChen.primeOwnCubeGatedProfile (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Rat.cast.{0} Real Real.instRatCast
                (@ImbalancedChen.selectedPrefixCellCap (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) I
                  old nu a b m j))
              t)
            (@ImbalancedChen.primeOwnCubeGatedProfile (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Rat.cast.{0} Real Real.instRatCast old) t))
          (@Finset.prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real
            Real.instCommMonoid
            (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
            @HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (t i)))
```

## ImbalancedChen.tendsto_actualSelectedPrefixLowerDensity_ceil_normalized

模块 `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (I : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) (old nu a b : Rat)
  (ha : @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) a)
  (hab : @LT.lt.{0} Rat Rat.instLT a b)
  (hbo :
    @LE.le.{0} Rat Rat.instLE
      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
        (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))) b)
      old)
  (m : Nat)
  (J :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (hchecks :
    ∀
      (j :
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Membership.mem.{0, 0}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Finset.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Finset.instSetLike.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          J j →
        @Eq.{1} Bool
          (@ImbalancedChen.selectedBoxCapCheck (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) I old nu
            (@ImbalancedChen.qLogPrimeMeshLo (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a b m j)
            (@ImbalancedChen.qLogPrimeMeshHi (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a b m j))
          Bool.true),
  @Filter.Tendsto.{0, 0} Nat Real
    (fun (N : Nat) =>
      @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (ImbalancedChen.actualSelectedPrefixLowerDensity N
            (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
              (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
              (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                (@Nat.cast.{0} Real Real.instNatCast N) (@Rat.cast.{0} Real Real.instRatCast b)))
            I old nu a b m J)
          (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))
        (ImbalancedChen.singularSeries N))
    (@Min.min.{0} (Filter.{0} Nat) (@Filter.instInf.{0} Nat) (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@Filter.principal.{0} Nat
        (@Set.ofPred.{0} Nat fun (N : Nat) =>
          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N)
            (@Even.{0} Nat instAddNat N))))
    (@nhds.{0} Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (Real.exp (@Neg.neg.{0} Real Real.instNeg Real.eulerMascheroniConstant)))
            (@Rat.cast.{0} Real Real.instRatCast b))
          (MathlibNt.SieveTheory.suzukiContinuousLowerFactor
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@Rat.cast.{0} Real Real.instRatCast old) (@Rat.cast.{0} Real Real.instRatCast b))))
        (ImbalancedChen.selectedPrefixLowerRestorationIntegral I old nu a b m J)))
```

## ImbalancedChen.tendsto_actualSelectedPrefixLowerDensity_normalized

模块 `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (I : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) (old nu a b : Rat)
  (ha : @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) a)
  (hab : @LT.lt.{0} Rat Rat.instLT a b)
  (hbo :
    @LE.le.{0} Rat Rat.instLE
      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
        (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))) b)
      old)
  (m : Nat)
  (J :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (hchecks :
    ∀
      (j :
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Membership.mem.{0, 0}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Finset.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Finset.instSetLike.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          J j →
        @Eq.{1} Bool
          (@ImbalancedChen.selectedBoxCapCheck (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) I old nu
            (@ImbalancedChen.qLogPrimeMeshLo (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a b m j)
            (@ImbalancedChen.qLogPrimeMeshHi (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a b m j))
          Bool.true)
  (cap : Nat → Nat)
  (hcap :
    @Filter.Eventually.{0} Nat
      (fun (N : Nat) =>
        @LE.le.{0} Real Real.instLE
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N) (@Rat.cast.{0} Real Real.instRatCast b))
          (@Nat.cast.{0} Real Real.instNatCast (cap N)))
      (@Min.min.{0} (Filter.{0} Nat) (@Filter.instInf.{0} Nat) (@Filter.atTop.{0} Nat Nat.instPreorder)
        (@Filter.principal.{0} Nat
          (@Set.ofPred.{0} Nat fun (N : Nat) =>
            And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N)
              (@Even.{0} Nat instAddNat N))))),
  @Filter.Tendsto.{0, 0} Nat Real
    (fun (N : Nat) =>
      @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (ImbalancedChen.actualSelectedPrefixLowerDensity N (cap N) I old nu a b m J)
          (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))
        (ImbalancedChen.singularSeries N))
    (@Min.min.{0} (Filter.{0} Nat) (@Filter.instInf.{0} Nat) (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@Filter.principal.{0} Nat
        (@Set.ofPred.{0} Nat fun (N : Nat) =>
          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N)
            (@Even.{0} Nat instAddNat N))))
    (@nhds.{0} Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (Real.exp (@Neg.neg.{0} Real Real.instNeg Real.eulerMascheroniConstant)))
            (@Rat.cast.{0} Real Real.instRatCast b))
          (MathlibNt.SieveTheory.suzukiContinuousLowerFactor
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@Rat.cast.{0} Real Real.instRatCast old) (@Rat.cast.{0} Real Real.instRatCast b))))
        (ImbalancedChen.selectedPrefixLowerRestorationIntegral I old nu a b m J)))
```

## ImbalancedChen.tendsto_actualSelectedPrefixLowerDensity_restoration

模块 `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (I : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) (old nu a b : Rat)
  (ha : @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) a)
  (hab : @LT.lt.{0} Rat Rat.instLT a b) (hbo : @LE.le.{0} Rat Rat.instLE b old) (m : Nat)
  (J :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (hchecks :
    ∀
      (j :
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Membership.mem.{0, 0}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Finset.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Finset.instSetLike.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          J j →
        @Eq.{1} Bool
          (@ImbalancedChen.selectedBoxCapCheck (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) I old nu
            (@ImbalancedChen.qLogPrimeMeshLo (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a b m j)
            (@ImbalancedChen.qLogPrimeMeshHi (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a b m j))
          Bool.true)
  (cap : Nat → Nat)
  (hcap :
    @Filter.Eventually.{0} Nat
      (fun (N : Nat) =>
        @LE.le.{0} Real Real.instLE
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N) (@Rat.cast.{0} Real Real.instRatCast b))
          (@Nat.cast.{0} Real Real.instNatCast (cap N)))
      (@Min.min.{0} (Filter.{0} Nat) (@Filter.instInf.{0} Nat) (@Filter.atTop.{0} Nat Nat.instPreorder)
        (@Filter.principal.{0} Nat
          (@Set.ofPred.{0} Nat fun (N : Nat) =>
            And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N)
              (@Even.{0} Nat instAddNat N))))),
  @Filter.Tendsto.{0, 0} Nat Real
    (fun (N : Nat) =>
      @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (ImbalancedChen.actualSelectedPrefixLowerDensity N (cap N) I old nu a b m J)
            (ImbalancedChen.actualSmallRosserMinusDensity N (cap N)
              (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                (@Nat.cast.{0} Real Real.instNatCast N) (@Rat.cast.{0} Real Real.instRatCast b))
              (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                (@Nat.cast.{0} Real Real.instNatCast N) (@Rat.cast.{0} Real Real.instRatCast old))))
          (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))
        (ImbalancedChen.singularSeries N))
    (@Min.min.{0} (Filter.{0} Nat) (@Filter.instInf.{0} Nat) (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@Filter.principal.{0} Nat
        (@Set.ofPred.{0} Nat fun (N : Nat) =>
          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N)
            (@Even.{0} Nat instAddNat N))))
    (@nhds.{0} Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (ImbalancedChen.selectedPrefixLowerRestorationIntegral I old nu a b m J))
```

## ImbalancedChen.tendsto_actualSelectedPrefixLowerOwnCubeSum

模块 `ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (I : Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) (old nu a b : Rat)
  (ha : @LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) a)
  (hab : @LT.lt.{0} Rat Rat.instLT a b) (m : Nat)
  (J :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (cap : Nat → Nat)
  (hcap :
    @Filter.Eventually.{0} Nat
      (fun (N : Nat) =>
        @LE.le.{0} Real Real.instLE
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N) (@Rat.cast.{0} Real Real.instRatCast b))
          (@Nat.cast.{0} Real Real.instNatCast (cap N)))
      (@Min.min.{0} (Filter.{0} Nat) (@Filter.instInf.{0} Nat) (@Filter.atTop.{0} Nat Nat.instPreorder)
        (@Filter.principal.{0} Nat
          (@Set.ofPred.{0} Nat fun (N : Nat) =>
            And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N)
              (@Even.{0} Nat instAddNat N))))),
  @Filter.Tendsto.{0, 0} Nat Real
    (fun (N : Nat) =>
      @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@ImbalancedChen.actualSelectedPrefixOwnCubeSum (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            Bool.true N (cap N)
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (@Nat.cast.{0} Real Real.instNatCast N) (@Rat.cast.{0} Real Real.instRatCast b))
            I old nu a b m J)
          (Real.log (@Nat.cast.{0} Real Real.instNatCast N)))
        (ImbalancedChen.singularSeries N))
    (@Min.min.{0} (Filter.{0} Nat) (@Filter.instInf.{0} Nat) (@Filter.atTop.{0} Nat Nat.instPreorder)
      (@Filter.principal.{0} Nat
        (@Set.ofPred.{0} Nat fun (N : Nat) =>
          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N)
            (@Even.{0} Nat instAddNat N))))
    (@nhds.{0} Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (ImbalancedChen.selectedPrefixLowerRestorationIntegral I old nu a b m J))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.adopted_coarse_lower

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
@LE.le.{0} Real Real.instLE
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 640339)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 640339) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 640338) (instOfNatNat (nat_lit 640338)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 640337) (instOfNatNat (nat_lit 640337)))))))
    (@OfNat.ofNat.{0} Real (nat_lit 15210735000)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 15210735000) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15210734999) (instOfNatNat (nat_lit 15210734999)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 15210734998) (instOfNatNat (nat_lit 15210734998))))))))
  ImbalancedChen.Certificates.AboveMuSecondCoarse.totalChartIntegral
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
(k u v : Real) → Real
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator.eq_1

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (k u v : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator k u v)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual k u v))
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual k u v))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator_pos

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {k u v : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator k u v)
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
(k : Real) → Real
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral.eq_1

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (k : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral k)
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel k))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral_eq_literal

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (k : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral k)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 6)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
          (@abs.{0} Real Real.lattice Real.instAddGroup k))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          ImbalancedChen.Certificates.AboveMuSecondCoarse.step
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@intervalIntegral.{0} Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (fun (u : Real) =>
          @intervalIntegral.{0} Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (fun (v : Real) =>
              @HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) u
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) v))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
                      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
                    (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual k u v))
                  (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual k u v)))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral_lower_of_denominatorCap

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {k D : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (hD :
    ∀ (u : Real),
      @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
          (@Set.Icc.{0} Real Real.instPreorder
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          u →
        ∀ (v : Real),
          @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
              (@Set.Icc.{0} Real Real.instPreorder
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
              v →
            @LE.le.{0} Real Real.instLE (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator k u v) D),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@abs.{0} Real Real.lattice Real.instAddGroup k)
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          ImbalancedChen.Certificates.AboveMuSecondCoarse.step
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      D)
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral k)
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chartInterior_gates

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {k u v : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Ioo.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Ioo.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  And
    (@LT.lt.{0} Real Real.instLT
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)))
    (And
      (@LT.lt.{0} Real Real.instLT
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v)))
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)))
      (And
        (@LT.lt.{0} Real Real.instLT
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)))
        (@LT.lt.{0} Real Real.instLT
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v)))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chartInterior_mem_physicalDomain

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {k u v : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Ioo.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Ioo.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  @Membership.mem.{0, 0} (Prod.{0, 0} Real Real) (Set.{0} (Prod.{0, 0} Real Real))
    (@Set.instMembership.{0} (Prod.{0, 0} Real Real)) ImbalancedChen.Certificates.AboveMuSecondCoarse.physicalDomain
    (@Prod.mk.{0, 0} Real Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
(k u v : Real) → Real
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel._proof_1

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel.eq_1

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (k u v : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel k u v)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 6)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                  ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel._proof_1))
              (@abs.{0} Real Real.lattice Real.instAddGroup k))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              ImbalancedChen.Certificates.AboveMuSecondCoarse.step
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) u
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) v))
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator k u v))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel_eq_physical_pullback

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {k u v : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel k u v)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
                  (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
                (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v)))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
                (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
            (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@abs.{0} Real Real.lattice Real.instAddGroup k)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            ImbalancedChen.Certificates.AboveMuSecondCoarse.step
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        u))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
(u : Real) → Real
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX._proof_1

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX_eq

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (u : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      ImbalancedChen.Certificates.AboveMuSecondCoarse.mu
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        ImbalancedChen.Certificates.AboveMuSecondCoarse.step u))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
(k u v : Real) → Real
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY_eq

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (k u v : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      ImbalancedChen.Certificates.AboveMuSecondCoarse.mu
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) k
            ImbalancedChen.Certificates.AboveMuSecondCoarse.step)
          u)
        v))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chart_bounds

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {k u v : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  And
    (@LE.le.{0} Real Real.instLE ImbalancedChen.Certificates.AboveMuSecondCoarse.mu
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
    (And
      (@LE.le.{0} Real Real.instLE (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u)
        ImbalancedChen.Certificates.AboveMuSecondCoarse.rho)
      (And
        (@LE.le.{0} Real Real.instLE
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 16)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
        (And
          (@LE.le.{0} Real Real.instLE (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v)
            ImbalancedChen.Certificates.AboveMuSecondCoarse.rho)
          (And
            (@LE.le.{0} Real Real.instLE ImbalancedChen.Certificates.AboveMuSecondCoarse.rho
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual k u v))
            (@LE.le.{0} Real Real.instLE ImbalancedChen.Certificates.AboveMuSecondCoarse.rho
              (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual k u v))))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.chart_factors_pos

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {k u v : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  And
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
    (And
      (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
      (And
        (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual k u v))
        (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual k u v))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.continuousOn_chartKernel

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {k : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))),
  @ContinuousOn.{0, 0} (Prod.{0, 0} Real Real) Real
    (@instTopologicalSpaceProd.{0, 0} Real Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (fun (p : Prod.{0, 0} Real Real) =>
      ImbalancedChen.Certificates.AboveMuSecondCoarse.chartKernel k (@Prod.fst.{0, 0} Real Real p)
        (@Prod.snd.{0, 0} Real Real p))
    (@SProd.sprod.{0, 0, 0} (Set.{0} Real) (Set.{0} Real) (Set.{0} (Prod.{0, 0} Real Real))
      (@Set.instSProd.{0, 0} Real Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
(t : Real) → Real
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope._proof_1

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope._proof_2

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope._proof_3

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope._proof_4

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope_chartX

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {u : Real}
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u),
  @Eq.{1} Real
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 153)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 153) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 151) (instOfNatNat (nat_lit 151)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 256)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 256) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 255) (instOfNatNat (nat_lit 255)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 254) (instOfNatNat (nat_lit 254))))))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          ImbalancedChen.Certificates.AboveMuSecondCoarse.step)
        u))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope_chartY

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {k u v : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  @Eq.{1} Real
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 153)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 153) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 151) (instOfNatNat (nat_lit 151)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 256)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 256) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 255) (instOfNatNat (nat_lit 255)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 254) (instOfNatNat (nat_lit 254))))))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 3)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
            ImbalancedChen.Certificates.AboveMuSecondCoarse.step)
          u)
        v))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.mu

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Real
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.mu._proof_1

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.mu._proof_2

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.mu.eq_1

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Real ImbalancedChen.Certificates.AboveMuSecondCoarse.mu
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 25)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 25) Real.instNatCast
        ImbalancedChen.Certificates.AboveMuSecondCoarse.mu._proof_1))
    (@OfNat.ofNat.{0} Real (nat_lit 128)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
        ImbalancedChen.Certificates.AboveMuSecondCoarse.mu._proof_2)))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.negativeDenominatorCap

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Real
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.negativeDenominatorCap._proof_1

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.negativeDenominatorCap.eq_1

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Real ImbalancedChen.Certificates.AboveMuSecondCoarse.negativeDenominatorCap
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      ImbalancedChen.Certificates.AboveMuSecondCoarse.rho ImbalancedChen.Certificates.AboveMuSecondCoarse.mu)
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 5)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
            ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual._proof_2))
        (@OfNat.ofNat.{0} Real (nat_lit 24)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 24) Real.instNatCast
            ImbalancedChen.Certificates.AboveMuSecondCoarse.negativeDenominatorCap._proof_1)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.negative_chart_lower

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
@LE.le.{0} Real Real.instLE
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 3)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@OfNat.ofNat.{0} Real (nat_lit 95000)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 95000) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 94999) (instOfNatNat (nat_lit 94999)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 94998) (instOfNatNat (nat_lit 94998))))))))
  (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral
    (@Neg.neg.{0} Real Real.instNeg
      (@OfNat.ofNat.{0} Real (nat_lit 3)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.negative_chart_upper_bounds

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {u v : Real}
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  And
    (@LE.le.{0} Real Real.instLE
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
        u v)
      ImbalancedChen.Certificates.AboveMuSecondCoarse.mu)
    (And
      (@LE.le.{0} Real Real.instLE
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual
          (@Neg.neg.{0} Real Real.instNeg
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
          u v)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 5)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
          (@OfNat.ofNat.{0} Real (nat_lit 24)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 24) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))))))
      (@LE.le.{0} Real Real.instLE
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual
          (@Neg.neg.{0} Real Real.instNeg
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
          u v)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 5)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
          (@OfNat.ofNat.{0} Real (nat_lit 24)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 24) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))))))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.negative_denominator_le

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {u v : Real}
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  @LE.le.{0} Real Real.instLE
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator
      (@Neg.neg.{0} Real Real.instNeg
        (@OfNat.ofNat.{0} Real (nat_lit 3)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
      u v)
    ImbalancedChen.Certificates.AboveMuSecondCoarse.negativeDenominatorCap
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
(k u v : Real) → Real
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual_semantics

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {k u v : Real}
  (hk :
    Or
      (@Eq.{1} Real k
        (@Neg.neg.{0} Real Real.instNeg
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
      (@Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual k u v)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
(k u v : Real) → Real
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual._proof_1

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 158) (instOfNatNat (nat_lit 158)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual._proof_2

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual._proof_3

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 767) (instOfNatNat (nat_lit 767)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual_semantics

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {k u : Real} (v : Real)
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual k u v)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope
          (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
        (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartX u))
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartY k u v))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.physicalDomain

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Set.{0} (Prod.{0, 0} Real Real)
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.physicalDomain._proof_1

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.positiveDenominatorCap

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Real
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.positiveDenominatorCap._proof_1

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.positiveDenominatorCap._proof_2

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 255) (instOfNatNat (nat_lit 255)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.positiveDenominatorCap.eq_1

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Real ImbalancedChen.Certificates.AboveMuSecondCoarse.positiveDenominatorCap
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      ImbalancedChen.Certificates.AboveMuSecondCoarse.rho (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 53)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 53) Real.instNatCast
            ImbalancedChen.Certificates.AboveMuSecondCoarse.positiveDenominatorCap._proof_1))
        (@OfNat.ofNat.{0} Real (nat_lit 256)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 256) Real.instNatCast
            ImbalancedChen.Certificates.AboveMuSecondCoarse.positiveDenominatorCap._proof_2)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.positive_chart_lower

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
@LE.le.{0} Real Real.instLE
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 32)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
    (@OfNat.ofNat.{0} Real (nat_lit 3042147)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 3042147) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3042146) (instOfNatNat (nat_lit 3042146)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3042145) (instOfNatNat (nat_lit 3042145))))))))
  (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartIntegral
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.positive_chart_upper_bounds

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {u v : Real}
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  And
    (@LE.le.{0} Real Real.instLE
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.oldResidual
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) u v)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 53)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 53) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 51) (instOfNatNat (nat_lit 51)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 256)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 256) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 255) (instOfNatNat (nat_lit 255)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 254) (instOfNatNat (nat_lit 254)))))))))
    (@LE.le.{0} Real Real.instLE
      (ImbalancedChen.Certificates.AboveMuSecondCoarse.newResidual
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) u v)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 53)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 53) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 51) (instOfNatNat (nat_lit 51)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 256)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 256) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 255) (instOfNatNat (nat_lit 255)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 254) (instOfNatNat (nat_lit 254)))))))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.positive_denominator_le

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {u v : Real}
  (hu :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      u)
  (hv :
    @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
      (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      v),
  @LE.le.{0} Real Real.instLE
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.chartDenominator
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) u v)
    ImbalancedChen.Certificates.AboveMuSecondCoarse.positiveDenominatorCap
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.rho

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Real
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.rho._proof_1

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.rho._proof_2

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 95) (instOfNatNat (nat_lit 95)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.rho.eq_1

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Real ImbalancedChen.Certificates.AboveMuSecondCoarse.rho
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 19)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
        ImbalancedChen.Certificates.AboveMuSecondCoarse.rho._proof_1))
    (@OfNat.ofNat.{0} Real (nat_lit 96)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 96) Real.instNatCast
        ImbalancedChen.Certificates.AboveMuSecondCoarse.rho._proof_2)))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
(f : Real → Real → Real) → Real
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral.eq_1

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (f : Real → Real → Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral f)
    (@intervalIntegral.{0} Real Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (fun (u : Real) =>
        @intervalIntegral.{0} Real Real.normedAddCommGroup
          (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
          (fun (v : Real) => f u v) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral_weightedMass

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (C : Real),
  @Eq.{1} Real
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral fun (u v : Real) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) u
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) v))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) C
      (@OfNat.ofNat.{0} Real (nat_lit 6)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.step

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Real
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.step._proof_1

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 383) (instOfNatNat (nat_lit 383)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.step.eq_1

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Real ImbalancedChen.Certificates.AboveMuSecondCoarse.step
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
    (@OfNat.ofNat.{0} Real (nat_lit 384)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 384) Real.instNatCast
        ImbalancedChen.Certificates.AboveMuSecondCoarse.step._proof_1)))
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.step_eq

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Real ImbalancedChen.Certificates.AboveMuSecondCoarse.step
  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
    ImbalancedChen.Certificates.AboveMuSecondCoarse.rho ImbalancedChen.Certificates.AboveMuSecondCoarse.mu)
```

## ImbalancedChen.Certificates.AboveMuSecondCoarse.totalChartIntegral

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
Real
```

## _private.ImbalancedChen.Certificates.AboveMuSecondCoarse.0.ImbalancedChen.Certificates.AboveMuSecondCoarse.envelope_of_ge_mu

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {t : Real} (ht : @LE.le.{0} Real Real.instLE ImbalancedChen.Certificates.AboveMuSecondCoarse.mu t),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope t)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 57)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 57) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 55) (instOfNatNat (nat_lit 55)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 64)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62))))))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          t)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
```

## _private.ImbalancedChen.Certificates.AboveMuSecondCoarse.0.ImbalancedChen.Certificates.AboveMuSecondCoarse.envelope_of_le_mu

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {t : Real} (ht : @LE.le.{0} Real Real.instLE t ImbalancedChen.Certificates.AboveMuSecondCoarse.mu),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.endpointEnvelope t)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) t)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
```

## _private.ImbalancedChen.Certificates.AboveMuSecondCoarse.0.ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral_eq_setIntegral

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (f : Real → Real → Real)
  (hf :
    @ContinuousOn.{0, 0} (Prod.{0, 0} Real Real) Real
      (@instTopologicalSpaceProd.{0, 0} Real Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (fun (p : Prod.{0, 0} Real Real) => f (@Prod.fst.{0, 0} Real Real p) (@Prod.snd.{0, 0} Real Real p))
      (@SProd.sprod.{0, 0, 0} (Set.{0} Real) (Set.{0} Real) (Set.{0} (Prod.{0, 0} Real Real))
        (@Set.instSProd.{0, 0} Real Real)
        (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))),
  @Eq.{1} Real (ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral f)
    (@MeasureTheory.integral.{0, 0} (Prod.{0, 0} Real Real) Real Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (@Prod.instMeasurableSpace.{0, 0} Real Real
        (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
        (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace))
      (@MeasureTheory.Measure.restrict.{0} (Prod.{0, 0} Real Real)
        (@Prod.instMeasurableSpace.{0, 0} Real Real
          (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
          (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace))
        (@MeasureTheory.Measure.prod.{0, 0} Real Real
          (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
          (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
          (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)
          (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
        (@SProd.sprod.{0, 0, 0} (Set.{0} Real) (Set.{0} Real) (Set.{0} (Prod.{0, 0} Real Real))
          (@Set.instSProd.{0, 0} Real Real)
          (@Set.Ioc.{0} Real Real.instPreorder
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (@Set.Ioc.{0} Real Real.instPreorder
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
      fun (p : Prod.{0, 0} Real Real) => f (@Prod.fst.{0, 0} Real Real p) (@Prod.snd.{0, 0} Real Real p))
```

## _private.ImbalancedChen.Certificates.AboveMuSecondCoarse.0.ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral_mono

模块 `ImbalancedChen.Certificates.AboveMuSecondCoarse`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {f g : Real → Real → Real}
  (hf :
    @ContinuousOn.{0, 0} (Prod.{0, 0} Real Real) Real
      (@instTopologicalSpaceProd.{0, 0} Real Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (fun (p : Prod.{0, 0} Real Real) => f (@Prod.fst.{0, 0} Real Real p) (@Prod.snd.{0, 0} Real Real p))
      (@SProd.sprod.{0, 0, 0} (Set.{0} Real) (Set.{0} Real) (Set.{0} (Prod.{0, 0} Real Real))
        (@Set.instSProd.{0, 0} Real Real)
        (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
  (hg :
    @ContinuousOn.{0, 0} (Prod.{0, 0} Real Real) Real
      (@instTopologicalSpaceProd.{0, 0} Real Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)))
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (fun (p : Prod.{0, 0} Real Real) => g (@Prod.fst.{0, 0} Real Real p) (@Prod.snd.{0, 0} Real Real p))
      (@SProd.sprod.{0, 0, 0} (Set.{0} Real) (Set.{0} Real) (Set.{0} (Prod.{0, 0} Real Real))
        (@Set.instSProd.{0, 0} Real Real)
        (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        (@Set.Icc.{0} Real Real.instPreorder (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
  (hfg :
    ∀ (u : Real),
      @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
          (@Set.Icc.{0} Real Real.instPreorder
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          u →
        ∀ (v : Real),
          @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
              (@Set.Icc.{0} Real Real.instPreorder
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
              v →
            @LE.le.{0} Real Real.instLE (f u v) (g u v)),
  @LE.le.{0} Real Real.instLE (ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral f)
    (ImbalancedChen.Certificates.AboveMuSecondCoarse.squareIntegral g)
```

## ImbalancedChen.Certificates.PairedIntegralCertificate

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
Type
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.K

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.Valid

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(c : ImbalancedChen.Certificates.PairedIntegralCertificate) → Prop
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.Z

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

## ImbalancedChen.Certificates.PairedIntegralCertificate._sizeOf_1

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(t : ImbalancedChen.Certificates.PairedIntegralCertificate) → Nat
```

## ImbalancedChen.Certificates.PairedIntegralCertificate._sizeOf_inst

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
SizeOf.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.a

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.bracketLower

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(c : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.bracketLower.eq_1

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate),
  @Eq.{1} Rat (ImbalancedChen.Certificates.PairedIntegralCertificate.bracketLower c)
    (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
        (ImbalancedChen.Certificates.PairedIntegralCertificate.a c))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
          (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (ImbalancedChen.Certificates.RationalLogCertificate.upper
            (ImbalancedChen.Certificates.PairedIntegralCertificate.logZ c)))
        (ImbalancedChen.Certificates.PairedIntegralCertificate.Z c)))
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.bracketUpper

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(c : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.bracketUpper.eq_1

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate),
  @Eq.{1} Rat (ImbalancedChen.Certificates.PairedIntegralCertificate.bracketUpper c)
    (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
        (ImbalancedChen.Certificates.PairedIntegralCertificate.a c))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
          (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (ImbalancedChen.Certificates.RationalLogCertificate.lower
            (ImbalancedChen.Certificates.PairedIntegralCertificate.logZ c)))
        (ImbalancedChen.Certificates.PairedIntegralCertificate.Z c)))
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.casesOn

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
{motive : (t : ImbalancedChen.Certificates.PairedIntegralCertificate) → Sort u} →
  (t : ImbalancedChen.Certificates.PairedIntegralCertificate) →
    (mk :
        (K a tl tr ul ur Z : Rat) →
          (logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate) →
            (lower upper : Rat) →
              motive
                (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K a tl tr ul ur Z logT logU logZ lower
                  upper)) →
      motive t
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.check

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(c : ImbalancedChen.Certificates.PairedIntegralCertificate) → Bool
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.check_sound

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate)
  (hcheck : @Eq.{1} Bool (ImbalancedChen.Certificates.PairedIntegralCertificate.check c) Bool.true),
  And
    (@LE.le.{0} Real Real.instLE
      (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.lower c))
      (ImbalancedChen.Certificates.pairedLocalIntegral
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.K c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.a c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.tl c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.tr c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.ul c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.ur c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.Z c))))
    (@LE.le.{0} Real Real.instLE
      (ImbalancedChen.Certificates.pairedLocalIntegral
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.K c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.a c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.tl c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.tr c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.ul c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.ur c))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.Z c)))
      (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.upper c)))
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.ctorIdx

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → Nat
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.logT

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → ImbalancedChen.Certificates.RationalLogCertificate
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.logU

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → ImbalancedChen.Certificates.RationalLogCertificate
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.logZ

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → ImbalancedChen.Certificates.RationalLogCertificate
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.lower

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.mk

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(K a tl tr ul ur Z : Rat) →
  (logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate) →
    (lower upper : Rat) → ImbalancedChen.Certificates.PairedIntegralCertificate
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.mk._flat_ctor

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(K a tl tr ul ur Z : Rat) →
  (logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate) →
    (lower upper : Rat) → ImbalancedChen.Certificates.PairedIntegralCertificate
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.mk.inj

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {K a tl tr ul ur Z : Rat} {logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate}
  {lower upper K_1 a_1 tl_1 tr_1 ul_1 ur_1 Z_1 : Rat}
  {logT_1 logU_1 logZ_1 : ImbalancedChen.Certificates.RationalLogCertificate} {lower_1 upper_1 : Rat},
  @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
      (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K a tl tr ul ur Z logT logU logZ lower upper)
      (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K_1 a_1 tl_1 tr_1 ul_1 ur_1 Z_1 logT_1 logU_1 logZ_1
        lower_1 upper_1) →
    And (@Eq.{1} Rat K K_1)
      (And (@Eq.{1} Rat a a_1)
        (And (@Eq.{1} Rat tl tl_1)
          (And (@Eq.{1} Rat tr tr_1)
            (And (@Eq.{1} Rat ul ul_1)
              (And (@Eq.{1} Rat ur ur_1)
                (And (@Eq.{1} Rat Z Z_1)
                  (And (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate logT logT_1)
                    (And (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate logU logU_1)
                      (And (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate logZ logZ_1)
                        (And (@Eq.{1} Rat lower lower_1) (@Eq.{1} Rat upper upper_1)))))))))))
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.mk.injEq

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (K a tl tr ul ur Z : Rat) (logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate)
  (lower upper K_1 a_1 tl_1 tr_1 ul_1 ur_1 Z_1 : Rat)
  (logT_1 logU_1 logZ_1 : ImbalancedChen.Certificates.RationalLogCertificate) (lower_1 upper_1 : Rat),
  @Eq.{1} Prop
    (@Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
      (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K a tl tr ul ur Z logT logU logZ lower upper)
      (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K_1 a_1 tl_1 tr_1 ul_1 ur_1 Z_1 logT_1 logU_1 logZ_1
        lower_1 upper_1))
    (And (@Eq.{1} Rat K K_1)
      (And (@Eq.{1} Rat a a_1)
        (And (@Eq.{1} Rat tl tl_1)
          (And (@Eq.{1} Rat tr tr_1)
            (And (@Eq.{1} Rat ul ul_1)
              (And (@Eq.{1} Rat ur ur_1)
                (And (@Eq.{1} Rat Z Z_1)
                  (And (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate logT logT_1)
                    (And (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate logU logU_1)
                      (And (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate logZ logZ_1)
                        (And (@Eq.{1} Rat lower lower_1) (@Eq.{1} Rat upper upper_1))))))))))))
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.mk.noConfusion

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
{P : Sort u} →
  {K a tl tr ul ur Z : Rat} →
    {logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate} →
      {lower upper K' a' tl' tr' ul' ur' Z' : Rat} →
        {logT' logU' logZ' : ImbalancedChen.Certificates.RationalLogCertificate} →
          {lower' upper' : Rat} →
            (eq :
                @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
                  (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K a tl tr ul ur Z logT logU logZ lower
                    upper)
                  (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K' a' tl' tr' ul' ur' Z' logT' logU' logZ'
                    lower' upper')) →
              (k :
                  (K_eq : @Eq.{1} Rat K K') →
                    (a_eq : @Eq.{1} Rat a a') →
                      (tl_eq : @Eq.{1} Rat tl tl') →
                        (tr_eq : @Eq.{1} Rat tr tr') →
                          (ul_eq : @Eq.{1} Rat ul ul') →
                            (ur_eq : @Eq.{1} Rat ur ur') →
                              (Z_eq : @Eq.{1} Rat Z Z') →
                                (logT_eq : @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate logT logT') →
                                  (logU_eq : @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate logU logU') →
                                    (logZ_eq : @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate logZ logZ') →
                                      (lower_eq : @Eq.{1} Rat lower lower') →
                                        (upper_eq : @Eq.{1} Rat upper upper') → P) →
                P
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.mk.sizeOf_spec

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (K a tl tr ul ur Z : Rat) (logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate) (lower upper : Rat),
  @Eq.{1} Nat
    (@SizeOf.sizeOf.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
      ImbalancedChen.Certificates.PairedIntegralCertificate._sizeOf_inst
      (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K a tl tr ul ur Z logT logU logZ lower upper))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst K))
                          (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst a))
                        (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst tl))
                      (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst tr))
                    (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst ul))
                  (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst ur))
                (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst Z))
              (@SizeOf.sizeOf.{1} ImbalancedChen.Certificates.RationalLogCertificate
                ImbalancedChen.Certificates.RationalLogCertificate._sizeOf_inst logT))
            (@SizeOf.sizeOf.{1} ImbalancedChen.Certificates.RationalLogCertificate
              ImbalancedChen.Certificates.RationalLogCertificate._sizeOf_inst logU))
          (@SizeOf.sizeOf.{1} ImbalancedChen.Certificates.RationalLogCertificate
            ImbalancedChen.Certificates.RationalLogCertificate._sizeOf_inst logZ))
        (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst lower))
      (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst upper))
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.noConfusion

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
{P : Sort u} →
  {t t' : ImbalancedChen.Certificates.PairedIntegralCertificate} →
    (eq : @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate t t') →
      ImbalancedChen.Certificates.PairedIntegralCertificate.noConfusionType.{u} P t t'
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.noConfusionType

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(P : Sort u) → (t t' : ImbalancedChen.Certificates.PairedIntegralCertificate) → Sort u
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.productLower

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(c : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.productLower.eq_1

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate),
  @Eq.{1} Rat (ImbalancedChen.Certificates.PairedIntegralCertificate.productLower c)
    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
            (ImbalancedChen.Certificates.PairedIntegralCertificate.K c)
            (@OfNat.ofNat.{0} Rat (nat_lit 80) (@Rat.instOfNat (nat_lit 80))))
          (ImbalancedChen.Certificates.RationalLogCertificate.lower
            (ImbalancedChen.Certificates.PairedIntegralCertificate.logT c)))
        (ImbalancedChen.Certificates.RationalLogCertificate.lower
          (ImbalancedChen.Certificates.PairedIntegralCertificate.logU c)))
      (ImbalancedChen.Certificates.PairedIntegralCertificate.bracketLower c))
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.productUpper

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(c : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.productUpper.eq_1

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate),
  @Eq.{1} Rat (ImbalancedChen.Certificates.PairedIntegralCertificate.productUpper c)
    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
            (ImbalancedChen.Certificates.PairedIntegralCertificate.K c)
            (@OfNat.ofNat.{0} Rat (nat_lit 80) (@Rat.instOfNat (nat_lit 80))))
          (ImbalancedChen.Certificates.RationalLogCertificate.upper
            (ImbalancedChen.Certificates.PairedIntegralCertificate.logT c)))
        (ImbalancedChen.Certificates.RationalLogCertificate.upper
          (ImbalancedChen.Certificates.PairedIntegralCertificate.logU c)))
      (ImbalancedChen.Certificates.PairedIntegralCertificate.bracketUpper c))
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.rec

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
{motive : (t : ImbalancedChen.Certificates.PairedIntegralCertificate) → Sort u} →
  (mk :
      (K a tl tr ul ur Z : Rat) →
        (logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate) →
          (lower upper : Rat) →
            motive
              (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K a tl tr ul ur Z logT logU logZ lower upper)) →
    (t : ImbalancedChen.Certificates.PairedIntegralCertificate) → motive t
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.recOn

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
{motive : (t : ImbalancedChen.Certificates.PairedIntegralCertificate) → Sort u} →
  (t : ImbalancedChen.Certificates.PairedIntegralCertificate) →
    (mk :
        (K a tl tr ul ur Z : Rat) →
          (logT logU logZ : ImbalancedChen.Certificates.RationalLogCertificate) →
            (lower upper : Rat) →
              motive
                (ImbalancedChen.Certificates.PairedIntegralCertificate.mk K a tl tr ul ur Z logT logU logZ lower
                  upper)) →
      motive t
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.sum_check_sound

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {ι : Type u_1} (s : Finset.{u_1} ι) (c : ι → ImbalancedChen.Certificates.PairedIntegralCertificate)
  (hchecks :
    ∀ (i : ι),
      @Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} ι) ι (@Finset.instSetLike.{u_1} ι)) s i →
        @Eq.{1} Bool (ImbalancedChen.Certificates.PairedIntegralCertificate.check (c i)) Bool.true),
  And
    (@LE.le.{0} Real Real.instLE
      (@Rat.cast.{0} Real Real.instRatCast
        (@Finset.sum.{u_1, 0} ι Rat Rat.addCommMonoid s fun (i : ι) =>
          ImbalancedChen.Certificates.PairedIntegralCertificate.lower (c i)))
      (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid s fun (i : ι) =>
        ImbalancedChen.Certificates.pairedLocalIntegral
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.K (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.a (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.tl (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.tr (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.ul (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.ur (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.Z (c i)))))
    (@LE.le.{0} Real Real.instLE
      (@Finset.sum.{u_1, 0} ι Real Real.instAddCommMonoid s fun (i : ι) =>
        ImbalancedChen.Certificates.pairedLocalIntegral
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.K (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.a (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.tl (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.tr (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.ul (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.ur (c i)))
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedIntegralCertificate.Z (c i))))
      (@Rat.cast.{0} Real Real.instRatCast
        (@Finset.sum.{u_1, 0} ι Rat Rat.addCommMonoid s fun (i : ι) =>
          ImbalancedChen.Certificates.PairedIntegralCertificate.upper (c i))))
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.tl

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.tr

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.ul

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.upper

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.ur

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.Certificates.PairedIntegralCertificate) → Rat
```

## ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
DecidableEq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
```

## ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(x x_1 : ImbalancedChen.Certificates.PairedIntegralCertificate) →
  Decidable (@Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate x x_1)
```

## ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_1

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 : Rat),
  @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
    (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
    (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
```

## ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_10

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 b_2 b_3 : Rat) (b_4 b_5 b_6 : ImbalancedChen.Certificates.RationalLogCertificate) (b_7 b_8 : Rat),
  Not (@Eq.{1} Rat a_3 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 b b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8) →
      False
```

## ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_11

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 b_2 b_3 b_4 : Rat) (b_5 b_6 b_7 : ImbalancedChen.Certificates.RationalLogCertificate)
  (b_8 b_9 : Rat),
  Not (@Eq.{1} Rat a_2 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 b b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9) →
      False
```

## ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_12

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 b_2 b_3 b_4 b_5 : Rat) (b_6 b_7 b_8 : ImbalancedChen.Certificates.RationalLogCertificate)
  (b_9 b_10 : Rat),
  Not (@Eq.{1} Rat a_1 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a b b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10) →
      False
```

## ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_13

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 b_2 b_3 b_4 b_5 b_6 : Rat) (b_7 b_8 b_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (b_10 b_11 : Rat),
  Not (@Eq.{1} Rat a b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk b b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10 b_11) →
      False
```

## ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_2

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b : Rat),
  Not (@Eq.{1} Rat a_11 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 b) →
      False
```

## ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_3

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 : Rat),
  Not (@Eq.{1} Rat a_10 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 b b_1) →
      False
```

## ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_4

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate) (a_10 a_11 : Rat)
  (b : ImbalancedChen.Certificates.RationalLogCertificate) (b_1 b_2 : Rat),
  Not (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate a_9 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 b b_1 b_2) →
      False
```

## ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_5

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate) (a_10 a_11 : Rat)
  (b b_1 : ImbalancedChen.Certificates.RationalLogCertificate) (b_2 b_3 : Rat),
  Not (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate a_8 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 b b_1 b_2 b_3) →
      False
```

## ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_6

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate) (a_10 a_11 : Rat)
  (b b_1 b_2 : ImbalancedChen.Certificates.RationalLogCertificate) (b_3 b_4 : Rat),
  Not (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate a_7 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 b b_1 b_2 b_3 b_4) →
      False
```

## ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_7

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b : Rat) (b_1 b_2 b_3 : ImbalancedChen.Certificates.RationalLogCertificate) (b_4 b_5 : Rat),
  Not (@Eq.{1} Rat a_6 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 b b_1 b_2 b_3 b_4 b_5) →
      False
```

## ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_8

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 : Rat) (b_2 b_3 b_4 : ImbalancedChen.Certificates.RationalLogCertificate) (b_5 b_6 : Rat),
  Not (@Eq.{1} Rat a_5 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 b b_1 b_2 b_3 b_4 b_5 b_6) →
      False
```

## ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq._proof_9

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate)
  (a_10 a_11 b b_1 b_2 : Rat) (b_3 b_4 b_5 : ImbalancedChen.Certificates.RationalLogCertificate) (b_6 b_7 : Rat),
  Not (@Eq.{1} Rat a_4 b) →
    @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10 a_11)
        (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 b b_1 b_2 b_3 b_4 b_5 b_6 b_7) →
      False
```

## ImbalancedChen.Certificates.instDecidableEqPairedIntegralCertificate.decEq.match_1

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(motive :
    ImbalancedChen.Certificates.PairedIntegralCertificate →
      ImbalancedChen.Certificates.PairedIntegralCertificate → Sort u_1) →
  (x x_1 : ImbalancedChen.Certificates.PairedIntegralCertificate) →
    (h_1 :
        (a a_1 a_2 a_3 a_4 a_5 a_6 : Rat) →
          (a_7 a_8 a_9 : ImbalancedChen.Certificates.RationalLogCertificate) →
            (a_10 a_11 b b_1 b_2 b_3 b_4 b_5 b_6 : Rat) →
              (b_7 b_8 b_9 : ImbalancedChen.Certificates.RationalLogCertificate) →
                (b_10 b_11 : Rat) →
                  motive
                    (ImbalancedChen.Certificates.PairedIntegralCertificate.mk a a_1 a_2 a_3 a_4 a_5 a_6 a_7 a_8 a_9 a_10
                      a_11)
                    (ImbalancedChen.Certificates.PairedIntegralCertificate.mk b b_1 b_2 b_3 b_4 b_5 b_6 b_7 b_8 b_9 b_10
                      b_11)) →
      motive x x_1
```

## ImbalancedChen.Certificates.instDecidableValid_1

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
(c : ImbalancedChen.Certificates.PairedIntegralCertificate) →
  Decidable (ImbalancedChen.Certificates.PairedIntegralCertificate.Valid c)
```

## ImbalancedChen.Certificates.instReprPairedIntegralCertificate

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
Repr.{0} ImbalancedChen.Certificates.PairedIntegralCertificate
```

## ImbalancedChen.Certificates.instReprPairedIntegralCertificate.repr

模块 `ImbalancedChen.Certificates.PairedCertificateChecker`；格式 `PP_ALL_COMPLETE`。

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate → Nat → Std.Format
```

## ImbalancedChen.Certificates.intervalIntegrable_pairedFibreKernel

模块 `ImbalancedChen.Certificates.PairedFibreIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {a Z : Real}
  (ha : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
  (hAZ : @LE.le.{0} Real Real.instLE a Z),
  @IntervalIntegrable.{0} Real
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (@NormedAddGroup.toENormedAddMonoid.{0} Real
      (@NormedAddCommGroup.toNormedAddGroup.{0} Real Real.normedAddCommGroup))
    (fun (z : Real) =>
      @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (Real.log
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            z a))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace) a Z
```

## ImbalancedChen.Certificates.pairedFibreIntegral

模块 `ImbalancedChen.Certificates.PairedFibreIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
(a Z : Real) → Real
```

## ImbalancedChen.Certificates.pairedFibreIntegral_eq

模块 `ImbalancedChen.Certificates.PairedFibreIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {a Z : Real}
  (ha : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
  (hAZ : @LE.le.{0} Real Real.instLE a Z),
  @Eq.{1} Real (ImbalancedChen.Certificates.pairedFibreIntegral a Z)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) a)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (Real.log
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Z a)))
        Z))
```

## ImbalancedChen.Certificates.pairedFibreIntegral_eq_iterated

模块 `ImbalancedChen.Certificates.PairedFibreIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {a Z : Real}
  (ha : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
  (hAZ : @LE.le.{0} Real Real.instLE a Z),
  @Eq.{1} Real
    (@intervalIntegral.{0} Real Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (fun (z : Real) =>
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@intervalIntegral.{0} Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (fun (w : Real) =>
              @HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) w)
            a z (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)))
      a Z (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
    (ImbalancedChen.Certificates.pairedFibreIntegral a Z)
```

## ImbalancedChen.Certificates.pairedFibreKernel

模块 `ImbalancedChen.Certificates.PairedFibreIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
(t u z w : Real) → Real
```

## ImbalancedChen.Certificates.pairedFibreKernel.eq_1

模块 `ImbalancedChen.Certificates.PairedFibreIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (t u z w : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.pairedFibreKernel t u z w)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) t)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) u)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) w))))
```

## ImbalancedChen.Certificates.pairedFibreKernel_eq

模块 `ImbalancedChen.Certificates.PairedFibreIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (t u z w : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.pairedFibreKernel t u z w)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) t u)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        w))
```

## ImbalancedChen.Certificates.pairedLocalIntegral

模块 `ImbalancedChen.Certificates.PairedFibreIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
(K a tl tr ul ur Z : Real) → Real
```

## ImbalancedChen.Certificates.pairedLocalIntegral._proof_1

模块 `ImbalancedChen.Certificates.PairedFibreIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.pairedLocalIntegral.eq_1

模块 `ImbalancedChen.Certificates.PairedFibreIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (K a tl tr ul ur Z : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.pairedLocalIntegral K a tl tr ul ur Z)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) K
        (@OfNat.ofNat.{0} Real (nat_lit 80)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 80) Real.instNatCast
            ImbalancedChen.Certificates.pairedLocalIntegral._proof_1)))
      (@intervalIntegral.{0} Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (fun (t : Real) =>
          @intervalIntegral.{0} Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (fun (u : Real) =>
              @intervalIntegral.{0} Real Real.normedAddCommGroup
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                  (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                (fun (z : Real) =>
                  @intervalIntegral.{0} Real Real.normedAddCommGroup
                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                    (fun (w : Real) => ImbalancedChen.Certificates.pairedFibreKernel t u z w) a z
                    (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
                a Z (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
            ul ur (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
        tl tr (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)))
```

## ImbalancedChen.Certificates.pairedLocalIntegral_eq

模块 `ImbalancedChen.Certificates.PairedFibreIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (K : Real) {a tl tr ul ur Z : Real}
  (ha : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
  (hAZ : @LE.le.{0} Real Real.instLE a Z)
  (htl : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) tl)
  (htr : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) tr)
  (hul : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ul)
  (hur : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ur),
  @Eq.{1} Real (ImbalancedChen.Certificates.pairedLocalIntegral K a tl tr ul ur Z)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            K
            (@OfNat.ofNat.{0} Real (nat_lit 80)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 80) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))))))
          (Real.log
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) tr tl)))
        (Real.log
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            ur ul)))
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) a)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (Real.log
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) Z a)))
          Z)))
```

## ImbalancedChen.Certificates.pairedLocalIntegral_eq_literal

模块 `ImbalancedChen.Certificates.PairedFibreIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (K a tl tr ul ur Z : Real),
  @Eq.{1} Real (ImbalancedChen.Certificates.pairedLocalIntegral K a tl tr ul ur Z)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) K
        (@OfNat.ofNat.{0} Real (nat_lit 80)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 80) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))))))
      (@intervalIntegral.{0} Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (fun (t : Real) =>
          @intervalIntegral.{0} Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (fun (u : Real) =>
              @intervalIntegral.{0} Real Real.normedAddCommGroup
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                  (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                (fun (z : Real) =>
                  @intervalIntegral.{0} Real Real.normedAddCommGroup
                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                    (fun (w : Real) =>
                      @HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) t u)
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat
                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                              z (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          w))
                    a z (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
                a Z (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
            ul ur (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
        tl tr (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)))
```

## _private.ImbalancedChen.Certificates.PairedFibreIntegral.0.ImbalancedChen.Certificates.hasDerivAt_pairedFibrePrimitive

模块 `ImbalancedChen.Certificates.PairedFibreIntegral`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {a z : Real}
  (ha : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
  (hz : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z),
  @HasDerivAt.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Real
    Real.instAddCommGroup
    (@Semiring.toModule.{0} Real
      (@DivisionSemiring.toSemiring.{0} Real
        (@Semifield.toDivisionSemiring.{0} Real
          (@Field.toSemifield.{0} Real
            (@NormedField.toField.{0} Real
              (@NontriviallyNormedField.toNormedField.{0} Real
                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
    (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (@IsModuleTopology.toContinuousSMul.{0, 0} Real
      (@UniformSpace.toTopologicalSpace.{0} Real
        (@PseudoMetricSpace.toUniformSpace.{0} Real
          (@SeminormedRing.toPseudoMetricSpace.{0} Real
            (@SeminormedCommRing.toSeminormedRing.{0} Real
              (@NormedCommRing.toSeminormedCommRing.{0} Real
                (@NormedField.toNormedCommRing.{0} Real
                  (@NontriviallyNormedField.toNormedField.{0} Real
                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
      Real Real.instAdd
      (@SMulZeroClass.toSMul.{0, 0} Real Real
        (@AddZero.toZero.{0} Real
          (@AddZeroClass.toAddZero.{0} Real
            (@AddMonoid.toAddZeroClass.{0} Real
              (@SubNegMonoid.toAddMonoid.{0} Real
                (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup))))))
        (@DistribSMul.toSMulZeroClass.{0, 0} Real Real
          (@AddMonoid.toAddZeroClass.{0} Real
            (@SubNegMonoid.toAddMonoid.{0} Real
              (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup))))
          (@DistribMulAction.toDistribSMul.{0, 0} Real Real
            (@Semiring.toMonoid.{0} Real
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@NontriviallyNormedField.toNormedField.{0} Real
                        (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
            (@SubNegMonoid.toAddMonoid.{0} Real
              (@AddGroup.toSubNegMonoid.{0} Real (@AddCommGroup.toAddGroup.{0} Real Real.instAddCommGroup)))
            (@Module.toDistribMulAction.{0, 0} Real Real
              (@DivisionSemiring.toSemiring.{0} Real
                (@Semifield.toDivisionSemiring.{0} Real
                  (@Field.toSemifield.{0} Real
                    (@NormedField.toField.{0} Real
                      (@NontriviallyNormedField.toNormedField.{0} Real
                        (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
              (@AddCommGroup.toAddCommMonoid.{0} Real Real.instAddCommGroup)
              (@Semiring.toModule.{0} Real
                (@DivisionSemiring.toSemiring.{0} Real
                  (@Semifield.toDivisionSemiring.{0} Real
                    (@Field.toSemifield.{0} Real
                      (@NormedField.toField.{0} Real
                        (@NontriviallyNormedField.toNormedField.{0} Real
                          (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))))))
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@IsTopologicalSemiring.toIsModuleTopology.{0} Real Real.semiring
        (@UniformSpace.toTopologicalSpace.{0} Real
          (@PseudoMetricSpace.toUniformSpace.{0} Real
            (@SeminormedRing.toPseudoMetricSpace.{0} Real
              (@SeminormedCommRing.toSeminormedRing.{0} Real
                (@NormedCommRing.toSeminormedCommRing.{0} Real
                  (@NormedField.toNormedCommRing.{0} Real
                    (@NontriviallyNormedField.toNormedField.{0} Real
                      (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
        (@IsTopologicalRing.toIsTopologicalSemiring.{0} Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real
              (@SeminormedRing.toPseudoMetricSpace.{0} Real
                (@SeminormedCommRing.toSeminormedRing.{0} Real
                  (@NormedCommRing.toSeminormedCommRing.{0} Real
                    (@NormedField.toNormedCommRing.{0} Real
                      (@NontriviallyNormedField.toNormedField.{0} Real
                        (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))))
          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Real
            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
              (@CommRing.toNonUnitalCommRing.{0} Real Real.commRing)))
          instIsTopologicalRingReal)))
    (fun (x : Real) =>
      @Neg.neg.{0} Real Real.instNeg
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (Real.log x))
            (Real.log a))
          x))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (Real.log
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) z
          a))
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) z
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    z
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.Valid.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate),
  @Eq.{1} Prop (ImbalancedChen.Certificates.PairedIntegralCertificate.Valid c)
    (And
      (@LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
        (ImbalancedChen.Certificates.PairedIntegralCertificate.K c))
      (And
        (@LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (ImbalancedChen.Certificates.PairedIntegralCertificate.a c))
        (And
          (@LE.le.{0} Rat Rat.instLE (ImbalancedChen.Certificates.PairedIntegralCertificate.a c)
            (ImbalancedChen.Certificates.PairedIntegralCertificate.Z c))
          (And
            (@LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
              (ImbalancedChen.Certificates.PairedIntegralCertificate.tl c))
            (And
              (@LE.le.{0} Rat Rat.instLE (ImbalancedChen.Certificates.PairedIntegralCertificate.tl c)
                (ImbalancedChen.Certificates.PairedIntegralCertificate.tr c))
              (And
                (@LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                  (ImbalancedChen.Certificates.PairedIntegralCertificate.ul c))
                (And
                  (@LE.le.{0} Rat Rat.instLE (ImbalancedChen.Certificates.PairedIntegralCertificate.ul c)
                    (ImbalancedChen.Certificates.PairedIntegralCertificate.ur c))
                  (And
                    (@Eq.{1} Rat
                      (ImbalancedChen.Certificates.RationalLogCertificate.argument
                        (ImbalancedChen.Certificates.PairedIntegralCertificate.logT c))
                      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                        (ImbalancedChen.Certificates.PairedIntegralCertificate.tr c)
                        (ImbalancedChen.Certificates.PairedIntegralCertificate.tl c)))
                    (And
                      (@Eq.{1} Rat
                        (ImbalancedChen.Certificates.RationalLogCertificate.argument
                          (ImbalancedChen.Certificates.PairedIntegralCertificate.logU c))
                        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                          (ImbalancedChen.Certificates.PairedIntegralCertificate.ur c)
                          (ImbalancedChen.Certificates.PairedIntegralCertificate.ul c)))
                      (And
                        (@Eq.{1} Rat
                          (ImbalancedChen.Certificates.RationalLogCertificate.argument
                            (ImbalancedChen.Certificates.PairedIntegralCertificate.logZ c))
                          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                            (ImbalancedChen.Certificates.PairedIntegralCertificate.Z c)
                            (ImbalancedChen.Certificates.PairedIntegralCertificate.a c)))
                        (And
                          (@Eq.{1} Bool
                            (ImbalancedChen.Certificates.RationalLogCertificate.check
                              (ImbalancedChen.Certificates.PairedIntegralCertificate.logT c))
                            Bool.true)
                          (And
                            (@Eq.{1} Bool
                              (ImbalancedChen.Certificates.RationalLogCertificate.check
                                (ImbalancedChen.Certificates.PairedIntegralCertificate.logU c))
                              Bool.true)
                            (And
                              (@Eq.{1} Bool
                                (ImbalancedChen.Certificates.RationalLogCertificate.check
                                  (ImbalancedChen.Certificates.PairedIntegralCertificate.logZ c))
                                Bool.true)
                              (And
                                (@LE.le.{0} Rat Rat.instLE
                                  (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                  (ImbalancedChen.Certificates.RationalLogCertificate.lower
                                    (ImbalancedChen.Certificates.PairedIntegralCertificate.logT c)))
                                (And
                                  (@LE.le.{0} Rat Rat.instLE
                                    (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                    (ImbalancedChen.Certificates.RationalLogCertificate.lower
                                      (ImbalancedChen.Certificates.PairedIntegralCertificate.logU c)))
                                  (And
                                    (@LE.le.{0} Rat Rat.instLE
                                      (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                      (ImbalancedChen.Certificates.PairedIntegralCertificate.bracketLower c))
                                    (And
                                      (@LE.le.{0} Rat Rat.instLE
                                        (ImbalancedChen.Certificates.PairedIntegralCertificate.lower c)
                                        (ImbalancedChen.Certificates.PairedIntegralCertificate.productLower c))
                                      (@LE.le.{0} Rat Rat.instLE
                                        (ImbalancedChen.Certificates.PairedIntegralCertificate.productUpper c)
                                        (ImbalancedChen.Certificates.PairedIntegralCertificate.upper
                                          c)))))))))))))))))))
```

## ImbalancedChen.Certificates.PairedIntegralCertificate.check.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (c : ImbalancedChen.Certificates.PairedIntegralCertificate),
  @Eq.{1} Bool (ImbalancedChen.Certificates.PairedIntegralCertificate.check c)
    (@Decidable.decide (ImbalancedChen.Certificates.PairedIntegralCertificate.Valid c)
      (ImbalancedChen.Certificates.instDecidableValid_1 c))
```

## ImbalancedChen.Certificates.PairedV2.K.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Rat ImbalancedChen.Certificates.PairedV2.K
  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
    (@OfNat.ofNat.{0} Rat (nat_lit 8452171) (@Rat.instOfNat (nat_lit 8452171)))
    (@OfNat.ofNat.{0} Rat (nat_lit 1250000) (@Rat.instOfNat (nat_lit 1250000))))
```

## ImbalancedChen.Certificates.PairedV2.a.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Rat ImbalancedChen.Certificates.PairedV2.a
  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
    (@OfNat.ofNat.{0} Rat (nat_lit 417) (@Rat.instOfNat (nat_lit 417)))
    (@OfNat.ofNat.{0} Rat (nat_lit 5000) (@Rat.instOfNat (nat_lit 5000))))
```

## ImbalancedChen.Certificates.PairedV2.d.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Rat ImbalancedChen.Certificates.PairedV2.d
  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
    (@OfNat.ofNat.{0} Rat (nat_lit 59) (@Rat.instOfNat (nat_lit 59)))
    (@OfNat.ofNat.{0} Rat (nat_lit 250) (@Rat.instOfNat (nat_lit 250))))
```

## ImbalancedChen.Certificates.PairedV2.firstCertificate.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate ImbalancedChen.Certificates.PairedV2.firstCertificate
  (ImbalancedChen.Certificates.PairedIntegralCertificate.mk ImbalancedChen.Certificates.PairedV2.K
    ImbalancedChen.Certificates.PairedV2.a
    (ImbalancedChen.Certificates.PairedV2.tLower ImbalancedChen.Certificates.PairedV2.firstTIndex)
    (ImbalancedChen.Certificates.PairedV2.tUpper ImbalancedChen.Certificates.PairedV2.firstTIndex)
    (ImbalancedChen.Certificates.PairedV2.uLower ImbalancedChen.Certificates.PairedV2.firstUIndex)
    (ImbalancedChen.Certificates.PairedV2.uUpper ImbalancedChen.Certificates.PairedV2.firstUIndex)
    ImbalancedChen.Certificates.PairedV2.firstZ
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 1875373) (@Rat.instOfNat (nat_lit 1875373)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1874722) (@Rat.instOfNat (nat_lit 1874722))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 347191204489) (@Rat.instOfNat (nat_lit 347191204489)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 347191214953) (@Rat.instOfNat (nat_lit 347191214953)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000)))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 388777) (@Rat.instOfNat (nat_lit 388777)))
        (@OfNat.ofNat.{0} Rat (nat_lit 388434) (@Rat.instOfNat (nat_lit 388434))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 176528638941) (@Rat.instOfNat (nat_lit 176528638941)))
        (@OfNat.ofNat.{0} Rat (nat_lit 200000000000000) (@Rat.instOfNat (nat_lit 200000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 882643366613) (@Rat.instOfNat (nat_lit 882643366613)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000)))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 25362703) (@Rat.instOfNat (nat_lit 25362703)))
        (@OfNat.ofNat.{0} Rat (nat_lit 14802944) (@Rat.instOfNat (nat_lit 14802944))))
      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 538453624463727) (@Rat.instOfNat (nat_lit 538453624463727)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 538453686055971) (@Rat.instOfNat (nat_lit 538453686055971)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000)))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 31703) (@Rat.instOfNat (nat_lit 31703)))
      (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000) (@Rat.instOfNat (nat_lit 1000000000000))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 31704) (@Rat.instOfNat (nat_lit 31704)))
      (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000) (@Rat.instOfNat (nat_lit 1000000000000)))))
```

## ImbalancedChen.Certificates.PairedV2.firstDiscardedQ80.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Nat ImbalancedChen.Certificates.PairedV2.firstDiscardedQ80
  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
```

## ImbalancedChen.Certificates.PairedV2.firstFibreSupport

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
(t u z w : Real) → Prop
```

## ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 937360) (instOfNatNat (nat_lit 937360)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_10

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_11

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 76088108) (instOfNatNat (nat_lit 76088108)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_12

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 532479999) (instOfNatNat (nat_lit 532479999)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_2

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 4095999) (instOfNatNat (nat_lit 4095999)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_3

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1875372) (instOfNatNat (nat_lit 1875372)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_4

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 8191999) (instOfNatNat (nat_lit 8191999)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_5

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 194216) (instOfNatNat (nat_lit 194216)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_6

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1279999) (instOfNatNat (nat_lit 1279999)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_7

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 388776) (instOfNatNat (nat_lit 388776)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_8

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 2559999) (instOfNatNat (nat_lit 2559999)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_9

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.PairedV2.firstFibreSupport.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (t u z w : Real),
  @Eq.{1} Prop (ImbalancedChen.Certificates.PairedV2.firstFibreSupport t u z w)
    (And
      (@LE.le.{0} Real Real.instLE
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 937361)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 937361) Real.instNatCast
              ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_1))
          (@OfNat.ofNat.{0} Real (nat_lit 4096000)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4096000) Real.instNatCast
              ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_2)))
        t)
      (And
        (@LE.le.{0} Real Real.instLE t
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1875373)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 1875373) Real.instNatCast
                ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_3))
            (@OfNat.ofNat.{0} Real (nat_lit 8192000)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8192000) Real.instNatCast
                ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_4))))
        (And
          (@LE.le.{0} Real Real.instLE
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 194217)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 194217) Real.instNatCast
                  ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_5))
              (@OfNat.ofNat.{0} Real (nat_lit 1280000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 1280000) Real.instNatCast
                  ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_6)))
            u)
          (And
            (@LE.le.{0} Real Real.instLE u
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 388777)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 388777) Real.instNatCast
                    ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_7))
                (@OfNat.ofNat.{0} Real (nat_lit 2560000)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2560000) Real.instNatCast
                    ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_8))))
            (And
              (@LT.lt.{0} Real Real.instLT
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 417)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                      ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_9))
                  (@OfNat.ofNat.{0} Real (nat_lit 5000)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                      ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_10)))
                w)
              (And (@LT.lt.{0} Real Real.instLT w z)
                (@LT.lt.{0} Real Real.instLT z
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 76088109)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 76088109) Real.instNatCast
                        ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_11))
                    (@OfNat.ofNat.{0} Real (nat_lit 532480000)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 532480000) Real.instNatCast
                        ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_12))))))))))
```

## ImbalancedChen.Certificates.PairedV2.firstIntegral

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
Real
```

## ImbalancedChen.Certificates.PairedV2.firstIntegral._proof_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 8452170) (instOfNatNat (nat_lit 8452170)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.PairedV2.firstIntegral._proof_2

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1249999) (instOfNatNat (nat_lit 1249999)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.Certificates.PairedV2.firstIntegral.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Real ImbalancedChen.Certificates.PairedV2.firstIntegral
  (ImbalancedChen.Certificates.pairedLocalIntegral
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 8452171)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 8452171) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstIntegral._proof_1))
      (@OfNat.ofNat.{0} Real (nat_lit 1250000)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 1250000) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstIntegral._proof_2)))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 417)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_9))
      (@OfNat.ofNat.{0} Real (nat_lit 5000)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_10)))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 937361)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 937361) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_1))
      (@OfNat.ofNat.{0} Real (nat_lit 4096000)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4096000) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_2)))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1875373)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 1875373) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_3))
      (@OfNat.ofNat.{0} Real (nat_lit 8192000)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 8192000) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_4)))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 194217)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 194217) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_5))
      (@OfNat.ofNat.{0} Real (nat_lit 1280000)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 1280000) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_6)))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 388777)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 388777) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_7))
      (@OfNat.ofNat.{0} Real (nat_lit 2560000)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2560000) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_8)))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 76088109)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 76088109) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_11))
      (@OfNat.ofNat.{0} Real (nat_lit 532480000)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 532480000) Real.instNatCast
          ImbalancedChen.Certificates.PairedV2.firstFibreSupport._proof_12))))
```

## ImbalancedChen.Certificates.PairedV2.firstIntegral_bounds

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
And
  (@LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 31703)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 31703) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31702) (instOfNatNat (nat_lit 31702)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 31701) (instOfNatNat (nat_lit 31701)))))))
      (@OfNat.ofNat.{0} Real (nat_lit 1000000000000)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 1000000000000) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat
            (@OfNat.ofNat.{0} Nat (nat_lit 999999999999) (instOfNatNat (nat_lit 999999999999)))
            (@Nat.instNeZeroSucc
              (@OfNat.ofNat.{0} Nat (nat_lit 999999999998) (instOfNatNat (nat_lit 999999999998))))))))
    ImbalancedChen.Certificates.PairedV2.firstIntegral)
  (@LE.le.{0} Real Real.instLE ImbalancedChen.Certificates.PairedV2.firstIntegral
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 31704)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 31704) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31703) (instOfNatNat (nat_lit 31703)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 31702) (instOfNatNat (nat_lit 31702)))))))
      (@OfNat.ofNat.{0} Real (nat_lit 1000000000000)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 1000000000000) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat
            (@OfNat.ofNat.{0} Nat (nat_lit 999999999999) (instOfNatNat (nat_lit 999999999999)))
            (@Nat.instNeZeroSucc
              (@OfNat.ofNat.{0} Nat (nat_lit 999999999998) (instOfNatNat (nat_lit 999999999998)))))))))
```

## ImbalancedChen.Certificates.PairedV2.firstIntegral_pos

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
  ImbalancedChen.Certificates.PairedV2.firstIntegral
```

## ImbalancedChen.Certificates.PairedV2.firstIntegral_semantics

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Real ImbalancedChen.Certificates.PairedV2.firstIntegral
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 8452171)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 8452171) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8452170) (instOfNatNat (nat_lit 8452170)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8452169) (instOfNatNat (nat_lit 8452169)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 1250000)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 1250000) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1249999) (instOfNatNat (nat_lit 1249999)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1249998) (instOfNatNat (nat_lit 1249998))))))))
      (@OfNat.ofNat.{0} Real (nat_lit 80)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 80) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))))))
    (@intervalIntegral.{0} Real Real.normedAddCommGroup
      (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
        (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
        (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
      (fun (t : Real) =>
        @intervalIntegral.{0} Real Real.normedAddCommGroup
          (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
            (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
            (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
          (fun (u : Real) =>
            @intervalIntegral.{0} Real Real.normedAddCommGroup
              (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
              (fun (z : Real) =>
                @intervalIntegral.{0} Real Real.normedAddCommGroup
                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                    (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                  (fun (w : Real) =>
                    @HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) t u)
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            z (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        w))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 417)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
                    (@OfNat.ofNat.{0} Real (nat_lit 5000)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998))))))))
                  z (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 417)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
                (@OfNat.ofNat.{0} Real (nat_lit 5000)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998))))))))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 76088109)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 76088109) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 76088108) (instOfNatNat (nat_lit 76088108)))
                      (@Nat.instNeZeroSucc
                        (@OfNat.ofNat.{0} Nat (nat_lit 76088107) (instOfNatNat (nat_lit 76088107)))))))
                (@OfNat.ofNat.{0} Real (nat_lit 532480000)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 532480000) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat
                      (@OfNat.ofNat.{0} Nat (nat_lit 532479999) (instOfNatNat (nat_lit 532479999)))
                      (@Nat.instNeZeroSucc
                        (@OfNat.ofNat.{0} Nat (nat_lit 532479998) (instOfNatNat (nat_lit 532479998))))))))
              (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 194217)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 194217) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 194216) (instOfNatNat (nat_lit 194216)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 194215) (instOfNatNat (nat_lit 194215)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 1280000)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 1280000) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1279999) (instOfNatNat (nat_lit 1279999)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1279998) (instOfNatNat (nat_lit 1279998))))))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 388777)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 388777) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 388776) (instOfNatNat (nat_lit 388776)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 388775) (instOfNatNat (nat_lit 388775)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 2560000)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2560000) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2559999) (instOfNatNat (nat_lit 2559999)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2559998) (instOfNatNat (nat_lit 2559998))))))))
          (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 937361)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 937361) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 937360) (instOfNatNat (nat_lit 937360)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 937359) (instOfNatNat (nat_lit 937359)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 4096000)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 4096000) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4095999) (instOfNatNat (nat_lit 4095999)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4095998) (instOfNatNat (nat_lit 4095998))))))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1875373)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 1875373) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1875372) (instOfNatNat (nat_lit 1875372)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1875371) (instOfNatNat (nat_lit 1875371)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 8192000)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 8192000) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8191999) (instOfNatNat (nat_lit 8191999)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8191998) (instOfNatNat (nat_lit 8191998))))))))
      (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)))
```

## ImbalancedChen.Certificates.PairedV2.firstTIndex.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Nat ImbalancedChen.Certificates.PairedV2.firstTIndex
  (@OfNat.ofNat.{0} Nat (nat_lit 422) (instOfNatNat (nat_lit 422)))
```

## ImbalancedChen.Certificates.PairedV2.firstUIndex.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Nat ImbalancedChen.Certificates.PairedV2.firstUIndex
  (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))
```

## ImbalancedChen.Certificates.PairedV2.firstZ.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Rat ImbalancedChen.Certificates.PairedV2.firstZ
  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
    (@OfNat.ofNat.{0} Rat (nat_lit 76088109) (@Rat.instOfNat (nat_lit 76088109)))
    (@OfNat.ofNat.{0} Rat (nat_lit 532480000) (@Rat.instOfNat (nat_lit 532480000))))
```

## ImbalancedChen.Certificates.PairedV2.first_certificate_checked

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Bool
  (ImbalancedChen.Certificates.PairedIntegralCertificate.check ImbalancedChen.Certificates.PairedV2.firstCertificate)
  Bool.true
```

## ImbalancedChen.Certificates.PairedV2.first_coordinates

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
And
  (@Eq.{1} Rat (ImbalancedChen.Certificates.PairedV2.tLower ImbalancedChen.Certificates.PairedV2.firstTIndex)
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 937361) (@Rat.instOfNat (nat_lit 937361)))
      (@OfNat.ofNat.{0} Rat (nat_lit 4096000) (@Rat.instOfNat (nat_lit 4096000)))))
  (And
    (@Eq.{1} Rat (ImbalancedChen.Certificates.PairedV2.tUpper ImbalancedChen.Certificates.PairedV2.firstTIndex)
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 1875373) (@Rat.instOfNat (nat_lit 1875373)))
        (@OfNat.ofNat.{0} Rat (nat_lit 8192000) (@Rat.instOfNat (nat_lit 8192000)))))
    (And
      (@Eq.{1} Rat (ImbalancedChen.Certificates.PairedV2.uLower ImbalancedChen.Certificates.PairedV2.firstUIndex)
        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@OfNat.ofNat.{0} Rat (nat_lit 194217) (@Rat.instOfNat (nat_lit 194217)))
          (@OfNat.ofNat.{0} Rat (nat_lit 1280000) (@Rat.instOfNat (nat_lit 1280000)))))
      (@Eq.{1} Rat (ImbalancedChen.Certificates.PairedV2.uUpper ImbalancedChen.Certificates.PairedV2.firstUIndex)
        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@OfNat.ofNat.{0} Rat (nat_lit 388777) (@Rat.instOfNat (nat_lit 388777)))
          (@OfNat.ofNat.{0} Rat (nat_lit 2560000) (@Rat.instOfNat (nat_lit 2560000)))))))
```

## ImbalancedChen.Certificates.PairedV2.first_cutoff_definition

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Rat ImbalancedChen.Certificates.PairedV2.firstZ
  (@Min.min.{0} Rat Rat.instInf
    (ImbalancedChen.Certificates.PairedV2.uLower ImbalancedChen.Certificates.PairedV2.firstUIndex)
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
        (@OfNat.ofNat.{0} Rat (nat_lit 3) (@Rat.instOfNat (nat_lit 3)))
        (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
          (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
            (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
            (ImbalancedChen.Certificates.PairedV2.tUpper ImbalancedChen.Certificates.PairedV2.firstTIndex))
          (ImbalancedChen.Certificates.PairedV2.uUpper ImbalancedChen.Certificates.PairedV2.firstUIndex)))
      (@OfNat.ofNat.{0} Rat (nat_lit 13) (@Rat.instOfNat (nat_lit 13)))))
```

## ImbalancedChen.Certificates.PairedV2.first_fibre_argument

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {t u z w : Real} (hs : ImbalancedChen.Certificates.PairedV2.firstFibreSupport t u z w),
  And
    (@LT.lt.{0} Real Real.instLT
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 417)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
        (@OfNat.ofNat.{0} Real (nat_lit 5000)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998))))))))
      w)
    (And (@LT.lt.{0} Real Real.instLT w z)
      (And (@LT.lt.{0} Real Real.instLT z u)
        (And
          (@LT.lt.{0} Real Real.instLT u
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 123) (instOfNatNat (nat_lit 123)))))))))
          (And
            (@LT.lt.{0} Real Real.instLT
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 19)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))))
                (@OfNat.ofNat.{0} Real (nat_lit 125)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 123) (instOfNatNat (nat_lit 123))))))))
              t)
            (And
              (@LT.lt.{0} Real Real.instLT t
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 59)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 57) (instOfNatNat (nat_lit 57)))))))
                  (@OfNat.ofNat.{0} Real (nat_lit 250)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 249) (instOfNatNat (nat_lit 249)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248)))))))))
              (@LE.le.{0} Real Real.instLE
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 7)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 7) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))
                  (@OfNat.ofNat.{0} Real (nat_lit 3)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) t)
                        u)
                      z)
                    w)
                  z)))))))
```

## ImbalancedChen.Certificates.PairedV2.first_fibre_nonempty

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
@Exists.{1} Real fun (t : Real) =>
  @Exists.{1} Real fun (u : Real) =>
    @Exists.{1} Real fun (z : Real) =>
      @Exists.{1} Real fun (w : Real) => ImbalancedChen.Certificates.PairedV2.firstFibreSupport t u z w
```

## ImbalancedChen.Certificates.PairedV2.first_geometry_checked

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
And
  (@LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
    ImbalancedChen.Certificates.PairedV2.a)
  (And (@LT.lt.{0} Rat Rat.instLT ImbalancedChen.Certificates.PairedV2.a ImbalancedChen.Certificates.PairedV2.firstZ)
    (And
      (@LE.le.{0} Rat Rat.instLE ImbalancedChen.Certificates.PairedV2.firstZ
        (ImbalancedChen.Certificates.PairedV2.uLower ImbalancedChen.Certificates.PairedV2.firstUIndex))
      (And
        (@LT.lt.{0} Rat Rat.instLT
          (ImbalancedChen.Certificates.PairedV2.uLower ImbalancedChen.Certificates.PairedV2.firstUIndex)
          (ImbalancedChen.Certificates.PairedV2.uUpper ImbalancedChen.Certificates.PairedV2.firstUIndex))
        (And
          (@LT.lt.{0} Rat Rat.instLT
            (ImbalancedChen.Certificates.PairedV2.uUpper ImbalancedChen.Certificates.PairedV2.firstUIndex)
            ImbalancedChen.Certificates.PairedV2.h)
          (And
            (@LT.lt.{0} Rat Rat.instLT ImbalancedChen.Certificates.PairedV2.h
              (ImbalancedChen.Certificates.PairedV2.tLower ImbalancedChen.Certificates.PairedV2.firstTIndex))
            (And
              (@LT.lt.{0} Rat Rat.instLT
                (ImbalancedChen.Certificates.PairedV2.tLower ImbalancedChen.Certificates.PairedV2.firstTIndex)
                (ImbalancedChen.Certificates.PairedV2.tUpper ImbalancedChen.Certificates.PairedV2.firstTIndex))
              (And
                (@LT.lt.{0} Rat Rat.instLT
                  (ImbalancedChen.Certificates.PairedV2.tUpper ImbalancedChen.Certificates.PairedV2.firstTIndex)
                  ImbalancedChen.Certificates.PairedV2.d)
                (And
                  (@LE.le.{0} Rat Rat.instLE
                    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                        (@OfNat.ofNat.{0} Rat (nat_lit 13) (@Rat.instOfNat (nat_lit 13)))
                        (@OfNat.ofNat.{0} Rat (nat_lit 3) (@Rat.instOfNat (nat_lit 3))))
                      ImbalancedChen.Certificates.PairedV2.firstZ)
                    (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                      (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                        (ImbalancedChen.Certificates.PairedV2.tUpper ImbalancedChen.Certificates.PairedV2.firstTIndex))
                      (ImbalancedChen.Certificates.PairedV2.uUpper ImbalancedChen.Certificates.PairedV2.firstUIndex)))
                  (And
                    (@LE.le.{0} Rat Rat.instLE
                      (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                        (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                            (@OfNat.ofNat.{0} Rat (nat_lit 57) (@Rat.instOfNat (nat_lit 57)))
                            (@OfNat.ofNat.{0} Rat (nat_lit 64) (@Rat.instOfNat (nat_lit 64))))
                          (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                            (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                              (@OfNat.ofNat.{0} Rat (nat_lit 5) (@Rat.instOfNat (nat_lit 5)))
                              (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))))
                            (ImbalancedChen.Certificates.PairedV2.tLower
                              ImbalancedChen.Certificates.PairedV2.firstTIndex)))
                        (ImbalancedChen.Certificates.PairedV2.uLower ImbalancedChen.Certificates.PairedV2.firstUIndex))
                      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                        (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                        ImbalancedChen.Certificates.PairedV2.a))
                    (@Eq.{1} Nat ImbalancedChen.Certificates.PairedV2.firstDiscardedQ80
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))))))
```

## ImbalancedChen.Certificates.PairedV2.h.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Rat ImbalancedChen.Certificates.PairedV2.h
  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
    (@OfNat.ofNat.{0} Rat (nat_lit 19) (@Rat.instOfNat (nat_lit 19)))
    (@OfNat.ofNat.{0} Rat (nat_lit 125) (@Rat.instOfNat (nat_lit 125))))
```

## ImbalancedChen.Certificates.PairedV2.mu.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Rat ImbalancedChen.Certificates.PairedV2.mu
  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
    (@OfNat.ofNat.{0} Rat (nat_lit 25) (@Rat.instOfNat (nat_lit 25)))
    (@OfNat.ofNat.{0} Rat (nat_lit 128) (@Rat.instOfNat (nat_lit 128))))
```

## ImbalancedChen.Certificates.PairedV2.tLower.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (i : Nat),
  @Eq.{1} Rat (ImbalancedChen.Certificates.PairedV2.tLower i)
    (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) ImbalancedChen.Certificates.PairedV2.mu
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub) ImbalancedChen.Certificates.PairedV2.d
            ImbalancedChen.Certificates.PairedV2.mu)
          (@Nat.cast.{0} Rat Rat.instNatCast i))
        (@OfNat.ofNat.{0} Rat (nat_lit 512) (@Rat.instOfNat (nat_lit 512)))))
```

## ImbalancedChen.Certificates.PairedV2.tUpper.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (i : Nat),
  @Eq.{1} Rat (ImbalancedChen.Certificates.PairedV2.tUpper i)
    (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) ImbalancedChen.Certificates.PairedV2.mu
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub) ImbalancedChen.Certificates.PairedV2.d
            ImbalancedChen.Certificates.PairedV2.mu)
          (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) (@Nat.cast.{0} Rat Rat.instNatCast i)
            (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))
        (@OfNat.ofNat.{0} Rat (nat_lit 512) (@Rat.instOfNat (nat_lit 512)))))
```

## ImbalancedChen.Certificates.PairedV2.uLower.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (j : Nat),
  @Eq.{1} Rat (ImbalancedChen.Certificates.PairedV2.uLower j)
    (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) ImbalancedChen.Certificates.PairedV2.a
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub) ImbalancedChen.Certificates.PairedV2.h
            ImbalancedChen.Certificates.PairedV2.a)
          (@Nat.cast.{0} Rat Rat.instNatCast j))
        (@OfNat.ofNat.{0} Rat (nat_lit 512) (@Rat.instOfNat (nat_lit 512)))))
```

## ImbalancedChen.Certificates.PairedV2.uUpper.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (j : Nat),
  @Eq.{1} Rat (ImbalancedChen.Certificates.PairedV2.uUpper j)
    (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) ImbalancedChen.Certificates.PairedV2.a
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub) ImbalancedChen.Certificates.PairedV2.h
            ImbalancedChen.Certificates.PairedV2.a)
          (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) (@Nat.cast.{0} Rat Rat.instNatCast j)
            (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))
        (@OfNat.ofNat.{0} Rat (nat_lit 512) (@Rat.instOfNat (nat_lit 512)))))
```

## ImbalancedChen.Certificates.RationalLogCertificate.Valid.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (c : ImbalancedChen.Certificates.RationalLogCertificate),
  @Eq.{1} Prop (ImbalancedChen.Certificates.RationalLogCertificate.Valid c)
    (And
      (@LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
        (ImbalancedChen.Certificates.RationalLogCertificate.argument c))
      (And
        (@LE.le.{0} Rat Rat.instLE (ImbalancedChen.Certificates.RationalLogCertificate.lower c)
          (ImbalancedChen.Certificates.logSeriesLower (ImbalancedChen.Certificates.RationalLogCertificate.argument c)
            (ImbalancedChen.Certificates.RationalLogCertificate.terms c)))
        (@LE.le.{0} Rat Rat.instLE
          (ImbalancedChen.Certificates.logSeriesUpper (ImbalancedChen.Certificates.RationalLogCertificate.argument c)
            (ImbalancedChen.Certificates.RationalLogCertificate.terms c))
          (ImbalancedChen.Certificates.RationalLogCertificate.upper c))))
```

## ImbalancedChen.Certificates.RationalLogCertificate.check.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (c : ImbalancedChen.Certificates.RationalLogCertificate),
  @Eq.{1} Bool (ImbalancedChen.Certificates.RationalLogCertificate.check c)
    (@Decidable.decide (ImbalancedChen.Certificates.RationalLogCertificate.Valid c)
      (ImbalancedChen.Certificates.instDecidableValid c))
```

## ImbalancedChen.Certificates.logParameter.eq_1

模块 `ImbalancedChen.Certificates.PairedV2`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (q : Rat),
  @Eq.{1} Rat (ImbalancedChen.Certificates.logParameter q)
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub) q
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
      (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) q
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))))
```

## ImbalancedChen.Certificates.PairedV2.K

模块 `ImbalancedChen.Certificates.PairedV2Data`；格式 `PP_ALL_COMPLETE`。

```lean
Rat
```

## ImbalancedChen.Certificates.PairedV2.a

模块 `ImbalancedChen.Certificates.PairedV2Data`；格式 `PP_ALL_COMPLETE`。

```lean
Rat
```

## ImbalancedChen.Certificates.PairedV2.d

模块 `ImbalancedChen.Certificates.PairedV2Data`；格式 `PP_ALL_COMPLETE`。

```lean
Rat
```

## ImbalancedChen.Certificates.PairedV2.firstCertificate

模块 `ImbalancedChen.Certificates.PairedV2Data`；格式 `PP_ALL_COMPLETE`。

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate
```

## ImbalancedChen.Certificates.PairedV2.firstDiscardedQ80

模块 `ImbalancedChen.Certificates.PairedV2Data`；格式 `PP_ALL_COMPLETE`。

```lean
Nat
```

## ImbalancedChen.Certificates.PairedV2.firstGroup

模块 `ImbalancedChen.Certificates.PairedV2Data`；格式 `PP_ALL_COMPLETE`。

```lean
String
```

## ImbalancedChen.Certificates.PairedV2.firstOrdinal

模块 `ImbalancedChen.Certificates.PairedV2Data`；格式 `PP_ALL_COMPLETE`。

```lean
Nat
```

## ImbalancedChen.Certificates.PairedV2.firstStoredLowerQ160

模块 `ImbalancedChen.Certificates.PairedV2Data`；格式 `PP_ALL_COMPLETE`。

```lean
Int
```

## ImbalancedChen.Certificates.PairedV2.firstStoredUpperQ160

模块 `ImbalancedChen.Certificates.PairedV2Data`；格式 `PP_ALL_COMPLETE`。

```lean
Int
```

## ImbalancedChen.Certificates.PairedV2.firstTIndex

模块 `ImbalancedChen.Certificates.PairedV2Data`；格式 `PP_ALL_COMPLETE`。

```lean
Nat
```

## ImbalancedChen.Certificates.PairedV2.firstUIndex

模块 `ImbalancedChen.Certificates.PairedV2Data`；格式 `PP_ALL_COMPLETE`。

```lean
Nat
```

## ImbalancedChen.Certificates.PairedV2.firstZ

模块 `ImbalancedChen.Certificates.PairedV2Data`；格式 `PP_ALL_COMPLETE`。

```lean
Rat
```

## ImbalancedChen.Certificates.PairedV2.h

模块 `ImbalancedChen.Certificates.PairedV2Data`；格式 `PP_ALL_COMPLETE`。

```lean
Rat
```

## ImbalancedChen.Certificates.PairedV2.mu

模块 `ImbalancedChen.Certificates.PairedV2Data`；格式 `PP_ALL_COMPLETE`。

```lean
Rat
```

## ImbalancedChen.Certificates.PairedV2.tLower

模块 `ImbalancedChen.Certificates.PairedV2Data`；格式 `PP_ALL_COMPLETE`。

```lean
(i : Nat) → Rat
```

## ImbalancedChen.Certificates.PairedV2.tUpper

模块 `ImbalancedChen.Certificates.PairedV2Data`；格式 `PP_ALL_COMPLETE`。

```lean
(i : Nat) → Rat
```

## ImbalancedChen.Certificates.PairedV2.uLower

模块 `ImbalancedChen.Certificates.PairedV2Data`；格式 `PP_ALL_COMPLETE`。

```lean
(j : Nat) → Rat
```

## ImbalancedChen.Certificates.PairedV2.uUpper

模块 `ImbalancedChen.Certificates.PairedV2Data`；格式 `PP_ALL_COMPLETE`。

```lean
(j : Nat) → Rat
```

## ImbalancedChen.Certificates.PairedV2.E0Geometry

模块 `ImbalancedChen.Certificates.PairedV2Geometry`；格式 `PP_ALL_COMPLETE`。

```lean
(i j : Nat) → (Z : Rat) → Prop
```

## ImbalancedChen.Certificates.PairedV2.E0Geometry.cutoff_bound

模块 `ImbalancedChen.Certificates.PairedV2Geometry`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {i j : Nat} {Z : Rat} (hg : ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z),
  @LE.le.{0} Rat Rat.instLE
    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 13) (@Rat.instOfNat (nat_lit 13)))
        (@OfNat.ofNat.{0} Rat (nat_lit 3) (@Rat.instOfNat (nat_lit 3))))
      Z)
    (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
      (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (ImbalancedChen.Certificates.PairedV2.tUpper i))
      (ImbalancedChen.Certificates.PairedV2.uUpper j))
```

## ImbalancedChen.Certificates.PairedV2.E0Geometry.fibre_argument

模块 `ImbalancedChen.Certificates.PairedV2Geometry`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {i j : Nat} {Z : Rat} (hg : ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z) {t u z w : Real}
  (hs : ImbalancedChen.Certificates.PairedV2.openFibreSupport i j Z t u z w),
  And (@LT.lt.{0} Real Real.instLT (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.a) w)
    (And (@LT.lt.{0} Real Real.instLT w z)
      (And (@LT.lt.{0} Real Real.instLT z u)
        (And
          (@LT.lt.{0} Real Real.instLT u (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.h))
          (And
            (@LT.lt.{0} Real Real.instLT (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.h) t)
            (And
              (@LT.lt.{0} Real Real.instLT t
                (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.d))
              (@LE.le.{0} Real Real.instLE
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 7)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 7) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))
                  (@OfNat.ofNat.{0} Real (nat_lit 3)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) t)
                        u)
                      z)
                    w)
                  z)))))))
```

## ImbalancedChen.Certificates.PairedV2.E0Geometry.fibre_nonempty

模块 `ImbalancedChen.Certificates.PairedV2Geometry`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {i j : Nat} {Z : Rat} (hg : ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z),
  @Exists.{1} Real fun (t : Real) =>
    @Exists.{1} Real fun (u : Real) =>
      @Exists.{1} Real fun (z : Real) =>
        @Exists.{1} Real fun (w : Real) => ImbalancedChen.Certificates.PairedV2.openFibreSupport i j Z t u z w
```

## ImbalancedChen.Certificates.PairedV2.E0Geometry.residual_bound

模块 `ImbalancedChen.Certificates.PairedV2Geometry`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {i j : Nat} {Z : Rat} (hg : ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z) {t u : Real}
  (ht :
    @LE.le.{0} Real Real.instLE (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedV2.tLower i)) t)
  (hu :
    @LE.le.{0} Real Real.instLE (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedV2.uLower j))
      u),
  @LE.le.{0} Real Real.instLE
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 57)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 57) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 55) (instOfNatNat (nat_lit 55)))))))
          (@OfNat.ofNat.{0} Real (nat_lit 64)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62))))))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 5)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          t))
      u)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.a))
```

## ImbalancedChen.Certificates.PairedV2.e0GeometryCheck

模块 `ImbalancedChen.Certificates.PairedV2Geometry`；格式 `PP_ALL_COMPLETE`。

```lean
(i j : Nat) → (Z : Rat) → Bool
```

## ImbalancedChen.Certificates.PairedV2.e0GeometryCheck_fibre_argument

模块 `ImbalancedChen.Certificates.PairedV2Geometry`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {i j : Nat} {Z : Rat} (hcheck : @Eq.{1} Bool (ImbalancedChen.Certificates.PairedV2.e0GeometryCheck i j Z) Bool.true)
  {t u z w : Real} (hs : ImbalancedChen.Certificates.PairedV2.openFibreSupport i j Z t u z w),
  And (@LT.lt.{0} Real Real.instLT (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.a) w)
    (And (@LT.lt.{0} Real Real.instLT w z)
      (And (@LT.lt.{0} Real Real.instLT z u)
        (And
          (@LT.lt.{0} Real Real.instLT u (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.h))
          (And
            (@LT.lt.{0} Real Real.instLT (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.h) t)
            (And
              (@LT.lt.{0} Real Real.instLT t
                (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.d))
              (@LE.le.{0} Real Real.instLE
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 7)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 7) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))
                  (@OfNat.ofNat.{0} Real (nat_lit 3)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) t)
                        u)
                      z)
                    w)
                  z)))))))
```

## ImbalancedChen.Certificates.PairedV2.e0GeometryCheck_sound

模块 `ImbalancedChen.Certificates.PairedV2Geometry`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {i j : Nat} {Z : Rat} (hcheck : @Eq.{1} Bool (ImbalancedChen.Certificates.PairedV2.e0GeometryCheck i j Z) Bool.true),
  ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z
```

## ImbalancedChen.Certificates.PairedV2.instDecidableE0Geometry

模块 `ImbalancedChen.Certificates.PairedV2Geometry`；格式 `PP_ALL_COMPLETE`。

```lean
(i j : Nat) → (Z : Rat) → Decidable (ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z)
```

## ImbalancedChen.Certificates.PairedV2.openFibreSupport

模块 `ImbalancedChen.Certificates.PairedV2Geometry`；格式 `PP_ALL_COMPLETE`。

```lean
(i j : Nat) → (Z : Rat) → (t u z w : Real) → Prop
```

## ImbalancedChen.Certificates.PairedV2.E0Geometry.eq_1

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (i j : Nat) (Z : Rat),
  @Eq.{1} Prop (ImbalancedChen.Certificates.PairedV2.E0Geometry i j Z)
    (And (@LT.lt.{0} Nat instLTNat i (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))))
      (And (@LT.lt.{0} Nat instLTNat j (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))))
        (And
          (@LT.lt.{0} Rat Rat.instLT (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
            ImbalancedChen.Certificates.PairedV2.a)
          (And (@LT.lt.{0} Rat Rat.instLT ImbalancedChen.Certificates.PairedV2.a Z)
            (And
              (@Eq.{1} Rat Z
                (@Min.min.{0} Rat Rat.instInf (ImbalancedChen.Certificates.PairedV2.uLower j)
                  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                      (@OfNat.ofNat.{0} Rat (nat_lit 3) (@Rat.instOfNat (nat_lit 3)))
                      (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                        (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                          (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                          (ImbalancedChen.Certificates.PairedV2.tUpper i))
                        (ImbalancedChen.Certificates.PairedV2.uUpper j)))
                    (@OfNat.ofNat.{0} Rat (nat_lit 13) (@Rat.instOfNat (nat_lit 13))))))
              (And (@LE.le.{0} Rat Rat.instLE Z (ImbalancedChen.Certificates.PairedV2.uLower j))
                (And
                  (@LT.lt.{0} Rat Rat.instLT (ImbalancedChen.Certificates.PairedV2.uLower j)
                    (ImbalancedChen.Certificates.PairedV2.uUpper j))
                  (And
                    (@LE.le.{0} Rat Rat.instLE (ImbalancedChen.Certificates.PairedV2.uUpper j)
                      ImbalancedChen.Certificates.PairedV2.h)
                    (And
                      (@LT.lt.{0} Rat Rat.instLT ImbalancedChen.Certificates.PairedV2.h
                        (ImbalancedChen.Certificates.PairedV2.tLower i))
                      (And
                        (@LT.lt.{0} Rat Rat.instLT (ImbalancedChen.Certificates.PairedV2.tLower i)
                          (ImbalancedChen.Certificates.PairedV2.tUpper i))
                        (And
                          (@LE.le.{0} Rat Rat.instLE (ImbalancedChen.Certificates.PairedV2.tUpper i)
                            ImbalancedChen.Certificates.PairedV2.d)
                          (@LE.le.{0} Rat Rat.instLE
                            (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                              (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                                (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                                  (@OfNat.ofNat.{0} Rat (nat_lit 57) (@Rat.instOfNat (nat_lit 57)))
                                  (@OfNat.ofNat.{0} Rat (nat_lit 64) (@Rat.instOfNat (nat_lit 64))))
                                (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                                    (@OfNat.ofNat.{0} Rat (nat_lit 5) (@Rat.instOfNat (nat_lit 5)))
                                    (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2))))
                                  (ImbalancedChen.Certificates.PairedV2.tLower i)))
                              (ImbalancedChen.Certificates.PairedV2.uLower j))
                            (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                              (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                              ImbalancedChen.Certificates.PairedV2.a)))))))))))))
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0000.eq_1

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
  ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0000
  (ImbalancedChen.Certificates.PairedIntegralCertificate.mk ImbalancedChen.Certificates.PairedV2.K
    ImbalancedChen.Certificates.PairedV2.a
    (ImbalancedChen.Certificates.PairedV2.tLower (@OfNat.ofNat.{0} Nat (nat_lit 422) (instOfNatNat (nat_lit 422))))
    (ImbalancedChen.Certificates.PairedV2.tUpper (@OfNat.ofNat.{0} Nat (nat_lit 422) (instOfNatNat (nat_lit 422))))
    (ImbalancedChen.Certificates.PairedV2.uLower (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510))))
    (ImbalancedChen.Certificates.PairedV2.uUpper (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 76088109) (@Rat.instOfNat (nat_lit 76088109)))
      (@OfNat.ofNat.{0} Rat (nat_lit 532480000) (@Rat.instOfNat (nat_lit 532480000))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 1875373) (@Rat.instOfNat (nat_lit 1875373)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1874722) (@Rat.instOfNat (nat_lit 1874722))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 347191204489) (@Rat.instOfNat (nat_lit 347191204489)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 347191214953) (@Rat.instOfNat (nat_lit 347191214953)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000)))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 388777) (@Rat.instOfNat (nat_lit 388777)))
        (@OfNat.ofNat.{0} Rat (nat_lit 388434) (@Rat.instOfNat (nat_lit 388434))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 176528638941) (@Rat.instOfNat (nat_lit 176528638941)))
        (@OfNat.ofNat.{0} Rat (nat_lit 200000000000000) (@Rat.instOfNat (nat_lit 200000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 882643366613) (@Rat.instOfNat (nat_lit 882643366613)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000)))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 25362703) (@Rat.instOfNat (nat_lit 25362703)))
        (@OfNat.ofNat.{0} Rat (nat_lit 14802944) (@Rat.instOfNat (nat_lit 14802944))))
      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 538453624463727) (@Rat.instOfNat (nat_lit 538453624463727)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 538453686055971) (@Rat.instOfNat (nat_lit 538453686055971)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000)))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 634063221377) (@Rat.instOfNat (nat_lit 634063221377)))
      (@OfNat.ofNat.{0} Rat (nat_lit 20000000000000000000) (@Rat.instOfNat (nat_lit 20000000000000000000))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 3170317936341) (@Rat.instOfNat (nat_lit 3170317936341)))
      (@OfNat.ofNat.{0} Rat (nat_lit 100000000000000000000) (@Rat.instOfNat (nat_lit 100000000000000000000)))))
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0001.eq_1

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
  ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0001
  (ImbalancedChen.Certificates.PairedIntegralCertificate.mk ImbalancedChen.Certificates.PairedV2.K
    ImbalancedChen.Certificates.PairedV2.a
    (ImbalancedChen.Certificates.PairedV2.tLower (@OfNat.ofNat.{0} Nat (nat_lit 422) (instOfNatNat (nat_lit 422))))
    (ImbalancedChen.Certificates.PairedV2.tUpper (@OfNat.ofNat.{0} Nat (nat_lit 422) (instOfNatNat (nat_lit 422))))
    (ImbalancedChen.Certificates.PairedV2.uLower (@OfNat.ofNat.{0} Nat (nat_lit 511) (instOfNatNat (nat_lit 511))))
    (ImbalancedChen.Certificates.PairedV2.uUpper (@OfNat.ofNat.{0} Nat (nat_lit 511) (instOfNatNat (nat_lit 511))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 1170333) (@Rat.instOfNat (nat_lit 1170333)))
      (@OfNat.ofNat.{0} Rat (nat_lit 8192000) (@Rat.instOfNat (nat_lit 8192000))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 1875373) (@Rat.instOfNat (nat_lit 1875373)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1874722) (@Rat.instOfNat (nat_lit 1874722))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 347191204489) (@Rat.instOfNat (nat_lit 347191204489)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 347191214953) (@Rat.instOfNat (nat_lit 347191214953)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000)))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 389120) (@Rat.instOfNat (nat_lit 389120)))
        (@OfNat.ofNat.{0} Rat (nat_lit 388777) (@Rat.instOfNat (nat_lit 388777))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 2755827571) (@Rat.instOfNat (nat_lit 2755827571)))
        (@OfNat.ofNat.{0} Rat (nat_lit 3125000000000) (@Rat.instOfNat (nat_lit 3125000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 35274599767) (@Rat.instOfNat (nat_lit 35274599767)))
        (@OfNat.ofNat.{0} Rat (nat_lit 40000000000000) (@Rat.instOfNat (nat_lit 40000000000000)))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 1950555) (@Rat.instOfNat (nat_lit 1950555)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1138688) (@Rat.instOfNat (nat_lit 1138688))))
      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 538237220351071) (@Rat.instOfNat (nat_lit 538237220351071)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 134559320408441) (@Rat.instOfNat (nat_lit 134559320408441)))
        (@OfNat.ofNat.{0} Rat (nat_lit 250000000000000) (@Rat.instOfNat (nat_lit 250000000000000)))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 1582705120377) (@Rat.instOfNat (nat_lit 1582705120377)))
      (@OfNat.ofNat.{0} Rat (nat_lit 50000000000000000000) (@Rat.instOfNat (nat_lit 50000000000000000000))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 126616482467) (@Rat.instOfNat (nat_lit 126616482467)))
      (@OfNat.ofNat.{0} Rat (nat_lit 4000000000000000000) (@Rat.instOfNat (nat_lit 4000000000000000000)))))
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0002.eq_1

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
  ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0002
  (ImbalancedChen.Certificates.PairedIntegralCertificate.mk ImbalancedChen.Certificates.PairedV2.K
    ImbalancedChen.Certificates.PairedV2.a
    (ImbalancedChen.Certificates.PairedV2.tLower (@OfNat.ofNat.{0} Nat (nat_lit 423) (instOfNatNat (nat_lit 423))))
    (ImbalancedChen.Certificates.PairedV2.tUpper (@OfNat.ofNat.{0} Nat (nat_lit 423) (instOfNatNat (nat_lit 423))))
    (ImbalancedChen.Certificates.PairedV2.uLower (@OfNat.ofNat.{0} Nat (nat_lit 509) (instOfNatNat (nat_lit 509))))
    (ImbalancedChen.Certificates.PairedV2.uUpper (@OfNat.ofNat.{0} Nat (nat_lit 509) (instOfNatNat (nat_lit 509))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 9511851) (@Rat.instOfNat (nat_lit 9511851)))
      (@OfNat.ofNat.{0} Rat (nat_lit 66560000) (@Rat.instOfNat (nat_lit 66560000))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 1876024) (@Rat.instOfNat (nat_lit 1876024)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1875373) (@Rat.instOfNat (nat_lit 1875373))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 347070704593) (@Rat.instOfNat (nat_lit 347070704593)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 173535357523) (@Rat.instOfNat (nat_lit 173535357523)))
        (@OfNat.ofNat.{0} Rat (nat_lit 500000000000000) (@Rat.instOfNat (nat_lit 500000000000000)))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 388434) (@Rat.instOfNat (nat_lit 388434)))
        (@OfNat.ofNat.{0} Rat (nat_lit 388091) (@Rat.instOfNat (nat_lit 388091))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 3450870867) (@Rat.instOfNat (nat_lit 3450870867)))
        (@OfNat.ofNat.{0} Rat (nat_lit 3906250000000) (@Rat.instOfNat (nat_lit 3906250000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 883423114317) (@Rat.instOfNat (nat_lit 883423114317)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000)))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 3170617) (@Rat.instOfNat (nat_lit 3170617)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1850368) (@Rat.instOfNat (nat_lit 1850368))))
      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 26927083162251) (@Rat.instOfNat (nat_lit 26927083162251)))
        (@OfNat.ofNat.{0} Rat (nat_lit 50000000000000) (@Rat.instOfNat (nat_lit 50000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 269270862481803) (@Rat.instOfNat (nat_lit 269270862481803)))
        (@OfNat.ofNat.{0} Rat (nat_lit 500000000000000) (@Rat.instOfNat (nat_lit 500000000000000)))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 1586437652383) (@Rat.instOfNat (nat_lit 1586437652383)))
      (@OfNat.ofNat.{0} Rat (nat_lit 50000000000000000000) (@Rat.instOfNat (nat_lit 50000000000000000000))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 1586438569309) (@Rat.instOfNat (nat_lit 1586438569309)))
      (@OfNat.ofNat.{0} Rat (nat_lit 50000000000000000000) (@Rat.instOfNat (nat_lit 50000000000000000000)))))
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0003.eq_1

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
  ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0003
  (ImbalancedChen.Certificates.PairedIntegralCertificate.mk ImbalancedChen.Certificates.PairedV2.K
    ImbalancedChen.Certificates.PairedV2.a
    (ImbalancedChen.Certificates.PairedV2.tLower (@OfNat.ofNat.{0} Nat (nat_lit 423) (instOfNatNat (nat_lit 423))))
    (ImbalancedChen.Certificates.PairedV2.tUpper (@OfNat.ofNat.{0} Nat (nat_lit 423) (instOfNatNat (nat_lit 423))))
    (ImbalancedChen.Certificates.PairedV2.uLower (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510))))
    (ImbalancedChen.Certificates.PairedV2.uUpper (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 9509793) (@Rat.instOfNat (nat_lit 9509793)))
      (@OfNat.ofNat.{0} Rat (nat_lit 66560000) (@Rat.instOfNat (nat_lit 66560000))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 1876024) (@Rat.instOfNat (nat_lit 1876024)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1875373) (@Rat.instOfNat (nat_lit 1875373))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 347070704593) (@Rat.instOfNat (nat_lit 347070704593)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 173535357523) (@Rat.instOfNat (nat_lit 173535357523)))
        (@OfNat.ofNat.{0} Rat (nat_lit 500000000000000) (@Rat.instOfNat (nat_lit 500000000000000)))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 388777) (@Rat.instOfNat (nat_lit 388777)))
        (@OfNat.ofNat.{0} Rat (nat_lit 388434) (@Rat.instOfNat (nat_lit 388434))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 176528638941) (@Rat.instOfNat (nat_lit 176528638941)))
        (@OfNat.ofNat.{0} Rat (nat_lit 200000000000000) (@Rat.instOfNat (nat_lit 200000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 882643366613) (@Rat.instOfNat (nat_lit 882643366613)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000)))))
    (ImbalancedChen.Certificates.RationalLogCertificate.mk
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 3169931) (@Rat.instOfNat (nat_lit 3169931)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1850368) (@Rat.instOfNat (nat_lit 1850368))))
      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 134581319546397) (@Rat.instOfNat (nat_lit 134581319546397)))
        (@OfNat.ofNat.{0} Rat (nat_lit 250000000000000) (@Rat.instOfNat (nat_lit 250000000000000))))
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 538325339594069) (@Rat.instOfNat (nat_lit 538325339594069)))
        (@OfNat.ofNat.{0} Rat (nat_lit 1000000000000000) (@Rat.instOfNat (nat_lit 1000000000000000)))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 1583981804581) (@Rat.instOfNat (nat_lit 1583981804581)))
      (@OfNat.ofNat.{0} Rat (nat_lit 50000000000000000000) (@Rat.instOfNat (nat_lit 50000000000000000000))))
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@OfNat.ofNat.{0} Rat (nat_lit 3167965434447) (@Rat.instOfNat (nat_lit 3167965434447)))
      (@OfNat.ofNat.{0} Rat (nat_lit 100000000000000000000) (@Rat.instOfNat (nat_lit 100000000000000000000)))))
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificate_inputs

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  And
    (@Eq.{1} Rat
      (ImbalancedChen.Certificates.PairedIntegralCertificate.K
        (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
      ImbalancedChen.Certificates.PairedV2.K)
    (And
      (@Eq.{1} Rat
        (ImbalancedChen.Certificates.PairedIntegralCertificate.a
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
        ImbalancedChen.Certificates.PairedV2.a)
      (And
        (@Eq.{1} Rat
          (ImbalancedChen.Certificates.PairedIntegralCertificate.tl
            (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
          (ImbalancedChen.Certificates.PairedV2.tLower
            (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
        (And
          (@Eq.{1} Rat
            (ImbalancedChen.Certificates.PairedIntegralCertificate.tr
              (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
            (ImbalancedChen.Certificates.PairedV2.tUpper
              (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
          (And
            (@Eq.{1} Rat
              (ImbalancedChen.Certificates.PairedIntegralCertificate.ul
                (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
              (ImbalancedChen.Certificates.PairedV2.uLower
                (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
            (And
              (@Eq.{1} Rat
                (ImbalancedChen.Certificates.PairedIntegralCertificate.ur
                  (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
                (ImbalancedChen.Certificates.PairedV2.uUpper
                  (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
              (@Eq.{1} Rat
                (ImbalancedChen.Certificates.PairedIntegralCertificate.Z
                  (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
                (ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i)))))))
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificates.eq_1

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @Eq.{1} ImbalancedChen.Certificates.PairedIntegralCertificate
    (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)
    (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.{1}
      (fun (x : Nat) => ImbalancedChen.Certificates.PairedIntegralCertificate)
      (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i)
      (fun (_ : Unit) => ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0000)
      (fun (_ : Unit) => ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0001)
      (fun (_ : Unit) => ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0002) fun (x : Nat) =>
      ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0003)
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificates_checked

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @Eq.{1} Bool
    (ImbalancedChen.Certificates.PairedIntegralCertificate.check
      (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
    Bool.true
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.fibre_argument

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) {t u z w : Real}
  (hs :
    ImbalancedChen.Certificates.PairedV2.openFibreSupport
      (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))
      (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))
      (ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i) t u z w),
  And (@LT.lt.{0} Real Real.instLT (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.a) w)
    (And (@LT.lt.{0} Real Real.instLT w z)
      (And (@LT.lt.{0} Real Real.instLT z u)
        (And
          (@LT.lt.{0} Real Real.instLT u (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.h))
          (And
            (@LT.lt.{0} Real Real.instLT (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.h) t)
            (And
              (@LT.lt.{0} Real Real.instLT t
                (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.d))
              (@LE.le.{0} Real Real.instLE
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 7)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 7) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))
                  (@OfNat.ofNat.{0} Real (nat_lit 3)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) t)
                        u)
                      z)
                    w)
                  z)))))))
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.fibre_nonempty

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @Exists.{1} Real fun (t : Real) =>
    @Exists.{1} Real fun (u : Real) =>
      @Exists.{1} Real fun (z : Real) =>
        @Exists.{1} Real fun (w : Real) =>
          ImbalancedChen.Certificates.PairedV2.openFibreSupport
            (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))
            (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))
            (ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i) t u z w
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.geometry_checked

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  ImbalancedChen.Certificates.PairedV2.E0Geometry
    (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))
    (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))
    (ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i)
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.integral

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
Real
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.integral.eq_1

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Real ImbalancedChen.Certificates.PairedV2.Prefix4.integral
  (@Finset.sum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real.instAddCommMonoid
    (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
    ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral i)
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.integral_bounds

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
And
  (@LE.le.{0} Real Real.instLE
    (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.Prefix4.lowerBound)
    ImbalancedChen.Certificates.PairedV2.Prefix4.integral)
  (@LE.le.{0} Real Real.instLE ImbalancedChen.Certificates.PairedV2.Prefix4.integral
    (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.Prefix4.upperBound))
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.integral_bounds._simp_1_2

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @Eq.{1} Real
    (ImbalancedChen.Certificates.pairedLocalIntegral
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.K
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.a
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.tl
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.tr
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.ul
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.ur
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.Z
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))))
    (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral i)
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.integral_pos

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
  ImbalancedChen.Certificates.PairedV2.Prefix4.integral
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.integral_semantics

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Real ImbalancedChen.Certificates.PairedV2.Prefix4.integral
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.K)
      (@OfNat.ofNat.{0} Real (nat_lit 80)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 80) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 79) (instOfNatNat (nat_lit 79)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))))))
    (@Finset.sum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real.instAddCommMonoid
      (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
      @intervalIntegral.{0} Real Real.normedAddCommGroup
        (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
          (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
          (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
        (fun (t : Real) =>
          @intervalIntegral.{0} Real Real.normedAddCommGroup
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
              (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
              (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
            (fun (u : Real) =>
              @intervalIntegral.{0} Real Real.normedAddCommGroup
                (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                  (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                (fun (z : Real) =>
                  @intervalIntegral.{0} Real Real.normedAddCommGroup
                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Real Real.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup.{0} Real Real.normedAddCommGroup)
                      (@RCLike.toInnerProductSpaceReal.{0} Real Real.instRCLike))
                    (fun (w : Real) =>
                      @HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) t u)
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat
                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                              z (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          w))
                    (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.a) z
                    (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
                (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.a)
                (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i))
                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
            (@Rat.cast.{0} Real Real.instRatCast
              (ImbalancedChen.Certificates.PairedV2.uLower
                (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
            (@Rat.cast.{0} Real Real.instRatCast
              (ImbalancedChen.Certificates.PairedV2.uUpper
                (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
            (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))
        (@Rat.cast.{0} Real Real.instRatCast
          (ImbalancedChen.Certificates.PairedV2.tLower
            (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
        (@Rat.cast.{0} Real Real.instRatCast
          (ImbalancedChen.Certificates.PairedV2.tUpper
            (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)))
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.lowerBound.eq_1

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Rat ImbalancedChen.Certificates.PairedV2.Prefix4.lowerBound
  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
    (@OfNat.ofNat.{0} Rat (nat_lit 12676565261567) (@Rat.instOfNat (nat_lit 12676565261567)))
    (@OfNat.ofNat.{0} Rat (nat_lit 100000000000000000000) (@Rat.instOfNat (nat_lit 100000000000000000000))))
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.lower_sum

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Rat
  (@Finset.sum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Rat Rat.addCommMonoid
    (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
    ImbalancedChen.Certificates.PairedIntegralCertificate.lower
      (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
  ImbalancedChen.Certificates.PairedV2.Prefix4.lowerBound
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.row0000_checked

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Bool
  (ImbalancedChen.Certificates.PairedIntegralCertificate.check
    ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0000)
  Bool.true
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.row0001_checked

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Bool
  (ImbalancedChen.Certificates.PairedIntegralCertificate.check
    ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0001)
  Bool.true
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.row0002_checked

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Bool
  (ImbalancedChen.Certificates.PairedIntegralCertificate.check
    ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0002)
  Bool.true
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.row0003_checked

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Bool
  (ImbalancedChen.Certificates.PairedIntegralCertificate.check
    ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0003)
  Bool.true
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.eq_1

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @Eq.{1} (Prod.{0, 0} Nat Nat) (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i)
    (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.{1} (fun (x : Nat) => Prod.{0, 0} Nat Nat)
      (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i)
      (fun (_ : Unit) =>
        @Prod.mk.{0, 0} Nat Nat (@OfNat.ofNat.{0} Nat (nat_lit 422) (instOfNatNat (nat_lit 422)))
          (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510))))
      (fun (_ : Unit) =>
        @Prod.mk.{0, 0} Nat Nat (@OfNat.ofNat.{0} Nat (nat_lit 422) (instOfNatNat (nat_lit 422)))
          (@OfNat.ofNat.{0} Nat (nat_lit 511) (instOfNatNat (nat_lit 511))))
      (fun (_ : Unit) =>
        @Prod.mk.{0, 0} Nat Nat (@OfNat.ofNat.{0} Nat (nat_lit 423) (instOfNatNat (nat_lit 423)))
          (@OfNat.ofNat.{0} Nat (nat_lit 509) (instOfNatNat (nat_lit 509))))
      fun (x : Nat) =>
      @Prod.mk.{0, 0} Nat Nat (@OfNat.ofNat.{0} Nat (nat_lit 423) (instOfNatNat (nat_lit 423)))
        (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510))))
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
(i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) → Real
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral.eq_1

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @Eq.{1} Real (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral i)
    (ImbalancedChen.Certificates.pairedLocalIntegral
      (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.K)
      (@Rat.cast.{0} Real Real.instRatCast ImbalancedChen.Certificates.PairedV2.a)
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedV2.tLower
          (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedV2.tUpper
          (@Prod.fst.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedV2.uLower
          (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedV2.uUpper
          (@Prod.snd.{0, 0} Nat Nat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices i))))
      (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i)))
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral_eq_certificate

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @Eq.{1} Real (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIntegral i)
    (ImbalancedChen.Certificates.pairedLocalIntegral
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.K
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.a
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.tl
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.tr
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.ul
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.ur
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i)))
      (@Rat.cast.{0} Real Real.instRatCast
        (ImbalancedChen.Certificates.PairedIntegralCertificate.Z
          (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))))
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ.eq_1

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @Eq.{1} Rat (ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ i)
    (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.{1} (fun (x : Nat) => Rat)
      (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i)
      (fun (_ : Unit) =>
        @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@OfNat.ofNat.{0} Rat (nat_lit 76088109) (@Rat.instOfNat (nat_lit 76088109)))
          (@OfNat.ofNat.{0} Rat (nat_lit 532480000) (@Rat.instOfNat (nat_lit 532480000))))
      (fun (_ : Unit) =>
        @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@OfNat.ofNat.{0} Rat (nat_lit 1170333) (@Rat.instOfNat (nat_lit 1170333)))
          (@OfNat.ofNat.{0} Rat (nat_lit 8192000) (@Rat.instOfNat (nat_lit 8192000))))
      (fun (_ : Unit) =>
        @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@OfNat.ofNat.{0} Rat (nat_lit 9511851) (@Rat.instOfNat (nat_lit 9511851)))
          (@OfNat.ofNat.{0} Rat (nat_lit 66560000) (@Rat.instOfNat (nat_lit 66560000))))
      fun (x : Nat) =>
      @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@OfNat.ofNat.{0} Rat (nat_lit 9509793) (@Rat.instOfNat (nat_lit 9509793)))
        (@OfNat.ofNat.{0} Rat (nat_lit 66560000) (@Rat.instOfNat (nat_lit 66560000))))
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.upperBound.eq_1

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Rat ImbalancedChen.Certificates.PairedV2.Prefix4.upperBound
  (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
    (@OfNat.ofNat.{0} Rat (nat_lit 12676572571081) (@Rat.instOfNat (nat_lit 12676572571081)))
    (@OfNat.ofNat.{0} Rat (nat_lit 100000000000000000000) (@Rat.instOfNat (nat_lit 100000000000000000000))))
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.upper_sum

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Rat
  (@Finset.sum.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Rat Rat.addCommMonoid
    (@Finset.univ.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
    fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
    ImbalancedChen.Certificates.PairedIntegralCertificate.upper
      (ImbalancedChen.Certificates.PairedV2.Prefix4.certificates i))
  ImbalancedChen.Certificates.PairedV2.Prefix4.upperBound
```

## _private.ImbalancedChen.Certificates.PairedV2Prefix4.0.ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.eq_1

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (motive : Nat → Sort u_1) (h_1 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (h_2 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (h_3 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (h_4 : (x : Nat) → motive x),
  @Eq.{u_1} (motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.{u_1} motive
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) h_1 h_2 h_3 h_4)
    (h_1 Unit.unit)
```

## _private.ImbalancedChen.Certificates.PairedV2Prefix4.0.ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.eq_2

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (motive : Nat → Sort u_1) (h_1 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (h_2 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (h_3 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (h_4 : (x : Nat) → motive x),
  @Eq.{u_1} (motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.{u_1} motive
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) h_1 h_2 h_3 h_4)
    (h_2 Unit.unit)
```

## _private.ImbalancedChen.Certificates.PairedV2Prefix4.0.ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.eq_3

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (motive : Nat → Sort u_1) (h_1 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (h_2 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (h_3 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (h_4 : (x : Nat) → motive x),
  @Eq.{u_1} (motive (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.{u_1} motive
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h_1 h_2 h_3 h_4)
    (h_3 Unit.unit)
```

## _private.ImbalancedChen.Certificates.PairedV2Prefix4.0.ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.eq_4

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (motive : Nat → Sort u_1) (x : Nat)
  (h_1 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (h_2 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
  (h_3 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (h_4 : (x : Nat) → motive x),
  (@Eq.{1} Nat x (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) → False) →
    (@Eq.{1} Nat x (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → False) →
      (@Eq.{1} Nat x (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → False) →
        @Eq.{u_1} (motive x)
          (ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.{u_1} motive x h_1 h_2 h_3 h_4) (h_4 x)
```

## _private.ImbalancedChen.Certificates.PairedV2Prefix4.0.ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1.splitter

模块 `ImbalancedChen.Certificates.PairedV2Prefix4`；格式 `PP_ALL_COMPLETE`。

```lean
(motive : Nat → Sort u_1) →
  (x : Nat) →
    (h_1 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
      (h_2 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        (h_3 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          (h_4 :
              (x : Nat) →
                (@Eq.{1} Nat x (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) → False) →
                  (@Eq.{1} Nat x (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → False) →
                    (@Eq.{1} Nat x (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → False) → motive x) →
            motive x
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0000

模块 `ImbalancedChen.Certificates.PairedV2Prefix4Data`；格式 `PP_ALL_COMPLETE`。

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0001

模块 `ImbalancedChen.Certificates.PairedV2Prefix4Data`；格式 `PP_ALL_COMPLETE`。

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0002

模块 `ImbalancedChen.Certificates.PairedV2Prefix4Data`；格式 `PP_ALL_COMPLETE`。

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificate0003

模块 `ImbalancedChen.Certificates.PairedV2Prefix4Data`；格式 `PP_ALL_COMPLETE`。

```lean
ImbalancedChen.Certificates.PairedIntegralCertificate
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.certificates

模块 `ImbalancedChen.Certificates.PairedV2Prefix4Data`；格式 `PP_ALL_COMPLETE`。

```lean
(i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
  ImbalancedChen.Certificates.PairedIntegralCertificate
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.lowerBound

模块 `ImbalancedChen.Certificates.PairedV2Prefix4Data`；格式 `PP_ALL_COMPLETE`。

```lean
Rat
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices

模块 `ImbalancedChen.Certificates.PairedV2Prefix4Data`；格式 `PP_ALL_COMPLETE`。

```lean
(i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) → Prod.{0, 0} Nat Nat
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.rowIndices.match_1

模块 `ImbalancedChen.Certificates.PairedV2Prefix4Data`；格式 `PP_ALL_COMPLETE`。

```lean
(motive : Nat → Sort u_1) →
  (x : Nat) →
    (h_1 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
      (h_2 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        (h_3 : (_ : Unit) → motive (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          (h_4 : (x : Nat) → motive x) → motive x
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.rowOrdinal

模块 `ImbalancedChen.Certificates.PairedV2Prefix4Data`；格式 `PP_ALL_COMPLETE`。

```lean
(i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) → Nat
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.rowZ

模块 `ImbalancedChen.Certificates.PairedV2Prefix4Data`；格式 `PP_ALL_COMPLETE`。

```lean
(i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) → Rat
```

## ImbalancedChen.Certificates.PairedV2.Prefix4.upperBound

模块 `ImbalancedChen.Certificates.PairedV2Prefix4Data`；格式 `PP_ALL_COMPLETE`。

```lean
Rat
```

## ImbalancedChen.Certificates.RationalLogCertificate

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
Type
```

## ImbalancedChen.Certificates.RationalLogCertificate.Valid

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(c : ImbalancedChen.Certificates.RationalLogCertificate) → Prop
```

## ImbalancedChen.Certificates.RationalLogCertificate._sizeOf_1

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(t : ImbalancedChen.Certificates.RationalLogCertificate) → Nat
```

## ImbalancedChen.Certificates.RationalLogCertificate._sizeOf_inst

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
SizeOf.{1} ImbalancedChen.Certificates.RationalLogCertificate
```

## ImbalancedChen.Certificates.RationalLogCertificate.argument

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.Certificates.RationalLogCertificate) → Rat
```

## ImbalancedChen.Certificates.RationalLogCertificate.casesOn

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
{motive : (t : ImbalancedChen.Certificates.RationalLogCertificate) → Sort u} →
  (t : ImbalancedChen.Certificates.RationalLogCertificate) →
    (mk :
        (argument : Rat) →
          (terms : Nat) →
            (lower upper : Rat) →
              motive (ImbalancedChen.Certificates.RationalLogCertificate.mk argument terms lower upper)) →
      motive t
```

## ImbalancedChen.Certificates.RationalLogCertificate.check

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(c : ImbalancedChen.Certificates.RationalLogCertificate) → Bool
```

## ImbalancedChen.Certificates.RationalLogCertificate.check_sound

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (c : ImbalancedChen.Certificates.RationalLogCertificate)
  (hcheck : @Eq.{1} Bool (ImbalancedChen.Certificates.RationalLogCertificate.check c) Bool.true),
  And
    (@LE.le.{0} Real Real.instLE
      (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.RationalLogCertificate.lower c))
      (Real.log (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.RationalLogCertificate.argument c))))
    (@LE.le.{0} Real Real.instLE
      (Real.log (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.RationalLogCertificate.argument c)))
      (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.Certificates.RationalLogCertificate.upper c)))
```

## ImbalancedChen.Certificates.RationalLogCertificate.ctorIdx

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
ImbalancedChen.Certificates.RationalLogCertificate → Nat
```

## ImbalancedChen.Certificates.RationalLogCertificate.lower

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.Certificates.RationalLogCertificate) → Rat
```

## ImbalancedChen.Certificates.RationalLogCertificate.mk

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(argument : Rat) → (terms : Nat) → (lower upper : Rat) → ImbalancedChen.Certificates.RationalLogCertificate
```

## ImbalancedChen.Certificates.RationalLogCertificate.mk._flat_ctor

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(argument : Rat) → (terms : Nat) → (lower upper : Rat) → ImbalancedChen.Certificates.RationalLogCertificate
```

## ImbalancedChen.Certificates.RationalLogCertificate.mk.inj

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {argument : Rat} {terms : Nat} {lower upper argument_1 : Rat} {terms_1 : Nat} {lower_1 upper_1 : Rat},
  @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate
      (ImbalancedChen.Certificates.RationalLogCertificate.mk argument terms lower upper)
      (ImbalancedChen.Certificates.RationalLogCertificate.mk argument_1 terms_1 lower_1 upper_1) →
    And (@Eq.{1} Rat argument argument_1)
      (And (@Eq.{1} Nat terms terms_1) (And (@Eq.{1} Rat lower lower_1) (@Eq.{1} Rat upper upper_1)))
```

## ImbalancedChen.Certificates.RationalLogCertificate.mk.injEq

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (argument : Rat) (terms : Nat) (lower upper argument_1 : Rat) (terms_1 : Nat) (lower_1 upper_1 : Rat),
  @Eq.{1} Prop
    (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate
      (ImbalancedChen.Certificates.RationalLogCertificate.mk argument terms lower upper)
      (ImbalancedChen.Certificates.RationalLogCertificate.mk argument_1 terms_1 lower_1 upper_1))
    (And (@Eq.{1} Rat argument argument_1)
      (And (@Eq.{1} Nat terms terms_1) (And (@Eq.{1} Rat lower lower_1) (@Eq.{1} Rat upper upper_1))))
```

## ImbalancedChen.Certificates.RationalLogCertificate.mk.noConfusion

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
{P : Sort u} →
  {argument : Rat} →
    {terms : Nat} →
      {lower upper argument' : Rat} →
        {terms' : Nat} →
          {lower' upper' : Rat} →
            (eq :
                @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate
                  (ImbalancedChen.Certificates.RationalLogCertificate.mk argument terms lower upper)
                  (ImbalancedChen.Certificates.RationalLogCertificate.mk argument' terms' lower' upper')) →
              (k :
                  (argument_eq : @Eq.{1} Rat argument argument') →
                    (terms_eq : @Eq.{1} Nat terms terms') →
                      (lower_eq : @Eq.{1} Rat lower lower') → (upper_eq : @Eq.{1} Rat upper upper') → P) →
                P
```

## ImbalancedChen.Certificates.RationalLogCertificate.mk.sizeOf_spec

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (argument : Rat) (terms : Nat) (lower upper : Rat),
  @Eq.{1} Nat
    (@SizeOf.sizeOf.{1} ImbalancedChen.Certificates.RationalLogCertificate
      ImbalancedChen.Certificates.RationalLogCertificate._sizeOf_inst
      (ImbalancedChen.Certificates.RationalLogCertificate.mk argument terms lower upper))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst argument))
          (@SizeOf.sizeOf.{1} Nat instSizeOfNat terms))
        (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst lower))
      (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst upper))
```

## ImbalancedChen.Certificates.RationalLogCertificate.noConfusion

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
{P : Sort u} →
  {t t' : ImbalancedChen.Certificates.RationalLogCertificate} →
    (eq : @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate t t') →
      ImbalancedChen.Certificates.RationalLogCertificate.noConfusionType.{u} P t t'
```

## ImbalancedChen.Certificates.RationalLogCertificate.noConfusionType

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(P : Sort u) → (t t' : ImbalancedChen.Certificates.RationalLogCertificate) → Sort u
```

## ImbalancedChen.Certificates.RationalLogCertificate.rec

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
{motive : (t : ImbalancedChen.Certificates.RationalLogCertificate) → Sort u} →
  (mk :
      (argument : Rat) →
        (terms : Nat) →
          (lower upper : Rat) →
            motive (ImbalancedChen.Certificates.RationalLogCertificate.mk argument terms lower upper)) →
    (t : ImbalancedChen.Certificates.RationalLogCertificate) → motive t
```

## ImbalancedChen.Certificates.RationalLogCertificate.recOn

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
{motive : (t : ImbalancedChen.Certificates.RationalLogCertificate) → Sort u} →
  (t : ImbalancedChen.Certificates.RationalLogCertificate) →
    (mk :
        (argument : Rat) →
          (terms : Nat) →
            (lower upper : Rat) →
              motive (ImbalancedChen.Certificates.RationalLogCertificate.mk argument terms lower upper)) →
      motive t
```

## ImbalancedChen.Certificates.RationalLogCertificate.terms

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.Certificates.RationalLogCertificate) → Nat
```

## ImbalancedChen.Certificates.RationalLogCertificate.upper

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.Certificates.RationalLogCertificate) → Rat
```

## ImbalancedChen.Certificates.instDecidableEqRationalLogCertificate

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
DecidableEq.{1} ImbalancedChen.Certificates.RationalLogCertificate
```

## ImbalancedChen.Certificates.instDecidableEqRationalLogCertificate.decEq

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(x x_1 : ImbalancedChen.Certificates.RationalLogCertificate) →
  Decidable (@Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate x x_1)
```

## ImbalancedChen.Certificates.instDecidableEqRationalLogCertificate.decEq._proof_1

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a : Rat) (a_1 : Nat) (a_2 a_3 : Rat),
  @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate
    (ImbalancedChen.Certificates.RationalLogCertificate.mk a a_1 a_2 a_3)
    (ImbalancedChen.Certificates.RationalLogCertificate.mk a a_1 a_2 a_3)
```

## ImbalancedChen.Certificates.instDecidableEqRationalLogCertificate.decEq._proof_2

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a : Rat) (a_1 : Nat) (a_2 a_3 b : Rat),
  Not (@Eq.{1} Rat a_3 b) →
    @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate
        (ImbalancedChen.Certificates.RationalLogCertificate.mk a a_1 a_2 a_3)
        (ImbalancedChen.Certificates.RationalLogCertificate.mk a a_1 a_2 b) →
      False
```

## ImbalancedChen.Certificates.instDecidableEqRationalLogCertificate.decEq._proof_3

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a : Rat) (a_1 : Nat) (a_2 a_3 b b_1 : Rat),
  Not (@Eq.{1} Rat a_2 b) →
    @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate
        (ImbalancedChen.Certificates.RationalLogCertificate.mk a a_1 a_2 a_3)
        (ImbalancedChen.Certificates.RationalLogCertificate.mk a a_1 b b_1) →
      False
```

## ImbalancedChen.Certificates.instDecidableEqRationalLogCertificate.decEq._proof_4

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a : Rat) (a_1 : Nat) (a_2 a_3 : Rat) (b : Nat) (b_1 b_2 : Rat),
  Not (@Eq.{1} Nat a_1 b) →
    @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate
        (ImbalancedChen.Certificates.RationalLogCertificate.mk a a_1 a_2 a_3)
        (ImbalancedChen.Certificates.RationalLogCertificate.mk a b b_1 b_2) →
      False
```

## ImbalancedChen.Certificates.instDecidableEqRationalLogCertificate.decEq._proof_5

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a : Rat) (a_1 : Nat) (a_2 a_3 b : Rat) (b_1 : Nat) (b_2 b_3 : Rat),
  Not (@Eq.{1} Rat a b) →
    @Eq.{1} ImbalancedChen.Certificates.RationalLogCertificate
        (ImbalancedChen.Certificates.RationalLogCertificate.mk a a_1 a_2 a_3)
        (ImbalancedChen.Certificates.RationalLogCertificate.mk b b_1 b_2 b_3) →
      False
```

## ImbalancedChen.Certificates.instDecidableEqRationalLogCertificate.decEq.match_1

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(motive :
    ImbalancedChen.Certificates.RationalLogCertificate →
      ImbalancedChen.Certificates.RationalLogCertificate → Sort u_1) →
  (x x_1 : ImbalancedChen.Certificates.RationalLogCertificate) →
    (h_1 :
        (a : Rat) →
          (a_1 : Nat) →
            (a_2 a_3 b : Rat) →
              (b_1 : Nat) →
                (b_2 b_3 : Rat) →
                  motive (ImbalancedChen.Certificates.RationalLogCertificate.mk a a_1 a_2 a_3)
                    (ImbalancedChen.Certificates.RationalLogCertificate.mk b b_1 b_2 b_3)) →
      motive x x_1
```

## ImbalancedChen.Certificates.instDecidableValid

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(c : ImbalancedChen.Certificates.RationalLogCertificate) →
  Decidable (ImbalancedChen.Certificates.RationalLogCertificate.Valid c)
```

## ImbalancedChen.Certificates.instReprRationalLogCertificate

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
Repr.{0} ImbalancedChen.Certificates.RationalLogCertificate
```

## ImbalancedChen.Certificates.instReprRationalLogCertificate.repr

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
ImbalancedChen.Certificates.RationalLogCertificate → Nat → Std.Format
```

## ImbalancedChen.Certificates.logParameter

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(q : Rat) → Rat
```

## ImbalancedChen.Certificates.logSeriesLower

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(q : Rat) → (n : Nat) → Rat
```

## ImbalancedChen.Certificates.logSeriesLower.eq_1

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (q : Rat) (n : Nat),
  @Eq.{1} Rat (ImbalancedChen.Certificates.logSeriesLower q n)
    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
      (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
      (@Finset.sum.{0, 0} Nat Rat Rat.addCommMonoid (Finset.range n) fun (i : Nat) =>
        @HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
            (ImbalancedChen.Certificates.logParameter q)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Nat.cast.{0} Rat Rat.instNatCast
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
```

## ImbalancedChen.Certificates.logSeriesUpper

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(q : Rat) → (n : Nat) → Rat
```

## ImbalancedChen.Certificates.logSeriesUpper.eq_1

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (q : Rat) (n : Nat),
  @Eq.{1} Rat (ImbalancedChen.Certificates.logSeriesUpper q n)
    (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd) (ImbalancedChen.Certificates.logSeriesLower q n)
      (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
          (@HPow.hPow.{0, 0, 0} Rat Nat Rat (@instHPow.{0, 0} Rat Nat Rat.instPowNat)
            (ImbalancedChen.Certificates.logParameter q)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
          (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
          (@HPow.hPow.{0, 0, 0} Rat Nat Rat
            (@instHPow.{0, 0} Rat Nat (@NPow.toPow.{0} Rat (@Monoid.toNPow.{0} Rat Rat.monoid)))
            (ImbalancedChen.Certificates.logParameter q)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
```

## _private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_bounds

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {q : Rat} (hq : @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) q),
  And
    (@LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
      (ImbalancedChen.Certificates.logParameter q))
    (@LT.lt.{0} Rat Rat.instLT (ImbalancedChen.Certificates.logParameter q)
      (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
```

## _private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_identity

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {q : Rat} (hq : @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) q),
  @Eq.{1} Rat
    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
      (@HAdd.hAdd.{0, 0, 0} Rat Rat Rat (@instHAdd.{0} Rat Rat.instAdd)
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (ImbalancedChen.Certificates.logParameter q))
      (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) (ImbalancedChen.Certificates.logParameter q)))
    q
```

## _private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_identity._simp_1_1

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 2) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## _private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_identity._simp_1_2

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 3) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## _private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_identity._simp_1_3

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_2} [inst : Zero.{u_2} α]
  [inst_1 : OfNat.{u_2} α (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))]
  [@NeZero.{u_2} α inst (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)],
  @Eq.{1} Prop
    (@Eq.{u_2 + 1} α (@OfNat.ofNat.{u_2} α (nat_lit 4) inst_1)
      (@OfNat.ofNat.{u_2} α (nat_lit 0) (@Zero.toOfNat0.{u_2} α inst)))
    False
```

## _private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_identity._simp_1_4

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {M₀ : Type u_1} [inst : Mul.{u_1} M₀] [inst_1 : Zero.{u_1} M₀] [@NoZeroDivisors.{u_1} M₀ inst inst_1] {a b : M₀}
  (ha : @Ne.{u_1 + 1} M₀ a (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
  (hb : @Ne.{u_1 + 1} M₀ b (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1))),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} M₀ (@HMul.hMul.{u_1, u_1, u_1} M₀ M₀ M₀ (@instHMul.{u_1} M₀ inst) a b)
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0) (@Zero.toOfNat0.{u_1} M₀ inst_1)))
    False
```

## _private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_identity._simp_1_5

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {M₀ : Type u_1} [inst : MonoidWithZero.{u_1} M₀] {a : M₀}
  [@IsReduced.{u_1} M₀
      (@MulZeroClass.toZero.{u_1} M₀
        (@MulZeroOneClass.toMulZeroClass.{u_1} M₀ (@MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst)))
      (@NPow.toPow.{u_1} M₀ (@Monoid.toNPow.{u_1} M₀ (@MonoidWithZero.toMonoid.{u_1} M₀ inst)))]
  (n : Nat)
  (h :
    @Ne.{u_1 + 1} M₀ a
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0)
        (@Zero.toOfNat0.{u_1} M₀
          (@MulZeroClass.toZero.{u_1} M₀
            (@MulZeroOneClass.toMulZeroClass.{u_1} M₀ (@MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst)))))),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} M₀
      (@HPow.hPow.{u_1, 0, u_1} M₀ Nat M₀
        (@instHPow.{u_1, 0} M₀ Nat
          (@NPow.toPow.{u_1} M₀ (@Monoid.toNPow.{u_1} M₀ (@MonoidWithZero.toMonoid.{u_1} M₀ inst))))
        a n)
      (@OfNat.ofNat.{u_1} M₀ (nat_lit 0)
        (@Zero.toOfNat0.{u_1} M₀
          (@MulZeroClass.toZero.{u_1} M₀
            (@MulZeroOneClass.toMulZeroClass.{u_1} M₀ (@MonoidWithZero.toMulZeroOneClass.{u_1} M₀ inst))))))
    False
```

## _private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_identity._simp_1_6

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {G₀ : Type u_3} [inst : GroupWithZero.{u_3} G₀] {a : G₀} (n : Int),
  @Ne.{u_3 + 1} G₀ a
      (@OfNat.ofNat.{u_3} G₀ (nat_lit 0)
        (@Zero.toOfNat0.{u_3} G₀
          (@MulZeroClass.toZero.{u_3} G₀
            (@MulZeroOneClass.toMulZeroClass.{u_3} G₀
              (@MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (@GroupWithZero.toMonoidWithZero.{u_3} G₀ inst)))))) →
    @Eq.{1} Prop
      (@Eq.{u_3 + 1} G₀
        (@HPow.hPow.{u_3, 0, u_3} G₀ Int G₀
          (@instHPow.{u_3, 0} G₀ Int
            (@ZPow.toPow.{u_3} G₀ (@DivInvMonoid.toZPow.{u_3} G₀ (@GroupWithZero.toDivInvMonoid.{u_3} G₀ inst))))
          a n)
        (@OfNat.ofNat.{u_3} G₀ (nat_lit 0)
          (@Zero.toOfNat0.{u_3} G₀
            (@MulZeroClass.toZero.{u_3} G₀
              (@MulZeroOneClass.toMulZeroClass.{u_3} G₀
                (@MonoidWithZero.toMulZeroOneClass.{u_3} G₀ (@GroupWithZero.toMonoidWithZero.{u_3} G₀ inst)))))))
      False
```

## _private.ImbalancedChen.Certificates.RationalLogCertificate.0.ImbalancedChen.Certificates.logParameter_identity._simp_1_7

模块 `ImbalancedChen.Certificates.RationalLogCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {R : Type u_1} [inst : AddMonoidWithOne.{u_1} R] [@CharZero.{u_1} R inst] (n : Nat),
  @Eq.{1} Prop
    (@Eq.{u_1 + 1} R
      (@HAdd.hAdd.{u_1, u_1, u_1} R R R
        (@instHAdd.{u_1} R
          (@AddSemigroup.toAdd.{u_1} R
            (@AddMonoid.toAddSemigroup.{u_1} R (@AddMonoidWithOne.toAddMonoid.{u_1} R inst))))
        (@Nat.cast.{u_1} R (@AddMonoidWithOne.toNatCast.{u_1} R inst) n)
        (@OfNat.ofNat.{u_1} R (nat_lit 1) (@One.toOfNat1.{u_1} R (@AddMonoidWithOne.toOne.{u_1} R inst))))
      (@OfNat.ofNat.{u_1} R (nat_lit 0)
        (@Zero.toOfNat0.{u_1} R
          (@AddZero.toZero.{u_1} R
            (@AddZeroClass.toAddZero.{u_1} R
              (@AddMonoid.toAddZeroClass.{u_1} R (@AddMonoidWithOne.toAddMonoid.{u_1} R inst)))))))
    False
```

## ImbalancedChen.currentChen_buchstab_eleven_twentieths

模块 `ImbalancedChen.CurrentChenBuchstabRefinement`；格式 `DEFAULT_META_PPEXPR_COMPLETE`。

```lean
∀ {s : ℝ}, 7 / 3 ≤ s → 11 / 20 ≤ LiLiuPrereqBuchstab.buchstab s
```

## ImbalancedChen.currentChen_buchstab_lower_first_segment

模块 `ImbalancedChen.CurrentChenBuchstabRefinement`；格式 `DEFAULT_META_PPEXPR_COMPLETE`。

```lean
∀ {s : ℝ}, 7 / 3 ≤ s → s ≤ 3 → 11 / 20 ≤ LiLiuPrereqBuchstab.buchstab s
```

## ImbalancedChen.currentChen_buchstab_lower_on_tail

模块 `ImbalancedChen.CurrentChenBuchstabRefinement`；格式 `DEFAULT_META_PPEXPR_COMPLETE`。

```lean
∀ {a L : ℝ},
  2 ≤ a →
    (∀ u ∈ Set.Icc a (a + 1), L ≤ LiLiuPrereqBuchstab.buchstab u) →
      ∀ (u : ℝ), a ≤ u → L ≤ LiLiuPrereqBuchstab.buchstab u
```

## ImbalancedChen.currentChen_buchstab_lower_transition

模块 `ImbalancedChen.CurrentChenBuchstabRefinement`；格式 `DEFAULT_META_PPEXPR_COMPLETE`。

```lean
∀ {s : ℝ}, 3 ≤ s → s ≤ 10 / 3 → 11 / 20 ≤ LiLiuPrereqBuchstab.buchstab s
```

## _private.ImbalancedChen.CurrentChenBuchstabRefinement.0.ImbalancedChen.currentChen_log_rational_lower

模块 `ImbalancedChen.CurrentChenBuchstabRefinement`；格式 `DEFAULT_META_PPEXPR_COMPLETE`。

```lean
∀ {x : ℝ}, 1 ≤ x → 2 * ((x - 1) / (x + 1)) ≤ Real.log x
```

## ImbalancedChen.currentC.eq_1

模块 `ImbalancedChen.CurrentChenLowerScale`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Real ImbalancedChen.currentC
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 49044063)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 49044063) Real.instNatCast ImbalancedChen.currentC._proof_1))
    (@OfNat.ofNat.{0} Real (nat_lit 25000000)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 25000000) Real.instNatCast ImbalancedChen.currentC._proof_2)))
```

## ImbalancedChen.currentChen_four_currentC

模块 `ImbalancedChen.CurrentChenLowerScale`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1} Real
  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
    (@OfNat.ofNat.{0} Real (nat_lit 4)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
    ImbalancedChen.currentC)
  (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
    (@OfNat.ofNat.{0} Real (nat_lit 49044063)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 49044063) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 49044062) (instOfNatNat (nat_lit 49044062)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 49044061) (instOfNatNat (nat_lit 49044061)))))))
    (@OfNat.ofNat.{0} Real (nat_lit 6250000)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 6250000) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 6249999) (instOfNatNat (nat_lit 6249999)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6249998) (instOfNatNat (nat_lit 6249998))))))))
```

## ImbalancedChen.currentChen_lower_scale_from_finite_weight_bound

模块 `ImbalancedChen.CurrentChenLowerScale`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {N : Nat} (E : Prod.{0, 0} Nat Nat → Prop) {etaMean : Real}
  (hN :
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@Nat.cast.{0} Real Real.instNatCast N))
  (hA :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
        (@Nat.cast.{0} Real Real.instNatCast N)
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 417)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
          (@OfNat.ofNat.{0} Real (nat_lit 5000)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998))))))))))
  (hweight :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 4)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
            ImbalancedChen.currentC)
          etaMean)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenPairedPrimeSum N E)),
  @LE.le.{0} Real Real.instLE
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) ImbalancedChen.currentC
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            etaMean
            (@OfNat.ofNat.{0} Real (nat_lit 4)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
        (ImbalancedChen.singularNormalization N))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 123)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 123) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 122) (instOfNatNat (nat_lit 122)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 121) (instOfNatNat (nat_lit 121)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                (@Nat.cast.{0} Real Real.instNatCast N)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 417)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
                  (@OfNat.ofNat.{0} Real (nat_lit 5000)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998)))))))))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
    (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.D12 N))
```

## ImbalancedChen.currentChen_lower_scale_of_equal_finite_budgets

模块 `ImbalancedChen.CurrentChenLowerScale`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {N : Nat} (E : Prod.{0, 0} Nat Nat → Prop) {epsilon : Real}
  (hweight :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 4)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
            ImbalancedChen.currentC)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            epsilon))
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenPairedPrimeSum N E))
  (hcount :
    @LE.le.{0} Real Real.instLE
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (ImbalancedChen.currentChenPairedPrimeSum N E)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            epsilon)
          (ImbalancedChen.singularNormalization N)))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 4)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
        (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.D12 N)))),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) ImbalancedChen.currentC epsilon)
      (ImbalancedChen.singularNormalization N))
    (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.D12 N))
```

## ImbalancedChen.currentChen_lower_scale_of_finite_budgets

模块 `ImbalancedChen.CurrentChenLowerScale`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {N : Nat} (E : Prod.{0, 0} Nat Nat → Prop) {epsilon etaMean etaCount : Real}
  (hbudget :
    @LE.le.{0} Real Real.instLE (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) etaMean etaCount)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 4)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
        epsilon))
  (hweight :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 4)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
            ImbalancedChen.currentC)
          etaMean)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenPairedPrimeSum N E))
  (hcount :
    @LE.le.{0} Real Real.instLE
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (ImbalancedChen.currentChenPairedPrimeSum N E)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) etaCount
          (ImbalancedChen.singularNormalization N)))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 4)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
        (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.D12 N)))),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) ImbalancedChen.currentC epsilon)
      (ImbalancedChen.singularNormalization N))
    (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.D12 N))
```

## ImbalancedChen.chenPairedElevenWeight_eq_unselected

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (n : Nat) (N A H D C : Real) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Real (ImbalancedChen.chenPairedElevenWeight n N A H D C E)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 3)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                          (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.chenY1 n A)))
                        (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.chenY2 n H)))
                      (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.chenY3 n A C)))
                    (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.chenY4 n A D)))
                  (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.chenY5 n A H)))
                (@Nat.cast.{0} Real Real.instNatCast
                  (ImbalancedChen.chenY6Selected n A H D fun (t : Prod.{0, 0} Nat Nat) => Not (E t))))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.chenY7 n N D))))
            (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.chenY8 n N A C)))
          (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.chenY9 n N H D)))
        (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.chenY10 n A H)))
      (@Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY11Selected n A H D fun (t : Prod.{0, 0} Nat Nat) => Not (E t))))
```

## ImbalancedChen.chenY10PrimeSelector

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
(N : Nat) → (A H : Real) → Finset.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
```

## ImbalancedChen.chenY10PrimeSelector.eq_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (A H : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)))
    (ImbalancedChen.chenY10PrimeSelector N A H)
    (@Finset.filter.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
      (fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
        And
          (@LE.le.{0} Real Real.instLE A
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))))
          (And
            (@LT.lt.{0} Nat instLTNat
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
            (And
              (@LT.lt.{0} Nat instLTNat
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
              (And
                (@LT.lt.{0} Nat instLTNat
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
                  H)))))
      (fun (a : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
        @instDecidableAnd
          (@LE.le.{0} Real Real.instLE A
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
          (And
            (@LT.lt.{0} Nat instLTNat
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (And
              (@LT.lt.{0} Nat instLTNat
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (And
                (@LT.lt.{0} Nat instLTNat
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H))))
          (Real.decidableLE A
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
          (@instDecidableAnd
            (@LT.lt.{0} Nat instLTNat
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (And
              (@LT.lt.{0} Nat instLTNat
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (And
                (@LT.lt.{0} Nat instLTNat
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H)))
            (Nat.decLt (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (@instDecidableAnd
              (@LT.lt.{0} Nat instLTNat
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (And
                (@LT.lt.{0} Nat instLTNat
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H))
              (Nat.decLt (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (@instDecidableAnd
                (@LT.lt.{0} Nat instLTNat
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H)
                (Nat.decLt (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                (Real.decidableLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H)))))
      (@SProd.sprod.{0, 0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Finset.{0} (Prod.{0, 0} Nat Nat))
        (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)))
        (@Finset.instSProd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
        (@SProd.sprod.{0, 0, 0} (Finset.{0} Nat) (Finset.{0} Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
          (@Finset.instSProd.{0, 0} Nat Nat) (ImbalancedChen.chenAdditivePrimeCarrier N)
          (ImbalancedChen.chenAdditivePrimeCarrier N))
        (@SProd.sprod.{0, 0, 0} (Finset.{0} Nat) (Finset.{0} Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
          (@Finset.instSProd.{0, 0} Nat Nat) (ImbalancedChen.chenAdditivePrimeCarrier N)
          (ImbalancedChen.chenAdditivePrimeCarrier N))))
```

## ImbalancedChen.chenY10Tuples_eq_selector_filter

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {N P : Nat}
  (hP :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ImbalancedChen.chenAdditivePrimeCarrier N) P)
  (A H : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)))
    (ImbalancedChen.chenY10Tuples (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P) A H)
    (@Finset.filter.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
      (fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
        ImbalancedChen.ChenQuotient
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
              (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
            (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
          (@Nat.cast.{0} Real Real.instNatCast
            (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P))
      (fun (a : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
        Classical.propDecidable
          (ImbalancedChen.ChenQuotient
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)))
      (ImbalancedChen.chenY10PrimeSelector N A H))
```

## ImbalancedChen.chenY10Tuples_eq_selector_filter._proof_1_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {N P : Nat} (hPN : @LT.lt.{0} Nat instLTNat P N),
  @Eq.{1} Nat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    False
```

## ImbalancedChen.chenY10Tuples_eq_selector_filter._simp_1_3

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : @DecidablePred.{u_1 + 1} α p] {s : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.filter.{u_1} α p inst s) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (p a))
```

## ImbalancedChen.chenY10Tuples_eq_selector_filter._simp_1_4

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} {β : Type u_2} {s : Finset.{u_1} α} {t : Finset.{u_2} β} {p : Prod.{u_1, u_2} α β},
  @Eq.{1} Prop
    (@Membership.mem.{max u_1 u_2, max u_1 u_2} (Prod.{u_1, u_2} α β) (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
      (@SetLike.instMembership.{max u_1 u_2, max u_1 u_2} (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
        (Prod.{u_1, u_2} α β) (@Finset.instSetLike.{max u_1 u_2} (Prod.{u_1, u_2} α β)))
      (@SProd.sprod.{u_1, u_2, max u_1 u_2} (Finset.{u_1} α) (Finset.{u_2} β)
        (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β)) (@Finset.instSProd.{u_1, u_2} α β) s t)
      p)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s
        (@Prod.fst.{u_1, u_2} α β p))
      (@Membership.mem.{u_2, u_2} β (Finset.{u_2} β)
        (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} β) β (@Finset.instSetLike.{u_2} β)) t
        (@Prod.snd.{u_1, u_2} α β p)))
```

## ImbalancedChen.chenY11FullPrimeSelector

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
(N : Nat) → (A H D : Real) → Finset.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
```

## ImbalancedChen.chenY11FullPrimeSelector.eq_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (A H D : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)))
    (ImbalancedChen.chenY11FullPrimeSelector N A H D)
    (@Finset.filter.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
      (fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
        And
          (@LE.le.{0} Real Real.instLE A
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))))
          (And
            (@LT.lt.{0} Nat instLTNat
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
            (And
              (@LT.lt.{0} Nat instLTNat
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
              (And
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
                  H)
                (And
                  (@LE.le.{0} Real Real.instLE H
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))))
                  (@LT.lt.{0} Real Real.instLT
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
                    D))))))
      (fun (a : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
        @instDecidableAnd
          (@LE.le.{0} Real Real.instLE A
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
          (And
            (@LT.lt.{0} Nat instLTNat
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (And
              (@LT.lt.{0} Nat instLTNat
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (And
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H)
                (And
                  (@LE.le.{0} Real Real.instLE H
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
                  (@LT.lt.{0} Real Real.instLT
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                    D)))))
          (Real.decidableLE A
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
          (@instDecidableAnd
            (@LT.lt.{0} Nat instLTNat
              (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (And
              (@LT.lt.{0} Nat instLTNat
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (And
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H)
                (And
                  (@LE.le.{0} Real Real.instLE H
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
                  (@LT.lt.{0} Real Real.instLT
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                    D))))
            (Nat.decLt (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (@instDecidableAnd
              (@LT.lt.{0} Nat instLTNat
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (And
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H)
                (And
                  (@LE.le.{0} Real Real.instLE H
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
                  (@LT.lt.{0} Real Real.instLT
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                    D)))
              (Nat.decLt (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (@instDecidableAnd
                (@LT.lt.{0} Real Real.instLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H)
                (And
                  (@LE.le.{0} Real Real.instLE H
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
                  (@LT.lt.{0} Real Real.instLT
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                    D))
                (Real.decidableLT
                  (@Nat.cast.{0} Real Real.instNatCast
                    (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                  H)
                (@instDecidableAnd
                  (@LE.le.{0} Real Real.instLE H
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
                  (@LT.lt.{0} Real Real.instLT
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                    D)
                  (Real.decidableLE H
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
                  (Real.decidableLT
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                    D))))))
      (@SProd.sprod.{0, 0, 0} (Finset.{0} (Prod.{0, 0} Nat Nat)) (Finset.{0} (Prod.{0, 0} Nat Nat))
        (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)))
        (@Finset.instSProd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
        (@SProd.sprod.{0, 0, 0} (Finset.{0} Nat) (Finset.{0} Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
          (@Finset.instSProd.{0, 0} Nat Nat) (ImbalancedChen.chenAdditivePrimeCarrier N)
          (ImbalancedChen.chenAdditivePrimeCarrier N))
        (@SProd.sprod.{0, 0, 0} (Finset.{0} Nat) (Finset.{0} Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
          (@Finset.instSProd.{0, 0} Nat Nat) (ImbalancedChen.chenAdditivePrimeCarrier N)
          (ImbalancedChen.chenAdditivePrimeCarrier N))))
```

## ImbalancedChen.chenY11FullTuples_eq_selector_filter

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {N P : Nat}
  (hP :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ImbalancedChen.chenAdditivePrimeCarrier N) P)
  (A H D : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)))
    (ImbalancedChen.chenY11FullTuples (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P) A H D)
    (@Finset.filter.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
      (fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
        ImbalancedChen.ChenQuotient
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
                (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
              (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
            (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
          (@Nat.cast.{0} Real Real.instNatCast
            (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P))
      (fun (a : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
        Classical.propDecidable
          (ImbalancedChen.ChenQuotient
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)))
      (ImbalancedChen.chenY11FullPrimeSelector N A H D))
```

## ImbalancedChen.chenY11FullTuples_eq_selector_filter._proof_1_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {N P : Nat} (hPN : @LT.lt.{0} Nat instLTNat P N),
  @Eq.{1} Nat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    False
```

## ImbalancedChen.chenY11FullTuples_eq_selector_filter._simp_1_3

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : @DecidablePred.{u_1 + 1} α p] {s : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.filter.{u_1} α p inst s) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (p a))
```

## ImbalancedChen.chenY11FullTuples_eq_selector_filter._simp_1_4

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} {β : Type u_2} {s : Finset.{u_1} α} {t : Finset.{u_2} β} {p : Prod.{u_1, u_2} α β},
  @Eq.{1} Prop
    (@Membership.mem.{max u_1 u_2, max u_1 u_2} (Prod.{u_1, u_2} α β) (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
      (@SetLike.instMembership.{max u_1 u_2, max u_1 u_2} (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
        (Prod.{u_1, u_2} α β) (@Finset.instSetLike.{max u_1 u_2} (Prod.{u_1, u_2} α β)))
      (@SProd.sprod.{u_1, u_2, max u_1 u_2} (Finset.{u_1} α) (Finset.{u_2} β)
        (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β)) (@Finset.instSProd.{u_1, u_2} α β) s t)
      p)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s
        (@Prod.fst.{u_1, u_2} α β p))
      (@Membership.mem.{u_2, u_2} β (Finset.{u_2} β)
        (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} β) β (@Finset.instSetLike.{u_2} β)) t
        (@Prod.snd.{u_1, u_2} α β p)))
```

## ImbalancedChen.chenY11Selected_add_compl

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (n : Nat) (A H D : Real) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.chenY11Selected n A H D E)
      (ImbalancedChen.chenY11Selected n A H D fun (t : Prod.{0, 0} Nat Nat) => Not (E t)))
    (ImbalancedChen.chenY11Full n A H D)
```

## ImbalancedChen.chenY6Selected_add_compl

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (n : Nat) (A H D : Real) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.chenY6Selected n A H D E)
      (ImbalancedChen.chenY6Selected n A H D fun (t : Prod.{0, 0} Nat Nat) => Not (E t)))
    (ImbalancedChen.chenY6 n A H D)
```

## ImbalancedChen.chenY7PrimeSelector

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
(N : Nat) → (D : Real) → Finset.{0} (Prod.{0, 0} Nat Nat)
```

## ImbalancedChen.chenY7PrimeSelector.eq_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (D : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} Nat Nat)) (ImbalancedChen.chenY7PrimeSelector N D)
    (@Finset.filter.{0} (Prod.{0, 0} Nat Nat)
      (fun (t : Prod.{0, 0} Nat Nat) =>
        And (@LE.le.{0} Real Real.instLE D (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t)))
          (And (@LT.lt.{0} Nat instLTNat (@Prod.fst.{0, 0} Nat Nat t) (@Prod.snd.{0, 0} Nat Nat t))
            (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t))
              (Real.sqrt
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@Nat.cast.{0} Real Real.instNatCast N)
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t)))))))
      (fun (a : Prod.{0, 0} Nat Nat) =>
        @instDecidableAnd
          (@LE.le.{0} Real Real.instLE D (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))
          (And (@LT.lt.{0} Nat instLTNat (@Prod.fst.{0, 0} Nat Nat a) (@Prod.snd.{0, 0} Nat Nat a))
            (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
              (Real.sqrt
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@Nat.cast.{0} Real Real.instNatCast N)
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a))))))
          (Real.decidableLE D (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))
          (@instDecidableAnd (@LT.lt.{0} Nat instLTNat (@Prod.fst.{0, 0} Nat Nat a) (@Prod.snd.{0, 0} Nat Nat a))
            (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
              (Real.sqrt
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@Nat.cast.{0} Real Real.instNatCast N)
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))))
            (Nat.decLt (@Prod.fst.{0, 0} Nat Nat a) (@Prod.snd.{0, 0} Nat Nat a))
            (Real.decidableLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
              (Real.sqrt
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@Nat.cast.{0} Real Real.instNatCast N)
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))))))
      (@SProd.sprod.{0, 0, 0} (Finset.{0} Nat) (Finset.{0} Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
        (@Finset.instSProd.{0, 0} Nat Nat) (ImbalancedChen.chenAdditivePrimeCarrier N)
        (ImbalancedChen.chenAdditivePrimeCarrier N)))
```

## ImbalancedChen.chenY7Tuples_eq_selector_filter

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {N P : Nat}
  (hP :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ImbalancedChen.chenAdditivePrimeCarrier N) P)
  (D : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} Nat Nat))
    (ImbalancedChen.chenY7Tuples (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
      (@Nat.cast.{0} Real Real.instNatCast N) D)
    (@Finset.filter.{0} (Prod.{0, 0} Nat Nat)
      (fun (t : Prod.{0, 0} Nat Nat) =>
        ImbalancedChen.ChenQuotient
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
            (@Prod.snd.{0, 0} Nat Nat t))
          (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P))
      (fun (a : Prod.{0, 0} Nat Nat) =>
        Classical.propDecidable
          (ImbalancedChen.ChenQuotient
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat a)
              (@Prod.snd.{0, 0} Nat Nat a))
            (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)))
      (ImbalancedChen.chenY7PrimeSelector N D))
```

## ImbalancedChen.chenY7Tuples_eq_selector_filter._proof_1_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {N P : Nat} (hPN : @LT.lt.{0} Nat instLTNat P N),
  @Eq.{1} Nat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    False
```

## ImbalancedChen.chenY7Tuples_eq_selector_filter._simp_1_3

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : @DecidablePred.{u_1 + 1} α p] {s : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.filter.{u_1} α p inst s) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (p a))
```

## ImbalancedChen.chenY7Tuples_eq_selector_filter._simp_1_4

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} {β : Type u_2} {s : Finset.{u_1} α} {t : Finset.{u_2} β} {p : Prod.{u_1, u_2} α β},
  @Eq.{1} Prop
    (@Membership.mem.{max u_1 u_2, max u_1 u_2} (Prod.{u_1, u_2} α β) (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
      (@SetLike.instMembership.{max u_1 u_2, max u_1 u_2} (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
        (Prod.{u_1, u_2} α β) (@Finset.instSetLike.{max u_1 u_2} (Prod.{u_1, u_2} α β)))
      (@SProd.sprod.{u_1, u_2, max u_1 u_2} (Finset.{u_1} α) (Finset.{u_2} β)
        (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β)) (@Finset.instSProd.{u_1, u_2} α β) s t)
      p)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s
        (@Prod.fst.{u_1, u_2} α β p))
      (@Membership.mem.{u_2, u_2} β (Finset.{u_2} β)
        (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} β) β (@Finset.instSetLike.{u_2} β)) t
        (@Prod.snd.{u_1, u_2} α β p)))
```

## ImbalancedChen.chenY8PrimeSelector

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
(N : Nat) → (A C : Real) → Finset.{0} (Prod.{0, 0} Nat Nat)
```

## ImbalancedChen.chenY8PrimeSelector.eq_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (A C : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} Nat Nat)) (ImbalancedChen.chenY8PrimeSelector N A C)
    (@Finset.filter.{0} (Prod.{0, 0} Nat Nat)
      (fun (t : Prod.{0, 0} Nat Nat) =>
        And (@LE.le.{0} Real Real.instLE A (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t)))
          (And (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t)) C)
            (And (@LE.le.{0} Real Real.instLE C (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t)))
              (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t))))))))
      (fun (a : Prod.{0, 0} Nat Nat) =>
        @instDecidableAnd
          (@LE.le.{0} Real Real.instLE A (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))
          (And (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)) C)
            (And (@LE.le.{0} Real Real.instLE C (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a)))
              (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))))))
          (Real.decidableLE A (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))
          (@instDecidableAnd
            (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)) C)
            (And (@LE.le.{0} Real Real.instLE C (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a)))
              (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a))))))
            (Real.decidableLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)) C)
            (@instDecidableAnd
              (@LE.le.{0} Real Real.instLE C (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a)))
              (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))))
              (Real.decidableLE C (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a)))
              (Real.decidableLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a))))))))
      (@SProd.sprod.{0, 0, 0} (Finset.{0} Nat) (Finset.{0} Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
        (@Finset.instSProd.{0, 0} Nat Nat) (ImbalancedChen.chenAdditivePrimeCarrier N)
        (ImbalancedChen.chenAdditivePrimeCarrier N)))
```

## ImbalancedChen.chenY8Tuples_eq_selector_filter

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {N P : Nat}
  (hP :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ImbalancedChen.chenAdditivePrimeCarrier N) P)
  (A C : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} Nat Nat))
    (ImbalancedChen.chenY8Tuples (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
      (@Nat.cast.{0} Real Real.instNatCast N) A C)
    (@Finset.filter.{0} (Prod.{0, 0} Nat Nat)
      (fun (t : Prod.{0, 0} Nat Nat) =>
        ImbalancedChen.ChenQuotient
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
            (@Prod.snd.{0, 0} Nat Nat t))
          (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P))
      (fun (a : Prod.{0, 0} Nat Nat) =>
        Classical.propDecidable
          (ImbalancedChen.ChenQuotient
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat a)
              (@Prod.snd.{0, 0} Nat Nat a))
            (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)))
      (ImbalancedChen.chenY8PrimeSelector N A C))
```

## ImbalancedChen.chenY8Tuples_eq_selector_filter._proof_1_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {N P : Nat} (hPN : @LT.lt.{0} Nat instLTNat P N),
  @Eq.{1} Nat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    False
```

## ImbalancedChen.chenY8Tuples_eq_selector_filter._simp_1_3

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : @DecidablePred.{u_1 + 1} α p] {s : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.filter.{u_1} α p inst s) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (p a))
```

## ImbalancedChen.chenY8Tuples_eq_selector_filter._simp_1_4

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} {β : Type u_2} {s : Finset.{u_1} α} {t : Finset.{u_2} β} {p : Prod.{u_1, u_2} α β},
  @Eq.{1} Prop
    (@Membership.mem.{max u_1 u_2, max u_1 u_2} (Prod.{u_1, u_2} α β) (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
      (@SetLike.instMembership.{max u_1 u_2, max u_1 u_2} (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
        (Prod.{u_1, u_2} α β) (@Finset.instSetLike.{max u_1 u_2} (Prod.{u_1, u_2} α β)))
      (@SProd.sprod.{u_1, u_2, max u_1 u_2} (Finset.{u_1} α) (Finset.{u_2} β)
        (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β)) (@Finset.instSProd.{u_1, u_2} α β) s t)
      p)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s
        (@Prod.fst.{u_1, u_2} α β p))
      (@Membership.mem.{u_2, u_2} β (Finset.{u_2} β)
        (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} β) β (@Finset.instSetLike.{u_2} β)) t
        (@Prod.snd.{u_1, u_2} α β p)))
```

## ImbalancedChen.chenY9PrimeSelector

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
(N : Nat) → (H D : Real) → Finset.{0} (Prod.{0, 0} Nat Nat)
```

## ImbalancedChen.chenY9PrimeSelector.eq_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (H D : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} Nat Nat)) (ImbalancedChen.chenY9PrimeSelector N H D)
    (@Finset.filter.{0} (Prod.{0, 0} Nat Nat)
      (fun (t : Prod.{0, 0} Nat Nat) =>
        And (@LE.le.{0} Real Real.instLE H (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t)))
          (And (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t)) D)
            (And (@LE.le.{0} Real Real.instLE D (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t)))
              (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t))))))))
      (fun (a : Prod.{0, 0} Nat Nat) =>
        @instDecidableAnd
          (@LE.le.{0} Real Real.instLE H (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))
          (And (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)) D)
            (And (@LE.le.{0} Real Real.instLE D (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a)))
              (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))))))
          (Real.decidableLE H (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))
          (@instDecidableAnd
            (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)) D)
            (And (@LE.le.{0} Real Real.instLE D (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a)))
              (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a))))))
            (Real.decidableLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)) D)
            (@instDecidableAnd
              (@LE.le.{0} Real Real.instLE D (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a)))
              (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a)))))
              (Real.decidableLE D (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a)))
              (Real.decidableLT (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a))
                (Real.sqrt
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Nat.cast.{0} Real Real.instNatCast N)
                    (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a))))))))
      (@SProd.sprod.{0, 0, 0} (Finset.{0} Nat) (Finset.{0} Nat) (Finset.{0} (Prod.{0, 0} Nat Nat))
        (@Finset.instSProd.{0, 0} Nat Nat) (ImbalancedChen.chenAdditivePrimeCarrier N)
        (ImbalancedChen.chenAdditivePrimeCarrier N)))
```

## ImbalancedChen.chenY9Tuples_eq_selector_filter

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {N P : Nat}
  (hP :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ImbalancedChen.chenAdditivePrimeCarrier N) P)
  (H D : Real),
  @Eq.{1} (Finset.{0} (Prod.{0, 0} Nat Nat))
    (ImbalancedChen.chenY9Tuples (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
      (@Nat.cast.{0} Real Real.instNatCast N) H D)
    (@Finset.filter.{0} (Prod.{0, 0} Nat Nat)
      (fun (t : Prod.{0, 0} Nat Nat) =>
        ImbalancedChen.ChenQuotient
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
            (@Prod.snd.{0, 0} Nat Nat t))
          (Real.sqrt
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@Nat.cast.{0} Real Real.instNatCast N)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t))
                (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t)))))
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P))
      (fun (a : Prod.{0, 0} Nat Nat) =>
        Classical.propDecidable
          (ImbalancedChen.ChenQuotient
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat a)
              (@Prod.snd.{0, 0} Nat Nat a))
            (Real.sqrt
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@Nat.cast.{0} Real Real.instNatCast N)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat a))
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat a)))))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)))
      (ImbalancedChen.chenY9PrimeSelector N H D))
```

## ImbalancedChen.chenY9Tuples_eq_selector_filter._proof_1_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {N P : Nat} (hPN : @LT.lt.{0} Nat instLTNat P N),
  @Eq.{1} Nat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    False
```

## ImbalancedChen.chenY9Tuples_eq_selector_filter._simp_1_3

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : @DecidablePred.{u_1 + 1} α p] {s : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.filter.{u_1} α p inst s) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (p a))
```

## ImbalancedChen.chenY9Tuples_eq_selector_filter._simp_1_4

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} {β : Type u_2} {s : Finset.{u_1} α} {t : Finset.{u_2} β} {p : Prod.{u_1, u_2} α β},
  @Eq.{1} Prop
    (@Membership.mem.{max u_1 u_2, max u_1 u_2} (Prod.{u_1, u_2} α β) (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
      (@SetLike.instMembership.{max u_1 u_2, max u_1 u_2} (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β))
        (Prod.{u_1, u_2} α β) (@Finset.instSetLike.{max u_1 u_2} (Prod.{u_1, u_2} α β)))
      (@SProd.sprod.{u_1, u_2, max u_1 u_2} (Finset.{u_1} α) (Finset.{u_2} β)
        (Finset.{max u_2 u_1} (Prod.{u_1, u_2} α β)) (@Finset.instSProd.{u_1, u_2} α β) s t)
      p)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s
        (@Prod.fst.{u_1, u_2} α β p))
      (@Membership.mem.{u_2, u_2} β (Finset.{u_2} β)
        (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} β) β (@Finset.instSetLike.{u_2} β)) t
        (@Prod.snd.{u_1, u_2} α β p)))
```

## ImbalancedChen.chen_prime_dvd_receiver_mem_additiveCarrier

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {N P p : Nat}
  (hP :
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (ImbalancedChen.chenAdditivePrimeCarrier N) P)
  (hp : Nat.Prime p)
  (hd : @Dvd.dvd.{0} Nat Nat.instDvd p (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)),
  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
    (ImbalancedChen.chenAdditivePrimeCarrier N) p
```

## ImbalancedChen.chen_prime_dvd_receiver_mem_additiveCarrier._proof_1_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {N P p : Nat} (hPN : @LT.lt.{0} Nat instLTNat P N),
  Not
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)) →
    False
```

## ImbalancedChen.chen_prime_dvd_receiver_mem_additiveCarrier._proof_1_2

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {N P p : Nat} (hPN : @LT.lt.{0} Nat instLTNat P N)
  (hle : @LE.le.{0} Nat instLENat p (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P))
  (hPpos : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) P),
  Not (@LT.lt.{0} Nat instLTNat p N) → False
```

## ImbalancedChen.chen_sum_quotient_tuple_card_moving_cutoff

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} [DecidableEq.{u_1 + 1} α] (N : Nat) (T : Finset.{u_1} α) (b : α → Nat) (z : α → Real),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{u_1} α
          (@Finset.filter.{u_1} α
            (fun (t : α) =>
              ImbalancedChen.ChenQuotient (b t) (z t)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P))
            (fun (a : α) =>
              Classical.propDecidable
                (ImbalancedChen.ChenQuotient (b a) (z a)
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)))
            T)))
    (@Finset.sum.{u_1, 0} α Real Real.instAddCommMonoid T fun (t : α) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat (ImbalancedChen.chenSiftedQuotientPrimeSource N (b t) (z t))))
```

## ImbalancedChen.currentChenPairedPrimeSum.eq_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Real (ImbalancedChen.currentChenPairedPrimeSum N E)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      ImbalancedChen.currentChenPairedWeight (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
        (@Nat.cast.{0} Real Real.instNatCast N) E)
```

## ImbalancedChen.currentChenPairedPrimeSum_eq_upsilon

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Real (ImbalancedChen.currentChenPairedPrimeSum N E)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 3)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                          (ImbalancedChen.currentChenUpsilon1 N))
                        (ImbalancedChen.currentChenUpsilon2 N))
                      (ImbalancedChen.currentChenUpsilon3 N))
                    (ImbalancedChen.currentChenUpsilon4 N))
                  (ImbalancedChen.currentChenUpsilon5 N))
                (ImbalancedChen.currentChenUpsilon6 N E))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (ImbalancedChen.currentChenUpsilon7 N)))
            (ImbalancedChen.currentChenUpsilon8 N))
          (ImbalancedChen.currentChenUpsilon9 N))
        (ImbalancedChen.currentChenUpsilon10 N))
      (ImbalancedChen.currentChenUpsilon11 N E))
```

## ImbalancedChen.currentChenPairedPrimeSum_ge_of_joint_last_bounds

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop) (l₁ l₂ u₃ u₄ l₅ l₆ u₇ u₈ u₉ u₁₀₁₁ : Real)
  (h₁ : @LE.le.{0} Real Real.instLE l₁ (ImbalancedChen.currentChenUpsilon1 N))
  (h₂ : @LE.le.{0} Real Real.instLE l₂ (ImbalancedChen.currentChenUpsilon2 N))
  (h₃ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon3 N) u₃)
  (h₄ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon4 N) u₄)
  (h₅ : @LE.le.{0} Real Real.instLE l₅ (ImbalancedChen.currentChenUpsilon5 N))
  (h₆ : @LE.le.{0} Real Real.instLE l₆ (ImbalancedChen.currentChenUpsilon6 N E))
  (h₇ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon7 N) u₇)
  (h₈ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon8 N) u₈)
  (h₉ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon9 N) u₉)
  (h₁₀₁₁ :
    @LE.le.{0} Real Real.instLE
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (ImbalancedChen.currentChenUpsilon10 N)
        (ImbalancedChen.currentChenUpsilon11 N E))
      u₁₀₁₁),
  @LE.le.{0} Real Real.instLE
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real (nat_lit 3)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                        l₁)
                      l₂)
                    u₃)
                  u₄)
                l₅)
              l₆)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              u₇))
          u₈)
        u₉)
      u₁₀₁₁)
    (ImbalancedChen.currentChenPairedPrimeSum N E)
```

## ImbalancedChen.currentChenPairedPrimeSum_ge_of_normalized_joint_last_bounds

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop) (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀₁₁ delta : Real)
  (h₁ :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) b₁ delta)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenUpsilon1 N))
  (h₂ :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) b₂ delta)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenUpsilon2 N))
  (h₃ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon3 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₃ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₄ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon4 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₄ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₅ :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) b₅ delta)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenUpsilon5 N))
  (h₆ :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) b₆ delta)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenUpsilon6 N E))
  (h₇ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon7 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₇ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₈ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon8 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₈ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₉ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon9 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₉ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₁₀₁₁ :
    @LE.le.{0} Real Real.instLE
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (ImbalancedChen.currentChenUpsilon10 N)
        (ImbalancedChen.currentChenUpsilon11 N E))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₁₀₁₁
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            delta))
        (ImbalancedChen.singularNormalization N))),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 3)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                            b₁)
                          b₂)
                        b₃)
                      b₄)
                    b₅)
                  b₆)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  b₇))
              b₈)
            b₉)
          b₁₀₁₁)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 14)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 14) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))))
          delta))
      (ImbalancedChen.singularNormalization N))
    (ImbalancedChen.currentChenPairedPrimeSum N E)
```

## ImbalancedChen.currentChenPairedPrimeSum_ge_of_normalized_term_bounds

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop) (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ delta : Real)
  (h₁ :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) b₁ delta)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenUpsilon1 N))
  (h₂ :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) b₂ delta)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenUpsilon2 N))
  (h₃ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon3 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₃ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₄ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon4 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₄ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₅ :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) b₅ delta)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenUpsilon5 N))
  (h₆ :
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) b₆ delta)
        (ImbalancedChen.singularNormalization N))
      (ImbalancedChen.currentChenUpsilon6 N E))
  (h₇ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon7 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₇ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₈ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon8 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₈ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₉ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon9 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₉ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₁₀ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon10 N)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₁₀ delta)
        (ImbalancedChen.singularNormalization N)))
  (h₁₁ :
    @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon11 N E)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) b₁₁ delta)
        (ImbalancedChen.singularNormalization N))),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@OfNat.ofNat.{0} Real (nat_lit 3)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                              b₁)
                            b₂)
                          b₃)
                        b₄)
                      b₅)
                    b₆)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    b₇))
                b₈)
              b₉)
            b₁₀)
          b₁₁)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 14)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 14) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))))
          delta))
      (ImbalancedChen.singularNormalization N))
    (ImbalancedChen.currentChenPairedPrimeSum N E)
```

## ImbalancedChen.currentChenPairedPrimeSum_ge_of_term_bounds

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop) (l₁ l₂ u₃ u₄ l₅ l₆ u₇ u₈ u₉ u₁₀ u₁₁ : Real)
  (h₁ : @LE.le.{0} Real Real.instLE l₁ (ImbalancedChen.currentChenUpsilon1 N))
  (h₂ : @LE.le.{0} Real Real.instLE l₂ (ImbalancedChen.currentChenUpsilon2 N))
  (h₃ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon3 N) u₃)
  (h₄ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon4 N) u₄)
  (h₅ : @LE.le.{0} Real Real.instLE l₅ (ImbalancedChen.currentChenUpsilon5 N))
  (h₆ : @LE.le.{0} Real Real.instLE l₆ (ImbalancedChen.currentChenUpsilon6 N E))
  (h₇ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon7 N) u₇)
  (h₈ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon8 N) u₈)
  (h₉ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon9 N) u₉)
  (h₁₀ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon10 N) u₁₀)
  (h₁₁ : @LE.le.{0} Real Real.instLE (ImbalancedChen.currentChenUpsilon11 N E) u₁₁),
  @LE.le.{0} Real Real.instLE
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 3)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                          l₁)
                        l₂)
                      u₃)
                    u₄)
                  l₅)
                l₆)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                u₇))
            u₈)
          u₉)
        u₁₀)
      u₁₁)
    (ImbalancedChen.currentChenPairedPrimeSum N E)
```

## ImbalancedChen.currentChenUpsilon1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
(N : Nat) → Real
```

## ImbalancedChen.currentChenUpsilon1._proof_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.currentChenUpsilon1._proof_2

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.currentChenUpsilon1.eq_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon1 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY1 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_2))))))
```

## ImbalancedChen.currentChenUpsilon10

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
(N : Nat) → Real
```

## ImbalancedChen.currentChenUpsilon10.eq_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon10 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY10 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_2))))))
```

## ImbalancedChen.currentChenUpsilon10_eq_siftedQuotientPrimeSource

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon10 N)
    (@Finset.sum.{0, 0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) Real Real.instAddCommMonoid
      (ImbalancedChen.chenY10PrimeSelector N
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 417)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 5000)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998)))))))))
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 19)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 125)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 123) (instOfNatNat (nat_lit 123))))))))))
      fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))))))
```

## ImbalancedChen.currentChenUpsilon11

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
(N : Nat) → (E : Prod.{0, 0} Nat Nat → Prop) → Real
```

## ImbalancedChen.currentChenUpsilon11.eq_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon11 N E)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY11Selected (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 59)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 250)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_2))))
          fun (t : Prod.{0, 0} Nat Nat) => Not (E t)))
```

## ImbalancedChen.currentChenUpsilon11_eq_siftedQuotientPrimeSource

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon11 N E)
    (@Finset.sum.{0, 0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) Real Real.instAddCommMonoid
      (@Finset.filter.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
        (fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
          Not (E (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
        (fun (a : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
          @instDecidableNot (E (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))
            (Classical.propDecidable (E (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a))))
        (ImbalancedChen.chenY11FullPrimeSelector N
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998)))))))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 123) (instOfNatNat (nat_lit 123)))))))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 59)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 57) (instOfNatNat (nat_lit 57)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 250)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 249) (instOfNatNat (nat_lit 249)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248)))))))))))
      fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))))))
```

## ImbalancedChen.currentChenUpsilon1_eq_actual_siftedSum

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (hN : @Even.{0} Nat instAddNat N),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon1 N)
    (@BoundingSieve.siftedSum
      (ImbalancedChen.chenInitialBoundingSieve N
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 417)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 5000)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998)))))))))
        hN))
```

## ImbalancedChen.currentChenUpsilon1_eq_actual_sifted_card

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (hN : @Even.{0} Nat instAddNat N),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon1 N)
    (@Nat.cast.{0} Real Real.instNatCast
      (@Finset.card.{0} Nat
        (ImbalancedChen.chenSiftedPrimeSource N
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998))))))))))))
```

## ImbalancedChen.currentChenUpsilon2

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
(N : Nat) → Real
```

## ImbalancedChen.currentChenUpsilon2._proof_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.currentChenUpsilon2._proof_2

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.currentChenUpsilon2.eq_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon2 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY2 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_2))))))
```

## ImbalancedChen.currentChenUpsilon2_eq_actual_siftedSum

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (hN : @Even.{0} Nat instAddNat N),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon2 N)
    (@BoundingSieve.siftedSum
      (ImbalancedChen.chenInitialBoundingSieve N
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 19)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 125)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 123) (instOfNatNat (nat_lit 123)))))))))
        hN))
```

## ImbalancedChen.currentChenUpsilon2_eq_actual_sifted_card

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (hN : @Even.{0} Nat instAddNat N),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon2 N)
    (@Nat.cast.{0} Real Real.instNatCast
      (@Finset.card.{0} Nat
        (ImbalancedChen.chenSiftedPrimeSource N
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 123) (instOfNatNat (nat_lit 123))))))))))))
```

## ImbalancedChen.currentChenUpsilon3

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
(N : Nat) → Real
```

## ImbalancedChen.currentChenUpsilon3._proof_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.currentChenUpsilon3.eq_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon3 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY3 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 3)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon3._proof_1))))))
```

## ImbalancedChen.currentChenUpsilon3_eq_siftedQuotientPrimeSource

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon3 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
      (ImbalancedChen.chenSinglePrimeSelector N
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 417)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 5000)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998)))))))))
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
      fun (p : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N p
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (@Nat.cast.{0} Real Real.instNatCast N)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 417)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
                (@OfNat.ofNat.{0} Real (nat_lit 5000)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998))))))))))))
```

## ImbalancedChen.currentChenUpsilon4

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
(N : Nat) → Real
```

## ImbalancedChen.currentChenUpsilon4._proof_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.currentChenUpsilon4._proof_2

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 249) (instOfNatNat (nat_lit 249)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.currentChenUpsilon4.eq_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon4 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY4 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 59)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 250)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_2))))))
```

## ImbalancedChen.currentChenUpsilon4_eq_siftedQuotientPrimeSource

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon4 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid
      (ImbalancedChen.chenSinglePrimeSelector N
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 417)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 5000)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998)))))))))
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 59)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 57) (instOfNatNat (nat_lit 57)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 250)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 249) (instOfNatNat (nat_lit 249)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))))))))))
      fun (p : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N p
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (@Nat.cast.{0} Real Real.instNatCast N)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 417)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
                (@OfNat.ofNat.{0} Real (nat_lit 5000)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998))))))))))))
```

## ImbalancedChen.currentChenUpsilon5

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
(N : Nat) → Real
```

## ImbalancedChen.currentChenUpsilon5.eq_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon5 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY5 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_2))))))
```

## ImbalancedChen.currentChenUpsilon5_eq_siftedQuotientPrimeSource

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon5 N)
    (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Real Real.instAddCommMonoid
      (ImbalancedChen.chenY5PrimeSelector N
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 417)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 5000)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998)))))))))
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 19)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 125)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 123) (instOfNatNat (nat_lit 123))))))))))
      fun (t : Prod.{0, 0} Nat Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
              (@Prod.snd.{0, 0} Nat Nat t))
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (@Nat.cast.{0} Real Real.instNatCast N)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 417)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
                (@OfNat.ofNat.{0} Real (nat_lit 5000)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998))))))))))))
```

## ImbalancedChen.currentChenUpsilon6

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
(N : Nat) → (E : Prod.{0, 0} Nat Nat → Prop) → Real
```

## ImbalancedChen.currentChenUpsilon6.eq_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon6 N E)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY6Selected (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 59)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 250)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_2))))
          fun (t : Prod.{0, 0} Nat Nat) => Not (E t)))
```

## ImbalancedChen.currentChenUpsilon6_eq_siftedQuotientPrimeSource

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon6 N E)
    (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Real Real.instAddCommMonoid
      (@Finset.filter.{0} (Prod.{0, 0} Nat Nat) (fun (t : Prod.{0, 0} Nat Nat) => Not (E t))
        (fun (a : Prod.{0, 0} Nat Nat) => @instDecidableNot (E a) (Classical.propDecidable (E a)))
        (ImbalancedChen.chenY6PrimeSelector N
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998)))))))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 123) (instOfNatNat (nat_lit 123)))))))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 59)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 57) (instOfNatNat (nat_lit 57)))))))
              (@OfNat.ofNat.{0} Real (nat_lit 250)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 249) (instOfNatNat (nat_lit 249)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248)))))))))))
      fun (t : Prod.{0, 0} Nat Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
              (@Prod.snd.{0, 0} Nat Nat t))
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (@Nat.cast.{0} Real Real.instNatCast N)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 417)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
                (@OfNat.ofNat.{0} Real (nat_lit 5000)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998))))))))))))
```

## ImbalancedChen.currentChenUpsilon7

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
(N : Nat) → Real
```

## ImbalancedChen.currentChenUpsilon7.eq_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon7 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY7 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 59)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 250)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_2))))))
```

## ImbalancedChen.currentChenUpsilon7_eq_siftedQuotientPrimeSource

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon7 N)
    (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Real Real.instAddCommMonoid
      (ImbalancedChen.chenY7PrimeSelector N
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 59)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 57) (instOfNatNat (nat_lit 57)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 250)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 249) (instOfNatNat (nat_lit 249)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))))))))))
      fun (t : Prod.{0, 0} Nat Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
              (@Prod.snd.{0, 0} Nat Nat t))
            (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t)))))
```

## ImbalancedChen.currentChenUpsilon8

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
(N : Nat) → Real
```

## ImbalancedChen.currentChenUpsilon8.eq_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon8 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY8 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 417)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 5000)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon1._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 3)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon3._proof_1))))))
```

## ImbalancedChen.currentChenUpsilon8_eq_siftedQuotientPrimeSource

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon8 N)
    (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Real Real.instAddCommMonoid
      (ImbalancedChen.chenY8PrimeSelector N
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 417)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 417) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 415) (instOfNatNat (nat_lit 415)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 5000)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 5000) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4999) (instOfNatNat (nat_lit 4999)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4998) (instOfNatNat (nat_lit 4998)))))))))
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
      fun (t : Prod.{0, 0} Nat Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
              (@Prod.snd.{0, 0} Nat Nat t))
            (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t)))))
```

## ImbalancedChen.currentChenUpsilon9

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
(N : Nat) → Real
```

## ImbalancedChen.currentChenUpsilon9.eq_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon9 N)
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY9 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 19)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 125)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon2._proof_2))))
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 59)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_1))
              (@OfNat.ofNat.{0} Real (nat_lit 250)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                  ImbalancedChen.currentChenUpsilon4._proof_2))))))
```

## ImbalancedChen.currentChenUpsilon9_eq_siftedQuotientPrimeSource

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat),
  @Eq.{1} Real (ImbalancedChen.currentChenUpsilon9 N)
    (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Real Real.instAddCommMonoid
      (ImbalancedChen.chenY9PrimeSelector N
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 19)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 19) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 125)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 125) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 123) (instOfNatNat (nat_lit 123)))))))))
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
          (@Nat.cast.{0} Real Real.instNatCast N)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 59)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 59) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 57) (instOfNatNat (nat_lit 57)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 250)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 250) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 249) (instOfNatNat (nat_lit 249)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 248) (instOfNatNat (nat_lit 248))))))))))
      fun (t : Prod.{0, 0} Nat Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
              (@Prod.snd.{0, 0} Nat Nat t))
            (Real.sqrt
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@Nat.cast.{0} Real Real.instNatCast N)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t))
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t))))))))
```

## ImbalancedChen.sum_chenY10_eq_siftedQuotientPrimeSource

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (A H : Real),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY10 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P) A H))
    (@Finset.sum.{0, 0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) Real Real.instAddCommMonoid
      (ImbalancedChen.chenY10PrimeSelector N A H) fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))))))
```

## ImbalancedChen.sum_chenY11Selected_eq_siftedQuotientPrimeSource

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (A H D : Real) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY11Selected (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P) A H D E))
    (@Finset.sum.{0, 0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) Real Real.instAddCommMonoid
      (@Finset.filter.{0} (Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat))
        (fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
          E (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
        (fun (a : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
          Classical.propDecidable (E (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) a)))
        (ImbalancedChen.chenY11FullPrimeSelector N A H D))
      fun (t : Prod.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat)) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@Prod.fst.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))
                  (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
                (@Prod.fst.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
              (@Prod.snd.{0, 0} Nat Nat (@Prod.snd.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t)))
            (@Nat.cast.{0} Real Real.instNatCast
              (@Prod.snd.{0, 0} Nat Nat (@Prod.fst.{0, 0} (Prod.{0, 0} Nat Nat) (Prod.{0, 0} Nat Nat) t))))))
```

## ImbalancedChen.sum_chenY11Selected_eq_siftedQuotientPrimeSource._simp_1_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {a b : Prop}, @Eq.{1} Prop (And a b) (And b a)
```

## ImbalancedChen.sum_chenY6Selected_eq_siftedQuotientPrimeSource

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (A H D : Real) (E : Prod.{0, 0} Nat Nat → Prop),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY6Selected (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P) A H D E))
    (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Real Real.instAddCommMonoid
      (@Finset.filter.{0} (Prod.{0, 0} Nat Nat) E (fun (a : Prod.{0, 0} Nat Nat) => Classical.propDecidable (E a))
        (ImbalancedChen.chenY6PrimeSelector N A H D))
      fun (t : Prod.{0, 0} Nat Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
              (@Prod.snd.{0, 0} Nat Nat t))
            A)))
```

## ImbalancedChen.sum_chenY6Selected_eq_siftedQuotientPrimeSource._simp_1_1

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {a b : Prop}, @Eq.{1} Prop (And a b) (And b a)
```

## ImbalancedChen.sum_chenY7_eq_siftedQuotientPrimeSource

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (D : Real),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY7 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@Nat.cast.{0} Real Real.instNatCast N) D))
    (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Real Real.instAddCommMonoid (ImbalancedChen.chenY7PrimeSelector N D)
      fun (t : Prod.{0, 0} Nat Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
              (@Prod.snd.{0, 0} Nat Nat t))
            (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t)))))
```

## ImbalancedChen.sum_chenY8_eq_siftedQuotientPrimeSource

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (A C : Real),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY8 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@Nat.cast.{0} Real Real.instNatCast N) A C))
    (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Real Real.instAddCommMonoid (ImbalancedChen.chenY8PrimeSelector N A C)
      fun (t : Prod.{0, 0} Nat Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
              (@Prod.snd.{0, 0} Nat Nat t))
            (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t)))))
```

## ImbalancedChen.sum_chenY9_eq_siftedQuotientPrimeSource

模块 `ImbalancedChen.CurrentChenMeanLedger`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Nat) (H D : Real),
  @Eq.{1} Real
    (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid (ImbalancedChen.chenAdditivePrimeCarrier N) fun (P : Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (ImbalancedChen.chenY9 (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) N P)
          (@Nat.cast.{0} Real Real.instNatCast N) H D))
    (@Finset.sum.{0, 0} (Prod.{0, 0} Nat Nat) Real Real.instAddCommMonoid (ImbalancedChen.chenY9PrimeSelector N H D)
      fun (t : Prod.{0, 0} Nat Nat) =>
      @Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{0} Nat
          (ImbalancedChen.chenSiftedQuotientPrimeSource N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@Prod.fst.{0, 0} Nat Nat t)
              (@Prod.snd.{0, 0} Nat Nat t))
            (Real.sqrt
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@Nat.cast.{0} Real Real.instNatCast N)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.fst.{0, 0} Nat Nat t))
                  (@Nat.cast.{0} Real Real.instNatCast (@Prod.snd.{0, 0} Nat Nat t))))))))
```

## ImbalancedChen.Certificates.PairedV2.first_fibre_buchstab_eleven_twentieths

模块 `ImbalancedChen.CurrentPairedBuchstabBridge`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {t u z w : Real} (hs : ImbalancedChen.Certificates.PairedV2.firstFibreSupport t u z w),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 11)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 11) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))))
      (@OfNat.ofNat.{0} Real (nat_lit 20)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))))))
    (LiLiuPrereqBuchstab.buchstab
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) t)
              u)
            z)
          w)
        z))
```

## ImbalancedChen.Certificates.PairedV2.first_fibre_buchstab_gain

模块 `ImbalancedChen.CurrentPairedBuchstabBridge`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {t u z w : Real} (hs : ImbalancedChen.Certificates.PairedV2.firstFibreSupport t u z w),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@OfNat.ofNat.{0} Real (nat_lit 20)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))))))
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (LiLiuPrereqBuchstab.buchstab
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) t)
                u)
              z)
            w)
          z))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
```

## ImbalancedChen.HistoricalPrefixCapData

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
Type
```

## ImbalancedChen.HistoricalPrefixCapData._sizeOf_1

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(t : ImbalancedChen.HistoricalPrefixCapData) → Nat
```

## ImbalancedChen.HistoricalPrefixCapData._sizeOf_inst

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
SizeOf.{1} ImbalancedChen.HistoricalPrefixCapData
```

## ImbalancedChen.HistoricalPrefixCapData.a

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.HistoricalPrefixCapData) → Rat
```

## ImbalancedChen.HistoricalPrefixCapData.actual_thirdToFifthSaving_eq

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData)
  (hab :
    @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D))
  (hcheck : @Eq.{1} Bool (ImbalancedChen.HistoricalPrefixCapData.levelCheck D) Bool.true)
  (base : Bool → List.{0} Nat → Bool) (N cap : Nat)
  (hN :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@Nat.cast.{0} Real Real.instNatCast N))
  (z : Real),
  @Eq.{1} Real
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@ImbalancedChen.firstExitRetainedPolynomial.{0} Nat
        (ImbalancedChen.thirdCappedUpperPolicy base
          (ImbalancedChen.HistoricalPrefixCapData.level3 D (@Nat.cast.{0} Real Real.instNatCast N)))
        (fun (p : Nat) =>
          @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@Nat.cast.{0} Real Real.instNatCast p)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
        (@List.nil.{0} Nat) Bool.true (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (ImbalancedChen.roughPrimeUniverse N cap
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z))
      (@ImbalancedChen.firstExitRetainedPolynomial.{0} Nat
        (ImbalancedChen.fifthCappedUpperPolicy base
          (ImbalancedChen.HistoricalPrefixCapData.level3 D (@Nat.cast.{0} Real Real.instNatCast N))
          (ImbalancedChen.HistoricalPrefixCapData.level5 D (@Nat.cast.{0} Real Real.instNatCast N)))
        (fun (p : Nat) =>
          @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@Nat.cast.{0} Real Real.instNatCast p)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
        (@List.nil.{0} Nat) Bool.true (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (ImbalancedChen.roughPrimeUniverse N cap
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z)))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (ImbalancedChen.actualHistoricalFourthSaving base
        (ImbalancedChen.HistoricalPrefixCapData.level3 D (@Nat.cast.{0} Real Real.instNatCast N))
        (ImbalancedChen.HistoricalPrefixCapData.level4 D (@Nat.cast.{0} Real Real.instNatCast N)) N cap z)
      (ImbalancedChen.actualHistoricalFifthSaving base
        (ImbalancedChen.HistoricalPrefixCapData.level3 D (@Nat.cast.{0} Real Real.instNatCast N))
        (ImbalancedChen.HistoricalPrefixCapData.level4 D (@Nat.cast.{0} Real Real.instNatCast N))
        (ImbalancedChen.HistoricalPrefixCapData.level5 D (@Nat.cast.{0} Real Real.instNatCast N)) N cap z))
```

## ImbalancedChen.HistoricalPrefixCapData.actual_thirdToFifthSaving_eq._proof_1_1

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (frontier : ImbalancedChen.FirstExitDepthState.{0} Nat)
  (hlen :
    @Eq.{1} Nat (@List.length.{0} Nat (@ImbalancedChen.FirstExitDepthState.selectedPrefix.{0} Nat frontier))
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
  (q : Nat),
  Not
      (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@List.length.{0} Nat (@ImbalancedChen.FirstExitDepthState.selectedPrefix.{0} Nat frontier))) →
    False
```

## ImbalancedChen.HistoricalPrefixCapData.b

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.HistoricalPrefixCapData) → Rat
```

## ImbalancedChen.HistoricalPrefixCapData.cap3

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.HistoricalPrefixCapData) →
  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m self)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    Rat
```

## ImbalancedChen.HistoricalPrefixCapData.cap4

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.HistoricalPrefixCapData) →
  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m self)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    Rat
```

## ImbalancedChen.HistoricalPrefixCapData.cap5

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.HistoricalPrefixCapData) →
  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m self)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    Rat
```

## ImbalancedChen.HistoricalPrefixCapData.casesOn

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
{motive : (t : ImbalancedChen.HistoricalPrefixCapData) → Sort u} →
  (t : ImbalancedChen.HistoricalPrefixCapData) →
    (mk :
        (a b : Rat) →
          (m : Nat) →
            (old : Rat) →
              (cells3 :
                  Finset.{0}
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                (cap3 :
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                      Rat) →
                  (cells4 :
                      Finset.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                          Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                    (cap4 :
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                            Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                          Rat) →
                      (cells5 :
                          Finset.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                              Fin
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                        (cap5 :
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                                Fin
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                              Rat) →
                          motive
                            (ImbalancedChen.HistoricalPrefixCapData.mk a b m old cells3 cap3 cells4 cap4 cells5 cap5)) →
      motive t
```

## ImbalancedChen.HistoricalPrefixCapData.cell3

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(D : ImbalancedChen.HistoricalPrefixCapData) →
  (j :
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m D)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    Rat
```

## ImbalancedChen.HistoricalPrefixCapData.cell4

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(D : ImbalancedChen.HistoricalPrefixCapData) →
  (j :
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m D)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    Rat
```

## ImbalancedChen.HistoricalPrefixCapData.cell5

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(D : ImbalancedChen.HistoricalPrefixCapData) →
  (j :
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m D)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    Rat
```

## ImbalancedChen.HistoricalPrefixCapData.cells3

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.HistoricalPrefixCapData) →
  Finset.{0}
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m self)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

## ImbalancedChen.HistoricalPrefixCapData.cells4

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.HistoricalPrefixCapData) →
  Finset.{0}
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m self)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

## ImbalancedChen.HistoricalPrefixCapData.cells5

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.HistoricalPrefixCapData) →
  Finset.{0}
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m self)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
```

## ImbalancedChen.HistoricalPrefixCapData.ctorIdx

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
ImbalancedChen.HistoricalPrefixCapData → Nat
```

## ImbalancedChen.HistoricalPrefixCapData.exponent3

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(D : ImbalancedChen.HistoricalPrefixCapData) →
  (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real) → Rat
```

## ImbalancedChen.HistoricalPrefixCapData.exponent3_le_exponent4

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData)
  (hab :
    @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D))
  (hcheck : @Eq.{1} Bool (ImbalancedChen.HistoricalPrefixCapData.levelCheck D) Bool.true)
  (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real),
  @LE.le.{0} Rat Rat.instLE
    (ImbalancedChen.HistoricalPrefixCapData.exponent3 D
      (@ImbalancedChen.historicalPrefixProject.{0} Real (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@Decidable.byContradiction
          (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (Nat.decLe (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          fun
            (a :
              Not
                (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) =>
          ImbalancedChen.HistoricalPrefixCapData.old4._proof_1 a)
        t))
    (ImbalancedChen.HistoricalPrefixCapData.exponent4 D t)
```

## ImbalancedChen.HistoricalPrefixCapData.exponent3_on_cell

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData)
  (hab :
    @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D))
  (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
  (j :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m D)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (ht :
    @Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
      (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real))
      (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real))
      (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.a D))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.b D))
        (ImbalancedChen.HistoricalPrefixCapData.m D) j)
      t),
  @Eq.{1} Rat (ImbalancedChen.HistoricalPrefixCapData.exponent3 D t) (ImbalancedChen.HistoricalPrefixCapData.cell3 D j)
```

## ImbalancedChen.HistoricalPrefixCapData.exponent3_outside

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData)
  (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
  (ht :
    ∀
      (j :
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (ImbalancedChen.HistoricalPrefixCapData.m D)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Membership.mem.{0, 0}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ImbalancedChen.HistoricalPrefixCapData.m D)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Finset.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Finset.instSetLike.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          (ImbalancedChen.HistoricalPrefixCapData.cells3 D) j →
        Not
          (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
            (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real))
            (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real))
            (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.a D))
              (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.b D))
              (ImbalancedChen.HistoricalPrefixCapData.m D) j)
            t)),
  @Eq.{1} Rat (ImbalancedChen.HistoricalPrefixCapData.exponent3 D t) (ImbalancedChen.HistoricalPrefixCapData.old D)
```

## ImbalancedChen.HistoricalPrefixCapData.exponent4

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(D : ImbalancedChen.HistoricalPrefixCapData) →
  (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real) → Rat
```

## ImbalancedChen.HistoricalPrefixCapData.exponent4.eq_1

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData)
  (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real),
  @Eq.{1} Rat (ImbalancedChen.HistoricalPrefixCapData.exponent4 D t)
    (@ImbalancedChen.historicalPrefixLookup (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D)
      (ImbalancedChen.HistoricalPrefixCapData.m D) (ImbalancedChen.HistoricalPrefixCapData.cells4 D)
      (ImbalancedChen.HistoricalPrefixCapData.cap4 D)
      (ImbalancedChen.HistoricalPrefixCapData.exponent3 D
        (@ImbalancedChen.historicalPrefixProject.{0} Real (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          ImbalancedChen.HistoricalPrefixCapData.old4._proof_2 t))
      t)
```

## ImbalancedChen.HistoricalPrefixCapData.exponent4_apply_sub

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData)
  (hab :
    @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D))
  (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real) (f : Rat → Real),
  @Eq.{1} Real
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (f (ImbalancedChen.HistoricalPrefixCapData.exponent4 D t))
      (f
        (ImbalancedChen.HistoricalPrefixCapData.exponent3 D
          (@ImbalancedChen.historicalPrefixProject.{0} Real
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@Decidable.byContradiction
              (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (Nat.decLe (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              fun
                (a :
                  Not
                    (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) =>
              ImbalancedChen.HistoricalPrefixCapData.old4._proof_1 a)
            t))))
    (@Finset.sum.{0, 0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m D)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      Real Real.instAddCommMonoid (ImbalancedChen.HistoricalPrefixCapData.cells4 D)
      fun
        (j :
          Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ImbalancedChen.HistoricalPrefixCapData.m D)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
      @ite.{1} Real
        (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
          (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
          (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
          (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.a D))
            (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.b D))
            (ImbalancedChen.HistoricalPrefixCapData.m D) j)
          t)
        (Classical.propDecidable
          (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
            (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.a D))
              (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.b D))
              (ImbalancedChen.HistoricalPrefixCapData.m D) j)
            t))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (f (ImbalancedChen.HistoricalPrefixCapData.cap4 D j)) (f (ImbalancedChen.HistoricalPrefixCapData.old4 D j)))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
```

## ImbalancedChen.HistoricalPrefixCapData.exponent4_le_exponent5

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData)
  (hab :
    @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D))
  (hcheck : @Eq.{1} Bool (ImbalancedChen.HistoricalPrefixCapData.levelCheck D) Bool.true)
  (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real),
  @LE.le.{0} Rat Rat.instLE
    (ImbalancedChen.HistoricalPrefixCapData.exponent4 D
      (@ImbalancedChen.historicalPrefixProject.{0} Real (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
        (@Decidable.byContradiction
          (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
          (Nat.decLe (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
          fun
            (a :
              Not
                (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))) =>
          ImbalancedChen.HistoricalPrefixCapData.old5._proof_1 a)
        t))
    (ImbalancedChen.HistoricalPrefixCapData.exponent5 D t)
```

## ImbalancedChen.HistoricalPrefixCapData.exponent4_on_cell

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData)
  (hab :
    @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D))
  (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
  (j :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m D)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (ht :
    @Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
      (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
      (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
      (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.a D))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.b D))
        (ImbalancedChen.HistoricalPrefixCapData.m D) j)
      t),
  @Eq.{1} Rat (ImbalancedChen.HistoricalPrefixCapData.exponent4 D t) (ImbalancedChen.HistoricalPrefixCapData.cell4 D j)
```

## ImbalancedChen.HistoricalPrefixCapData.exponent4_outside

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData)
  (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
  (ht :
    ∀
      (j :
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (ImbalancedChen.HistoricalPrefixCapData.m D)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Membership.mem.{0, 0}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ImbalancedChen.HistoricalPrefixCapData.m D)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Finset.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Finset.instSetLike.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          (ImbalancedChen.HistoricalPrefixCapData.cells4 D) j →
        Not
          (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
            (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.a D))
              (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.b D))
              (ImbalancedChen.HistoricalPrefixCapData.m D) j)
            t)),
  @Eq.{1} Rat (ImbalancedChen.HistoricalPrefixCapData.exponent4 D t)
    (ImbalancedChen.HistoricalPrefixCapData.exponent3 D
      (@ImbalancedChen.historicalPrefixProject.{0} Real (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@Decidable.byContradiction
          (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (Nat.decLe (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          fun
            (a :
              Not
                (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) =>
          ImbalancedChen.HistoricalPrefixCapData.old4._proof_1 a)
        t))
```

## ImbalancedChen.HistoricalPrefixCapData.exponent5

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(D : ImbalancedChen.HistoricalPrefixCapData) →
  (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real) → Rat
```

## ImbalancedChen.HistoricalPrefixCapData.exponent5.eq_1

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData)
  (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real),
  @Eq.{1} Rat (ImbalancedChen.HistoricalPrefixCapData.exponent5 D t)
    (@ImbalancedChen.historicalPrefixLookup (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
      (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D)
      (ImbalancedChen.HistoricalPrefixCapData.m D) (ImbalancedChen.HistoricalPrefixCapData.cells5 D)
      (ImbalancedChen.HistoricalPrefixCapData.cap5 D)
      (ImbalancedChen.HistoricalPrefixCapData.exponent4 D
        (@ImbalancedChen.historicalPrefixProject.{0} Real (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
          ImbalancedChen.HistoricalPrefixCapData.old5._proof_2 t))
      t)
```

## ImbalancedChen.HistoricalPrefixCapData.exponent5_apply_sub

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData)
  (hab :
    @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D))
  (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real) (f : Rat → Real),
  @Eq.{1} Real
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (f (ImbalancedChen.HistoricalPrefixCapData.exponent5 D t))
      (f
        (ImbalancedChen.HistoricalPrefixCapData.exponent4 D
          (@ImbalancedChen.historicalPrefixProject.{0} Real
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
            (@Decidable.byContradiction
              (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (Nat.decLe (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              fun
                (a :
                  Not
                    (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))) =>
              ImbalancedChen.HistoricalPrefixCapData.old5._proof_1 a)
            t))))
    (@Finset.sum.{0, 0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m D)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      Real Real.instAddCommMonoid (ImbalancedChen.HistoricalPrefixCapData.cells5 D)
      fun
        (j :
          Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ImbalancedChen.HistoricalPrefixCapData.m D)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
      @ite.{1} Real
        (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real)
          (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real))
          (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real))
          (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
            (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.a D))
            (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.b D))
            (ImbalancedChen.HistoricalPrefixCapData.m D) j)
          t)
        (Classical.propDecidable
          (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real)
            (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real))
            (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real))
            (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
              (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.a D))
              (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.b D))
              (ImbalancedChen.HistoricalPrefixCapData.m D) j)
            t))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (f (ImbalancedChen.HistoricalPrefixCapData.cap5 D j)) (f (ImbalancedChen.HistoricalPrefixCapData.old5 D j)))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
```

## ImbalancedChen.HistoricalPrefixCapData.exponent5_on_cell

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData)
  (hab :
    @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D))
  (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real)
  (j :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m D)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (ht :
    @Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real)
      (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real))
      (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real))
      (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.a D))
        (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.b D))
        (ImbalancedChen.HistoricalPrefixCapData.m D) j)
      t),
  @Eq.{1} Rat (ImbalancedChen.HistoricalPrefixCapData.exponent5 D t) (ImbalancedChen.HistoricalPrefixCapData.cell5 D j)
```

## ImbalancedChen.HistoricalPrefixCapData.exponent5_outside

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData)
  (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real)
  (ht :
    ∀
      (j :
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (ImbalancedChen.HistoricalPrefixCapData.m D)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Membership.mem.{0, 0}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ImbalancedChen.HistoricalPrefixCapData.m D)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Finset.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Finset.instSetLike.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          (ImbalancedChen.HistoricalPrefixCapData.cells5 D) j →
        Not
          (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real)
            (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real))
            (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real))
            (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
              (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.a D))
              (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.b D))
              (ImbalancedChen.HistoricalPrefixCapData.m D) j)
            t)),
  @Eq.{1} Rat (ImbalancedChen.HistoricalPrefixCapData.exponent5 D t)
    (ImbalancedChen.HistoricalPrefixCapData.exponent4 D
      (@ImbalancedChen.historicalPrefixProject.{0} Real (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
        (@Decidable.byContradiction
          (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
          (Nat.decLe (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
          fun
            (a :
              Not
                (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))) =>
          ImbalancedChen.HistoricalPrefixCapData.old5._proof_1 a)
        t))
```

## ImbalancedChen.HistoricalPrefixCapData.level3

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(D : ImbalancedChen.HistoricalPrefixCapData) → (N : Real) → (history : List.{0} Nat) → Real
```

## ImbalancedChen.HistoricalPrefixCapData.level3_ancestor_le_level4

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData)
  (hab :
    @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D))
  (hcheck : @Eq.{1} Bool (ImbalancedChen.HistoricalPrefixCapData.levelCheck D) Bool.true) (N : Real)
  (hN : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) N)
  (history : List.{0} Nat)
  (hlen : @Eq.{1} Nat (@List.length.{0} Nat history) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @LE.le.{0} Real Real.instLE
    (ImbalancedChen.HistoricalPrefixCapData.level3 D N
      (@ImbalancedChen.rosserAncestor.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) history))
    (ImbalancedChen.HistoricalPrefixCapData.level4 D N history)
```

## ImbalancedChen.HistoricalPrefixCapData.level3_ancestor_le_level4._proof_1_1

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (history : List.{0} Nat),
  Not
      (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
    False
```

## ImbalancedChen.HistoricalPrefixCapData.level3_outside

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : Real) (history : List.{0} Nat)
  (hout :
    ∀
      (j :
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (ImbalancedChen.HistoricalPrefixCapData.m D)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Membership.mem.{0, 0}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ImbalancedChen.HistoricalPrefixCapData.m D)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Finset.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Finset.instSetLike.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          (ImbalancedChen.HistoricalPrefixCapData.cells3 D) j →
        Not
          (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real)
            (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real))
            (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real))
            (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.a D))
              (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.b D))
              (ImbalancedChen.HistoricalPrefixCapData.m D) j)
            (ImbalancedChen.primeHistoryLogCoordinates N (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              history))),
  @Eq.{1} Real (ImbalancedChen.HistoricalPrefixCapData.level3 D N history)
    (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow) N
      (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.old D)))
```

## ImbalancedChen.HistoricalPrefixCapData.level4

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(D : ImbalancedChen.HistoricalPrefixCapData) → (N : Real) → (history : List.{0} Nat) → Real
```

## ImbalancedChen.HistoricalPrefixCapData.level4_ancestor_le_level5

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData)
  (hab :
    @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D))
  (hcheck : @Eq.{1} Bool (ImbalancedChen.HistoricalPrefixCapData.levelCheck D) Bool.true) (N : Real)
  (hN : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) N)
  (history : List.{0} Nat)
  (hlen : @Eq.{1} Nat (@List.length.{0} Nat history) (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))),
  @LE.le.{0} Real Real.instLE
    (ImbalancedChen.HistoricalPrefixCapData.level4 D N
      (@ImbalancedChen.rosserAncestor.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) history))
    (ImbalancedChen.HistoricalPrefixCapData.level5 D N history)
```

## ImbalancedChen.HistoricalPrefixCapData.level4_ancestor_le_level5._proof_1_1

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (history : List.{0} Nat),
  Not
      (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) →
    False
```

## ImbalancedChen.HistoricalPrefixCapData.level4_outside

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : Real) (history : List.{0} Nat)
  (hlen : @Eq.{1} Nat (@List.length.{0} Nat history) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
  (hout :
    ∀
      (j :
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (ImbalancedChen.HistoricalPrefixCapData.m D)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Membership.mem.{0, 0}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ImbalancedChen.HistoricalPrefixCapData.m D)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Finset.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Finset.instSetLike.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          (ImbalancedChen.HistoricalPrefixCapData.cells4 D) j →
        Not
          (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
            (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
            (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.a D))
              (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.b D))
              (ImbalancedChen.HistoricalPrefixCapData.m D) j)
            (ImbalancedChen.primeHistoryLogCoordinates N (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              history))),
  @Eq.{1} Real (ImbalancedChen.HistoricalPrefixCapData.level4 D N history)
    (ImbalancedChen.HistoricalPrefixCapData.level3 D N
      (@ImbalancedChen.rosserAncestor.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) history))
```

## ImbalancedChen.HistoricalPrefixCapData.level4_outside._proof_1_1

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (history : List.{0} Nat),
  Not
      (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
    False
```

## ImbalancedChen.HistoricalPrefixCapData.level5

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(D : ImbalancedChen.HistoricalPrefixCapData) → (N : Real) → (history : List.{0} Nat) → Real
```

## ImbalancedChen.HistoricalPrefixCapData.level5_outside

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : Real) (history : List.{0} Nat)
  (hlen : @Eq.{1} Nat (@List.length.{0} Nat history) (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
  (hout :
    ∀
      (j :
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (ImbalancedChen.HistoricalPrefixCapData.m D)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Membership.mem.{0, 0}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ImbalancedChen.HistoricalPrefixCapData.m D)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Finset.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Finset.instSetLike.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          (ImbalancedChen.HistoricalPrefixCapData.cells5 D) j →
        Not
          (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real)
            (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real))
            (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Real))
            (@ImbalancedChen.logPrimeMeshCell (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
              (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.a D))
              (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.b D))
              (ImbalancedChen.HistoricalPrefixCapData.m D) j)
            (ImbalancedChen.primeHistoryLogCoordinates N (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
              history))),
  @Eq.{1} Real (ImbalancedChen.HistoricalPrefixCapData.level5 D N history)
    (ImbalancedChen.HistoricalPrefixCapData.level4 D N
      (@ImbalancedChen.rosserAncestor.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) history))
```

## ImbalancedChen.HistoricalPrefixCapData.level5_outside._proof_1_1

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (history : List.{0} Nat),
  Not
      (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) →
    False
```

## ImbalancedChen.HistoricalPrefixCapData.levelCheck

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(D : ImbalancedChen.HistoricalPrefixCapData) → Bool
```

## ImbalancedChen.HistoricalPrefixCapData.levelCheck.eq_1

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData),
  @Eq.{1} Bool (ImbalancedChen.HistoricalPrefixCapData.levelCheck D)
    (Bool.and
      (@Decidable.decide
        (∀
          (a :
            Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (h :
            @Membership.mem.{0, 0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Finset.{0}
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (ImbalancedChen.HistoricalPrefixCapData.m D)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@SetLike.instMembership.{0, 0}
                (Finset.{0}
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (ImbalancedChen.HistoricalPrefixCapData.m D)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (ImbalancedChen.HistoricalPrefixCapData.m D)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@Finset.instSetLike.{0}
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (ImbalancedChen.HistoricalPrefixCapData.m D)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
              (ImbalancedChen.HistoricalPrefixCapData.cells3 D) a),
          @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.old D)
            (ImbalancedChen.HistoricalPrefixCapData.cap3 D a))
        (@Finset.decidableDforallFinset.{0}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ImbalancedChen.HistoricalPrefixCapData.m D)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (ImbalancedChen.HistoricalPrefixCapData.cells3 D)
          (fun
              (j :
                Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (ImbalancedChen.HistoricalPrefixCapData.m D)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (x :
                @Membership.mem.{0, 0}
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (ImbalancedChen.HistoricalPrefixCapData.m D)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (Finset.{0}
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (ImbalancedChen.HistoricalPrefixCapData.m D)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@SetLike.instMembership.{0, 0}
                    (Finset.{0}
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (ImbalancedChen.HistoricalPrefixCapData.m D)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (ImbalancedChen.HistoricalPrefixCapData.m D)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Finset.instSetLike.{0}
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (ImbalancedChen.HistoricalPrefixCapData.m D)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                  (ImbalancedChen.HistoricalPrefixCapData.cells3 D) j) =>
            @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.old D)
              (ImbalancedChen.HistoricalPrefixCapData.cap3 D j))
          fun
            (a :
              Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (h :
              @Membership.mem.{0, 0}
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (ImbalancedChen.HistoricalPrefixCapData.m D)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Finset.{0}
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (ImbalancedChen.HistoricalPrefixCapData.m D)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@SetLike.instMembership.{0, 0}
                  (Finset.{0}
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (ImbalancedChen.HistoricalPrefixCapData.m D)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (ImbalancedChen.HistoricalPrefixCapData.m D)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@Finset.instSetLike.{0}
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (ImbalancedChen.HistoricalPrefixCapData.m D)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                (ImbalancedChen.HistoricalPrefixCapData.cells3 D) a) =>
          Rat.instDecidableLe (ImbalancedChen.HistoricalPrefixCapData.old D)
            (ImbalancedChen.HistoricalPrefixCapData.cap3 D a)))
      (Bool.and
        (@Decidable.decide
          (∀
            (a :
              Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (h :
              @Membership.mem.{0, 0}
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (ImbalancedChen.HistoricalPrefixCapData.m D)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Finset.{0}
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (ImbalancedChen.HistoricalPrefixCapData.m D)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@SetLike.instMembership.{0, 0}
                  (Finset.{0}
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (ImbalancedChen.HistoricalPrefixCapData.m D)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (ImbalancedChen.HistoricalPrefixCapData.m D)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@Finset.instSetLike.{0}
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (ImbalancedChen.HistoricalPrefixCapData.m D)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                (ImbalancedChen.HistoricalPrefixCapData.cells4 D) a),
            @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.old4 D a)
              (ImbalancedChen.HistoricalPrefixCapData.cap4 D a))
          (@Finset.decidableDforallFinset.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (ImbalancedChen.HistoricalPrefixCapData.cells4 D)
            (fun
                (j :
                  Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (ImbalancedChen.HistoricalPrefixCapData.m D)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (x :
                  @Membership.mem.{0, 0}
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (ImbalancedChen.HistoricalPrefixCapData.m D)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Finset.{0}
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (ImbalancedChen.HistoricalPrefixCapData.m D)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (@SetLike.instMembership.{0, 0}
                      (Finset.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                          Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (ImbalancedChen.HistoricalPrefixCapData.m D)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (ImbalancedChen.HistoricalPrefixCapData.m D)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@Finset.instSetLike.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                          Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (ImbalancedChen.HistoricalPrefixCapData.m D)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                    (ImbalancedChen.HistoricalPrefixCapData.cells4 D) j) =>
              @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.old4 D j)
                (ImbalancedChen.HistoricalPrefixCapData.cap4 D j))
            fun
              (a :
                Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (ImbalancedChen.HistoricalPrefixCapData.m D)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (h :
                @Membership.mem.{0, 0}
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (ImbalancedChen.HistoricalPrefixCapData.m D)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (Finset.{0}
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (ImbalancedChen.HistoricalPrefixCapData.m D)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@SetLike.instMembership.{0, 0}
                    (Finset.{0}
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (ImbalancedChen.HistoricalPrefixCapData.m D)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (ImbalancedChen.HistoricalPrefixCapData.m D)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Finset.instSetLike.{0}
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (ImbalancedChen.HistoricalPrefixCapData.m D)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                  (ImbalancedChen.HistoricalPrefixCapData.cells4 D) a) =>
            Rat.instDecidableLe (ImbalancedChen.HistoricalPrefixCapData.old4 D a)
              (ImbalancedChen.HistoricalPrefixCapData.cap4 D a)))
        (@Decidable.decide
          (∀
            (a :
              Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (h :
              @Membership.mem.{0, 0}
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (ImbalancedChen.HistoricalPrefixCapData.m D)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Finset.{0}
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (ImbalancedChen.HistoricalPrefixCapData.m D)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@SetLike.instMembership.{0, 0}
                  (Finset.{0}
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (ImbalancedChen.HistoricalPrefixCapData.m D)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (ImbalancedChen.HistoricalPrefixCapData.m D)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@Finset.instSetLike.{0}
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (ImbalancedChen.HistoricalPrefixCapData.m D)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                (ImbalancedChen.HistoricalPrefixCapData.cells5 D) a),
            @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.old5 D a)
              (ImbalancedChen.HistoricalPrefixCapData.cap5 D a))
          (@Finset.decidableDforallFinset.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (ImbalancedChen.HistoricalPrefixCapData.cells5 D)
            (fun
                (j :
                  Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (ImbalancedChen.HistoricalPrefixCapData.m D)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (x :
                  @Membership.mem.{0, 0}
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (ImbalancedChen.HistoricalPrefixCapData.m D)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Finset.{0}
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (ImbalancedChen.HistoricalPrefixCapData.m D)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (@SetLike.instMembership.{0, 0}
                      (Finset.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                          Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (ImbalancedChen.HistoricalPrefixCapData.m D)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (ImbalancedChen.HistoricalPrefixCapData.m D)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@Finset.instSetLike.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                          Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (ImbalancedChen.HistoricalPrefixCapData.m D)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                    (ImbalancedChen.HistoricalPrefixCapData.cells5 D) j) =>
              @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.old5 D j)
                (ImbalancedChen.HistoricalPrefixCapData.cap5 D j))
            fun
              (a :
                Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (ImbalancedChen.HistoricalPrefixCapData.m D)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (h :
                @Membership.mem.{0, 0}
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (ImbalancedChen.HistoricalPrefixCapData.m D)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (Finset.{0}
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (ImbalancedChen.HistoricalPrefixCapData.m D)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@SetLike.instMembership.{0, 0}
                    (Finset.{0}
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (ImbalancedChen.HistoricalPrefixCapData.m D)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (ImbalancedChen.HistoricalPrefixCapData.m D)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@Finset.instSetLike.{0}
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (ImbalancedChen.HistoricalPrefixCapData.m D)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                  (ImbalancedChen.HistoricalPrefixCapData.cells5 D) a) =>
            Rat.instDecidableLe (ImbalancedChen.HistoricalPrefixCapData.old5 D a)
              (ImbalancedChen.HistoricalPrefixCapData.cap5 D a)))))
```

## ImbalancedChen.HistoricalPrefixCapData.levelCheck_of_selectedBoxCapChecks

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData)
  (I3 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m D)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
  (I4 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m D)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
  (I5 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m D)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Finset.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
  (nu3 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m D)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat)
  (nu4 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m D)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat)
  (nu5 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m D)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat)
  (h3 :
    ∀
      (j :
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (ImbalancedChen.HistoricalPrefixCapData.m D)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Membership.mem.{0, 0}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ImbalancedChen.HistoricalPrefixCapData.m D)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Finset.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Finset.instSetLike.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          (ImbalancedChen.HistoricalPrefixCapData.cells3 D) j →
        And
          (@Eq.{1} Rat (ImbalancedChen.HistoricalPrefixCapData.cap3 D j)
            (@ImbalancedChen.selectedBoxCap (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (I3 j)
              (ImbalancedChen.HistoricalPrefixCapData.old D) (nu3 j)
              (@ImbalancedChen.qLogPrimeMeshLo (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D)
                (ImbalancedChen.HistoricalPrefixCapData.m D) j)
              (@ImbalancedChen.qLogPrimeMeshHi (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D)
                (ImbalancedChen.HistoricalPrefixCapData.m D) j)))
          (@Eq.{1} Bool
            (@ImbalancedChen.selectedBoxCapCheck (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (I3 j)
              (ImbalancedChen.HistoricalPrefixCapData.old D) (nu3 j)
              (@ImbalancedChen.qLogPrimeMeshLo (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D)
                (ImbalancedChen.HistoricalPrefixCapData.m D) j)
              (@ImbalancedChen.qLogPrimeMeshHi (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D)
                (ImbalancedChen.HistoricalPrefixCapData.m D) j))
            Bool.true))
  (h4 :
    ∀
      (j :
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (ImbalancedChen.HistoricalPrefixCapData.m D)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Membership.mem.{0, 0}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ImbalancedChen.HistoricalPrefixCapData.m D)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Finset.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Finset.instSetLike.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          (ImbalancedChen.HistoricalPrefixCapData.cells4 D) j →
        And
          (@Eq.{1} Rat (ImbalancedChen.HistoricalPrefixCapData.cap4 D j)
            (@ImbalancedChen.selectedBoxCap (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (I4 j)
              (ImbalancedChen.HistoricalPrefixCapData.old4 D j) (nu4 j)
              (@ImbalancedChen.qLogPrimeMeshLo (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D)
                (ImbalancedChen.HistoricalPrefixCapData.m D) j)
              (@ImbalancedChen.qLogPrimeMeshHi (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D)
                (ImbalancedChen.HistoricalPrefixCapData.m D) j)))
          (@Eq.{1} Bool
            (@ImbalancedChen.selectedBoxCapCheck (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (I4 j)
              (ImbalancedChen.HistoricalPrefixCapData.old4 D j) (nu4 j)
              (@ImbalancedChen.qLogPrimeMeshLo (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D)
                (ImbalancedChen.HistoricalPrefixCapData.m D) j)
              (@ImbalancedChen.qLogPrimeMeshHi (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D)
                (ImbalancedChen.HistoricalPrefixCapData.m D) j))
            Bool.true))
  (h5 :
    ∀
      (j :
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (ImbalancedChen.HistoricalPrefixCapData.m D)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Membership.mem.{0, 0}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ImbalancedChen.HistoricalPrefixCapData.m D)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Finset.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Finset.instSetLike.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          (ImbalancedChen.HistoricalPrefixCapData.cells5 D) j →
        And
          (@Eq.{1} Rat (ImbalancedChen.HistoricalPrefixCapData.cap5 D j)
            (@ImbalancedChen.selectedBoxCap (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (I5 j)
              (ImbalancedChen.HistoricalPrefixCapData.old5 D j) (nu5 j)
              (@ImbalancedChen.qLogPrimeMeshLo (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D)
                (ImbalancedChen.HistoricalPrefixCapData.m D) j)
              (@ImbalancedChen.qLogPrimeMeshHi (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D)
                (ImbalancedChen.HistoricalPrefixCapData.m D) j)))
          (@Eq.{1} Bool
            (@ImbalancedChen.selectedBoxCapCheck (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (I5 j)
              (ImbalancedChen.HistoricalPrefixCapData.old5 D j) (nu5 j)
              (@ImbalancedChen.qLogPrimeMeshLo (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D)
                (ImbalancedChen.HistoricalPrefixCapData.m D) j)
              (@ImbalancedChen.qLogPrimeMeshHi (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D)
                (ImbalancedChen.HistoricalPrefixCapData.m D) j))
            Bool.true)),
  @Eq.{1} Bool (ImbalancedChen.HistoricalPrefixCapData.levelCheck D) Bool.true
```

## ImbalancedChen.HistoricalPrefixCapData.levelCheck_sound

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData)
  (h : @Eq.{1} Bool (ImbalancedChen.HistoricalPrefixCapData.levelCheck D) Bool.true),
  And
    (∀
      (j :
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (ImbalancedChen.HistoricalPrefixCapData.m D)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Membership.mem.{0, 0}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ImbalancedChen.HistoricalPrefixCapData.m D)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Finset.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Finset.instSetLike.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          (ImbalancedChen.HistoricalPrefixCapData.cells3 D) j →
        @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.old D)
          (ImbalancedChen.HistoricalPrefixCapData.cap3 D j))
    (And
      (∀
        (j :
          Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ImbalancedChen.HistoricalPrefixCapData.m D)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
        @Membership.mem.{0, 0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (Finset.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (@SetLike.instMembership.{0, 0}
              (Finset.{0}
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (ImbalancedChen.HistoricalPrefixCapData.m D)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Finset.instSetLike.{0}
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (ImbalancedChen.HistoricalPrefixCapData.m D)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (ImbalancedChen.HistoricalPrefixCapData.cells4 D) j →
          @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.old4 D j)
            (ImbalancedChen.HistoricalPrefixCapData.cap4 D j))
      (∀
        (j :
          Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (ImbalancedChen.HistoricalPrefixCapData.m D)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
        @Membership.mem.{0, 0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (ImbalancedChen.HistoricalPrefixCapData.m D)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (Finset.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (@SetLike.instMembership.{0, 0}
              (Finset.{0}
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (ImbalancedChen.HistoricalPrefixCapData.m D)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (ImbalancedChen.HistoricalPrefixCapData.m D)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Finset.instSetLike.{0}
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (ImbalancedChen.HistoricalPrefixCapData.m D)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (ImbalancedChen.HistoricalPrefixCapData.cells5 D) j →
          @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.old5 D j)
            (ImbalancedChen.HistoricalPrefixCapData.cap5 D j)))
```

## ImbalancedChen.HistoricalPrefixCapData.m

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.HistoricalPrefixCapData) → Nat
```

## ImbalancedChen.HistoricalPrefixCapData.mk

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(a b : Rat) →
  (m : Nat) →
    (old : Rat) →
      (cells3 :
          Finset.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        (cap3 :
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
              Rat) →
          (cells4 :
              Finset.{0}
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
            (cap4 :
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                  Rat) →
              (cells5 :
                  Finset.{0}
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                (cap5 :
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                      Rat) →
                  ImbalancedChen.HistoricalPrefixCapData
```

## ImbalancedChen.HistoricalPrefixCapData.mk._flat_ctor

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(a b : Rat) →
  (m : Nat) →
    (old : Rat) →
      (cells3 :
          Finset.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        (cap3 :
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
              Rat) →
          (cells4 :
              Finset.{0}
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
            (cap4 :
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                  Rat) →
              (cells5 :
                  Finset.{0}
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                (cap5 :
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                      Rat) →
                  ImbalancedChen.HistoricalPrefixCapData
```

## ImbalancedChen.HistoricalPrefixCapData.mk.inj

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {a b : Rat} {m : Nat} {old : Rat}
  {cells3 :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))}
  {cap3 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat}
  {cells4 :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))}
  {cap4 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat}
  {cells5 :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))}
  {cap5 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat}
  {a_1 b_1 : Rat} {m_1 : Nat} {old_1 : Rat}
  {cells3_1 :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))}
  {cap3_1 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat}
  {cells4_1 :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))}
  {cap4_1 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat}
  {cells5_1 :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))}
  {cap5_1 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat},
  @Eq.{1} ImbalancedChen.HistoricalPrefixCapData
      (ImbalancedChen.HistoricalPrefixCapData.mk a b m old cells3 cap3 cells4 cap4 cells5 cap5)
      (ImbalancedChen.HistoricalPrefixCapData.mk a_1 b_1 m_1 old_1 cells3_1 cap3_1 cells4_1 cap4_1 cells5_1 cap5_1) →
    And (@Eq.{1} Rat a a_1)
      (And (@Eq.{1} Rat b b_1)
        (And (@Eq.{1} Nat m m_1)
          (And (@Eq.{1} Rat old old_1)
            (And
              (@HEq.{1}
                (Finset.{0}
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                cells3
                (Finset.{0}
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                cells3_1)
              (And
                (@HEq.{1}
                  ((Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                    Rat)
                  cap3
                  ((Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                    Rat)
                  cap3_1)
                (And
                  (@HEq.{1}
                    (Finset.{0}
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    cells4
                    (Finset.{0}
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    cells4_1)
                  (And
                    (@HEq.{1}
                      ((Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                          Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                        Rat)
                      cap4
                      ((Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                          Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                        Rat)
                      cap4_1)
                    (And
                      (@HEq.{1}
                        (Finset.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                            Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        cells5
                        (Finset.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                            Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        cells5_1)
                      (@HEq.{1}
                        ((Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                            Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                          Rat)
                        cap5
                        ((Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                            Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                          Rat)
                        cap5_1)))))))))
```

## ImbalancedChen.HistoricalPrefixCapData.mk.injEq

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a b : Rat) (m : Nat) (old : Rat)
  (cells3 :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (cap3 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat)
  (cells4 :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (cap4 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat)
  (cells5 :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (cap5 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat)
  (a_1 b_1 : Rat) (m_1 : Nat) (old_1 : Rat)
  (cells3_1 :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (cap3_1 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat)
  (cells4_1 :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (cap4_1 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat)
  (cells5_1 :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (cap5_1 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat),
  @Eq.{1} Prop
    (@Eq.{1} ImbalancedChen.HistoricalPrefixCapData
      (ImbalancedChen.HistoricalPrefixCapData.mk a b m old cells3 cap3 cells4 cap4 cells5 cap5)
      (ImbalancedChen.HistoricalPrefixCapData.mk a_1 b_1 m_1 old_1 cells3_1 cap3_1 cells4_1 cap4_1 cells5_1 cap5_1))
    (And (@Eq.{1} Rat a a_1)
      (And (@Eq.{1} Rat b b_1)
        (And (@Eq.{1} Nat m m_1)
          (And (@Eq.{1} Rat old old_1)
            (And
              (@HEq.{1}
                (Finset.{0}
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                cells3
                (Finset.{0}
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                cells3_1)
              (And
                (@HEq.{1}
                  ((Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                    Rat)
                  cap3
                  ((Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                    Rat)
                  cap3_1)
                (And
                  (@HEq.{1}
                    (Finset.{0}
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    cells4
                    (Finset.{0}
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    cells4_1)
                  (And
                    (@HEq.{1}
                      ((Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                          Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                        Rat)
                      cap4
                      ((Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                          Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                        Rat)
                      cap4_1)
                    (And
                      (@HEq.{1}
                        (Finset.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                            Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        cells5
                        (Finset.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                            Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        cells5_1)
                      (@HEq.{1}
                        ((Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                            Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                          Rat)
                        cap5
                        ((Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                            Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m_1
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                          Rat)
                        cap5_1))))))))))
```

## ImbalancedChen.HistoricalPrefixCapData.mk.noConfusion

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
{P : Sort u} →
  {a b : Rat} →
    {m : Nat} →
      {old : Rat} →
        {cells3 :
            Finset.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))} →
          {cap3 :
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                Rat} →
            {cells4 :
                Finset.{0}
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))} →
              {cap4 :
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                    Rat} →
                {cells5 :
                    Finset.{0}
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))} →
                  {cap5 :
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                          Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                        Rat} →
                    {a' b' : Rat} →
                      {m' : Nat} →
                        {old' : Rat} →
                          {cells3' :
                              Finset.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                                  Fin
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m'
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))} →
                            {cap3' :
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                                    Fin
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m'
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                  Rat} →
                              {cells4' :
                                  Finset.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                                      Fin
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m'
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))} →
                                {cap4' :
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                                        Fin
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m'
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                      Rat} →
                                  {cells5' :
                                      Finset.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                                          Fin
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m'
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))} →
                                    {cap5' :
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                                            Fin
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m'
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                          Rat} →
                                      (eq :
                                          @Eq.{1} ImbalancedChen.HistoricalPrefixCapData
                                            (ImbalancedChen.HistoricalPrefixCapData.mk a b m old cells3 cap3 cells4 cap4
                                              cells5 cap5)
                                            (ImbalancedChen.HistoricalPrefixCapData.mk a' b' m' old' cells3' cap3'
                                              cells4' cap4' cells5' cap5')) →
                                        (k :
                                            (a_eq : @Eq.{1} Rat a a') →
                                              (b_eq : @Eq.{1} Rat b b') →
                                                (m_eq : @Eq.{1} Nat m m') →
                                                  (old_eq : @Eq.{1} Rat old old') →
                                                    (cells3_eq :
                                                        @HEq.{1}
                                                          (Finset.{0}
                                                            (Fin
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                  (instOfNatNat (nat_lit 3))) →
                                                              Fin
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat) m
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                    (instOfNatNat (nat_lit 1))))))
                                                          cells3
                                                          (Finset.{0}
                                                            (Fin
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                  (instOfNatNat (nat_lit 3))) →
                                                              Fin
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat) m'
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                    (instOfNatNat (nat_lit 1))))))
                                                          cells3') →
                                                      (cap3_eq :
                                                          @HEq.{1}
                                                            ((Fin
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                    (instOfNatNat (nat_lit 3))) →
                                                                Fin
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) m
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                      (instOfNatNat (nat_lit 1))))) →
                                                              Rat)
                                                            cap3
                                                            ((Fin
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                    (instOfNatNat (nat_lit 3))) →
                                                                Fin
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) m'
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                      (instOfNatNat (nat_lit 1))))) →
                                                              Rat)
                                                            cap3') →
                                                        (cells4_eq :
                                                            @HEq.{1}
                                                              (Finset.{0}
                                                                (Fin
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                      (instOfNatNat (nat_lit 4))) →
                                                                  Fin
                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                      (@instHAdd.{0} Nat instAddNat) m
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                        (instOfNatNat (nat_lit 1))))))
                                                              cells4
                                                              (Finset.{0}
                                                                (Fin
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                      (instOfNatNat (nat_lit 4))) →
                                                                  Fin
                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                      (@instHAdd.{0} Nat instAddNat) m'
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                        (instOfNatNat (nat_lit 1))))))
                                                              cells4') →
                                                          (cap4_eq :
                                                              @HEq.{1}
                                                                ((Fin
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                        (instOfNatNat (nat_lit 4))) →
                                                                    Fin
                                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                        (@instHAdd.{0} Nat instAddNat) m
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                          (instOfNatNat (nat_lit 1))))) →
                                                                  Rat)
                                                                cap4
                                                                ((Fin
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                        (instOfNatNat (nat_lit 4))) →
                                                                    Fin
                                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                        (@instHAdd.{0} Nat instAddNat) m'
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                          (instOfNatNat (nat_lit 1))))) →
                                                                  Rat)
                                                                cap4') →
                                                            (cells5_eq :
                                                                @HEq.{1}
                                                                  (Finset.{0}
                                                                    (Fin
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 5)
                                                                          (instOfNatNat (nat_lit 5))) →
                                                                      Fin
                                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                          (@instHAdd.{0} Nat instAddNat) m
                                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                            (instOfNatNat (nat_lit 1))))))
                                                                  cells5
                                                                  (Finset.{0}
                                                                    (Fin
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 5)
                                                                          (instOfNatNat (nat_lit 5))) →
                                                                      Fin
                                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                          (@instHAdd.{0} Nat instAddNat) m'
                                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                            (instOfNatNat (nat_lit 1))))))
                                                                  cells5') →
                                                              (cap5_eq :
                                                                  @HEq.{1}
                                                                    ((Fin
                                                                          (@OfNat.ofNat.{0} Nat (nat_lit 5)
                                                                            (instOfNatNat (nat_lit 5))) →
                                                                        Fin
                                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                            (@instHAdd.{0} Nat instAddNat) m
                                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                              (instOfNatNat (nat_lit 1))))) →
                                                                      Rat)
                                                                    cap5
                                                                    ((Fin
                                                                          (@OfNat.ofNat.{0} Nat (nat_lit 5)
                                                                            (instOfNatNat (nat_lit 5))) →
                                                                        Fin
                                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                            (@instHAdd.{0} Nat instAddNat) m'
                                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                              (instOfNatNat (nat_lit 1))))) →
                                                                      Rat)
                                                                    cap5') →
                                                                P) →
                                          P
```

## ImbalancedChen.HistoricalPrefixCapData.mk.sizeOf_spec

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (a b : Rat) (m : Nat) (old : Rat)
  (cells3 :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (cap3 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat)
  (cells4 :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (cap4 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat)
  (cells5 :
    Finset.{0}
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (cap5 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat),
  @Eq.{1} Nat
    (@SizeOf.sizeOf.{1} ImbalancedChen.HistoricalPrefixCapData ImbalancedChen.HistoricalPrefixCapData._sizeOf_inst
      (ImbalancedChen.HistoricalPrefixCapData.mk a b m old cells3 cap3 cells4 cap4 cells5 cap5))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst a))
                (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst b))
              (@SizeOf.sizeOf.{1} Nat instSizeOfNat m))
            (@SizeOf.sizeOf.{1} Rat Rat._sizeOf_inst old))
          (@SizeOf.sizeOf.{1}
            (Finset.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (@Finset._sizeOf_inst.{0}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (instSizeOfDefault.{1}
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                  Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            cells3))
        (@SizeOf.sizeOf.{1}
          (Finset.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@Finset._sizeOf_inst.{0}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (instSizeOfDefault.{1}
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          cells4))
      (@SizeOf.sizeOf.{1}
        (Finset.{0}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@Finset._sizeOf_inst.{0}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (instSizeOfDefault.{1}
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        cells5))
```

## ImbalancedChen.HistoricalPrefixCapData.noConfusion

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
{P : Sort u} →
  {t t' : ImbalancedChen.HistoricalPrefixCapData} →
    (eq : @Eq.{1} ImbalancedChen.HistoricalPrefixCapData t t') →
      ImbalancedChen.HistoricalPrefixCapData.noConfusionType.{u} P t t'
```

## ImbalancedChen.HistoricalPrefixCapData.noConfusionType

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(P : Sort u) → (t t' : ImbalancedChen.HistoricalPrefixCapData) → Sort u
```

## ImbalancedChen.HistoricalPrefixCapData.old

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(self : ImbalancedChen.HistoricalPrefixCapData) → Rat
```

## ImbalancedChen.HistoricalPrefixCapData.old4

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(D : ImbalancedChen.HistoricalPrefixCapData) →
  (j :
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m D)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    Rat
```

## ImbalancedChen.HistoricalPrefixCapData.old4._proof_1

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
Not
    (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
  False
```

## ImbalancedChen.HistoricalPrefixCapData.old4._proof_2

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
```

## ImbalancedChen.HistoricalPrefixCapData.old5

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(D : ImbalancedChen.HistoricalPrefixCapData) →
  (j :
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.HistoricalPrefixCapData.m D)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    Rat
```

## ImbalancedChen.HistoricalPrefixCapData.old5._proof_1

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
Not
    (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) →
  False
```

## ImbalancedChen.HistoricalPrefixCapData.old5._proof_2

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
```

## ImbalancedChen.HistoricalPrefixCapData.old_le_exponent3

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData)
  (hcheck : @Eq.{1} Bool (ImbalancedChen.HistoricalPrefixCapData.levelCheck D) Bool.true)
  (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real),
  @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.old D)
    (ImbalancedChen.HistoricalPrefixCapData.exponent3 D t)
```

## ImbalancedChen.HistoricalPrefixCapData.rec

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
{motive : (t : ImbalancedChen.HistoricalPrefixCapData) → Sort u} →
  (mk :
      (a b : Rat) →
        (m : Nat) →
          (old : Rat) →
            (cells3 :
                Finset.{0}
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                    Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
              (cap3 :
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                    Rat) →
                (cells4 :
                    Finset.{0}
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                  (cap4 :
                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                          Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                        Rat) →
                    (cells5 :
                        Finset.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                            Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                      (cap5 :
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                              Fin
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                            Rat) →
                        motive
                          (ImbalancedChen.HistoricalPrefixCapData.mk a b m old cells3 cap3 cells4 cap4 cells5 cap5)) →
    (t : ImbalancedChen.HistoricalPrefixCapData) → motive t
```

## ImbalancedChen.HistoricalPrefixCapData.recOn

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
{motive : (t : ImbalancedChen.HistoricalPrefixCapData) → Sort u} →
  (t : ImbalancedChen.HistoricalPrefixCapData) →
    (mk :
        (a b : Rat) →
          (m : Nat) →
            (old : Rat) →
              (cells3 :
                  Finset.{0}
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                      Fin
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                (cap3 :
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                        Fin
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                      Rat) →
                  (cells4 :
                      Finset.{0}
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                          Fin
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                    (cap4 :
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
                            Fin
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                          Rat) →
                      (cells5 :
                          Finset.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                              Fin
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                        (cap5 :
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                                Fin
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                              Rat) →
                          motive
                            (ImbalancedChen.HistoricalPrefixCapData.mk a b m old cells3 cap3 cells4 cap4 cells5 cap5)) →
      motive t
```

## ImbalancedChen.HistoricalPrefixCapData.upperFifthPolicy

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(D : ImbalancedChen.HistoricalPrefixCapData) → (N : Real) → Bool → List.{0} Nat → Bool
```

## ImbalancedChen.HistoricalPrefixCapData.upperFifthPolicy.eq_1

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : Real),
  @Eq.{1} (Bool → List.{0} Nat → Bool) (ImbalancedChen.HistoricalPrefixCapData.upperFifthPolicy D N)
    (ImbalancedChen.fifthCappedUpperPolicy
      (ImbalancedChen.ordinaryParityRosserPolicy Bool.false
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow) N
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.old D))))
      (ImbalancedChen.HistoricalPrefixCapData.level3 D N) (ImbalancedChen.HistoricalPrefixCapData.level5 D N))
```

## ImbalancedChen.HistoricalPrefixCapData.upperFifthPolicy_eq_oddFirstExitPolicy

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : Real),
  @Eq.{1} (Bool → List.{0} Nat → Bool) (ImbalancedChen.HistoricalPrefixCapData.upperFifthPolicy D N)
    (@ImbalancedChen.oddFirstExitPolicy.{0} Nat fun (pre : List.{0} Nat) =>
      ImbalancedChen.HistoricalPrefixCapData.upperFifthPolicy D N Bool.false pre)
```

## ImbalancedChen.HistoricalPrefixCapData.upperFifthPolicy_even

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : Real) (pre : List.{0} Nat),
  @Eq.{1} Bool (ImbalancedChen.HistoricalPrefixCapData.upperFifthPolicy D N Bool.true pre) Bool.true
```

## ImbalancedChen.HistoricalPrefixCapData.upperFourthPolicy

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(D : ImbalancedChen.HistoricalPrefixCapData) → (N : Real) → Bool → List.{0} Nat → Bool
```

## ImbalancedChen.HistoricalPrefixCapData.upperFourthPolicy.eq_1

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : Real),
  @Eq.{1} (Bool → List.{0} Nat → Bool) (ImbalancedChen.HistoricalPrefixCapData.upperFourthPolicy D N)
    (ImbalancedChen.fourthCappedUpperPolicy
      (ImbalancedChen.ordinaryParityRosserPolicy Bool.false
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow) N
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.old D))))
      (ImbalancedChen.HistoricalPrefixCapData.level3 D N) (ImbalancedChen.HistoricalPrefixCapData.level4 D N))
```

## ImbalancedChen.HistoricalPrefixCapData.upperFourthPolicy_even

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : Real) (pre : List.{0} Nat),
  @Eq.{1} Bool (ImbalancedChen.HistoricalPrefixCapData.upperFourthPolicy D N Bool.true pre) Bool.true
```

## ImbalancedChen.HistoricalPrefixCapData.upperThirdPolicy

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
(D : ImbalancedChen.HistoricalPrefixCapData) → (N : Real) → Bool → List.{0} Nat → Bool
```

## ImbalancedChen.HistoricalPrefixCapData.upperThirdPolicy.eq_1

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : Real),
  @Eq.{1} (Bool → List.{0} Nat → Bool) (ImbalancedChen.HistoricalPrefixCapData.upperThirdPolicy D N)
    (ImbalancedChen.thirdCappedUpperPolicy
      (ImbalancedChen.ordinaryParityRosserPolicy Bool.false
        (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow) N
          (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.old D))))
      (ImbalancedChen.HistoricalPrefixCapData.level3 D N))
```

## ImbalancedChen.HistoricalPrefixCapData.upperThirdPolicy_even

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData) (N : Real) (pre : List.{0} Nat),
  @Eq.{1} Bool (ImbalancedChen.HistoricalPrefixCapData.upperThirdPolicy D N Bool.true pre) Bool.true
```

## ImbalancedChen.HistoricalPrefixCapData.upperThirdToFifthSaving_eq

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (D : ImbalancedChen.HistoricalPrefixCapData)
  (hab :
    @LE.le.{0} Rat Rat.instLE (ImbalancedChen.HistoricalPrefixCapData.a D) (ImbalancedChen.HistoricalPrefixCapData.b D))
  (hcheck : @Eq.{1} Bool (ImbalancedChen.HistoricalPrefixCapData.levelCheck D) Bool.true) (N cap : Nat)
  (hN :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@Nat.cast.{0} Real Real.instNatCast N))
  (z : Real),
  @Eq.{1} Real
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@ImbalancedChen.firstExitRetainedPolynomial.{0} Nat
        (ImbalancedChen.HistoricalPrefixCapData.upperThirdPolicy D (@Nat.cast.{0} Real Real.instNatCast N))
        (fun (p : Nat) =>
          @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@Nat.cast.{0} Real Real.instNatCast p)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
        (@List.nil.{0} Nat) Bool.true (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (ImbalancedChen.roughPrimeUniverse N cap
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z))
      (@ImbalancedChen.firstExitRetainedPolynomial.{0} Nat
        (ImbalancedChen.HistoricalPrefixCapData.upperFifthPolicy D (@Nat.cast.{0} Real Real.instNatCast N))
        (fun (p : Nat) =>
          @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@Nat.cast.{0} Real Real.instNatCast p)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
        (@List.nil.{0} Nat) Bool.true (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (ImbalancedChen.roughPrimeUniverse N cap
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z)))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (ImbalancedChen.actualHistoricalFourthSaving
        (ImbalancedChen.ordinaryParityRosserPolicy Bool.false
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.old D))))
        (ImbalancedChen.HistoricalPrefixCapData.level3 D (@Nat.cast.{0} Real Real.instNatCast N))
        (ImbalancedChen.HistoricalPrefixCapData.level4 D (@Nat.cast.{0} Real Real.instNatCast N)) N cap z)
      (ImbalancedChen.actualHistoricalFifthSaving
        (ImbalancedChen.ordinaryParityRosserPolicy Bool.false
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N)
            (@Rat.cast.{0} Real Real.instRatCast (ImbalancedChen.HistoricalPrefixCapData.old D))))
        (ImbalancedChen.HistoricalPrefixCapData.level3 D (@Nat.cast.{0} Real Real.instNatCast N))
        (ImbalancedChen.HistoricalPrefixCapData.level4 D (@Nat.cast.{0} Real Real.instNatCast N))
        (ImbalancedChen.HistoricalPrefixCapData.level5 D (@Nat.cast.{0} Real Real.instNatCast N)) N cap z))
```

## ImbalancedChen.fifthCappedUpperPolicy.eq_1

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (base : Bool → List.{0} Nat → Bool) (Q3 Q5 : List.{0} Nat → Real),
  @Eq.{1} (Bool → List.{0} Nat → Bool) (ImbalancedChen.fifthCappedUpperPolicy base Q3 Q5)
    (@ImbalancedChen.firstExitDepthSplicePolicy.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (ImbalancedChen.thirdCappedUpperPolicy base Q3)
      (ImbalancedChen.frozenParityRosserPolicy Bool.false (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
        Q5))
```

## ImbalancedChen.fourthCappedUpperPolicy.eq_1

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (base : Bool → List.{0} Nat → Bool) (Q3 Q4 : List.{0} Nat → Real),
  @Eq.{1} (Bool → List.{0} Nat → Bool) (ImbalancedChen.fourthCappedUpperPolicy base Q3 Q4)
    (@ImbalancedChen.firstExitDepthSplicePolicy.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (ImbalancedChen.thirdCappedUpperPolicy base Q3)
      (ImbalancedChen.frozenParityRosserPolicy Bool.false (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        Q4))
```

## ImbalancedChen.historicalPrefixAncestorCell_unique

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {r d m : Nat} (hrd : @LE.le.{0} Nat instLENat r d) {a b : Real} (hab : @LE.le.{0} Real Real.instLE a b)
  {j :
    Fin d →
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {q :
    Fin r →
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {t : Fin d → Real}
  (ht :
    @Membership.mem.{0, 0} (Fin d → Real) (Set.{0} (Fin d → Real)) (@Set.instMembership.{0} (Fin d → Real))
      (@ImbalancedChen.logPrimeMeshCell d a b m j) t)
  (hq :
    @Membership.mem.{0, 0} (Fin r → Real) (Set.{0} (Fin r → Real)) (@Set.instMembership.{0} (Fin r → Real))
      (@ImbalancedChen.logPrimeMeshCell r a b m q) (@ImbalancedChen.historicalPrefixProject.{0} Real r d hrd t)),
  @Eq.{1}
    (Fin r →
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    q
    (@ImbalancedChen.historicalPrefixProject.{0}
      (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      r d hrd j)
```

## ImbalancedChen.historicalPrefixLookup

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
{d : Nat} →
  (a b : Rat) →
    (m : Nat) →
      (J :
          Finset.{0}
            (Fin d →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        (cap :
            (Fin d →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
              Rat) →
          (fallback : Rat) → (t : Fin d → Real) → Rat
```

## ImbalancedChen.historicalPrefixLookup_apply_sub

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {d : Nat} (a b : Rat) (hab : @LE.le.{0} Rat Rat.instLE a b) (m : Nat)
  (J :
    Finset.{0}
      (Fin d →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (cap :
    (Fin d →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat)
  (fallback : Rat) (t : Fin d → Real) (f : Rat → Real),
  @Eq.{1} Real
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (f (@ImbalancedChen.historicalPrefixLookup d a b m J cap fallback t)) (f fallback))
    (@Finset.sum.{0, 0}
      (Fin d →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      Real Real.instAddCommMonoid J
      fun
        (j :
          Fin d →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
      @ite.{1} Real
        (@Membership.mem.{0, 0} (Fin d → Real) (Set.{0} (Fin d → Real)) (@Set.instMembership.{0} (Fin d → Real))
          (@ImbalancedChen.logPrimeMeshCell d (@Rat.cast.{0} Real Real.instRatCast a)
            (@Rat.cast.{0} Real Real.instRatCast b) m j)
          t)
        (Classical.propDecidable
          (@Membership.mem.{0, 0} (Fin d → Real) (Set.{0} (Fin d → Real)) (@Set.instMembership.{0} (Fin d → Real))
            (@ImbalancedChen.logPrimeMeshCell d (@Rat.cast.{0} Real Real.instRatCast a)
              (@Rat.cast.{0} Real Real.instRatCast b) m j)
            t))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (f (cap j)) (f fallback))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
```

## ImbalancedChen.historicalPrefixLookup_apply_sub._simp_1_1

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Sort u_1} {p : α → Prop}, @Eq.{1} Prop (Not (@Exists.{u_1} α fun (x : α) => p x)) (∀ (x : α), Not (p x))
```

## ImbalancedChen.historicalPrefixLookup_apply_sub._simp_1_2

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {a b : Prop}, @Eq.{1} Prop (Not (And a b)) (a → Not b)
```

## ImbalancedChen.historicalPrefixLookup_ge_fallback

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {d : Nat} (a b : Rat) (m : Nat)
  (J :
    Finset.{0}
      (Fin d →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (old cap :
    (Fin d →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat)
  (fallback : Rat) (t : Fin d → Real)
  (hlevel :
    ∀
      (j :
        Fin d →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Membership.mem.{0, 0}
          (Fin d →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Finset.{0}
            (Fin d →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0}
              (Fin d →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (Fin d →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Finset.instSetLike.{0}
              (Fin d →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          J j →
        @LE.le.{0} Rat Rat.instLE (old j) (cap j))
  (hinherit :
    ∀
      (j :
        Fin d →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Membership.mem.{0, 0}
          (Fin d →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Finset.{0}
            (Fin d →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0}
              (Fin d →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (Fin d →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Finset.instSetLike.{0}
              (Fin d →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          J j →
        @Membership.mem.{0, 0} (Fin d → Real) (Set.{0} (Fin d → Real)) (@Set.instMembership.{0} (Fin d → Real))
            (@ImbalancedChen.logPrimeMeshCell d (@Rat.cast.{0} Real Real.instRatCast a)
              (@Rat.cast.{0} Real Real.instRatCast b) m j)
            t →
          @Eq.{1} Rat fallback (old j)),
  @LE.le.{0} Rat Rat.instLE fallback (@ImbalancedChen.historicalPrefixLookup d a b m J cap fallback t)
```

## ImbalancedChen.historicalPrefixLookup_on_any_cell

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {d : Nat} (a b : Rat) (hab : @LE.le.{0} Rat Rat.instLE a b) (m : Nat)
  (J :
    Finset.{0}
      (Fin d →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (cap :
    (Fin d →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat)
  (fallback : Rat) (t : Fin d → Real)
  (j :
    Fin d →
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (ht :
    @Membership.mem.{0, 0} (Fin d → Real) (Set.{0} (Fin d → Real)) (@Set.instMembership.{0} (Fin d → Real))
      (@ImbalancedChen.logPrimeMeshCell d (@Rat.cast.{0} Real Real.instRatCast a)
        (@Rat.cast.{0} Real Real.instRatCast b) m j)
      t),
  @Eq.{1} Rat (@ImbalancedChen.historicalPrefixLookup d a b m J cap fallback t)
    (@ite.{1} Rat
      (@Membership.mem.{0, 0}
        (Fin d →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (Finset.{0}
          (Fin d →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@SetLike.instMembership.{0, 0}
          (Finset.{0}
            (Fin d →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (Fin d →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Finset.instSetLike.{0}
            (Fin d →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        J j)
      (@Finset.decidableMem.{0}
        (Fin d →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (fun
            (a b :
              Fin d →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
          @Fintype.decidablePiFintype.{0, 0} (Fin d)
            (fun (a : Fin d) =>
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (fun (a : Fin d) =>
              instDecidableEqFin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (Fin.fintype d) a b)
        j J)
      (cap j) fallback)
```

## ImbalancedChen.historicalPrefixLookup_on_cell

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {d : Nat} (a b : Rat) (hab : @LE.le.{0} Rat Rat.instLE a b) (m : Nat)
  (J :
    Finset.{0}
      (Fin d →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (cap :
    (Fin d →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat)
  (fallback : Rat) (t : Fin d → Real)
  (j :
    Fin d →
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (hj :
    @Membership.mem.{0, 0}
      (Fin d →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (Finset.{0}
        (Fin d →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@SetLike.instMembership.{0, 0}
        (Finset.{0}
          (Fin d →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (Fin d →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Finset.instSetLike.{0}
          (Fin d →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
      J j)
  (ht :
    @Membership.mem.{0, 0} (Fin d → Real) (Set.{0} (Fin d → Real)) (@Set.instMembership.{0} (Fin d → Real))
      (@ImbalancedChen.logPrimeMeshCell d (@Rat.cast.{0} Real Real.instRatCast a)
        (@Rat.cast.{0} Real Real.instRatCast b) m j)
      t),
  @Eq.{1} Rat (@ImbalancedChen.historicalPrefixLookup d a b m J cap fallback t) (cap j)
```

## ImbalancedChen.historicalPrefixLookup_outside

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {d : Nat} (a b : Rat) (m : Nat)
  (J :
    Finset.{0}
      (Fin d →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
  (cap :
    (Fin d →
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      Rat)
  (fallback : Rat) (t : Fin d → Real)
  (ht :
    ∀
      (j :
        Fin d →
          Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @Membership.mem.{0, 0}
          (Fin d →
            Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (Finset.{0}
            (Fin d →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@SetLike.instMembership.{0, 0}
            (Finset.{0}
              (Fin d →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (Fin d →
              Fin
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Finset.instSetLike.{0}
              (Fin d →
                Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          J j →
        Not
          (@Membership.mem.{0, 0} (Fin d → Real) (Set.{0} (Fin d → Real)) (@Set.instMembership.{0} (Fin d → Real))
            (@ImbalancedChen.logPrimeMeshCell d (@Rat.cast.{0} Real Real.instRatCast a)
              (@Rat.cast.{0} Real Real.instRatCast b) m j)
            t)),
  @Eq.{1} Rat (@ImbalancedChen.historicalPrefixLookup d a b m J cap fallback t) fallback
```

## ImbalancedChen.historicalPrefixProject

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
{α : Type u_1} → {r d : Nat} → (hrd : @LE.le.{0} Nat instLENat r d) → (t : Fin d → α) → Fin r → α
```

## ImbalancedChen.historicalPrefixProject.congr_simp

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} {r d : Nat} (hrd : @LE.le.{0} Nat instLENat r d) (t t_1 : Fin d → α)
  (e_t : @Eq.{u_1 + 1} (Fin d → α) t t_1) (a a_1 : Fin r),
  @Eq.{1} (Fin r) a a_1 →
    @Eq.{u_1 + 1} α (@ImbalancedChen.historicalPrefixProject.{u_1} α r d hrd t a)
      (@ImbalancedChen.historicalPrefixProject.{u_1} α r d hrd t_1 a_1)
```

## ImbalancedChen.historicalPrefixProject.eq_1

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} {r d : Nat} (hrd : @LE.le.{0} Nat instLENat r d) (t : Fin d → α) (i : Fin r),
  @Eq.{u_1 + 1} α (@ImbalancedChen.historicalPrefixProject.{u_1} α r d hrd t i) (t (@Fin.castLE r d hrd i))
```

## ImbalancedChen.historicalPrefixProject_comp

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} {r d e : Nat} (hrd : @LE.le.{0} Nat instLENat r d) (hde : @LE.le.{0} Nat instLENat d e)
  (t : Fin e → α),
  @Eq.{u_1 + 1} (Fin r → α)
    (@ImbalancedChen.historicalPrefixProject.{u_1} α r d hrd
      (@ImbalancedChen.historicalPrefixProject.{u_1} α d e hde t))
    (@ImbalancedChen.historicalPrefixProject.{u_1} α r e (@LE.le.trans.{0} Nat Nat.instPreorder r d e hrd hde) t)
```

## ImbalancedChen.mem_logPrimeMeshCell_historicalPrefixProject

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {r d m : Nat} (hrd : @LE.le.{0} Nat instLENat r d) {a b : Real}
  {j :
    Fin d →
      Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {t : Fin d → Real}
  (ht :
    @Membership.mem.{0, 0} (Fin d → Real) (Set.{0} (Fin d → Real)) (@Set.instMembership.{0} (Fin d → Real))
      (@ImbalancedChen.logPrimeMeshCell d a b m j) t),
  @Membership.mem.{0, 0} (Fin r → Real) (Set.{0} (Fin r → Real)) (@Set.instMembership.{0} (Fin r → Real))
    (@ImbalancedChen.logPrimeMeshCell r a b m
      (@ImbalancedChen.historicalPrefixProject.{0}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) m
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        r d hrd j))
    (@ImbalancedChen.historicalPrefixProject.{0} Real r d hrd t)
```

## ImbalancedChen.primeHistoryLogCoordinates_eq_historicalPrefixProject

模块 `ImbalancedChen.HistoricalPrefixCertificate`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N : Real) {r d : Nat} (hrd : @LE.le.{0} Nat instLENat r d) {history : List.{0} Nat}
  (hlen : @Eq.{1} Nat (@List.length.{0} Nat history) d),
  @Eq.{1} (Fin r → Real)
    (ImbalancedChen.primeHistoryLogCoordinates N r (@ImbalancedChen.rosserAncestor.{0} Nat r history))
    (@ImbalancedChen.historicalPrefixProject.{0} Real r d hrd (ImbalancedChen.primeHistoryLogCoordinates N d history))
```

## ImbalancedChen.mem_ordinaryLowerFourFrontierTuples_iff

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (Q : Real) (N cap : Nat) (w z : Real) (p : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat),
  Iff
    (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat)
      (Finset.{0}
        (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          Nat))
      (@SetLike.instMembership.{0, 0}
        (Finset.{0}
          (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            Nat))
        (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          Nat)
        (@Finset.instSetLike.{0}
          (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            Nat)))
      (ImbalancedChen.firstExitFrontierTuples (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (ImbalancedChen.ordinaryParityRosserPolicy Bool.true Q) (ImbalancedChen.roughPrimeUniverse N cap w z))
      p)
    (And
      (@StrictAnti.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Nat
        (@PartialOrder.toPreorder.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@Fin.instPartialOrder (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
        Nat.instPreorder p)
      (And
        (∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
          And (@LT.lt.{0} Nat instLTNat (p i) cap)
            (And (Nat.Prime (p i))
              (And (Not (@Dvd.dvd.{0} Nat Nat.instDvd (p i) N))
                (And (@LE.le.{0} Real Real.instLE w (@Nat.cast.{0} Real Real.instNatCast (p i)))
                  (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (p i)) z)))))
        (@LT.lt.{0} Real Real.instLT
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@Nat.cast.{0} Real Real.instNatCast
              (p
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Nat.cast.{0} Real Real.instNatCast
                (p
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 1)
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (nat_lit 1)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          Q)))
```

## ImbalancedChen.mem_ordinaryLowerFourFrontierTuples_iff_log

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (N cap : Nat) (old w z : Real)
  (hN : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N)
  (hzcap : @LE.le.{0} Real Real.instLE z (@Nat.cast.{0} Real Real.instNatCast cap))
  (p : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat),
  Iff
    (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat)
      (Finset.{0}
        (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          Nat))
      (@SetLike.instMembership.{0, 0}
        (Finset.{0}
          (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            Nat))
        (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          Nat)
        (@Finset.instSetLike.{0}
          (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            Nat)))
      (ImbalancedChen.firstExitFrontierTuples (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (ImbalancedChen.ordinaryParityRosserPolicy Bool.true
          (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
            (@Nat.cast.{0} Real Real.instNatCast N) old))
        (ImbalancedChen.roughPrimeUniverse N cap w z))
      p)
    (And
      (@StrictAnti.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Nat
        (@PartialOrder.toPreorder.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@Fin.instPartialOrder (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
        Nat.instPreorder p)
      (And
        (∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
          And (Nat.Prime (p i))
            (And (Not (@Dvd.dvd.{0} Nat Nat.instDvd (p i) N))
              (And (@LE.le.{0} Real Real.instLE w (@Nat.cast.{0} Real Real.instNatCast (p i)))
                (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (p i)) z))))
        (@LT.lt.{0} Real Real.instLT
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@ImbalancedChen.actualPrimeTupleLog (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N p
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0))))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 3)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
              (@ImbalancedChen.actualPrimeTupleLog (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N p
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 1)
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1))))))
          old)))
```

## ImbalancedChen.mem_ordinaryLowerFourFrontierTuples_iff_of_cutoff_le_cap

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (Q : Real) (N cap : Nat) (w z : Real)
  (hzcap : @LE.le.{0} Real Real.instLE z (@Nat.cast.{0} Real Real.instNatCast cap))
  (p : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat),
  Iff
    (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat)
      (Finset.{0}
        (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          Nat))
      (@SetLike.instMembership.{0, 0}
        (Finset.{0}
          (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            Nat))
        (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          Nat)
        (@Finset.instSetLike.{0}
          (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            Nat)))
      (ImbalancedChen.firstExitFrontierTuples (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (ImbalancedChen.ordinaryParityRosserPolicy Bool.true Q) (ImbalancedChen.roughPrimeUniverse N cap w z))
      p)
    (And
      (@StrictAnti.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Nat
        (@PartialOrder.toPreorder.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@Fin.instPartialOrder (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
        Nat.instPreorder p)
      (And
        (∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
          And (Nat.Prime (p i))
            (And (Not (@Dvd.dvd.{0} Nat Nat.instDvd (p i) N))
              (And (@LE.le.{0} Real Real.instLE w (@Nat.cast.{0} Real Real.instNatCast (p i)))
                (@LT.lt.{0} Real Real.instLT (@Nat.cast.{0} Real Real.instNatCast (p i)) z))))
        (@LT.lt.{0} Real Real.instLT
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@Nat.cast.{0} Real Real.instNatCast
              (p
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Nat.cast.{0} Real Real.instNatCast
                (p
                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 1)
                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (nat_lit 1)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          Q)))
```

## ImbalancedChen.mem_ordinaryLowerFourGateRegion

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (old : Real) (t : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real),
  Iff
    (@Membership.mem.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
      (Set.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
      (@Set.instMembership.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real))
      (@ImbalancedChen.primeAffineGateRegion (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) ImbalancedChen.ordinaryLowerFourGateForms
        (ImbalancedChen.ordinaryLowerFourGateBounds old))
      t)
    (And
      (@StrictAnti.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real
        (@PartialOrder.toPreorder.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@Fin.instPartialOrder (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
        Real.instPreorder t)
      (@LT.lt.{0} Real Real.instLT
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (t
            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 3)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (t
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 1)
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1))))))
        old))
```

## ImbalancedChen.mem_ordinaryLowerFourGateRegion._simp_1_3

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {n : Nat}
  {P :
    Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      Prop},
  @Eq.{1} Prop
    (∀
      (i :
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      P i)
    (And
      (P
        (@OfNat.ofNat.{0}
          (Fin
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (nat_lit 0)
          (@Fin.instOfNat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@instNeZeroNatHAdd_1 n (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
            (nat_lit 0))))
      (∀ (i : Fin n), P (@Fin.succ n i)))
```

## ImbalancedChen.mem_ordinaryLowerFourGateRegion._simp_1_4

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {a b c : Prop}, @Eq.{1} Prop (And (And a b) c) (And a (And b c))
```

## ImbalancedChen.ordinaryLowerFourGateBounds

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
(old : Real) → Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real
```

## ImbalancedChen.ordinaryLowerFourGateBounds.eq_1

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (old : Real),
  @Eq.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
    (ImbalancedChen.ordinaryLowerFourGateBounds old)
    (@Matrix.vecCons.{0} Real (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@Matrix.vecCons.{0} Real (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@Matrix.vecCons.{0} Real (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@Matrix.vecCons.{0} Real (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) old
            (@Matrix.vecEmpty.{0} Real)))))
```

## ImbalancedChen.ordinaryLowerFourGateForms

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
  @ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
    (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
    (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
      @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
      fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
    Real (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
    Real.instAddCommMonoid
    (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
      Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
    (@Semiring.toModule.{0} Real Real.semiring)
```

## ImbalancedChen.ordinaryLowerFourGateForms._proof_1

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
@NeZero.{0} Nat (@Zero.ofOfNat0.{0} Nat (instOfNatNat (nat_lit 0)))
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.ordinaryLowerFourGateForms._proof_2

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
@ContinuousAdd.{0} Real
  (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
  (@Distrib.toAdd.{0} Real
    (@NonUnitalNonAssocSemiring.toDistrib.{0} Real
      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Real
        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Real
          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
            (@CommRing.toNonUnitalCommRing.{0} Real Real.commRing))))))
```

## ImbalancedChen.ordinaryLowerFourGateForms._proof_3

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
@SMulCommClass.{0, 0, 0} Real Real Real
  (@Algebra.toSMul.{0, 0} Real Real Real.instCommSemiring (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring)
    (@Algebra.id.{0} Real Real.instCommSemiring))
  (@instSMulOfMul.{0} Real
    (@Distrib.toMul.{0} Real
      (@instDistribOfSemiring.{0} Real (@CommSemiring.toSemiring.{0} Real Real.instCommSemiring))))
```

## ImbalancedChen.ordinaryLowerFourGateForms._proof_4

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
@ContinuousConstSMul.{0, 0} Real Real
  (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
  (@instSMulOfMul.{0} Real Real.instMul)
```

## ImbalancedChen.ordinaryLowerFourGateForms._proof_5

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
Nat.AtLeastTwo
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## ImbalancedChen.ordinaryLowerFourGateForms.eq_1

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
@Eq.{1}
  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    @ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
        fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
        @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
        fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
      Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      Real.instAddCommMonoid
      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
        Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
      (@Semiring.toModule.{0} Real Real.semiring))
  ImbalancedChen.ordinaryLowerFourGateForms
  (@Matrix.vecCons.{0}
    (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
        fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
        @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
        fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
      Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      Real.instAddCommMonoid
      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
        Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
      (@Semiring.toModule.{0} Real Real.semiring))
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (@HSub.hSub.{0, 0, 0}
      (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
          @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
        Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        Real.instAddCommMonoid
        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
          Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
          @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
        Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        Real.instAddCommMonoid
        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
          Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
          @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
        Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        Real.instAddCommMonoid
        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
          Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@instHSub.{0}
        (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
            @UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
          Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          Real.instAddCommMonoid
          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
            Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
          (@Semiring.toModule.{0} Real Real.semiring))
        (@ContinuousLinearMap.sub.{0, 0, 0, 0} Real Real.instRing Real Real.instRing
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
            @UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommGroup)
          Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          Real.instAddCommGroup
          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
            Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
          (@Semiring.toModule.{0} Real Real.semiring)
          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)) instIsTopologicalAddGroupReal))
      ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
          @ContinuousLinearMap.proj.{0, 0, 0} Real Real.semiring
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
            (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
            (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
              @Semiring.toModule.{0} Real Real.semiring)
            i)
        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 1)
          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            ImbalancedChen.ordinaryLowerFourGateForms._proof_1 (nat_lit 1))))
      ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
          @ContinuousLinearMap.proj.{0, 0, 0} Real Real.semiring
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
            (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
            (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
              @Semiring.toModule.{0} Real Real.semiring)
            i)
        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            ImbalancedChen.ordinaryLowerFourGateForms._proof_1 (nat_lit 0)))))
    (@Matrix.vecCons.{0}
      (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
          @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
        Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        Real.instAddCommMonoid
        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
          Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@HSub.hSub.{0, 0, 0}
        (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
            @UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
          Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          Real.instAddCommMonoid
          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
            Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
          (@Semiring.toModule.{0} Real Real.semiring))
        (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
            @UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
          Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          Real.instAddCommMonoid
          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
            Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
          (@Semiring.toModule.{0} Real Real.semiring))
        (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
            @UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
          Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          Real.instAddCommMonoid
          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
            Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
          (@Semiring.toModule.{0} Real Real.semiring))
        (@instHSub.{0}
          (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
            (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
            Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            Real.instAddCommMonoid
            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
              Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
            (@Semiring.toModule.{0} Real Real.semiring))
          (@ContinuousLinearMap.sub.{0, 0, 0, 0} Real Real.instRing Real Real.instRing
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommGroup)
            Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            Real.instAddCommGroup
            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
              Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
            (@Semiring.toModule.{0} Real Real.semiring)
            (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring)) instIsTopologicalAddGroupReal))
        ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
            @ContinuousLinearMap.proj.{0, 0, 0} Real Real.semiring
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
              (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                @UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
              (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                @Semiring.toModule.{0} Real Real.semiring)
              i)
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 2)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              ImbalancedChen.ordinaryLowerFourGateForms._proof_1 (nat_lit 2))))
        ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
            @ContinuousLinearMap.proj.{0, 0, 0} Real Real.semiring
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
              (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                @UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
              (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                @Semiring.toModule.{0} Real Real.semiring)
              i)
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 1)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              ImbalancedChen.ordinaryLowerFourGateForms._proof_1 (nat_lit 1)))))
      (@Matrix.vecCons.{0}
        (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
            @UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
          Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          Real.instAddCommMonoid
          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
            Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
          (@Semiring.toModule.{0} Real Real.semiring))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@HSub.hSub.{0, 0, 0}
          (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
            (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
            Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            Real.instAddCommMonoid
            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
              Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
            (@Semiring.toModule.{0} Real Real.semiring))
          (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
            (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
            Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            Real.instAddCommMonoid
            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
              Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
            (@Semiring.toModule.{0} Real Real.semiring))
          (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
            (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
            Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            Real.instAddCommMonoid
            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
              Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
            (@Semiring.toModule.{0} Real Real.semiring))
          (@instHSub.{0}
            (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
              (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                @UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
              Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              Real.instAddCommMonoid
              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real
                Real Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
              (@Semiring.toModule.{0} Real Real.semiring))
            (@ContinuousLinearMap.sub.{0, 0, 0, 0} Real Real.instRing Real Real.instRing
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
              (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                @UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@Pi.addCommGroup.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommGroup)
              Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              Real.instAddCommGroup
              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real
                Real Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
              (@Semiring.toModule.{0} Real Real.semiring)
              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
              instIsTopologicalAddGroupReal))
          ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
              @ContinuousLinearMap.proj.{0, 0, 0} Real Real.semiring
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                  @UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
                (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                  @Semiring.toModule.{0} Real Real.semiring)
                i)
            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 3)
              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                ImbalancedChen.ordinaryLowerFourGateForms._proof_1 (nat_lit 3))))
          ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
              @ContinuousLinearMap.proj.{0, 0, 0} Real Real.semiring
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                  @UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
                (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                  @Semiring.toModule.{0} Real Real.semiring)
                i)
            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 2)
              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                ImbalancedChen.ordinaryLowerFourGateForms._proof_1 (nat_lit 2)))))
        (@Matrix.vecCons.{0}
          (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
            (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
            (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
              @UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
            Real
            (@UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
            Real.instAddCommMonoid
            (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
              Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
            (@Semiring.toModule.{0} Real Real.semiring))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@HAdd.hAdd.{0, 0, 0}
            (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
              (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                @UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
              Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              Real.instAddCommMonoid
              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real
                Real Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
              (@Semiring.toModule.{0} Real Real.semiring))
            (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
              (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                @UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
              Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              Real.instAddCommMonoid
              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real
                Real Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
              (@Semiring.toModule.{0} Real Real.semiring))
            (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
              (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                @UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
              Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              Real.instAddCommMonoid
              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real
                Real Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
              (@Semiring.toModule.{0} Real Real.semiring))
            (@instHAdd.{0}
              (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
                (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                  fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                  @UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                  fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
                Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                Real.instAddCommMonoid
                (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real
                  Real Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
                (@Semiring.toModule.{0} Real Real.semiring))
              (@ContinuousLinearMap.add.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
                (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                  fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                  @UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                  fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
                Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                Real.instAddCommMonoid
                (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real
                  Real Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
                (@Semiring.toModule.{0} Real Real.semiring) ImbalancedChen.ordinaryLowerFourGateForms._proof_2))
            ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                @ContinuousLinearMap.proj.{0, 0, 0} Real Real.semiring
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                  (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                    @UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                    Real.instAddCommMonoid)
                  (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                    @Semiring.toModule.{0} Real Real.semiring)
                  i)
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  ImbalancedChen.ordinaryLowerFourGateForms._proof_1 (nat_lit 0))))
            (@HSMul.hSMul.{0, 0, 0} Real
              (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
                (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                  fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                  @UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                  fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
                Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                Real.instAddCommMonoid
                (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real
                  Real Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
                (@Semiring.toModule.{0} Real Real.semiring))
              (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
                (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                  fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                  @UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                  fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
                Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                Real.instAddCommMonoid
                (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real
                  Real Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
                (@Semiring.toModule.{0} Real Real.semiring))
              (@instHSMul.{0, 0} Real
                (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
                  (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                    @UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                    Real.instAddCommMonoid)
                  Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  Real.instAddCommMonoid
                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    Real Real Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
                  (@Semiring.toModule.{0} Real Real.semiring))
                (@ContinuousLinearMap.instSMul.{0, 0, 0, 0, 0} Real Real Real.semiring Real.semiring
                  (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
                  (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                    @UniformSpace.toTopologicalSpace.{0} Real
                      (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                    fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                    Real.instAddCommMonoid)
                  Real
                  (@UniformSpace.toTopologicalSpace.{0} Real
                    (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                  Real.instAddCommMonoid
                  (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    Real Real Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
                  (@Semiring.toModule.{0} Real Real.semiring) Real
                  (@instDistribSMul.{0} Real
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Real
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Real
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Real
                          (@CommRing.toNonUnitalCommRing.{0} Real Real.commRing)))))
                  ImbalancedChen.ordinaryLowerFourGateForms._proof_3
                  ImbalancedChen.ordinaryLowerFourGateForms._proof_4))
              (@OfNat.ofNat.{0} Real (nat_lit 3)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                  ImbalancedChen.ordinaryLowerFourGateForms._proof_5))
              ((fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                  @ContinuousLinearMap.proj.{0, 0, 0} Real Real.semiring
                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                    (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                      @UniformSpace.toTopologicalSpace.{0} Real
                        (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                    (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                      Real.instAddCommMonoid)
                    (fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                      @Semiring.toModule.{0} Real Real.semiring)
                    i)
                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 1)
                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    ImbalancedChen.ordinaryLowerFourGateForms._proof_1 (nat_lit 1))))))
          (@Matrix.vecEmpty.{0}
            (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
              (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
              (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
                @UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
              Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              Real.instAddCommMonoid
              (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real
                Real Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
              (@Semiring.toModule.{0} Real Real.semiring)))))))
```

## ImbalancedChen.ordinaryLowerFourGateForms_ne_zero

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (j : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
  @Ne.{1}
    (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
      (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
      (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
        fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
        @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
        fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
      Real
      (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
      Real.instAddCommMonoid
      (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
        Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
      (@Semiring.toModule.{0} Real Real.semiring))
    (ImbalancedChen.ordinaryLowerFourGateForms j)
    (@OfNat.ofNat.{0}
      (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
        (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
        (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
          @UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
        Real
        (@UniformSpace.toTopologicalSpace.{0} Real (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
        Real.instAddCommMonoid
        (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
          Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
        (@Semiring.toModule.{0} Real Real.semiring))
      (nat_lit 0)
      (@Zero.toOfNat0.{0}
        (@ContinuousLinearMap.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
            @UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
          Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          Real.instAddCommMonoid
          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
            Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
          (@Semiring.toModule.{0} Real Real.semiring))
        (@ContinuousLinearMap.zero.{0, 0, 0, 0} Real Real Real.semiring Real.semiring
          (@RingHom.id.{0} Real (@Semiring.toNonAssocSemiring.{0} Real Real.semiring))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Real)
          (@Pi.topologicalSpace.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) =>
            @UniformSpace.toTopologicalSpace.{0} Real
              (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real)
            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) => Real.instAddCommMonoid)
          Real
          (@UniformSpace.toTopologicalSpace.{0} Real
            (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
          Real.instAddCommMonoid
          (@Pi.Function.module.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Real Real
            Real.semiring Real.instAddCommMonoid (@Semiring.toModule.{0} Real Real.semiring))
          (@Semiring.toModule.{0} Real Real.semiring))))
```

## ImbalancedChen.ordinaryLowerFour_cube_test_iff_log

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {N : Nat} (hN : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) N) (old : Real)
  (p : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat)
  (hpos :
    ∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (p i)),
  Iff
    (@LT.lt.{0} Real Real.instLT
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Nat.cast.{0} Real Real.instNatCast
          (p
            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)))))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@Nat.cast.{0} Real Real.instNatCast
            (p
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 1)
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
        (@Nat.cast.{0} Real Real.instNatCast N) old))
    (@LT.lt.{0} Real Real.instLT
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@ImbalancedChen.actualPrimeTupleLog (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N p
          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 3)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          (@ImbalancedChen.actualPrimeTupleLog (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N p
            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 1)
              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1))))))
      old)
```

## ImbalancedChen.ordinaryLowerFour_parent_valid_iff

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (Q : Real) (p : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) → Nat)
  (hprime : ∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))), Nat.Prime (p i))
  (hsort :
    @StrictAnti.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) Nat
      (@PartialOrder.toPreorder.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@Fin.instPartialOrder (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      Nat.instPreorder p),
  Iff
    (@ImbalancedChen.FirstExitValidSelection.{0} Nat (ImbalancedChen.ordinaryParityRosserPolicy Bool.true Q)
      (@List.nil.{0} Nat) Bool.true
      (@List.dropLast.{0} Nat (@List.ofFn.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) p)))
    (@LT.lt.{0} Real Real.instLT
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Nat.cast.{0} Real Real.instNatCast
          (p
            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)))))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@Nat.cast.{0} Real Real.instNatCast
            (p
              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 1)
                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      Q)
```

## ImbalancedChen.ordinaryRosserPrefixAdmissible_lower_two_iff

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (Q : Real) (p1 p2 : Nat)
  (h2 : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p2)
  (h21 : @LT.lt.{0} Nat instLTNat p2 p1),
  Iff
    (ImbalancedChen.ordinaryRosserPrefixAdmissible Bool.true Q
      (@List.cons.{0} Nat p2 (@List.cons.{0} Nat p1 (@List.nil.{0} Nat))))
    (@LT.lt.{0} Real Real.instLT
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Nat.cast.{0} Real Real.instNatCast p1)
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@Nat.cast.{0} Real Real.instNatCast p2) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      Q)
```

## _private.ImbalancedChen.OrdinaryLowerFourFrontier.0.ImbalancedChen.lowerRosserAdmissibleSet_two_iff

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (Q : Real) (p1 p2 : Nat) (h21 : @LT.lt.{0} Nat instLTNat p2 p1),
  Iff
    (MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.LowerAdmissibleSet Q
      (@List.toFinset.{0} Nat instDecidableEqNat (@List.cons.{0} Nat p2 (@List.cons.{0} Nat p1 (@List.nil.{0} Nat)))))
    (@LT.lt.{0} Real Real.instLT
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Nat.cast.{0} Real Real.instNatCast p1)
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@Nat.cast.{0} Real Real.instNatCast p2) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      Q)
```

## _private.ImbalancedChen.OrdinaryLowerFourFrontier.0.ImbalancedChen.lowerRosserAdmissibleSet_two_iff._proof_1_4

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (p1 p2 : Nat) (h21 : @LT.lt.{0} Nat instLTNat p2 p1) (p : Nat),
  Not (Iff (And (Or (@Eq.{1} Nat p p2) (@Eq.{1} Nat p p1)) (@LE.le.{0} Nat instLENat p1 p)) (@Eq.{1} Nat p p1)) → False
```

## _private.ImbalancedChen.OrdinaryLowerFourFrontier.0.ImbalancedChen.lowerRosserAdmissibleSet_two_iff._proof_1_5

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (p1 p2 : Nat) (h21 : @LT.lt.{0} Nat instLTNat p2 p1) (p : Nat),
  Not
      (Iff (And (Or (@Eq.{1} Nat p p2) (@Eq.{1} Nat p p1)) (@LE.le.{0} Nat instLENat p2 p))
        (Or (@Eq.{1} Nat p p2) (@Eq.{1} Nat p p1))) →
    False
```

## _private.ImbalancedChen.OrdinaryLowerFourFrontier.0.ImbalancedChen.lowerRosserAdmissibleSet_two_iff._simp_1_1

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : @DecidablePred.{u_1 + 1} α p] {s : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.filter.{u_1} α p inst s) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (p a))
```

## _private.ImbalancedChen.OrdinaryLowerFourFrontier.0.ImbalancedChen.lowerRosserAdmissibleSet_two_iff._simp_1_2

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] {s : Finset.{u_1} α} {a b : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Insert.insert.{u_1, u_1} α (Finset.{u_1} α) (@Finset.instInsert.{u_1} α inst) b s) a)
    (Or (@Eq.{u_1 + 1} α a b)
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a))
```

## _private.ImbalancedChen.OrdinaryLowerFourFrontier.0.ImbalancedChen.lowerRosserAdmissibleSet_two_iff._simp_1_3

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} {a b : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Singleton.singleton.{u_1, u_1} α (Finset.{u_1} α) (@Finset.instSingleton.{u_1} α) a) b)
    (@Eq.{u_1 + 1} α b a)
```

## _private.ImbalancedChen.OrdinaryLowerFourFrontier.0.ImbalancedChen.lowerRosserAdmissibleSet_two_iff._simp_1_6

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] (a : α) (s : Finset.{u_1} α) (p : α → Prop),
  @Eq.{1} Prop
    (∀ (x : α),
      @Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
          (@Insert.insert.{u_1, u_1} α (Finset.{u_1} α) (@Finset.instInsert.{u_1} α inst) a s) x →
        p x)
    (And (p a)
      (∀ (x : α),
        @Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
            (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s x →
          p x))
```

## _private.ImbalancedChen.OrdinaryLowerFourFrontier.0.ImbalancedChen.lowerRosserAdmissibleSet_two_iff._simp_1_7

模块 `ImbalancedChen.OrdinaryLowerFourFrontier`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Sort u_1} {p : α → Prop} {a' : α}, @Eq.{1} Prop (∀ (a : α), @Eq.{u_1} α a a' → p a) (p a')
```

## ImbalancedChen.part3IntervalAPCount

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
(L U q a : Nat) → Nat
```

## ImbalancedChen.part3IntervalAPCount.eq_1

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (L U q a : Nat),
  @Eq.{1} Nat (ImbalancedChen.part3IntervalAPCount L U q a)
    (@Finset.card.{0} Nat
      (@Finset.filter.{0} Nat (fun (n : Nat) => Nat.ModEq q n a) (fun (a_1 : Nat) => @Nat.instDecidableModEq q a_1 a)
        (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder L U)))
```

## ImbalancedChen.part3IntervalAPCount_abs_sub_le_two

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (L U q a b : Nat) (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.part3IntervalAPCount L U q a))
        (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.part3IntervalAPCount L U q b))))
    (@OfNat.ofNat.{0} Real (nat_lit 2)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
```

## ImbalancedChen.part3IntervalAPCount_coprimeMean_error

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (L U q a : Nat) (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.part3IntervalAPCount L U q a))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.part3IntervalCoprimeCount L U q))
          (@Nat.cast.{0} Real Real.instNatCast (Nat.totient q)))))
    (@OfNat.ofNat.{0} Real (nat_lit 2)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
```

## ImbalancedChen.part3IntervalAPCount_le_add_two

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (L U q a b : Nat) (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q),
  @LE.le.{0} Nat instLENat (ImbalancedChen.part3IntervalAPCount L U q a)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ImbalancedChen.part3IntervalAPCount L U q b)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
```

## ImbalancedChen.part3IntervalAPCount_le_add_two._proof_1_1

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (L U q a b : Nat)
  (hU :
    @LE.le.{0} Nat instLENat
      (@Nat.count (fun (n : Nat) => Nat.ModEq q n a) (fun (a_1 : Nat) => @Nat.instDecidableModEq q a_1 a) U)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@Nat.count (fun (n : Nat) => Nat.ModEq q n b) (fun (a : Nat) => @Nat.instDecidableModEq q a b) U)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (hL :
    @LE.le.{0} Nat instLENat
      (@Nat.count (fun (n : Nat) => Nat.ModEq q n b) (fun (a : Nat) => @Nat.instDecidableModEq q a b) L)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@Nat.count (fun (n : Nat) => Nat.ModEq q n a) (fun (a_1 : Nat) => @Nat.instDecidableModEq q a_1 a) L)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (ha :
    @LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
      (@Nat.count (fun (n : Nat) => Nat.ModEq q n a) (fun (a_1 : Nat) => @Nat.instDecidableModEq q a_1 a) L)
      (@Nat.count (fun (n : Nat) => Nat.ModEq q n a) (fun (a_1 : Nat) => @Nat.instDecidableModEq q a_1 a) U))
  (hb :
    @LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder)
      (@Nat.count (fun (n : Nat) => Nat.ModEq q n b) (fun (a : Nat) => @Nat.instDecidableModEq q a b) L)
      (@Nat.count (fun (n : Nat) => Nat.ModEq q n b) (fun (a : Nat) => @Nat.instDecidableModEq q a b) U)),
  Not
      (@LE.le.{0} Nat instLENat
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Nat.count (fun (n : Nat) => Nat.ModEq q n a) (fun (a_1 : Nat) => @Nat.instDecidableModEq q a_1 a) U)
          (@Nat.count (fun (n : Nat) => Nat.ModEq q n a) (fun (a_1 : Nat) => @Nat.instDecidableModEq q a_1 a) L))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@Nat.count (fun (n : Nat) => Nat.ModEq q n b) (fun (a : Nat) => @Nat.instDecidableModEq q a b) U)
            (@Nat.count (fun (n : Nat) => Nat.ModEq q n b) (fun (a : Nat) => @Nat.instDecidableModEq q a b) L))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
    False
```

## ImbalancedChen.part3IntervalAPCount_le_add_two._proof_1_3

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (L U q : Nat) (hLU : Not (@LE.le.{0} Nat instLENat L U)), Not (@LE.le.{0} Nat instLENat U L) → False
```

## ImbalancedChen.part3IntervalCoprimeCount

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
(L U q : Nat) → Nat
```

## ImbalancedChen.part3IntervalCoprimeCount.eq_1

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (L U q : Nat),
  @Eq.{1} Nat (ImbalancedChen.part3IntervalCoprimeCount L U q)
    (@Finset.card.{0} Nat
      (@Finset.filter.{0} Nat (fun (n : Nat) => Nat.Coprime q n) (Nat.instDecidableCoprime q)
        (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder L U)))
```

## ImbalancedChen.part3IntervalCoprimeCount_eq_sum

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (L U q : Nat) (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q),
  @Eq.{1} Nat (ImbalancedChen.part3IntervalCoprimeCount L U q)
    (@Finset.sum.{0, 0} Nat Nat Nat.instAddCommMonoid
      (@Finset.filter.{0} Nat (fun (a : Nat) => Nat.Coprime q a) (Nat.instDecidableCoprime q) (Finset.range q))
      fun (a : Nat) => ImbalancedChen.part3IntervalAPCount L U q a)
```

## ImbalancedChen.part3IntervalCoprimeCount_eq_sum._simp_1_1

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : @DecidablePred.{u_1 + 1} α p] {s : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.filter.{u_1} α p inst s) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (p a))
```

## ImbalancedChen.part3LongSlotAPCount

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
(L U q a m : Nat) → Nat
```

## ImbalancedChen.part3LongSlotAPCount.eq_1

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (L U q a m : Nat),
  @Eq.{1} Nat (ImbalancedChen.part3LongSlotAPCount L U q a m)
    (@Finset.card.{0} Nat
      (@Finset.filter.{0} Nat
        (fun (n : Nat) => Nat.ModEq q (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) m n) a)
        (fun (a_1 : Nat) =>
          @Nat.instDecidableModEq q (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) m a_1) a)
        (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder L U)))
```

## ImbalancedChen.part3LongSlotCoprimeCount

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
(L U q m : Nat) → Nat
```

## ImbalancedChen.part3LongSlotCoprimeCount.eq_1

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (L U q m : Nat),
  @Eq.{1} Nat (ImbalancedChen.part3LongSlotCoprimeCount L U q m)
    (@Finset.card.{0} Nat
      (@Finset.filter.{0} Nat
        (fun (n : Nat) => Nat.Coprime (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) m n) q)
        (fun (a : Nat) =>
          Nat.instDecidableCoprime (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) m a) q)
        (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder L U)))
```

## ImbalancedChen.part3LongSlotRemainder

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
(L U q a m : Nat) → Real
```

## ImbalancedChen.part3LongSlotRemainder.eq_1

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (L U q a m : Nat),
  @Eq.{1} Real (ImbalancedChen.part3LongSlotRemainder L U q a m)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.part3LongSlotAPCount L U q a m))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@Nat.cast.{0} Real Real.instNatCast (ImbalancedChen.part3LongSlotCoprimeCount L U q m))
        (@Nat.cast.{0} Real Real.instNatCast (Nat.totient q))))
```

## ImbalancedChen.part3LongSlotRemainder_abs_le_two

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (L U q a m : Nat) (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q)
  (ha : Nat.Coprime a q),
  @LE.le.{0} Real Real.instLE
    (@abs.{0} Real Real.lattice Real.instAddGroup (ImbalancedChen.part3LongSlotRemainder L U q a m))
    (@OfNat.ofNat.{0} Real (nat_lit 2)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
```

## ImbalancedChen.part3LongSlotRemainder_eq_zero_of_not_coprime

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (L U q a m : Nat) (ha : Nat.Coprime a q) (hm : Not (Nat.Coprime m q)),
  @Eq.{1} Real (ImbalancedChen.part3LongSlotRemainder L U q a m)
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
```

## ImbalancedChen.part3LongSlotSignedError

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
(S Q : Finset.{0} Nat) → (α ρ : Nat → Complex) → (L U a : Nat) → Complex
```

## ImbalancedChen.part3LongSlotSignedError_norm_le

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (S Q : Finset.{0} Nat) (α ρ : Nat → Complex) (L U a : Nat)
  (hq :
    ∀ (q : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) Q q →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q)
  (ha :
    ∀ (q : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) Q q →
        Nat.Coprime a q),
  @LE.le.{0} Real Real.instLE
    (@Norm.norm.{0} Complex Complex.instNorm (ImbalancedChen.part3LongSlotSignedError S Q α ρ L U a))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid S fun (m : Nat) =>
          @Norm.norm.{0} Complex Complex.instNorm (α m)))
      (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid Q fun (q : Nat) =>
        @Norm.norm.{0} Complex Complex.instNorm (ρ q)))
```

## ImbalancedChen.part3LongSlotSignedError_norm_le_box

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (M D L U a : Nat) (α ρ : Nat → Complex)
  (hα :
    ∀ (m : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
          (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M)
          m →
        @LE.le.{0} Real Real.instLE (@Norm.norm.{0} Complex Complex.instNorm (α m))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hρ :
    ∀ (q : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
          (@Finset.filter.{0} Nat (fun (q : Nat) => Nat.Coprime a q) (Nat.instDecidableCoprime a)
            (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) D))
          q →
        @LE.le.{0} Real Real.instLE (@Norm.norm.{0} Complex Complex.instNorm (ρ q))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @LE.le.{0} Real Real.instLE
    (@Norm.norm.{0} Complex Complex.instNorm
      (ImbalancedChen.part3LongSlotSignedError
        (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M)
        (@Finset.filter.{0} Nat (fun (q : Nat) => Nat.Coprime a q) (Nat.instDecidableCoprime a)
          (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) D))
        α ρ L U a))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@Nat.cast.{0} Real Real.instNatCast M))
      (@Nat.cast.{0} Real Real.instNatCast D))
```

## ImbalancedChen.part3LongSlotSignedError_norm_le_card

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (S Q : Finset.{0} Nat) (α ρ : Nat → Complex) (L U a : Nat)
  (hq :
    ∀ (q : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) Q q →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q)
  (ha :
    ∀ (q : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) Q q →
        Nat.Coprime a q)
  (hα :
    ∀ (m : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) S m →
        @LE.le.{0} Real Real.instLE (@Norm.norm.{0} Complex Complex.instNorm (α m))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hρ :
    ∀ (q : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) Q q →
        @LE.le.{0} Real Real.instLE (@Norm.norm.{0} Complex Complex.instNorm (ρ q))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @LE.le.{0} Real Real.instLE
    (@Norm.norm.{0} Complex Complex.instNorm (ImbalancedChen.part3LongSlotSignedError S Q α ρ L U a))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat S)))
      (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} Nat Q)))
```

## ImbalancedChen.part3LongSlotSignedError_norm_le_of_mass

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (S Q : Finset.{0} Nat) (α ρ : Nat → Complex) (L U a : Nat) (M D : Real)
  (hq :
    ∀ (q : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) Q q →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q)
  (ha :
    ∀ (q : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) Q q →
        Nat.Coprime a q)
  (hM :
    @LE.le.{0} Real Real.instLE
      (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid S fun (m : Nat) =>
        @Norm.norm.{0} Complex Complex.instNorm (α m))
      M)
  (hD :
    @LE.le.{0} Real Real.instLE
      (@Finset.sum.{0, 0} Nat Real Real.instAddCommMonoid Q fun (q : Nat) =>
        @Norm.norm.{0} Complex Complex.instNorm (ρ q))
      D),
  @LE.le.{0} Real Real.instLE
    (@Norm.norm.{0} Complex Complex.instNorm (ImbalancedChen.part3LongSlotSignedError S Q α ρ L U a))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        M)
      D)
```

## _private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_Ico_filter_card_sub

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (L U : Nat) (hLU : @LE.le.{0} Nat instLENat L U) (P : Nat → Prop) [inst : @DecidablePred.{1} Nat P],
  @Eq.{1} Nat
    (@Finset.card.{0} Nat
      (@Finset.filter.{0} Nat P inst (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder L U)))
    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@Nat.count P inst U) (@Nat.count P inst L))
```

## _private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_Ico_filter_card_sub._proof_1_5

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (L U n : Nat),
  Not
      (Iff
        (And (@LE.le.{0} Nat (@Preorder.toLE.{0} Nat Nat.instPreorder) L n)
          (@LT.lt.{0} Nat (@Preorder.toLT.{0} Nat Nat.instPreorder) n U))
        (And (@LT.lt.{0} Nat instLTNat n U) (Not (@LT.lt.{0} Nat instLTNat n L)))) →
    False
```

## _private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_Ico_filter_card_sub._simp_1_1

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} {p : α → Prop} [inst : @DecidablePred.{u_1 + 1} α p] {s : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.filter.{u_1} α p inst s) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (p a))
```

## _private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_Ico_filter_card_sub._simp_1_2

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} [inst : Preorder.{u_1} α] [inst_1 : @LocallyFiniteOrder.{u_1} α inst] {a b x : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@Finset.Ico.{u_1} α inst inst_1 a b) x)
    (And (@LE.le.{u_1} α (@Preorder.toLE.{u_1} α inst) a x) (@LT.lt.{u_1} α (@Preorder.toLT.{u_1} α inst) x b))
```

## _private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_Ico_filter_card_sub._simp_1_3

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {α : Type u_1} [inst : DecidableEq.{u_1 + 1} α] {s t : Finset.{u_1} α} {a : α},
  @Eq.{1} Prop
    (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
      (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α))
      (@SDiff.sdiff.{u_1} (Finset.{u_1} α) (@Finset.instSDiff.{u_1} α inst) s t) a)
    (And
      (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
        (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) s a)
      (Not
        (@Membership.mem.{u_1, u_1} α (Finset.{u_1} α)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} α) α (@Finset.instSetLike.{u_1} α)) t a)))
```

## _private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_Ico_filter_card_sub._simp_1_4

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ {n m : Nat},
  @Eq.{1} Prop
    (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) (Finset.range n) m)
    (@LT.lt.{0} Nat instLTNat m n)
```

## _private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_prefix_count_le_add_one

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (U q a b : Nat) (hq : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q),
  @LE.le.{0} Nat instLENat
    (@Nat.count (fun (n : Nat) => Nat.ModEq q n a) (fun (a_1 : Nat) => @Nat.instDecidableModEq q a_1 a) U)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@Nat.count (fun (n : Nat) => Nat.ModEq q n b) (fun (a : Nat) => @Nat.instDecidableModEq q a b) U)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
```

## _private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_prefix_count_le_add_one._proof_1_1

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (U q a b : Nat),
  Not
      (@LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) U q)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) U q)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    False
```

## _private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_prefix_count_le_add_one._proof_1_2

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (U q a b : Nat),
  Not
      (@LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) U q)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) U q)
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    False
```

## _private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_prefix_count_le_add_one._proof_1_3

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (U q a b : Nat),
  Not
      (@LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) U q)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) U q)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    False
```

## _private.ImbalancedChen.Part3LongSlotDistribution.0.ImbalancedChen.part3_prefix_count_le_add_one._proof_1_4

模块 `ImbalancedChen.Part3LongSlotDistribution`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (U q a b : Nat),
  Not
      (@LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) U q)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) U q)
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    False
```

## ImbalancedChen.part3_eventually_longSlot_logAccuracy

模块 `ImbalancedChen.Part3LongSlotNormalization`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (theta : Real)
  (htheta : @LT.lt.{0} Real Real.instLT theta (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (K : Nat) (epsilon : Real)
  (hepsilon :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon),
  @Filter.Eventually.{0} Nat
    (fun (N : Nat) =>
      ∀ (M D L U a : Nat) (alpha rho : Nat → Complex),
        @LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Nat.cast.{0} Real Real.instNatCast M) (@Nat.cast.{0} Real Real.instNatCast D))
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (@Nat.cast.{0} Real Real.instNatCast N) theta) →
          (∀ (m : Nat),
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                  (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M)
                  m →
                @LE.le.{0} Real Real.instLE (@Norm.norm.{0} Complex Complex.instNorm (alpha m))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
            (∀ (q : Nat),
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    (@Finset.filter.{0} Nat (fun (q : Nat) => Nat.Coprime a q) (Nat.instDecidableCoprime a)
                      (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) D))
                    q →
                  @LE.le.{0} Real Real.instLE (@Norm.norm.{0} Complex Complex.instNorm (rho q))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
              @LE.le.{0} Real Real.instLE
                (@Norm.norm.{0} Complex Complex.instNorm
                  (ImbalancedChen.part3LongSlotSignedError
                    (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M)
                    (@Finset.filter.{0} Nat (fun (q : Nat) => Nat.Coprime a q) (Nat.instDecidableCoprime a)
                      (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) D))
                    alpha rho L U a))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon
                    (@Nat.cast.{0} Real Real.instNatCast N))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                    (Real.log (@Nat.cast.{0} Real Real.instNatCast N)) K)))
    (@Filter.atTop.{0} Nat Nat.instPreorder)
```

## ImbalancedChen.part3_eventually_longSlot_singularNormalization

模块 `ImbalancedChen.Part3LongSlotNormalization`；格式 `PP_ALL_COMPLETE`。

```lean
∀ (theta : Real)
  (htheta : @LT.lt.{0} Real Real.instLT theta (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (epsilon : Real)
  (hepsilon :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon),
  @Filter.Eventually.{0} Nat
    (fun (N : Nat) =>
      ∀ (M D L U a : Nat) (alpha rho : Nat → Complex),
        @LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Nat.cast.{0} Real Real.instNatCast M) (@Nat.cast.{0} Real Real.instNatCast D))
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (@Nat.cast.{0} Real Real.instNatCast N) theta) →
          (∀ (m : Nat),
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                  (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M)
                  m →
                @LE.le.{0} Real Real.instLE (@Norm.norm.{0} Complex Complex.instNorm (alpha m))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
            (∀ (q : Nat),
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                    (@Finset.filter.{0} Nat (fun (q : Nat) => Nat.Coprime a q) (Nat.instDecidableCoprime a)
                      (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) D))
                    q →
                  @LE.le.{0} Real Real.instLE (@Norm.norm.{0} Complex Complex.instNorm (rho q))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
              @LE.le.{0} Real Real.instLE
                (@Norm.norm.{0} Complex Complex.instNorm
                  (ImbalancedChen.part3LongSlotSignedError
                    (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M)
                    (@Finset.filter.{0} Nat (fun (q : Nat) => Nat.Coprime a q) (Nat.instDecidableCoprime a)
                      (@Finset.Icc.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) D))
                    alpha rho L U a))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon
                  (ImbalancedChen.singularNormalization N)))
    (@Filter.atTop.{0} Nat Nat.instPreorder)
```
