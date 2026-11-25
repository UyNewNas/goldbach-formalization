# P2.9: exact marked-prime-product fibre extraction

**Status: SOURCE_ONLY_UNCOMPILED. New mathematical, formal and kernel credit: 0.**

This package mechanically extracts the already written labelled-prime-product fibre bound into `ImbalancedChen.P2MarkedPrimeProductFibreCore`. It supplies the same original tuple definitions and public theorem to the radial tuple-count module without importing the unrelated full P5z analytic owner.

No estimate is reproved or weakened. Every transferred definition/proof block is copied byte-for-byte from its pinned original source. The public names remain:

- `ImbalancedChen.Part3.labelledPrimeTuples`
- `ImbalancedChen.Part3.labelledProduct`
- `ImbalancedChen.p5z_marked_prime_product_fibre_card_le`

The original private `p5z_prime_dvd_tuple_exists` helper is also copied verbatim. Its generated private name belongs to the new module, so its private FQN and compiled term ownership change. This package does not claim private-name or compiled-object identity.

## Reason for the dependency change

The original P5z source and its producer outputs had been located and bound. Its actual full import setup contains 9,572 modules and 44,328 output parts, with 24,504 parts outside the currently bound receiving context, including older Suzuki/native modules. The verification agent stopped that broad route instead of treating the original public theorem receipt as a complete receiving-closure receipt.

The radial consumer only needs two finite tuple definitions, one elementary private prime-divisor helper, and one finite fibre bound. Those blocks use standard Mathlib alone. The new core separates precisely that already existing mathematics; it does not reconstruct or qualify the unrelated original analytic closure.

The existing three accepted thin modules `FrozenConstants`, `RadialRoughMass`, and `PrimeDivisorFloorCore` remain byte-for-byte unchanged.

## Exact sources and transferred blocks

The original repository checkpoint is
`UyNewNas/goldbach-formalization@a929011ec95843553fc2e10b7291c8077e0952c0`.

| Original owner | Pinned blob | Original SHA256 |
| --- | --- | --- |
| `ImbalancedChen/Part3DistributionTargets.lean` | `178e0fa5acc4f1c5b77b1ff0a3d6b933c9ef3fe6` | `a0b43f877bb7bcdf7606e19281521a0165538c08c0495a2a3e2d58b66aeb08cc` |
| `ImbalancedChen/P5zMarkedPrimeFamilyMultiplicity.lean` | `c23692b7758ff09cb167fd45b21abe1d4a059e49` | `0c543de77f2436116a663d65af071f69b4be6759ae01c0c6228cb6e02c493c6f` |
| Existing radial tuple-count candidate | `11cadab32aa9230b17a8e54d8cdf0724c0c90bb4` | `4d3eefb216875f28876f0eddba415bec1bf3080789a6dd7a3e84cccfb223aae2` |

The complete private/public fibre proof region, including its original comments, is transferred. Its public declaration with a single terminal newline has SHA256
`cfc3ded8dcf6aad37c15bb48d56649663b0835f117e1db2a099c06de3ab1fb03`,
matching the previously inspected original proof block. The exact copied block, including its two original trailing newlines, has SHA256
`56935fc9c997a30bb66478d5650cfc033782f18dbe12c3e98371e068ebaba9c7`.
Both normalizations are registered to avoid conflating a delimiter difference with a proof change.

The two tuple definitions retain every slot and repeated prime; the fibre bound remains `rank ^ rank`, including rank zero. There is no injection claim for the product map, squarefree restriction, nonzero-rank hypothesis, new target premise, or changed numerical bound.

## Imports and source routing

The core has exactly four imports, all from the fixed standard Mathlib pin
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`:

```lean
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.GroupWithZero.Basic
```

The pinned `Associated` source itself uses `dvd_prod_of_mem`; `Fintype.BigOperators` supplies the constant-Pi cardinality lemma; `GroupWithZero.Basic` contains `pow_le_pow_left₀`. The imports were statically read against that pin. The list is a small explicit standard-library boundary, not a claim that every redundant transitive standard-library import has been eliminated.

The initial consumer extraction changes this one import:

```diff
-import ImbalancedChen.P5zMarkedPrimeFamilyMultiplicity
+import ImbalancedChen.P2MarkedPrimeProductFibreCore
```

The initial postimage `455fce3476aa7c8230a7afb726a8d02a223bde61` preserves every other byte. The currently selected postimage `de40d26b7be3b5287e3c4362fee35b73b79f0e74` additionally removes the unused `Wu2008DoubleSieve` item from one `open` command after the first actual normal build exposed it. All imports and every declaration/proof block are unchanged by this header repair. The current postimage stages to the original module path.

## Owner postimages and reversibility

Both original owners have exact preimages and postimages in this package.

- `Part3DistributionTargets`: remove only the contiguous two-definition region and add the new core import.
- `P5zMarkedPrimeFamilyMultiplicity`: remove only the contiguous private/public proof region and add the new core import.
- `RadialTupleCount`: replace the one import above; the recorded normal-build repair also removes only the now-unavailable, unused `Wu2008DoubleSieve` namespace from its `open` header.

Removing the new owner import and reinserting the exact original region at the registered offset reconstructs each original owner byte-for-byte. Restoring the removed `open` namespace and replacing the consumer import back reconstructs its exact original preimage. The original P5z final CRLF is preserved in its postimage.

When a broader closure contains either original owner together with this core, it must select the registered owner postimage, so each original public FQN is declared exactly once. The thin radial closure imports the new core directly and does not need to load either heavy owner. The owner postimages themselves are source-only compatibility candidates; this package does not claim their heavy import closures have been revalidated.

## First normal-build result and minimal header repair

The verification agent's `job_f761e0d8b28e47369e915aa7d21f3347` completed runtime/stock preflights. The exact thin core compiled normally. TupleCount then failed first at line 17 with `unknown namespace Wu2008DoubleSieve`. That invalidated its combined `open` command and caused the subsequent unqualified Finset/Buchstab names to fail. Kernel/full-owned gates had not begun.

The thin imports no longer declare that unrelated namespace. The source contains it once, only in the header, so the repair deletes that item without importing any older native owner. All declarations, statements, proof bodies, and the three imports are byte-identical to the initial postimage. A reverse one-line reconstruction of the initial postimage passes.

The complete first-attempt task stdout is Git blob `7591bf7b001f49b0c271ad3ffff57aff0e1db074`, SHA256 `3c8b17e73f5ae076908db36abd66b3a97c84c9e9e8280b6145b3dcd5856b566c`. It is full task output containing the normal-build diagnostic, not a claim of standalone normal-build.log byte identity. `TUPLE_HEADER_REPAIR.json` records the exact failed and repaired sources. The repaired consumer still requires actual revalidation; the successful core normal build alone gives no completed package or kernel credit.

## Duplicate check and verification boundary

The check inspected the untruncated original active tree (3,734 entries), the untruncated original source-only tree (9,575 entries), the current P2.9 branch delta already inspected for the aggregate package, and the existing fibre producer source. No corresponding thin core was found. The superficially similar active `FinitePrimeGeometryCore` was read and does not provide these Part3 tuple definitions or this fibre theorem. Empty default-branch text-search results were not treated as complete evidence by themselves.

All new Lean blobs were read back and SHA256-checked. The extraction and reverse reconstruction were checked in pure text before upload. Independent static review confirmed the namespaces, public FQNs, imports and private-owner boundary. No compilation or kernel check was run by the author.

The new core must receive its own normal compilation, named kernel checks, full-owned audit including its new private/generated names, and the required stock/runtime gates. The consumer must then be checked with the coherent thin input context. Those gates are assigned to the verification agent. Existing P5z public-export receipts are not silently promoted to a full-owned audit of the new module.

Only immutable Git blobs are created here. No active tree, commit, branch or ref is modified. `REGISTRY.json` records every source blob, source hash, transferred block and stage path. All credits remain zero until a separate accepted verification record says otherwise.


## Current consumer after the second normal attempt

Task `job_94fee3051ee845f09ae6a923c80df0b3` completed after 23.435 seconds and stopped at the TupleCount normal build. The unused namespace issue was resolved; the remaining error was the unconstrained codomain of `Nat.cast_nonneg` in `Finset.single_le_sum`.

The current consumer is blob `56572a3ad02bb9c35c535d87800b164542cd3d2f`, SHA256 `20d878534ba9e3fea689a605759e6a349ff3efa675ce54cf7a4e3ca265ac50c2`, 6,153 bytes / 128 lines. It adds only the explicit Fin index and Real cast to that proof step; theorem statements, imports and every other proof body are unchanged. The root readback and reverse byte check are in `TUPLE_REAL_CAST_REPAIR.json`.

Third validation task `job_99911fbda6b14d228ebc653cb2654cd7` permits normal source compilation only for TupleCount. The original core and accepted suppliers are bound and reused. Named kernel, full-owned and stock/runtime gates remain unchanged; no result or additional acceptance is claimed here. Earlier paragraphs record the previous source stages.
