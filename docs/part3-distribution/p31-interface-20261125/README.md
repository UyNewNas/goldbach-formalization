# P3.1 original physical modulus and common completion interface

## Scope and current verification state

This delivery targets dashboard **P3.1: 原始物理模数/共同区间/共同加法相位接口**.
It connects the original `CommonCompletedVariable` and `CoprimePacket` records
to already accepted manuscript-internal finite-completion estimates.
Fresh strict compilation, kernel replay and declaration auditing of the new
bridge are **pending** at this source commit. The dashboard has not been edited.

The analytic full-block estimate is an explicit hypothesis throughout. This
interface result does not prove Theorem J, PrimitiveShiu, fullNative6, the full
P3 restricted-medium-convolution estimate or the final 1 + 1.7482 theorem.
The historical source68 caller has its own unresolved source intake below.

## Manuscript correspondence

The reference is `UyNewNas/chen-imbalanced-semiprimes` at
`a988cba584d803ae2856a0de50efb582f4f3dd6a`, `paper/release-20261106/en`.
`BOARD_SCOPE.json` records the observed dashboard node and exact source links.

| Manuscript location | Formalization used here |
| --- | --- |
| `argument.tex`, `prop:current-medium`, lines 28–70 | Original full physical modulus `q1*q2*q3`, separated gamma factors, and exact coprime mean in `Part3DistributionTargets` and `Part3ComplexDispersion`; the already proved `MediumAtom.signedError_eq_groupedFactorGamma` preserves the physical product in `Part3FactorFiberDivisor`. |
| `analytic-appendix.tex`, `ana:kernel` and `ana:packet-coefficient`, lines 667–727 | The original `CommonCompletedVariable.weight` supplies one interval and one additive phase. `CoprimePacket.transformedCoefficient` retains its reduced-residue condition, original beta argument and phase `e(-n/z)`. |
| `analytic-appendix.tex`, `ana:exceptional-average`, lines 1040–1067 | Reuse the common finite Fourier completion in `Part3CommonIntervalFourier` and the arbitrary common-Ico estimate in `Part3ExceptionalWeightExtension`; the new consumer applies these to the literal original records. |

The old provenance comment in `Part3DistributionTargets` refers to an earlier
manuscript snapshot. Its unchanged mathematical interface was checked against
the 1106 passage above; it is not being presented as a newly authored 1106 file.

## Three new consumer theorems

Module: `ImbalancedChen.Part3CommonCompletedInterface`.

1. `sum_weight_mul_eq_sum_inter` proves the exact finite-sum identity between
   multiplying by `c.weight` and restricting the carrier to
   `Ico c.intervalLo c.intervalHi` with phase `c.additivePhase`.
2. `weight_weightedEnergy_le` transports the existing arbitrary-common-interval
   estimate to the original weight on `fullBlock j`. Zero, equal and reversed
   endpoints are permitted. For a reversed interval the sum is empty, and
   nonnegativity of the bound follows from the supplied full-block premise.
3. `packet_weightedEnergy_le` specializes the same statement to finite sums of
   the original `CoprimePacket.transformedCoefficient`. Packet data and carriers
   depend on a packet-label projection of the spectral index. The kernel may
   depend on the full spectral index. No coefficient array is selected anew
   when the common phase varies.

In both inequalities the same fixed coefficient array occurs in the conclusion
and the premise `forall rho, weightedEnergy (fullBlock j) rho T exponent a <= bound`.
The explicit finite-completion loss is

`4 * ((2 + log (period j))^2 * max 1 ((W / T)^cap) * bound)`.

All levels use the same `c`, hence the same interval and phase. The input
exponents satisfy `0 <= exponent i <= cap`, with `W > 0` and `T > 0`.
The wrapper does not supply the analytic premise and does not assert that an
arbitrary label map represents a manuscript spectral family: a downstream
consumer must instantiate the packet label consistently across spectral heights.

## Existing work reused without changes

`SOURCE_MANIFEST.json` binds each donor source to its saved accepted receipt.

| Module suffix | Complete owned declarations in the existing inventory |
| --- | ---: |
| `Part3DistributionTargets` | 91 |
| `Part3ComplexDispersion` | 30 |
| `Part3FactorFiberDivisor` | 30 |
| `Part3CommonIntervalFourier` | 92 |
| `Part3ExceptionalWeightExtension` | 43 |
| **Total reused** | **286** |

The first four use the saved `c509267` baseline receipt, which carries prior
accepted work forward and freshly rechecked its seven additional modules.
The fifth uses the `80d7eeb` spectral receipt. None of these five modules has
been rewritten or subjected to a redundant fresh strict/replay pass here.
Normal Lake dependency compilation, if required by a fresh CI checkout, is
separate from claiming a fresh acceptance pass over the old closure.

## Exact-source verification procedure

The existing verifier gains a one-module `interface` selection. Its complete
owned-declaration inventory, transitive axiom gate, source/pin checks, strict
compiler and original `leanchecker` replay remain unchanged. The new workflow
pins its actions and the original Lean `4.33.0-rc1` toolchain.

```sh
python3 verification/verify_part3_continuation.py --group interface \
  --expected-head "$(git rev-parse HEAD)" --output-dir .lake/p31-interface-verification
```

Source-only checks do not count as Lean verification. The final receipt must
name the exact code commit, module, complete declaration inventory, compiler
version and source/object/log hashes. Allowed transitive axioms are only
`Classical.choice`, `Quot.sound` and `propext`.

The designated P3 compiler and the backup returned `MCP SSE probe returned 429`
before executing a command. GitHub Actions is therefore used for the fresh
bridge verification. No remote compiler execution is claimed from those errors.

## Historical source68 boundary

The dashboard attaches a source-only, 59-byte namespace/API repair to an older
Shiu WindowGate caller. It references the original
`ImbalancedChen.Part3MediumPrimitiveShiuFiniteCover` source with SHA-256
`7bdcfdbbff4382da1ee4ba16ba9296b8995ceb11a43f78cf70af21f852549d39`.
Its original bytes were not found in the published source trees, the newer
yellow-closure branch, local work or the matching saved source metadata.
No replacement provider is created in this delivery.

A bounded follow-up checked the other two supplied private compiler services.
P1 and P2 answered their environment preflights, but their serial task queues
were occupied. The P1 read-only lookup never started and was cancelled; P2
rejected the lookup because its queue was full. No source search actually ran
in either environment. Their contents must therefore be recorded as uninspected,
not as evidence that the original file is absent there.

The new bridge neither imports this caller nor makes it compilable. The source68
repair, its provider and fullNative6 remain **unverified**. An acceptance of the
original interface contract must retain this independent historical note;
it cannot be used to certify all source-only attachments or the full P3 target.
