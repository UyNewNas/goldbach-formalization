# P3.6 — joint retained complements and actual head-block source

Base commit: `0632f2e1839bbdba1604c546bbc3be46b7536d47`.
Base tree: `410189b46e1ce82d91cbb070c40a0a54365ec73c`.
Branch: `chatgpt/p3-joint-complement-20261103`.
Packet: `docs/source-only/20261103-p3-joint-complement/`.

**SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED. FULL P3.6 REMAINS OPEN.**
No Lean/Lake/compiler, kernel replay, CI dispatch, numerical producer, finite guard, Codex task, connected-computer operation or child agent was run. No independent review or transitive axiom acceptance is claimed. The new VERIFY file is an unexecuted handoff. Earlier packets, production, toolchain, locked dependencies, manuscript, constants, full87 work and external tracker are unchanged. Publication is confined to a new branch and requests skipping CI; no PR, merge, release or manuscript publication is requested.

## Actual advance, and the boundary it does not cross

The preceding retained assembly first bounded each old pair and consequently retained `selectorMass = sum_t |sigma(t)|`. This packet constructs and bounds the **joint complementary coefficients before any per-pair discrepancy estimate**. Both old primes are inside the divisor encoding. The new summed complementary L1/L2 suppliers have neither selectorMass nor the number of head blocks as a factor.

This does NOT yet remove selectorMass from the preceding final PP bound. The head intervals vary with the old pair. Their possible overlap must still be handled in a family conductor argument; a norm on the complementary side alone is insufficient. This packet keeps the exact interval family and proves its remaining head-energy cost explicitly.

## 1. Literal joint retained complementary source

`P2GammaJointRetainedComplement.lean` constructs the tagged finite union

`{(t,y) : t in pairSupport N, y in retainedComplementLabels N t c cs H delta j l}`.

The complete complementary product remains `t1*t2*tail.prod*quotient`. The original quotient one, the projected source conditions, retained weights and all product collisions survive. The existing `jointFactorList` is reused as the code `[t1,t2] ++ tail ++ [quotient]`. A new actual-source injection proves

`card(jointRetainedFiber m) <= tau_(cs.length+3)(m)`.

For a full mother word `c::cs`, this order is one larger than the old fixed-pair complementary order and one smaller than the full joint-product order. The head prime is NOT a complementary factor.

The coefficient `jointBeta` is directly defined by its weighted fibre sum. Its exact equality to `sum_t sigma(t)*retainedBeta(t,m)` and an arbitrary-test identity are proved by finite reindexing, not assumed. The actual nonzero hat support supplies `0<m<=floor(2*V)`, where `V=lower delta l`. Complex selectors with `norm(sigma(t))<=height` are allowed; no new positivity premise is needed for these norm statements.

## 2. Total norms over a genuine partition of the old pairs

`P2GammaJointComplementBlockNorms.lean` partitions pairs by a fixed key. It retains different tests in different blocks. Each labelled complementary occurrence belongs to exactly one key, giving

`sum_a norm(beta_a(m)) <= height*tau_k(m)`, where `k=cs.length+3`.

The square bound is then obtained after this joint norm sum. The existing native divisor moments yield, on every finite `S subset (0,floor X]`,

`sum_a sum_m in S norm(beta_a(m)) <= height*X*(1+log X)^(k-1)`,

`sum_a sum_m in S norm(beta_a(m))^2 <= height^2*X*(1+log X)^(k^2-1)`.

These are total family norms, not a separate worst-case estimate to be multiplied by the number of blocks. `actual_block_raw_norms` supplies the original padded integer-row L2 and natural-row L1 at `X=2*V`. `actual_block_masked_energy` applies the existing quotient-unit projector only after constructing the original rows and proves contraction of the total energy. The source and weights remain independent of the later modulus, conductor and residue.

## 3. Exact original source, same rho, actual head windows

`P2GammaJointSameRhoBlockSource.lean` chooses the concrete key

`headKey(t) = actualPrimeCarrier N t c delta j` on occupied rows, and the empty carrier otherwise.

The empty key is justified by the existing exact zero-row theorem. It is not a change to an occupied source. The joint original row is proved equal to the sum of natural rectangles on these actual head keys and the joint complementary coefficients. The original AP-minus-exact-q-coprime-mean is unchanged.

`blockSource_eq_character` invokes the existing natural/character dictionary. `signed_original_eq_block_char` attaches the SAME `upperRho`, with its full beta factor and original 19/96 upper cutoff. Positive modulus and target coprimality are supplied by nonzero activity of this actual coefficient. Zero coefficients are handled before requesting those properties.

`eventually_chosen_signed_block_source` invokes the actual complete-scale threshold and chosen-grid supplier. One original-N threshold precedes every later pair, word, grid index, selector, allowed coefficient and finite modulus family. No local row-scale licence, PP estimate or source identity is an argument of this eventual theorem. `actual_head_block_beta_norms` instantiates the total complementary norms on the very same concrete key.

## Remaining head cost is explicit

Distinct keys can represent overlapping original head intervals. Define `headMultiplicity(p)` as the number of distinct head keys containing p. The new theorem proves the exact identity

`sum_a rowEnergy(padded_head_a)`
`  = sum_p headMultiplicity(p)*norm(primeHeadCoefficient(p))^2`.

No assertion that headMultiplicity is one, logarithmic, or uniformly bounded is made. In particular, applying a per-block conductor bound and dropping the block count would be invalid. A common interval-family treatment, for example a fully proved source-preserving decomposition, is still needed before the new complementary norms yield the desired joint low-rank distribution estimate. Such a decomposition is not provided by this packet.

## Scope and remaining work

- Full P3.6 and the previous final PP terminal remain open; this is not a completed positive-Theta or hUniformPP supplier.
- The new source identity covers the original upper rough-modulus-rank-at-most-two coefficient. It is not the high-rank/enhanced branch or every lower/marked coefficient class.
- Actual causal selection, common physical Q, positive-Theta conversion, empty-word handling, high-rank/enhanced branches and final PP/spectral assembly are unchanged obligations.
- The pinned external `MathlibNt/Wu2008DoubleSieve/SecondFunctionalMotherFinite.lean` at goldbach revision `09b97db5764ade1246bfb77206baa1b124760958` could not be read (404). No absence of empty mother words was inferred from that access failure.
- The original manuscript was not newly fetched. This increment follows the directly inspected finite source definitions and imported divisor/character interfaces; no new external analytic theorem is asserted.
- Source installation, elaboration, kernel and axiom audits remain to be performed by the existing verification workflow.

## Tracker delta (proposal only)

```text
黄｜P3.6 把估计实例化到同一rho和实际PP源族
    蓝｜实际joint retained complement重数及全分组L1/L2范数源码
    蓝｜实际head-key分组、同rho字符来源与共同阈值恒等式源码
    黄｜头部区间族的整体导子估计：显式保留headMultiplicity成本
    黄｜共同物理Q、positive-Theta、空母词、高秩/增强分支与全PP总装
```

The new bounded source scopes alone are proposed blue. No new green item and no external tracker update are claimed.

## Performed checks

Only byte hashes, source declaration/import inventories, JSON parsing and a comment-stripped forbidden-form scan were executed. They are not Lean checks and do not establish proof correctness or successful elaboration. REGISTRY records the exact files, direct dependencies and validation boundary.
