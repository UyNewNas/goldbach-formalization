# P1.4 — original full-87 reflected AP: anchored beta-jump correction (source-only)

**Baseline:** verified previous P1.4 HEAD `56b9d85593a6c00b0211d15e47c9017e8ce179c4` (prior proof source `99d0da2`; frozen manuscript unchanged). This packet is an independent descendant, NOT main/master.

## Genuine manuscript-internal advance

The previous full-modulus Abel decomposition controlled a correction using unweighted reflected-prime prefix discrepancy from a=0 for every k<=m. With the original complete modulus b=(p::pre).prod, put

- m=N/b+1 (Lean Nat division, including b=0);
- ell=max(floor(N/(2b))+1, floor(X/b)+1), the **original strict** lower quotient gate;
- w(a)=1_{a in actualPrimitiveRosserRoom} * actualSmallRosserPlus(a), preserving its actual sign, gaps, and support;
- Q(k)=sum_{a<k}(1_{N-ab in chenPrimePrefix N}-mean(b)), where mean is still an arbitrary **full-modulus** reference scalar.

Because the actual room is contained in [ell, min(ceil L,m)), both w(0) and w(m) vanish. The new finite Lean candidate proves the exact telescoping identity

    sum_{t<m} (w(t)-w(t+1)) = w(0)-w(m) = 0,

and hence the original correction is **unchanged** by anchoring:

    C_b = sum_{t<m} (w(t)-w(t+1)) * (Q(t+1)-Q(ell)).

The actual PLUS-beta sum minus mean(b) times its **same** room mass equals this anchored C_b, by the preceding exact Abel theorem; this new source does not replace the producer, parent or original signed List.

New conditional bound: it is sufficient that |Q(t+1)-Q(ell)|<=E_b ONLY at t<m for which w(t) != w(t+1). Then

    |C_b| <= E_b * sum_{t<m} |w(t)-w(t+1)|.

This is a different and more localized AP input, not an assertion that the E_b bound is known. The crossing jump t=ell-1 has Q(ell)-Q(ell)=0; other jumps outside the bounded room vanish. The original variation and occurrence weights remain fully payable. One cannot claim E_b is automatically smaller than the old zero-origin bound at the same numerical threshold (triangle inequality can cost a factor 2); it may, however, remove an irrelevant long initial prefix and all nonjump endpoints. The exact global physical and signed parent transport remains the preceding `56b9d85` proof packet: the new theorem refines the same inner correction, it does NOT pay lower a second time.

## Checks actually performed

- GitHub readback: new Lean source blob `a30a8f7463eef3bdc3d192df6cd3754fa8d6de37` from new independent branch; source first commit `70f8b40bd8e78c178a336571687977ca5ec2090f`. 193 nonempty/empty source lines prior to final newline, 4 named public theorem candidates plus finite support helpers. Candidate proof statements/proof bodies have NOT been elaborated.
- Fixed project `lean-toolchain` read: `leanprover/lean4:v4.33.0-rc1` (blob `fd85b262bf1c734663aa8292b0101f672168788f`). `lake-manifest.json`: mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `09b97db5764ade1246bfb77206baa1b124760958`.
- Frozen manuscript read at pin `9731290e8f53cffda44129906cde6a965eaa869b`: body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` matches. c=49044063/25000000; K=8452171/1250000 unchanged.
- Execution environment: `lean --version`, `lake --version`, `elan --version` all exit 127 (command not found). Container cgroup memory.max=4294967296 bytes (4 GiB). A public git remote probe was also blocked by DNS (git exit 128); the authorized GitHub connector read/writes succeeded. No toolchain upgrade, CI, Codex, main write, local machine access, or extra resources.
- Independent exact-rational diagnostic: 15,000 seeded cases with varied N, b incl. 0, strict lower/upper gates, signed beta holes, and reference means; zero failures of anchored equality, jump variation bound, or zero endpoints. In 14,591 synthetic cases the zero-origin maximum used by the old bound was numerically larger than the anchored jump maximum. Many cases had no jumps; this is not a producer-specific rate, theorem, or H_N estimate.
- **Status: SOURCE_ONLY / UNEVALUATED / UNCOMPILED.** No Lean elaboration, kernel replay, transitive axiom audit, independent review, or saved87 certification.

## Unpaid, exact next steps

(1) Typecheck staged prior source-only imports under frozen Lean/mathlib/native; repair any real errors. (2) Obtain/verify a same-rho **primitive reflected AP interval-prefix** input on the complete actual b, at each beta jump and original ell, with N-uniform quantifiers and correct center/modulus-prime corrections. (3) Evaluate the actual beta variation and signed fifth/sixth occurrence budget against H_N, avoiding double payment. (4) Then resume lower corrections, ordinary residual integral, saved87, RAW/BOTH, rank9, changed/tagged and both independent reserves. P1.4 remains YELLOW.
