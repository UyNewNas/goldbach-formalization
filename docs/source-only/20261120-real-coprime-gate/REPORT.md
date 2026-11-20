# P1.4 — actual full87 real-cutoff coprime correction, conditional source gate

**P1.4 remains YELLOW; SOURCE_ONLY / UNEVALUATED / UNCOMPILED.**

## Recovery, frozen references and scope
- Verified previous durable branch: `chatgpt/p1-full87-real-primitive-tail-20261120-1810`, HEAD `0785c94e053e68e128fc20e48b371dfd61e60669`. Its source `82fe02b` provides the original three-book high-physical-modulus invoice and receiver Fubini identity; its low-d and unit-coefficient antecedents remain SOURCE_ONLY.
- This packet's distinct branch: `chatgpt/p1-full87-real-coprime-gate-20261120-1910`, created from that exact HEAD; source commit `c1f40b2ad329b484dbf5e0fd161f4b9a75575842`, path `docs/source-only/20261120-real-coprime-gate/P1Full87RealCoprimeGate.lean`; verified Git blob `4f4922fbebc409d99e4a52ea3ade84e566e0d43d`, 196 newline-separated lines including the final empty line.
- Manuscript: `chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, Blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`; no pin changes.
- Toolchain: `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. c=`49044063/25000000`, K=`8452171/1250000`, unchanged.

## Substantive new source-only mathematical candidate
- The old generic `realHalfProductSource_coprime_of_dvd_sieveProduct` assumes the rounded **natural cap** `Nat.ceil z ≤ T^(b/(1+b))`. But the actual physical support has primes strictly **below real z**, precisely `p < Nat.ceil z` for integral primes. Therefore the original **real cap** `z ≤ T^(b/(1+b))` already suffices; no artificial one-unit ceiling penalty is necessary.
- New private proofs `source_coprime_of_real_endpoint` and `real_coprime_mass_eq_card_of_real_endpoint`: from `b>0`, `T>0`, `z≤T^(b/(1+b))` and `d | sieveProduct N (Nat.ceil z)`, every `m` in the original real half-product source is coprime to `d`, so its exact coprime mass is the **total original source cardinality**.
- `actual_full87_delta_real_coprime_correction_zero`: fix ORIGINAL full87 RAW `R` and LICENSED `S`, `Q=actualSmallRoughModuli(S false) ∪ actualSmallRoughModuli(R false)`, and the ORIGINAL physical `trueDDeltaRho`. Under `w≤z`, the project theorem `actualSmallRoughModuli_dvd_sieveProduct_ceil` places **every Q modulus** inside the same small-prime product. Thus for the same physical coefficient and the same real source, `realPhysicalCoprimeCorrection b N T Q rho = 0`. This does not assert nonnegativity or a sieve majorant for signed rho.
- `actual_full87_real_receiver_high_only_primitive`: under the above explicit gate **and** `1≤w`, reuse the preceding source-only low-modulus reindexing. Exact receiver = original source cardinality times the same high-d reciprocal-totient density + the same signed high-d primitive distribution error. Its deviation from the main density has one finite absolute primitive-discrepancy invoice on `Q.filter (w^5≤d)`. No separate coprime correction or duplicate low-d charge is left in this conditional regime.
- Strict original prime cutoff remains strict, `d=w^5` remains in the high carrier; actual Q, same `rho`, occurrence multiplicities, dynamic parent and beta attachment remain unchanged. The result does **not** claim the geometric gate has been installed for the final frozen full87 `T,b,z` or that the remaining tail is `o(H_N)`.

## Remaining genuine mathematical obligations
1. Authenticate frozen full87 final epsilon/w/z/L/cap and the physical coefficient's exact parameter application; separately prove the REAL source gate `w≤z`, `b>0`, `T>0`, `z≤T^(b/(1+b))` at the actual chosen T,b,z. These are explicit conditional hypotheses, not newly verified inputs.
2. Give the **same** high-d primitive discrepancy an `H_N` payment. Confirm final LICENSED causal signed-PP license and common smooth `W_N`; no automatic license follows from unit coefficient size.
3. Prove rank5/7/9 and deeper first divergence corresponds to original dynamic parent/87-owner occurrences, including changed/tagged, BOTH and inherited and their multiplicities.
4. Authenticate saved87 ordinary residual integral and numeric gain, lower-half correction, stopped events, producer/outside and the TWO independent compiler/density reserves. No double payment.
5. Stage the existing source-only dependency closure and perform fixed-version Lean elaboration, kernel replay, transitive axioms audit and independent review before any promotion.

## Actual validation and limitations
- GitHub source file read back at Blob `4f4922fbebc409d99e4a52ea3ade84e566e0d43d`; the source and commit are real. One public zero-correction theorem, one public joint exact-identity/absolute-invoice theorem, two private source helpers.
- Executed `lean --version`, `lake --version`, `elan --version` in the current authorized environment: each command not found (exit 127). cgroup `memory.max=4294967296` bytes. No importable source-only closure staged, no type checking, no kernel replay, no axiom audit or independent review; **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**.
- No new analytic axiom, `sorry`, `admit`, `native_decide`, `unsafe`, external proof, CI dispatch, Codex or main/master modification. A static scan and blob hash are not Lean acceptance.
