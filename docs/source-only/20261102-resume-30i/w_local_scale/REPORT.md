# I w_local_scale: complete HB scale and the SAME computed W dyadic gates

`local_step_complete=true`, `task_complete=false`, `compiled=false`, `kernel_verified=false`, `formal_credit=0`. The implemented local step is the numerical complete-scale conversion and exact dyadic restriction of H's actual ALL16 W coefficient. The broad original PP target remains open. These are source proof bodies pending independent static review and user compilation; no inherited H or production compilation claim is made.

Assigned model/effort: `gpt-6.1-sol` / `xhigh`; inherited runtime not independently introspected. Baseline branch is `codex/proof-continuation-20261015`, HEAD `25afcbff11562df51ef7ac5113c879123fcd64c6`. Only `docs/source-only/20261102-resume-30i/w_local_scale` was written. No compiler, lake, build, CI, mathematical finite/checker/decision execution, quota inspection, subagent, production installation or commit was run. Text reads/searches, edits, Git baseline reads and SHA256 hashing are the only local operations.

## Original statement and exact source

The manuscript is `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`, SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`. Lines 264–354 require the same signed coefficient in count and exact coprime mean, preserve marked multiplicities, use the complete outer product as local scale, and retain the original order-three HB identity and parameter order.

The detailed coefficient completion module, SHA256 `a6cfa86f625242527df3ba485a7e86867b84e289bca651c0e8b942be36f0fc69`, sections 5–7 (lines 144–270), supplies the three separate endpoint monomials, `qscale=log_x N`, the source/state alpha distinction, residual-only marked normalization, full common beta and the substitution `A=U*x^(-zeta)`. The prime-product completion module, SHA256 `a953b3233c1249b4791830da33b76a58b19ca110a5e1b5b6172b3248a00053e1`, section 2 (lines 72–117) supplies the smooth complete-product trim, actual HB groups and complementary-product dyadic regrouping; section 4 (lines 151–184) supplies the medium window.

The H source was checked at its actual bytes: `P5ActualComputedWNormalizedLicence.lean` SHA256 `cf7a82f26eaca15276750ad16e099f7ed878956c887259951e758f8c9f10d850` and `P5All16ComputedMarkedTensorBudget.lean` SHA256 `f580288ea6e0c3277d4501ea14e07e58b8b937b2c4d57376d57b47de91d5be0e`. H's exact frozen `labelGroups` module remains SHA256 `9bf15c2e6f17b3377563ca1d9d674bd0be1fb0f7dde1e0a2fde4774a1c409f48`. No H source or metadata was edited.

## Implemented local proof

`P5OriginalHBCompleteProductScale.lean` derives the scale from the literal existing ordered HB factor tuples. For each original group it proves the exact dyadic HB identity **divided by that original group's log(n)**. `all_original_group_logs` preserves one independent such denominator for every original group; neither the selected occurrence's logarithm nor the logarithm of the full product replaces them. Signed binomial HB scalars, occurrence multiplicities, real Mobius cutoffs and the original log role remain the existing source objects. Nonzero normalized blocks inherit the actual six-slot product window from the original active coefficient theorem, rather than from a new HB profile assumption.

Concatenating actual group tuples gives exactly the product of their original group integers. For any selected occurrence p, its complementary integer is the product of **all** other outer occurrences. The proof derives p times that complement equals the complete product from actual tuple membership. If fixed dyadic block labels b,v own p and its complement, then for U=lower(b), V=lower(v), x=UV:

`x <= complete product <= 4*x`.

This is the complete local Medium product after complementary dyadic regrouping. The original smooth trim and upper support therefore give `N^(1-kappa0)/4 <= x <= C*N`. The factor 4 is exact for these two active blocks; it is not a replacement for the earlier individual-rectangle constants in the manuscript. The residue theorem absorbs this fixed constant uniformly and derives `C^(-1)*x <= N <= x^(1+kappa)` for every original buffered trim `kappa0 < kappa/(4*(1+kappa))`. No N–x relation is assumed. `qscale_relation` proves `x^(log N/log x)=N` and `0<qscale<=1+kappa`. The source residue alpha is not identified with a sieve-state alpha.

`P5ActualComputedWLocalScale.lean` reuses the existing finite-bank choices `zeta=kappaMax(n,eta)/16` and `sigma=zeta/2000`. The existing all16 common-parameter minimum gives `1024*zeta<=delta` at **every** actual W owner. The original analytic restriction `0<kappa<=sigma/200` implies H's `kappa<=delta/64`; no smaller original trim or replacement bank is chosen.

One threshold precedes N, x, U, the W owner, fine mesh, residual rank, beta exponent and arithmetic tuples. From the original window `x^(2*zeta)<=U<=x^(1/3+zeta/2)`, it derives `1<=A<=N^(1/3)` for `A=U*x^(-zeta)`. It then calls H's genuine `actual_computed_W_beta_monomials`, not an assumed local monomial interface. Its factors are precisely H's computed normalized words. Their third endpoint is the **entire** `N^epsilon*labelEndpoint(group3)`, uniformly in every active small beta term. H/G's exact beta costs remain 2*epsilon, 2*epsilon and 39*epsilon/16, with the original condition epsilon<=delta/4; no representative e is chosen to reduce those costs.

The proof converts the N-power margins to local x-power margins using a proved strict power gap and the original complete support. It retains `N^(7/32)` in the second Medium monomial; it does not put qscale=1 or drop the source-alpha-dependent inequality. Replacing A by U is then paid explicitly in the logarithms of all three positive monomials. The result is the existing literal `NumericGates`:

- `Q1 < U*x^(-sigma)`;
- `U^2*Q2*Q3^2 < x^(1-8*sigma)`;
- `N^(7/32)*U*Q1*Q2^5*Q3^2 < x^(2-15*sigma)`;
- `U^(23/16)*Q1*Q2^(73/16)*Q3^(39/16) < x^(2-15*sigma)`.

The three elementary analytic helper proof bodies follow the existing ORIGINAL15 module's argument. Only numerical definitions/finite-bank parameters are reused from that module. Its ordinary15 arithmetic factor theorem is never applied to W; the actual endpoint theorem called is H's W theorem.

`P5ActualComputedWDyadicConsumer.lean` takes exact `[2^i,2^(i+1))` restrictions of these same three functions, using the existing unique half-open dyadic module. Active support bounds come from H's actual gamma/beta source, so each piece's lower length is at most its actual endpoint. The original fourth monomial has positive exponents on every Q_i; the existing proved downward lemma therefore retains all four strict gates with no factor-two inflation. Exact finite function reconstruction, actual enclosing factor carriers and one-bounds are included. Unit factors are retained at length 1. `exists_actual_HB_W_dyadic_threshold` combines the actual outer HB product proof, H W monomials and these active dyadic restrictions; it has no local monomial or N–x premise.

`full_marked_beta_endpoint_product` proves that the endpoint product contains all four marked slots, every residual occurrence and the whole beta level. `restoring_scalar_original` exposes the exact scalar `epsilon*(-1)^r*M1*M2*M3/M_res`. It does not divide by a marked factorial. The common coefficient, complete q, original sign and beta are unchanged in both count and mean.

The exact PP consumer is `original_all16_PP_consumer`. Its independent test is the existing original labelled-prime-product count minus **the same-modulus coprime mean**. It specializes H's proved full source identity to that test and keeps H's independent arithmetic remainder explicitly. Thus the local gates attach to a real W subsource of the same lower ALL16 coefficient, not to a coefficient newly declared equal to the target. This equality is finite algebra, not an analytic PP estimate.

## Scope, genuine remaining source gaps and analytic gaps

This delivery closes the N-scale-to-local-scale numerical conversion for the H-certified ALL16 W words and their active dyadic pieces. It also supplies reusable complete outer-HB support and original per-group logarithm identities. It does not certify the entire original smooth chart/Fourier/occurrence atlas, prove the exhaustive medium versus one/two-long classification, or pay any discarded source. In particular the actual smooth-family producer still has to instantiate the original trim, support, fixed rectangle and admissible profile data uniformly. Those are source-interface/analytic obligations, not premises hidden inside a new PP theorem. Actual tuple membership is used here; an arbitrary asserted HB-window/source-equality licence is not.

Still internal and open: the complete original source/atlas/profile reindex and smooth coverage; the geometric/Fourier budgets and logarithmic bank summation; original auxiliary k=1 SW for the actual selected HB source classes; complete modulus support/coprimality and squarefree/wall/remainder estimates on their real callers; the RestrictedMedium estimate; and final same-rho PP assembly. The sibling `k1_sw_source` owns actual singleton prime/SW profiles and explicitly does not assign SW to general multi-prime words or arbitrary divisor-bounded sequences. This module imports no sibling SW output and assumes no SW conclusion.

The positive-K upper coefficient is a separate source. The sibling `switched_group_capacity` has verified that H's W modulus words require U10/U11 `WholeCell` ownership and are not the outer positive Gamma word. Nothing here transfers the lower ALL16 coefficient or its numerical licence to that upper source. A genuine positive-upper coefficient/source bridge remains open.

No new external mathematical theorem is assumed. Existing foundational library results and the prior source-only H/G proof bodies are reused at exact pins. No manuscript contradiction has been established by this local conversion; the remaining source and analytic gaps are reported separately from a suspected mathematical gap, of which none is claimed here.

REGISTRY records exact module/import/install pins and eliminated/remaining obligations. Its scope is direct imports and explicitly relied-on manuscript/source inputs, not a claim that every transitive dependency is compiled or independently audited. Source, registry and report hashes are frozen in the delivery message; no production installation or formal credit accompanies them.
