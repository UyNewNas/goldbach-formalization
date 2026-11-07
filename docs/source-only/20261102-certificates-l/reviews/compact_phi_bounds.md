# L / compact_phi_bounds — independent source review

Reviewer: `/root/h_review_certificate`, Astra/xhigh, independent of the author.

**SOURCE_REVIEW_PASS for the narrow pointwise step.** The literal original phi upper bound and complete original Q80 lowerDifference pointwise lower bound are justified by the inspected source. P2.4.leaf_integrals, full enclosure soundness, the actual adaptive run and the endpoint remain **OPEN**. All decisive finite guards are **UNEVALUATED**; compiled=false, kernel_verified=false, formal_credit=0.

| File | SHA256 |
| --- | --- |
| P2OriginalCompactQ80PhiBounds.lean | acb8dc99b75592174915fdca5472aeca0c9c19e868313fab6cd5a57b9299e034 |
| P2OriginalCompactQ80LowerDifference.lean | c56e1db1552a7c14ec5cc79147745b276e8fcf5a0926129b8cb14108ebdcbff8 |
| REGISTRY.json | 91bb973ec6375f3f4f334edd40e76ac2df78cf07f068cd450e4bce940d6efbe6 |
| REPORT.md | a4cff6f7ecd6c79070e54916e513d33b23c2c304ebd8e234291387fe2ad62904 |

The verdict follows the author's explicit freeze. Both new sources, REGISTRY/REPORT and the L task were read. The original SieveTable(16384,12), phi_range and lower-difference branches were compared directly, together with the actual Q80 arithmetic and 32-term log source. The actual parent Table was read in full; the relevant Encloser, Arithmetic, Leaf and historical state-induction suppliers were inspected. Original/current manuscript and predecessor cap/kernel readings are retained at unchanged hashes. All 42 registered path/SHA claims and four final packet pins match.

The coordinate normalization is correct: phiRange contains coordinate integers, interpreted by rawValue=n/D, whereas table queries and lowerDifference use val=n/2^80. The proof does not confuse these scales despite their shared interval carrier. Both endpoint ceilings remain inside the tent minimum. The inclusive peak test, original x,y,xy,xyz,xz,yz maximum, B(z0) ceiling and final min with Theta are preserved.

The actual cap ceiling is proved only on the true ordered compact intersection. Below mu, the six-envelope identity is applied on its valid ordered domain. Above mu, the original source takes the scalar branch at x0>=mu; at equality the analytic definition still uses Phi. The proof pays this wall using original_mu_left, which gives Phi(mu,y,z)=v(mu). A mere v<=Phi inequality would not suffice for this upper bound, and no such substitution occurs.

The cap-hi residual is derived from the actual two-sided cap bounds and the original geometric residual. At a point of rootCell they imply cap_lo<=cap_hi, then cap_hi-x0-y0>0. NEW's lower and OLD's upper endpoint comparisons divide these positive pre-z residuals before subtracting one. The signed final nlo and ohi numerators may be negative; no unsupported sign assumption is introduced. The minimum increment has the correct direction and original z1 denominator:
`(Theta-cap_hi)/z1 <= NEW-OLD`.

The raw lower candidate uses the actual new query's lower endpoint minus the actual old query's upper endpoint. Monotonicity and the independently supplied nonnegative true factor gap pay max(0,...). For the correlated candidate, the literal olo>=2*z1 guard proves OLD>=2. With q=ohi/z0>=OLD and d=(Theta-cap_hi)/z1>=0, concavity gives
`f(q+d)-f(q) <= f(OLD+d)-f(OLD)`.
Since OLD+d<=NEW, monotonicity completes the lower bound. The query numerator
`ohi*z1+(Theta-cap_hi)*z0` and denominator `z0*z1` are exact. Concavity is never applied across the zero clamp.

Both query endpoints use the parent's actual max12 Q80 point function. The proof chain reaches the historical four-column recurrence through sourceState equality and actualTrapezoidIncrements/state induction; it does not take a table licence or a desired query enclosure as input. Signed-zero, interpolation and >12 tail branches are retained. The analytic fixed-increment theorem has no table parameter; unrelated P160 consumers in its containing file are not used by these result statements.

The complete lowerDifference theorem keeps the parent's nested inside/threshold tests and maxima, including the zero branch. Its only public assumptions are primitive Geometry and membership in the actual rootCell. This removes a real internal pointwise estimate. It supplies neither a leaf-integral lower bound nor a symmetry assertion for the actual asymmetric cap/kernel.

The actual Mathlib checkout was read through the supplied UNC path. Its HEAD is e4c91783ca8e6a7c693ae624ade32fd22d4e43c1 and its toolchain is leanprover/lean4:v4.33.0-rc1, matching the repository pin. The JSON separately records the actual source hashes for division-order and concavity APIs. Reading those sources does not certify elaboration.

Mass integration, symmetric full/half-domain treatment and odd rounding belong to the separate selection companion; the selected affine/Jensen upper candidate also needs separate review. The parent CompleteSoundness source is a separate consumer, and its existence does not enlarge the present acceptance. Parent full-enclosure composition, actual operation guards/run, endpoint certificate, resource feasibility and user-owned kernel verification remain outside this review. Parent proof-file changes require repinning and affected review reconsideration.

No mandatory correction, new external assumption or suspected manuscript contradiction was found in this scope. No Lean/lake/compiler/build/CI/meta elaborator, finite decision, checker, producer, numerical replay, Git operation, quota query or subagent was used. Only the two assigned L review files were written.


Final dependency refreeze: the parent Leaf is now `22625cbdbd57f6412e0074440fc30723e7c868506ec297026986368dd393bad4` (34491 bytes). Its claimed documentation-only change was independently verified: replacing only its top paragraph in memory with the exact previously read paragraph reproduces the entire old file at `e8024b2df23deac2944683ade08d97ea51a516a9d2b30e48f6d0895de8a43ef3` (34482 bytes). Thus the imports, namespace fix, definitions and proof bodies are unchanged; this is not merely reliance on the parent's description. No reconstructed source file was written.

The final Geometry, coordinate positivity/width, residual, actual cap floor, OLD floor and gap-nonnegativity suppliers were reread, together with Arithmetic's Q80 value and actual point-containment APIs. Arithmetic, Table and Encloser retain their previous exact hashes recorded in JSON. Both reviewed Lean files are unchanged, and all 42 registered claims and four packet pins have been rehashed against the final author metadata shown above. The narrow verdict is unchanged. No integral, CompleteSoundness, finite run, stored charge or endpoint acceptance is added; guards remain UNEVALUATED and formal credit remains zero.
