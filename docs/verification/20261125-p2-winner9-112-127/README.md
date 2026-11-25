# P2.10.3: original Winner9 pages 0112–0127

Base: `a929011ec95843553fc2e10b7291c8077e0952c0`. Frozen 1106 manuscript:
`a988cba584d803ae2856a0de50efb582f4f3dd6a` (same release TeX as upstream P2).
Toolchain: Lean 4.33.0-rc1, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
P2 private cloud, isolated working tree; no new CI.

- 16 archived pages, original ordinals **1792–2047**; all 256 original row
  inequalities remain attached to the original block/page/checker.
- Only additions to the archived page code: import/open already accepted
  `P2Winner9MaterializedLogChecker`, and apply its soundness theorem before
  each `decide +kernel`. Removing those additions recovers original renderer
  source byte-for-byte. No new axioms or native decision shortcuts.
- All 16 modules completed strict compilation (cloud job
  `a720765c766848a3bdc5726287b2093d`, two workers, `-t0 -j1 -M6144`,
  warnings as errors), independent stock `leanchecker` replay and complete
  owned-declaration/types/transitive-axiom audit (cloud job
  `ca9fbfa775374d1f97d46d4a329b7771`). Count: 544 owned declarations.
  The two audit workers were disjoint, not twin runs of the same page.
  Frozen local source/object hashes and dependency signatures are in the
  packaged per-page receipts. No historical dependency earned fresh credit.
- Evidence SHA-256: `c8ed23cf27418cb2766770c501547e7519cb46932fc1cc11d7fb012c76985e12`; 204 members
  individually read back against size and hash. Source-change hashes
  and exact original-page bindings are retained.

Combining this disjoint interval with the upstream 0–1791 yields
**2,048 / 11,026** accepted rows, leaving **8,978** outside accepted coverage.
The full numerical archive, complete-family integral terminal, original seed
supplier installation, and overall P2 remain open. This does not update the
distinct 17,572-row certificate, or establish any external theorem.
