# P3 independent07: five reported linter deletions

Actual diagnostic job: `1b7405b8ab8a408f837f5a2ab7c1789b`.
Input commit: `199383229f73ac0ffe0f7e058f82cfefbeaf696c`.
Saved log: `p3-independent-symbolic-07.log`, SHA-256
`473d3cece4e7c39de2007939bf96d15d77cf42f259528204e919ae9abf13cc7b`.

Only the five actual strict-linter findings were changed:

| File | Reported location | Exact deletion |
| --- | --- | --- |
| `BoundaryArbitraryLog.lean` | 62, 95 | Remove `<;> ring` after each successful `field_simp`. The separate final `ring` steps remain. |
| `OrdinaryRosserFirstExitPolicy.lean` | 317 | Remove unused `evenListLength_cons` from the nil parity case. |
| `OrdinaryRosserFirstExitPolicy.lean` | 319 | Remove unused `evenListLength_nil` from the cons parity case; retain the cons equation and induction hypothesis. |
| `OrdinaryRosserFirstExitPolicy.lean` | 398 | Remove unused `evenListLength_cons` from the empty-prefix parity premise. |

The input files are byte-identical at diagnostic commit `19938322` and current
HEAD `df755697047805456cdd1eb0614f191da31afde1`. Static reconstruction confirms
that each edited file equals those input bytes with exactly the reported
deletions. All **30 theorem headers**, **2 complete definition blocks**, and
imports are unchanged. `git diff --check` passed.

| File | Before SHA-256 | Candidate SHA-256 |
| --- | --- | --- |
| `BoundaryArbitraryLog.lean` | `2694e8398198c9edeab5f0c4bad70c514a22de21a0cec6edec33c2faec742167` | `d619a1e4786da43663b1e86b241543e1c702ebdfe2865597499aedb68f9604c4` |
| `OrdinaryRosserFirstExitPolicy.lean` | `46dcca7e7dd1ecee81605f8da848e62f6efa8abc04966549e020a4c641f6f60d` | `e26901056844813eaf0594eb17445c0d67a1f91c8723a2d1a0164530f161ae2a` |

Classification: proof-script redundancy only; no mathematical argument,
premise, selection policy, or logarithmic estimate changes. No linter was
disabled. No CI/archive review, Lean/Lake invocation, remote job, index change,
staging, or commit was performed. Actual retry is pending; this note grants
no compile or kernel credit.
