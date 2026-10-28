# coefficient_physical 第二批交付

新增 `P5OriginalH3LocalPhysicalQFibre.lean`。本次补齐了上一批缺少的真实局部 `q-fibre`，不再只把某个 pre 的 cap 等式与任意全局 q 的支持性质并列。文件文本闭合；未编译，正式验收信用为 0。

`H3Leaf` 的几何条件检查同一实际保留粗素数叶自身的 `rosserAncestor 8 leaf.selected`，并保留第一批的四项实际第三/第六祖先 cap 比较。局部 pair 是真实小素数载体中的 `a` 与该 H3 粗素数根叶，局部模数就是 `q=a*leaf.selected.prod` 的精确像。严格小/粗素数分解唯一性，加上已有保留素数叶乘积单射，证明这个 pair 由 q 唯一确定。

新 `localRho_eq_masked_global` 逐点证明：在这个局部像上，局部 rho 等于原始 `actualSmallRoughRho`；像外为零。`atom_eq_signed_leaf_beta` 保留真实叶符号，正叶选择 betaPlus，负叶选择 betaMinus。`local_signed_test_eq_pairs` 对任意带符号算术测试给出同一局部 rho 的无重数叶对重索引；因此可以分别代入 AP count、exact coprime mean 以及两者之差。

`active_q_unique_local_fibre` 从非零局部 rho 反向恢复唯一小因子/真实根叶、严格 `a<L`，并由该叶自己的第八祖先得到 H3 的实际 guard、mask138 与同一 raised exponent。最后 `physical_h3_local_rho` 直接专门化到第一批定义的 corrected-parent `physicalRho`。

必须保留拓扑边界：实际 `physicalRho` 通过 `fixedRoughSupport` 使用 `oddFirstExitPolicy (physicalPolicy ... false)` 的根叶。本文件严格沿这一定义，未把它无证换成完整 Bool policy 的叶。若要把含第三 lower-residual 的完整 family 与这个 oddified carrier 等同，还需要独立的 parity/attachment 工作。

这一批的局部 q-fibre 步骤已给出完整证明文本。原完整目标中的全局合法因果祖先供应、87 域 coverage/owner、不交、积分收益、密度 telescope 与 K 仍未完成，所以 `local_step_complete=true` 而 `task_complete=false`。未发现新的原稿数学缺口。第一批和生产文件均未修改；未运行 Lean/lake、数值 checker 或 Git。
