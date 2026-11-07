# certificate_omega 第二批交付

已完成本批分配的原始 `sourceSmallLog` directed Horner/tail 局部证明源码：`OriginalPairedN48SmallLogSoundness.lean`。完整文件文本闭合；尚未编译、正式信用为 0。`task_complete=false` 统一针对最初完整 uniform Omega query/证书目标；`local_step_complete=true` 与 `batch_target_source_complete=true` 仅指本批明确的 sourceSmallLog soundness 窄步源码，相对于精确 source-only 依赖和原有纯算术 producer predicate。

原始 Python 使用48项逆序 Horner，以及 `2*x^97/(97*(1-x^2))` 尾项。现有 RationalLogCertificate 的 Mathlib 上界没有 `/97`，不能直接用于原始 token。本文件准确复用 Mathlib 的有限对数余项导数：余项 F 的导数为 y^96/(1-y^2)，比较函数 G(y)=y^97/[97*(1-x^2)] 的导数为 y^96/(1-x^2)。在 0<=y<=x<1 上 G'-F'>=0，且两者在0为0，由此得到原始 `/97` 上界；下界复用现有 odd-sum lower theorem。

程序连接严格沿真实代码：对任意 coefficient index list 证明原始 signed `sourceAdd`/`sourceMul` fold 的 enclosure soundness；再用保留自由 accumulator 的归纳证明 reversed range Horner=sum+z^n*acc，最后识别 `2*x*poly(x*x)` 与真实48项 odd sum。`sourcePow`、neg/sub、tail 的 `/97` 和 `/[1-z]` 均使用第一批严格 directed arithmetic。忽略 tail 的 lower endpoint是合法的，因为原始 lower 使用正项级数下界；upper正好使用原代码的 result.hi+tail.hi。

正分母没有引入新的实数结论假设：独立 sourceSmallLog theorem 明确要求原有整数 lower endpoint>0；实际 2mesh<i<=3mesh 的 theorem 直接从既存 SourceProducerValid 的同一子句取得它，并用同一 predicate 中的 U-row定义和实际 Buchstab `[2,3]` 闭式得到真实 weighted U enclosure。最后 `all_weighted_nodes_of_original_local_error` 消除第一批 hlog 前提，只保留独立 SharpCellError。

还需证明真实 delayed Buchstab 的 h^3/6 曲率界，提供实际 source arrays 的纯算术有效性，完成 cell bulge/max query、Z_B/costHi 和历史 floor 绑定。本批没有运行数组 checker、编译、Lean/lake、数值 replay 或额度检查，也没有改第一批/生产文件/Git/看板。未发现原稿新的数学缺口。
