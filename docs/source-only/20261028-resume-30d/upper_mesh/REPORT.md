# upper_mesh 第四批：实际 adopted bank 与固定父 trim

交付两份新 Lean：`P1OriginalFifthAdoptedOwnerBank.lean`、`P1OriginalFifthUniformAdoptedBankError.lean`，另有精确登记。本批文件文本闭合，未编译、未执行 checker/kernel，正式信用为0。`local_step_complete=true`；完整原目标和整批 prescribed total error 的无条件归档应用仍为false，因为实际归档 trim 小于容许量尚未证明。

这次实际构造 bank，消除了上一批的外供 adoption verdict。每个raw先保留它原来的decode labels，取0/e两处原始 `selectedFifthCells` 的交，再筛选两处真实firstStop=true。由原始membership字典证明该bank对自身J在两端确实selected且stop；每个label仍来自同一raw decoder。B13现在直接作用于这个构造，无需调用方先假设全部verdict。被滤掉的真实区域没有被宣布无质量。

固定parent精确取 `raw.originalBox∩原始0..19/96半开ambient`，并证明它等于以max/min截断原端点的真实logPrimeBox，体积等于五个clipped宽度的ofReal乘积。`omittedParent`精确定义为该固定parent减去共同adopted bank在0处的真实owner union；它还精确等于全部decoded Ico cell减去该owner union后的并，所以原格内部部分历史门槛失败也被保留。真正KeyInjective的原行银行具有两两互斥的trim域。

对实际positive literal variable-MI kernel，完整父积分减baseline积分恰为遗漏域上的非负积分；以第二批真实M_raw乘实际遗漏体积控制该质量。于是固定raw bank的真实误差满足

`|buffered retained sum − fixed parent sum| ≤ bankEnvelope(e) + trimVolumeBank(e,q)`。

随后用具体rowModulus/M先选一个正有理e，使整个固定raw bank的moving error<eta/2，再选同一个实际refinement q，并自动得到该q的原Ico完整decode cover。结果为

`|buffered retained sum − fixed parent sum| < eta/2 + 真实trimVolumeBank`。

若这个实际几何trim≤eta/2，总误差严格小于eta。代码没有把trim小偷偷放进parameter存在性：构造允许省略owner，但正测度省略不能只靠e→0消失。全归档实际trim上界/零trim cover、全87域共用祖先、same-rho及K仍开放。upper_jensen同批专门处理两个named父的zero-trim与child-reserve重组，本任务没有重复它，也没有把两个named父当全归档。

原始手稿范围和全部直接/语义依赖raw SHA见REGISTRY.json。前30c源码、登记、报告均已重新核对SHA并冻结，未修改。

{
  "sources": [
    {
      "path": "docs/source-only/20261028-resume-30d/upper_mesh/P1OriginalFifthAdoptedOwnerBank.lean",
      "sha256": "a52ecf8fd672136f3e2e22289914356094483698020512dd18de6bcde7bf00e4",
      "lines": 237
    },
    {
      "path": "docs/source-only/20261028-resume-30d/upper_mesh/P1OriginalFifthUniformAdoptedBankError.lean",
      "sha256": "5c0012206c93e05871ead313c5e410217e751073f81e76b3abf6c2806c59973d",
      "lines": 150
    }
  ],
  "public_theorems": 26,
  "all_declarations": 41
}
