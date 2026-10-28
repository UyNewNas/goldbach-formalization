# certificate_rows 第二批交验

已写完整局部源码 `P2Winner9SelectedRowRealJacobian.lean`。本批指定的实线性等价、det/Jacobian 与实际 support 测度连接已在源码中闭合；原始 row21/22 整体绑定目标仍未完成，故 local_step_complete=true、task_complete=false。所有源码与依赖均未编译，正式信用为0。

证明从第一批原始有理边矩阵开始：`Rat.cast_det` 把 determinant 嵌入 ℝ；`Matrix.toLin'` 与有限维 continuous linear map 保留 determinant，再以 `ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero` 构造可逆实映射。这里的非退化证据来自原始有理 determinant source，未把实映射存在、所需 Jacobian 或目标体积改成前提。

新源码逐坐标证明该 CLE 的 affinePoint 就是第一批同一个九顶点 ordered-edge map，并把 `physicalSupport` 与直接由实际顶点定义的 `sourceSupport` 等同。因此可直接应用前稿的真实 Lebesgue affine-image theorem，得到 sourceSupport 上任意实函数的积分、体积及原始 physical mixed/upper integrand 的传输。具体 row21/22 的 Jacobian 均为 `8! * literal physicalVolume`，两行 support 的积分体积各自等于原始 literal volume，并单独给出正 Jacobian 守卫以供后续加权比值消去。

没有执行第一批 closed `decide +kernel`、Lean/lake、producer、数值或证书 checker；第一批文件完整冻结。当前结果始终相对于这些未编译依赖。真实 Y/deviation 与 `SimplexData` 整数尺度的对应、mixed identity、cap/floor/all22/all17572 与当前c仍待完成。未发现新的原稿数学缺口。

使用的 Mathlib API 直接读取钉住的 `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1` 源码：[Rat.cast_det](https://raw.githubusercontent.com/leanprover-community/mathlib4/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean)、[det_toLin'](https://raw.githubusercontent.com/leanprover-community/mathlib4/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/LinearAlgebra/Determinant.lean)、[有限维连续化与det非零构造器](https://raw.githubusercontent.com/leanprover-community/mathlib4/e4c91783ca8e6a7c693ae624ade32fd22d4e43c1/Mathlib/Topology/Algebra/Module/FiniteDimension.lean)。精确本地依赖及远端读到的源码hash均记于REGISTRY.json。
