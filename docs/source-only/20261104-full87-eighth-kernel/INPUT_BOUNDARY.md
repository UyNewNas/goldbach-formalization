# 稿内证明与稿外输入边界

本轮只实现 P1.4 的稿内第八层残余核控制，不实现稿外数论定理。

## 稿内对象与本轮新增

- 采用原87 Source、comparison/newCap、原 finiteCap、原有 licensedCap 与 level6Exponent；不修改数组、策略或 occurrence 列表。
- 核的规范化按稿内 `eq:current-eighth-saving`：系数4，无 Chen 四分之一、无排序阶乘。
- 从原 Source 直接推导正下端点与残余分母下界，证明真实核可积；证明舍入损失、实际 parent 上的保守比较、与已有参数顺序相容的共同积分预算。
- mathlib 固定版本中的测度、可测性、积分支配与有限和工具按原依赖复用，不重新证明库定理。

稿件核对 pin：`UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`，`paper/source/manuscript-body.tex:434-485`，blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`。只核对相关段落，不宣称全稿或最新数值包重新认证。

## 稿外输入：只记录，不实现

PNT/Mertens、原稿引用的经典筛法/分布/谱论定理，继续留在项目稿外输入审计清单。本轮没有新增其 Lean 证明、公理、wrapper 或假装已经供应的许可字段。未在本轮逐项核对的精确定理号、版本、参数范围、归一化与共同阈值，继续标为待核实。

## 仍属稿内的剩余义务

实际新第八层 signed frontier 到残余核积分的同对象均值桥；第六层过滤动作损失；原 full-q/beta、重数、边界/重复异常与 changed/tagged 算术覆盖；全 saved 档案几何及原积分/数值增益覆盖；两本独立 reserve 与最终同 rho 装配。这些不能因为会调用稿外定理就变成稿外假设。

本轮仅支付第八层真实核的裁剪/舍入/盒遗漏解析预算。不能把它称为第六层损失、总 signed gain、素数计数误差或完整 reserve 的付款。

同源编译、kernel replay、传递公理检查、原有限证书求值和独立复核属于形式化验收，不是稿外输入；本轮均未执行。

工具链保持 Lean `leanprover/lean4:v4.33.0-rc1`、mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`、原上游 `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`。
