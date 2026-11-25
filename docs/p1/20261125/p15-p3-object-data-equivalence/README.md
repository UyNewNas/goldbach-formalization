# P3 五组现有对象的完整 ModuleData 对比

状态：`FIVE_PAIRS_BOUND_COMPLETE_MODULEDATA_MODULO_VERIFIED_PACKAGE`。
P3 任务 `310d3f4f31094285923a911a771814b4` 已成功执行，退出码为 0。
这是既有对象的只读数据比较，不是新增数学 owner 的编译或内核验收，也不表示对象已经接入 P1。

## 精确比较范围

本次只比较 `P3_REUSE.json` 已列出的五组旧接受对象与当前对象：
`Part3OffDiagonalModuli`、`Part3OriginalDyadicChartPartition`、
`Part3PrimeProductChartTransfer`、`Part3PrimeProductVonMangoldt`、
`Part3ProperPrimePowerCount`。固定复用清单的 SHA-256 为
`1aab54f7655ca68ae24294d49eff3c1f08455d3c31982c78d1e017888bc1316b`；
该原清单和其中旧对象的 hash 均未修改。

独立 IO 程序逐一检查原对象的完整 `ModuleData`、全部常量与证明、imports flags、
额外常量名和完整 extension 顺序。两个输入都必须先通过原字节往返序列化检查。
唯一允许的差异是同一位置的
`_private.Lean.Compiler.ModPkgExt.0.Lean.modPkgExt`：使用 Lean 的原生 typed setter
验证旧对象为 `none`、当前对象为 `some "imbalancedChen"` 后，去掉这一条已验证的
package payload，再对全部剩余 `ModuleData` 作逐字节比较。

五组比较全部通过。每组精确旧／新 SHA-256、原真实 trace、比较结果、运行标识和
云内证据位置见 `PUBLIC_RESULT.json`。完整 constants、私有声明内容和运行时文件
inventory 保留在原云证据目录，本目录只保存有界结果及其 hash。

## 运行时绑定与首次尝试

固定 Python wrapper 绑定全部 77 项原项目源码、配置、既有接受回执、对象与真实
trace、Lean 工具链及实际载入的系统库，且在每组和最终结束时检查输入未变。
每个当前 `.olean` 的实际 Lake 字节 hash 必须等于原 trace 的 `outputs.o`。
生成的比较产物只写入独立证据目录，不进入任何项目 import 或缓存路径。

首次任务 `1ca99e78a1904d569546a86e10c87bed` 未被计为成功：wrapper 发现运行时
映射中的 `/etc/ld.so.cache` 尚未预绑定。`FIRST_ATTEMPT_BOUNDARY.json` 保留这一
失败范围。修订仅在首次 `ldd` 与子进程之前将实际 loader cache 纳入指纹；完整工具链
和库清单检查没有删除。精确修订和独立审查见 `LOADER_CACHE_REPAIR_REVIEW.json`。
最终 wrapper SHA-256 为
`b1965d917fbb8effd18735d119d86009ba1db7979577af9d2090018f724fdaff`，
Lean IO witness SHA-256 为
`6397b5690ae3cdf1aab169bfbc076fd576c93720ae9bec74c81136f2f9773385`。

## 接入边界

结果仅将这五个当前对象的数据绑定到相应旧接受对象，允许差异仅为已验证的 package
assignment。它没有证明 native ABI 相同，没有证明被导入对象的字节相同，也没有
证明 P1 的 stock Lake 缓存就绪。P3 原 trace 的 Lean 参数与 P1 当前配置之间的关系、
实际依赖对象和接收环境仍须另外核对；不能改写 trace 或旧接受 pin 来消除差异。

本目录没有重新编译五个已有数学证明，没有新增项目公理，也不增加 P1.5 完成信用。
原 guard、serializer、资源策略、normal/kernel/full-owned 验收接口均未修改。
