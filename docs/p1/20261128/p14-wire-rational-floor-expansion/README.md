原整数算法的定向 floor 证明接口。

模块 `ImbalancedChen.P5OriginalWireRationalFloorExpansion` 的隔离 normal、仅本模块 kernel 和完整 owned 审计已通过，含 18 项 owned 声明、10 项私有声明；独立只读复核无阻断。

Rational expression identity only, no integer floor or stored certificate.

不重编译或重放已验收依赖。完整类型、Lean.Expr、宇宙参数与公理均归档，公理仅标准三项。直接 Lean 验收不等同 Lake 命名目标或全导入闭包重放。P1.4/P1.5 总目标仍未闭合，原登记 18/21 和三个 HOLD 不变。

运行 `python -B package_evidence.py` 可重新核验文件指纹、回执、复用别名与归档。
