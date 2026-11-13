# 同尖点连续谱 Fourier 系数的名称修复

审查范围为 a6aec20e831aa7f905533bec69fd0f86cd2bf9b1 的 CompactTrace 单模块。原源第 41、42 行均由 `eisenstein` 调用裸 `nativeR`，声明所在的 `ActualContinuousClassFourier20261110` 在本文件未打开。相邻 CompactSpectrum 自己的 `open` 只在该文件有效。原傅里叶声明第 139 行给出同一组所有本原入射参数上的 `nativeR a false n t`。这一定位修正了先前仅就数学结构通过的 pretrace 源选。

从 Git 对象读取原件、未改的配对 CompactSpectrum 及系数供应，再按字节验证两处替换恰好产生新件。前件 blob 为 `c17935df92c9a7da67899b542d7413d2b4497e73`，后件为 `9c7cdea7057b66c65ab32df0a58659d368ee8610`。两处均使用完整声明名 `ImbalancedChen.Part3.ActualContinuousClassFourier20261110.nativeR`。五个声明头和一个局部实例沿用原件。两侧的标记 n、m，布尔值 false，径向探针，高度参数 t 和 `nativeProduct` 的顺序与原空间 Gram 一致。

后续安装该模块时只取 12 的 3686 字节后件，SHA256 为 `390a1c64a67fb8eedf0aecae7d1258dbe3f2a4b4f3f59d21d5e49b6f4e570620`。配对 CompactSpectrum 复用原 blob `644e73675ede349875b0e42e3639defe8dc27e29`，系数本身使用 blob `cb7fdff1839edb0a6c5d18c1e6b9a75ada427e42`。09 的 open 变体 b11c059d 只作历史。审查只覆盖源码与原始哈希。新增定理、编译、内核核验及正式叶结论均为 0。
