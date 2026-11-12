# T18 独核 T23 全收据适用性补记

**准予归档两份文字，新增数学与 kernel 信用均为 0。** T23 单收据定理的共同阈值适用于每个指定的加法素数标签。对全部标签求和会引入真实收据基数，现有七源包的误差预算只对共同的一有界标记成立。

## 同一冻结词上的有限和

固定原根、根键、shape 与有序词，保留原历史列表的位置及各自系数 $\mu_o$。每个有效位置的 $E_o$ 正是用该根的 cellQ、该位置的 memberCutoff、整词乘积和原 rootMask 构成的 frozenCarrier。原词的粗糙性和原冻结载体与加法素数标签的等式给出 $E_o\subseteq\mathcal P_N$。因此按位置与标签交换有限和，得到
$$
\sum_{\ell\in\mathcal P_N}\mathrm{probe}_{\ell}(w)
=\sum_{o\in O_w}\mu_o\,|E_o| .
$$
这里的系数非负。T17 的 owned_member_masked_count 在原根纤维和物理支持前提下把 $|E_o|$ 等同于 originalReceiptLane 的基数。去掉根掩膜时须再计 rejectedChild。此前的 $\sum_{o\in O_w}\mu_o\le1$ 控制每个单标签探针，无法给上式右端相同的上界。

固定 $\ell$ 时，T23 控制的求和项是 $\mathrm{probe}_{\ell}(w)|I_0\theta_0-I_n\theta_n|/\mathcal H_N$。求和后仍带两侧几何 $\Theta$ 的差。真实收据行则在每侧取该侧准入指标乘该侧带标记基数。若要把每侧逐词写成同一 $b(w)\theta_v$，在两侧均准入且 $\theta_v>0$ 的词上还需要两侧基数与 $\theta_v$ 的比相同，并需所要求的标记界。非负族上的有向平均估计可以绕开这个逐词要求。真实差集筛质量、共同准入位置改变截止时的收据壳，以及重选标记时的位置差，仍各需相应估计。

T19 的 original_root_plateau 保证原根掩膜下两个均不超过 $N^a$ 的截止有相同计数。independent_upper_routes 对 106 行在同一纤维内给出两个上界的较小值。T07 的 all_good_pair_count_means 对四个普通双子窗口给出有向上界，右端保留 laneAP 和 oldHMass。T24 的全元组有向上筛保留精确互素修正、有符号 PP 余项和小素数费用。这些同源行支持补件对其适用范围的说明。全收据累计误差与 Y24、整体 H34 继续待证。

## 来源记录

逐字节复核两个补件及其引用的本地冻结索引、审单、相关来源和原稿。T07 源文件的内容重建 Git blob d415659231feb29f7f386edee4cb795e1b50367c。手稿本地文件重建 blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79 与 SHA-256 ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd。补件列出的七源索引和前次独审哈希一致。

PROVENANCE 所载访问经过按作者报告归档。一次只读 ls-tree 将手稿提交传给 Lean 源的部分克隆仓库，触发 upload-pack 远端读取尝试，返回两条 not our ref，最终退出码 1，未取得目标手稿树。该命令没有请求推送或修改远端引用。当前核验依据已有手稿文件与冻结哈希，未接触网络，也未审计客户端缓存或服务器日志。根随后禁止 T23 使用任何 Git 命令。此审单仅增加两份补件的归档记录。
