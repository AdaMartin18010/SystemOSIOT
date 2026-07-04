# 实时调度可调度性分析

> **权威来源**：Liu & Layland (1973), Buttazzo *Hard Real-Time Computing Systems*。
>
> **目标**：总结实时任务可调度性判定方法，并提供工程师可直接使用的公式与检查清单。

---

## 1. 实时任务模型

每个周期性任务：

$$
\tau_i = (C_i, T_i, D_i)
$$

- $C_i$: 最坏执行时间（WCET）
- $T_i$: 周期
- $D_i$: 相对截止期限

若 $D_i = T_i$，称“隐式截止期限”（implicit deadline）。

---

## 2. 利用率测试（Rate Monotonic, RM）

对于 $n$ 个独立、周期任务，$D_i = T_i$，优先级按周期越小越高（RM）。

**充分条件（Liu & Layland）**：

$$
U = \sum_{i=1}^{n} \frac{C_i}{T_i} \le n(2^{1/n} - 1)
$$

| n | 利用率上限 |
|---|-----------|
| 1 | 1.000 |
| 2 | 0.828 |
| 3 | 0.780 |
| 4 | 0.757 |
| ∞ | ln 2 ≈ 0.693 |

---

## 3. 响应时间分析（RTA）

更精确的判定：计算每个任务的最坏响应时间 $R_i$。

$$
R_i = C_i + \sum_{j \in hp(i)} \left\lceil \frac{R_i}{T_j} \right\rceil C_j
$$

迭代至收敛。若 $R_i \le D_i$，任务可调度。

---

## 4. EDF 可调度性

最早截止期限优先（EDF）是动态优先级最优调度。

**充要条件**：

$$
\sum_{i=1}^{n} \frac{C_i}{T_i} \le 1
$$

在单处理器、隐式截止期限下，利用率 ≤ 1 即可保证可调度。

---

## 5. 优先级倒置与继承

| 问题 | 解决方案 | 效果 |
|------|----------|------|
| 优先级倒置 | 优先级继承协议（PIP） | 阻塞时间有限 |
| 链式阻塞 | 优先级天花板协议（PCP） | 避免死锁 |
| 共享资源冲突 | 互斥锁 PI/PCP 属性 | 保证实时性 |

---

## 6. 工程师检查清单

- [ ] 明确每个任务的 $C_i, T_i, D_i$
- [ ] 测量或静态分析 WCET
- [ ] 选择 RM 或 EDF
- [ ] 计算利用率或执行 RTA
- [ ] 评估优先级倒置风险
- [ ] 配置 PI/PCP 互斥锁
- [ ] 使用 Trace/cyclictest 验证

---

## 7. 相关文件

- [RTOS 概念树](./rtos-concept-tree.md)
- [Linux vs RTOS 决策树](../06-decision-trees/linux-vs-rtos.md)

## 国际权威来源链接 / Authoritative Sources

- [Liu & Layland, "Scheduling Algorithms for Multiprogramming in a Hard-Real-Time Environment", JACM 1973](https://doi.org/10.1145/321738.321743)
- [Buttazzo, *Hard Real-Time Computing Systems* (Springer)](https://link.springer.com/book/10.1007/978-3-031-04138-0)
- [Rate Monotonic Analysis (NASA)](https://shemesh.larc.nasa.gov/fm/papers/RMA-93.pdf)
