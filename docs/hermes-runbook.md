# Hermes 持续推进运行手册（2026-11-17 起生效）


<!-- TOC START -->

- [Hermes 持续推进运行手册（2026-11-17 起生效）](#hermes-持续推进运行手册2026-11-17-起生效)
  - [0. 铁律（不可违反）](#0-铁律不可违反)
  - [1. 每轮 Loop 协议（中断自愈核心）](#1-每轮-loop-协议中断自愈核心)
  - [2. 三车道并行机制（CPU 脚本 / GPU / hermes）](#2-三车道并行机制cpu-脚本--gpu--hermes)
    - [分工](#分工)
    - [作业卡（states/queue/ 下的 JSON）](#作业卡statesqueue-下的-json)
    - [并行安全](#并行安全)
  - [3. 任务选择算法](#3-任务选择算法)
  - [4. 验收与完成定义（DoD）](#4-验收与完成定义dod)
  - [5. 事故恢复协议（文件失踪等）](#5-事故恢复协议文件失踪等)
  - [6. 用户依赖项（blockers，需人在 loop 外解决）](#6-用户依赖项blockers需人在-loop-外解决)
  - [7. 目录约定](#7-目录约定)

<!-- TOC END -->

> 本文件是 hermes 每轮 loop 的**唯一入口**。每轮开始先读本文件 + `states/hermes-state.json` + `states/journal.md` 末尾。
> 任务全集见 `states/task-queue.yaml`（机器可读）。状态与日志只在 `states/` 维护。
> 总纲：`research/2026-alignment-plan.md`（Phase R 路线图）；本手册将其转为可执行协议。

## 0. 铁律（不可违反）

1. **只移动不删除**：任何清理一律 `git mv` 到 `docs/Refactor/archive/`；唯二例外：(a) 用户明示删除的批次；(b) 保留期满的归档批次（须 journal 记录）。
2. **不 `git push`**；commit 规范：`hermes(<task-id>): <一句话>`，每任务至少一提交。
3. **每轮 loop 第一件事** = `python tools/integrity_check.py`。退出码 1（MISSING 文件）→ 立即进入恢复协议，不做任何其他操作。
4. 审计豁免清单（README / research/ / docs/ / 映射层 / .vscode / API文档标准.md）**不得扩大**，除非用户在对话中明示。
5. 单次影响 >20 个文件的操作：先在 journal 写明计划与回滚方式，再执行。
6. 不得声称"已形式化验证/已通过模型检验"，除非对应可执行工件存在于 `tools/` 且本地或 CI 跑通（治理规则第 4 条）。

## 1. 每轮 Loop 协议（中断自愈核心）

```
1. 读 states/hermes-state.json 与 journal 末尾 → 确认上轮断点
2. python tools/integrity_check.py
   - 退出码 1 → 恢复协议（见 §5）后终止本轮
   - 退出码 2 → 先处理 dirty（提交或记入 state.blockers）
3. 回收作业队列：states/queue/running/ 中 updated 超 30 分钟的卡 → 重置为 pending
4. 计算可执行任务：task-queue.yaml 中 status=pending 且 deps 全为 done 且 resources 就绪
5. 并行分派（见 §2 三车道）：把作业卡写入 states/queue/{cpu,gpu}/pending/
6. 执行/等待结果 → 逐卡验收（acceptance 命令通过才算 done）
7. 每完成一任务：git 提交 → 更新 hermes-state.json → journal 追加（≤5 行/任务）
8. 本轮无可做任务 → journal 记 "idle: <原因>"，结束
```

**中断恢复**：任何时刻被杀 → 下轮 loop 从第 1 步开始；running 卡超时回收；git 未提交改动由第 2 步发现。所有脚本必须幂等（重跑结果一致），这是任务准入条件。

## 2. 三车道并行机制（CPU 脚本 / GPU / hermes）

### 分工
| 车道 | 承担 | 特征 |
|---|---|---|
| **CPU 车道** | 确定性脚本任务：质量审计/归档对账、TOC 再生成、断链修复、完整性自检、基线版本核查、git 机械操作 | 幂等、无人值守、可批量；作业 = 一条 shell 命令或 python 脚本 |
| **GPU 车道** | 本地模型推理任务：B 类文件语义打分、近重复聚类（embedding）、模板填充检测、术语一致性检查 | 需 GPU；通过统一作业接口提交（见下） |
| **hermes 车道** | 编排与裁决：选任务、派单、验收、合并/归档决策、写计划、处理事故、与用户对话 | 每轮 loop 的大脑；不直接做大批量机械操作 |

### 作业卡（states/queue/ 下的 JSON）
```json
{
  "id": "gpu-breview-001",
  "task_ref": "T-BREVIEW",
  "lane": "gpu",
  "input": "states/queue/gpu-breview-001/in/",
  "output": "states/queue/gpu-breview-001/out/result.json",
  "prompt": "states/queue/gpu-breview-001/prompt.md",
  "acceptance": "test -s states/queue/gpu-breview-001/out/result.json",
  "status": "pending",
  "updated": "2026-11-17T00:00:00"
}
```
- CPU worker：`states/runners/cpu_worker.py`（轮询 cpu/pending，执行 command 字段，写 out，置 done/failed）
- GPU worker：`states/runners/gpu_worker.py` —— 适配器模式，默认对接本地 OpenAI 兼容 HTTP 端点（环境变量 `GPU_API_BASE`/`GPU_API_KEY`/`GPU_MODEL`），输入 = prompt.md + in/ 文件，输出 = out/result.json；换推理引擎只改这一个文件
- hermes 每轮：派单 → 轮询 → 验收 → 落库

### 并行安全
- 任务卡带 `touches`（涉及路径前缀）；两卡 touches 相交 → 串行（后卡等前卡 done）
- 一切文件变更先入 git（每任务一提交），冲突以 git status 为准，不强行合并

## 3. 任务选择算法

优先级 = P0 > P1 > P2；同 P 内：deps 少 > 阻塞少 > queue 顺序。
**P0（现在就能做）**：T-BREVIEW（GPU+hermes）、T-R7-REST（CPU+hermes）、T-R10（CPU）
**P1（工具链就绪后）**：T-R5-* 系列（CPU 脚本本机可验的子集先做：SMT/Z3；TLA+/Coq/Isabelle/Alloy 先出 draft）、T-R6-VERIFY
**P2（周期/排期）**：T-QUARTER、T-FLIPFLOP-WATCH、T-ARCHIVE-REVIEW（2027-02）
**PARKED（不主动做）**：Wave 3 重写（用户暂缓，未来 GPU 车道主力）、前沿 stub 立项、UPPAAL 工件

## 4. 验收与完成定义（DoD）

- 每个任务在 task-queue.yaml 里自带 `acceptance`（可执行判定）。通过 → status=done + commit；失败 → 重试 ≤2 次 → failed + blockers 记录。
- 结构性任务（归档/合并/重编号）完成后必须：审计复跑（`python tools/content_quality_audit.py`）+ `python tools/ci_quality_gate.py` PASS + `python tools/integrity_check.py` 干净。
- B 类裁决任务：每批产出 keep/archive 清单文件（`states/breview/batch-NNN.json`），archive 项 `git mv` 执行后 gate 仍 PASS。

## 5. 事故恢复协议（文件失踪等）

1. `git status --porcelain` 为空但 `integrity_check` 报 MISSING → 文件被外部删除且已提交：`git log --diff-filter=D -1 -- <path>` 找删除点，`git checkout <删除点>~1 -- <path>` 恢复。
2. 恢复后检查同类范围：`git ls-tree -r HEAD --name-only | while read f; do [ -f "$f" ] || echo "$f"; done`
3. journal 记 incident（时间、范围、恢复提交、怀疑原因——历史案例：E:\_src 疑在 OneDrive/受安全软件管控）。
4. 同一轮内若 MISSING 复发 → 停止 loop，要求用户排查同步盘/杀毒后重开。

## 6. 用户依赖项（blockers，需人在 loop 外解决）

- **WSL 安装 Coq 8.19+ 与 Isabelle 2024** → 解锁 T-R6-VERIFY 的 Coq/Isabelle 复验、T-R5-COQ/ISA 的本机验证
- **UPPAAL 学术许可证注册** → 解锁两个 UPPAAL 模型运行（或维持 draft）
- **确认 E:\_src 的 OneDrive/安全软件状态** → 防止文件再次失踪
- GPU worker 端点配置（`GPU_API_BASE` 等环境变量）

## 7. 目录约定

```
states/
  hermes-state.json     # 机器状态（当前任务、进度、blockers）
  journal.md            # 追加式日志（每任务 ≤5 行）
  task-queue.yaml       # 任务全集（唯一权威）
  breview/              # B 类裁决批次清单
  queue/{cpu,gpu}/{pending,running,done,failed}/   # 作业卡
  runners/              # cpu_worker.py / gpu_worker.py
tools/
  integrity_check.py    # 每轮第一道闸
  content_quality_audit.py / quality_audit_apply.py / quality_audit_reconcile.py
  ci_quality_gate.py / toc_generator.py / toc_validate.py / domain1_renumber.py
```
