# Markdown TOC 生成工具

多线程生成/更新 Markdown 目录（TOC）。自动在文档中按如下标记维护目录区块：

```text
<!-- TOC START -->

- [Markdown TOC 生成工具](#markdown-toc-生成工具)
  - [快速使用](#快速使用)
  - [参数说明](#参数说明)
  - [生成规则](#生成规则)
  - [常见问题](#常见问题)
  - [退出码与总结](#退出码与总结)
  - [TOC 校验工具](#toc-校验工具)
  - [在提交流程中启用校验](#在提交流程中启用校验)
- [一次性设置 hooksPath](#一次性设置-hookspath)
- [手动触发一次（可选）](#手动触发一次可选)
  - [形式化工件（Phase 9）](#形式化工件phase-9)

<!-- TOC END -->
```

- 默认在首个 H1 标题后插入；无 H1 则置于文件最前。
- 再次运行会就地更新该区块，非目录内容不被修改。
- 仅处理编号主题目录（如 `1.*`、`2.*` 等）及 `docs/Refactor`，除非使用 --all。

## 快速使用

- 干跑预览（不写文件）：

```bash
python tools/toc_generator.py --max-level 4 --workers 12
```

- 实际写入：

```bash
python tools/toc_generator.py --max-level 4 --workers 12 --apply
```

- 指定路径（可为文件或目录）：

```bash
python tools/toc_generator.py 1.* 2.* docs/Refactor --apply
```

- 不限制目录（全仓库 .md）：

```bash
python tools/toc_generator.py --all --apply
```

## 参数说明

- `paths`：可选。扫描目标，默认当前目录。
- `--max-level`：纳入目录的最大标题层级（1-6），默认 4。
- `--apply`：启用后写回文件；不带时为干跑。
- `--all`：不限制到编号目录与 `docs/Refactor`。
- `--workers`：并发线程数，默认 `CPU 核数`。

## 生成规则

- 标题锚点使用 GitHub 风格 slug，保留 CJK 字符；空白转 `-`，连续连字符折叠。
- 每级标题使用两个空格缩进：

```text
- H1
  - H2
    - H3
```

## 常见问题

- PowerShell 管道与 `cat`：如需显示长输出，直接运行命令即可；不要在 PowerShell 中使用 `| cat`。
- 已存在不完整标记：若发现 `<!-- TOC START -->` 无闭合 `<!-- TOC END -->`，会视为不存在并重新插入。

## 退出码与总结

执行结束会输出统计：处理文件数、变更数、未变更数、错误数，便于批量校验。

## TOC 校验工具

并行验证已有 TOC 的完整性与一致性：

```bash
python tools/toc_validate.py --max-level 4 --workers 12
```

说明：

- 检查缺失 TOC（存在标题却无 TOC）。
- 检查 TOC 中的锚点是否能在标题中解析。
- 对比 TOC 内容与根据当前标题重新生成的结果是否一致。
- 返回码非 0 表示存在问题，适合用于 CI/预提交钩子。

## 在提交流程中启用校验

- 预提交钩子：

```bash
# 一次性设置 hooksPath
git config core.hooksPath .githooks

# 手动触发一次（可选）
bash .githooks/pre-commit
```

- CI（Windows 代理示例）：

```powershell
powershell -ExecutionPolicy Bypass -File tools/ci_toc_check.ps1 -MaxLevel 4 -Workers 12
```

---

## 形式化工件（Phase 9）

本目录还包含网络、IoT、容器/微服务等主题的可执行形式化工件。`tools/tla-specifications/` 下全部 6 对 `.tla` / `.cfg` 已使用随附的 `tla2tools.jar` 通过 TLC 模型检验，验证日志见 `validation/verification-results/tla-phase9/`。

| 路径 | 引擎 | 内容 | 验证方式 |
|---|---|---|---|
| `tools/tla-specifications/Raft.tla` + `.cfg` | TLA+ / TLC | Raft 共识简化模型（Leader 选举、日志复制、安全性质） | `cd tools/tla-specifications && java -cp tla2tools.jar tlc2.TLC Raft -config Raft.cfg` |
| `tools/tla-specifications/Kubernetes.tla` + `.cfg` | TLA+ / TLC | Kubernetes Pod 生命周期与 Deployment 滚动更新 | `cd tools/tla-specifications && java -cp tla2tools.jar tlc2.TLC Kubernetes -config Kubernetes.cfg` |
| `tools/tla-specifications/QUIC.tla` + `.cfg` | TLA+ / TLC | QUIC/TCP 传输层握手状态机与安全性质 | `cd tools/tla-specifications && java -cp tla2tools.jar tlc2.TLC QUIC -config QUIC.cfg` |
| `tools/tla-specifications/TCP_CongestionControl.tla` + `.cfg` | TLA+ / TLC | TCP Reno/CUBIC 拥塞控制状态机（慢启动、拥塞避免、快速重传/恢复、超时） | `cd tools/tla-specifications && java -cp tla2tools.jar tlc2.TLC TCP_CongestionControl -config TCP_CongestionControl.cfg` |
| `tools/tla-specifications/BGP_PathSelection.tla` + `.cfg` | TLA+ / TLC | 3 路由器 BGP 路径选择、LOCAL_PREF/AS_PATH 选路、收敛性 | `cd tools/tla-specifications && java -cp tla2tools.jar tlc2.TLC BGP_PathSelection -config BGP_PathSelection.cfg` |
| `tools/tla-specifications/OSPF_LinkState.tla` + `.cfg` | TLA+ / TLC | OSPF 链路状态协议邻居状态机、LSA 泛洪、LSDB 同步与 SPF 计算 | `cd tools/tla-specifications && java -cp tla2tools.jar tlc2.TLC OSPF_LinkState -config OSPF_LinkState.cfg` |
| `tools/alloy-models/IoT_DeviceAccessControl.als` | Alloy 6 | IoT 设备访问控制：角色、权限、互斥与所有者约束 | `java -jar tools/alloy-models/org.alloytools.alloy.dist.jar exec -f tools/alloy-models/IoT_DeviceAccessControl.als` |
| `tools/smt-examples/Container_Resource_Allocation_v2.smt2` | Z3 4.13 | 多节点容器资源分配：CPU/内存 requests/limits、容量、反亲和性、bin-packing | `tools/engines/z3-4.13.0-x64-win/bin/z3.exe tools/smt-examples/Container_Resource_Allocation_v2.smt2` |

> 注意：TLC 需要从 `.tla` 文件所在目录运行；`tla2tools.jar` 已复制到 `tools/tla-specifications/` 以便使用。完整运行说明与状态见 `tools/tla-specifications/README.md`。
