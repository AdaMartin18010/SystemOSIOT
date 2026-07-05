import Lake
open Lake DSL

package «SystemOSIOTLean» where
  -- 单文件示例，无外部依赖

@[default_target]
lean_lib SystemOSIOTLean where
  roots := #[`SimpleTypeTheory, `PacketSeqMonotonicity]
