<!-- source-sha256: e6c406c4fadcc5283fe5652fe520a9977ccfa7ebd10490f3eb25913745d9712c -->
# `uncompress*` 的安全性

目标是 `Goal.uncompress2_z_safe`、`Goal.uncompress2_safe`、`Goal.uncompress_z_safe` 和 `Goal.uncompress_safe`（`ZlibF/Spec/Public/Utilities.lean`）。它们在 `ZlibF/Proof/public-uncompress-safe.lean` 中无前提地证明。

## 已证明的内容

对功能目标允许的每个输入：

- 调用运行时没有未定义行为并且返回（`C.run … = .ok`）；
- 参数错误返回 `Z_STREAM_ERROR`，且不改变任何东西；
- 否则调用最多向输出缓冲区和长度单元写入 `capacity` 个字节，不写其他任何地方；
- 每条返回路径上都释放每次分配；
- 返回码是 `Z_OK`、`Z_BUF_ERROR`、`Z_DATA_ERROR` 或 `Z_MEM_ERROR`，并且 `Z_MEM_ERROR` 只在某次分配失败之后出现。

关于写出的字节没有任何断言。那是功能目标，不在计划内。

## 结构

```mermaid
flowchart TD
  init["start_state：inflateInit2_ 以及绑定的流"] --> loop
  loop["loop_run_safe：err == Z_OK 时继续的循环"] --> call
  call["call_phase_safe：一次 inflate 调用（inflate_public）"] --> loop
  loop --> epi["结尾：保存计数、inflateEnd、释放流和保留的字节"]
  epi --> z["uncompress2_z_with_safe"]
  z --> w2["counted2_of_z：uncompress2"]
  z --> w1["single_of_counted：uncompress_z、uncompress"]
```

运行过程与功能证明共用。`SafeState` 和 `SafeFinal` 包含除格式事实以外的全部内容。功能证明用 `NoOver`（源数据开头的完整流都没有被读到结尾）扩展它们。包装函数对每种数据关系只证明一次（`CountedWith`、`SingleWith`）。安全目标使用关系 `SafeRel`：输出不超过容量，消耗的输入不超过源数据，返回码有文档说明。

## 证明所用的内容

- 每次调用 `inflate` 时使用 `inflate_public`（`Goal.inflate`）。
- 对每个可达流的解码器使用 `reachable_invariant_kind`。

没有使用 `DecoderFacts` 的任何字段，也没有使用 `inflate` 的任何功能事实。

## 终止

度量是未读的源数据加上未填充的空间：`avail_in + len + avail_out + left`。重新填充在流字段和剩余长度之间移动字节，所以保持它不变。每次返回 `Z_OK` 的调用都会消耗输入或写出输出（`Goal.inflate` 的进展条款：`rc = Z_OK → used ≠ 0 ∨ out ≠ []`），所以度量减小。开始时它至多是 `sourceLen + destLen < 2^64`，小于循环燃料。所用规则是 `cdoWhile_decreasing`。
