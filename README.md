# Verified Intermediate Representation

A verified implementation of the MLIR SSA-based datastructures.

## This fork

This repository is [VeIR](https://github.com/opencompl/veir) release v4.29.0 with
the changes below, maintained for the CatCrypt compiler package, which lowers its
`Com` programs to VeIR operations. The license is upstream's Apache License 2.0
([LICENSE](LICENSE)). The release tags `v4.33.1-catcrypt.1` and earlier name the
revisions the compiler package pins.

Changes from v4.29.0:

- `Veir/OpCode.lean`: the `func.call` opcode and the opcode families `catcrypt`
  (`unknown`, a placeholder for operations with no registered counterpart),
  `memref`, `polynomial`, `vector` and `x86vector`, which the CatCrypt lowering
  targets.
- `Veir/Verifier.lean` and `Veir/Properties.lean`: the verifier cases for the new
  opcodes, and a raised heartbeat limit on the opcode decidable-equality instance,
  whose case split grows with the square of the number of opcodes.
- `Veir/ForLean.lean` and its users: two list lemmas renamed, because Mathlib
  declares lemmas with the same names.
- `Veir/Printer.lean` and `Veir/Rewriter/Basic.lean` as Lean modules.
- `lean-toolchain`: Lean v4.33.1.

## Testing

Our testing framework is split into two parts: unit tests written in Lean and
[FileCheck](https://llvm.org/docs/CommandGuide/FileCheck.html) tests for the
command line tool `veir-opt`.

### Unit Tests

Run the unit tests with:

```bash
lake test
```

### FileCheck Tests

FileCheck tests require [uv](https://docs.astral.sh/uv/) to be installed.

First, install dependencies:

```bash
uv sync
```

Then run the tests:

```bash
uv run lit Test/
```

## Running the benchmarks

```bash
lake exe run-benchmarks add-fold-worklist
```

