module

/-
# Operation Codes

This file defines the `OpCode` inductive type, which represents the set of registered
operation codes in the Veir intermediate representation (IR). Each `OpCode` corresponds
to an operation definition.
-/

import Std.Data.HashMap
import Veir.Meta.OpCode

open Std

namespace Veir

@[opcodes]
inductive Arith where
| addi
| addui_extended
| andi
| ceildivsi
| ceildivui
| cmpi
| constant
| divsi
| divui
| extsi
| extui
| floordivsi
| maxsi
| maxui
| minsi
| minui
| muli
| mulsi_extended
| mului_extended
| ori
| remsi
| remui
| select
| shli
| shrsi
| shrui
| subi
| trunci
| xori

@[opcodes]
inductive Builtin where
| unregistered
| module

@[opcodes]
inductive Func where
| func
| return
| call

@[opcodes]
inductive Llvm where
| constant
| and
| or
| xor
| add
| sub
| shl
| lshr
| ashr
| mul
| sdiv
| udiv
| srem
| urem
| icmp
| select
| trunc
| sext
| zext
| return

@[opcodes]
inductive Riscv where
| li
| lui
| auipc
| addi
| slti
| sltiu
| andi
| ori
| xori
| addiw
| slli
| srli
| srai
| add
| sub
| sll
| slt
| sltu
| xor
| srl
| sra
| or
| and
| slliw
| srliw
| sraiw
| addw
| subw
| sllw
| srlw
| sraw
| rem
| remu
| remw
| remuw
| mul
| mulh
| mulhu
| mulhsu
| mulw
| div
| divw
| divu
| divuw
| adduw
| sh1adduw
| sh2adduw
| sh3adduw
| sh1add
| sh2add
| sh3add
| slliuw
| andn
| orn
| xnor
| max
| maxu
| min
| minu
| rol
| ror
| rolw
| rorw
| sextb
| sexth
| zexth
| clz
| clzw
| ctz
| ctzw
| cpop
| cpopw
| roriw
| rori
| bclr
| bext
| binv
| bset
| bclri
| bexti
| binvi
| bseti
| pack
| packh
| packw

@[opcodes]
inductive Mod_Arith where
| add
| constant
| mul
| sub

@[opcodes]
inductive Test where
| test

/-- CatCrypt dialect: a holding pen for CatCrypt ops with no direct
    counterpart in Veir's enum (pair/sum construction, etc.).
    Lowered ops use `catcrypt.unknown` which `mlir-opt` accepts under
    `--allow-unregistered-dialect`. -/
@[opcodes]
inductive Catcrypt where
| unknown

/-- MLIR `memref` dialect (buffer/memory references). Lets the CatCrypt
    `memref{Zero,Get,Set}` ops lower to registered `memref.*` ops instead of
    `catcrypt.unknown`. -/
@[opcodes]
inductive Memref where
| alloc
| alloca
| dealloc
| load
| store
| get_global
| global
| copy
| subview
| dim

/-- MLIR `polynomial` dialect (upstream, for lattice/FHE arithmetic over
    `Z_q[X]/(f)`). Target for lowering the `latticeDialect`
    (`ntt`/`invntt`/`basemul`/`polyAddN`/`polyMulC`). -/
@[opcodes]
inductive Polynomial where
| add
| sub
| mul
| mul_scalar
| ntt
| intt
| constant
| from_tensor
| to_tensor

/-- MLIR `vector` dialect (upstream). Target for lowering packed
    `stackArr w n` operations that the jasmin / Frodo / GF / MAYO / qruov
    emitters use to express SIMD-shaped arithmetic. Lets us route the
    packed-u16/u32/u64 emits to a registered MLIR dialect (`vector.*`)
    rather than `catcrypt.unknown`. Op coverage matches what the jasmin
    sopn vector-shape ops currently emit through the verified front. -/
@[opcodes]
inductive Vector where
| broadcast
| extract
| insert
| extractelement
| insertelement
| fma
| reduction
| splat
| load
| store
| transfer_read
| transfer_write
| shuffle

/-- MLIR `x86vector` dialect (upstream). Target for the x86-specific
    intrinsics jasmin's sopn carries through to assembly: PCLMUL
    (GF(2^k) carry-less multiply for GCM / GF arithmetic), AES-NI
    (AESENC / AESDEC for AES block primitives), and VPSHUFB
    (byte-shuffle for permutation networks). Today this block is the
    LANDING ZONE for lowering jasmin's `extCall "pclmulqdq"`,
    `"aesenc"`, `"vpshufb"` leaves to registered MLIR ops. -/
@[opcodes]
inductive X86vector where
| pclmulqdq
| aesenc
| aesenclast
| aesdec
| aesdeclast
| aeskeygenassist
| vpshufb
| mask_compress
| mask_rndscale
| rsqrt

public section

/-
  An operation code (OpCode) identifies the type of an operation.
  Each OpCode corresponds to a specific operation.
-/
set_option maxRecDepth 100000
#generate_op_codes

end
end Veir
