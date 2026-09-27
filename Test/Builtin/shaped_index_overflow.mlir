// RUN: VEIR_ROUNDTRIP
// The llvm.add flags print back as `3 : i32`, which mlir-opt rejects for llvm.add, so
// this file has no MLIR round trip.

"builtin.module"() ({
  "func.func"() <{function_type = (tensor<2x3xi32>, tensor<i8>, memref<4x8xi32>, memref<16xi64, 1>, i32) -> (), sym_name = "shaped"}> ({
  ^bb0(%t: tensor<2x3xi32>, %s: tensor<i8>, %m: memref<4x8xi32>, %ms: memref<16xi64, 1>, %x: i32):
    %0 = "llvm.add"(%x, %x) <{overflowFlags = #llvm.overflow<nsw, nuw>}> : (i32, i32) -> i32
    "func.return"() {catcrypt.n = 4 : index, catcrypt.d = dense<[1, 2, 3]> : tensor<3xi64>} : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "func.func"() <{"function_type" = (tensor<2x3xi32>, tensor<i8>, memref<4x8xi32>, memref<16xi64, 1>, i32) -> (), "sym_name" = "shaped"}>
// CHECK: "llvm.add"(%{{.*}}, %{{.*}}) <{"overflowFlags" = 3 : i32}> : (i32, i32) -> i32
// CHECK: "catcrypt.d" = dense<[1, 2, 3]> : tensor<3xi64>, "catcrypt.n" = 4 : index
