// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

"builtin.module"() ({
  "func.func"() <{function_type = (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32, true>, i32, tensor<4x!mod_arith.int<17 : i32>>) -> (), sym_name = "ops"}> ({
  ^bb0(%a: !mod_arith.int<17 : i32>, %m: !mod_arith.int<17 : i32, true>, %w: i32, %t: tensor<4x!mod_arith.int<17 : i32>>):
    %0 = "mod_arith.constant"() <{value = 13 : i32}> : () -> !mod_arith.int<17 : i32>
    %1 = "mod_arith.bitcast"(%a) : (!mod_arith.int<17 : i32>) -> i32
    %2 = "mod_arith.bitcast"(%w) : (i32) -> !mod_arith.int<17 : i32>
    %3 = "mod_arith.mont_reduce"(%w, %w) : (i32, i32) -> !mod_arith.int<17 : i32>
    %4 = "mod_arith.to_mont"(%a) : (!mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32, true>
    %5 = "mod_arith.from_mont"(%m) : (!mod_arith.int<17 : i32, true>) -> !mod_arith.int<17 : i32>
    %6 = "mod_arith.cmp"(%a, %0) <{predicate = 0 : i64}> : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> i1
    %7 = "mod_arith.negate"(%a) : (!mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
    %8 = "mod_arith.square"(%a) : (!mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
    %9 = "mod_arith.mont_square"(%m) : (!mod_arith.int<17 : i32, true>) -> !mod_arith.int<17 : i32, true>
    %10 = "mod_arith.inverse"(%a) : (!mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
    %11 = "mod_arith.double"(%a) : (!mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
    %12 = "mod_arith.mont_inverse"(%m) : (!mod_arith.int<17 : i32, true>) -> !mod_arith.int<17 : i32, true>
    %13 = "mod_arith.add"(%a, %0) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
    %14 = "mod_arith.sub"(%a, %0) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
    %15 = "mod_arith.mul"(%a, %0) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
    %16 = "mod_arith.mont_mul"(%m, %m) : (!mod_arith.int<17 : i32, true>, !mod_arith.int<17 : i32, true>) -> !mod_arith.int<17 : i32, true>
    %17 = "mod_arith.barrett_mul"(%a, %0) : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32>
    %18 = "mod_arith.negate"(%t) : (tensor<4x!mod_arith.int<17 : i32>>) -> tensor<4x!mod_arith.int<17 : i32>>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "func.func"() <{"function_type" = (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32, true>, i32, tensor<4x!mod_arith.int<17 : i32>>) -> (), "sym_name" = "ops"}>
// CHECK: "mod_arith.constant"() <{"value" = 13 : i32}> : () -> !mod_arith.int<17 : i32>
// CHECK: "mod_arith.bitcast"(%{{.*}}) : (!mod_arith.int<17 : i32>) -> i32
// CHECK: "mod_arith.bitcast"(%{{.*}}) : (i32) -> !mod_arith.int<17 : i32>
// CHECK: "mod_arith.mont_reduce"(%{{.*}}, %{{.*}}) : (i32, i32) -> !mod_arith.int<17 : i32>
// CHECK: "mod_arith.to_mont"(%{{.*}}) : (!mod_arith.int<17 : i32>) -> !mod_arith.int<17 : i32, true>
// CHECK: "mod_arith.from_mont"(%{{.*}}) : (!mod_arith.int<17 : i32, true>) -> !mod_arith.int<17 : i32>
// CHECK: "mod_arith.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = 0 : i64}> : (!mod_arith.int<17 : i32>, !mod_arith.int<17 : i32>) -> i1
// CHECK: "mod_arith.negate"
// CHECK: "mod_arith.square"
// CHECK: "mod_arith.mont_square"(%{{.*}}) : (!mod_arith.int<17 : i32, true>) -> !mod_arith.int<17 : i32, true>
// CHECK: "mod_arith.inverse"
// CHECK: "mod_arith.double"
// CHECK: "mod_arith.mont_inverse"
// CHECK: "mod_arith.add"
// CHECK: "mod_arith.sub"
// CHECK: "mod_arith.mul"
// CHECK: "mod_arith.mont_mul"
// CHECK: "mod_arith.barrett_mul"
// CHECK: "mod_arith.negate"(%{{.*}}) : (tensor<4x!mod_arith.int<17 : i32>>) -> tensor<4x!mod_arith.int<17 : i32>>
