// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

"builtin.module"() ({
  "func.func"() <{function_type = (!field.pf<7 : i32>, !field.pf<7 : i32, true>, !field.ef<2x!field.pf<7 : i32>, 6 : i32>, !field.ef<3x!field.ef<2x!field.pf<7 : i32>, 6 : i32>, dense<[1, 1]> : tensor<2xi32>>, i32) -> (), sym_name = "ops"}> ({
  ^bb0(%p: !field.pf<7 : i32>, %pm: !field.pf<7 : i32, true>, %e: !field.ef<2x!field.pf<7 : i32>, 6 : i32>, %e6: !field.ef<3x!field.ef<2x!field.pf<7 : i32>, 6 : i32>, dense<[1, 1]> : tensor<2xi32>>, %n: i32):
    %0 = "field.constant"() <{value = 3 : i32}> : () -> !field.pf<7 : i32>
    %1 = "field.constant"() <{value = dense<[1, 2]> : tensor<2xi32>}> : () -> !field.ef<2x!field.pf<7 : i32>, 6 : i32>
    %2 = "field.bitcast"(%p) : (!field.pf<7 : i32>) -> i32
    %3 = "field.cmp"(%p, %0) <{predicate = 1 : i64}> : (!field.pf<7 : i32>, !field.pf<7 : i32>) -> i1
    %4 = "field.to_mont"(%p) : (!field.pf<7 : i32>) -> !field.pf<7 : i32, true>
    %5 = "field.from_mont"(%pm) : (!field.pf<7 : i32, true>) -> !field.pf<7 : i32>
    %6 = "field.inverse"(%p) : (!field.pf<7 : i32>) -> !field.pf<7 : i32>
    %7 = "field.double"(%e) : (!field.ef<2x!field.pf<7 : i32>, 6 : i32>) -> !field.ef<2x!field.pf<7 : i32>, 6 : i32>
    %8 = "field.square"(%e6) : (!field.ef<3x!field.ef<2x!field.pf<7 : i32>, 6 : i32>, dense<[1, 1]> : tensor<2xi32>>) -> !field.ef<3x!field.ef<2x!field.pf<7 : i32>, 6 : i32>, dense<[1, 1]> : tensor<2xi32>>
    %9 = "field.negate"(%p) : (!field.pf<7 : i32>) -> !field.pf<7 : i32>
    %10 = "field.add"(%p, %0) : (!field.pf<7 : i32>, !field.pf<7 : i32>) -> !field.pf<7 : i32>
    %11 = "field.sub"(%e, %1) : (!field.ef<2x!field.pf<7 : i32>, 6 : i32>, !field.ef<2x!field.pf<7 : i32>, 6 : i32>) -> !field.ef<2x!field.pf<7 : i32>, 6 : i32>
    %12 = "field.mul"(%e, %p) : (!field.ef<2x!field.pf<7 : i32>, 6 : i32>, !field.pf<7 : i32>) -> !field.ef<2x!field.pf<7 : i32>, 6 : i32>
    %13 = "field.powui"(%p, %n) : (!field.pf<7 : i32>, i32) -> !field.pf<7 : i32>
    %14 = "field.powui"(%p, %n) <{unroll = false}> : (!field.pf<7 : i32>, i32) -> !field.pf<7 : i32>
    %15:2 = "field.ext_to_coeffs"(%e) : (!field.ef<2x!field.pf<7 : i32>, 6 : i32>) -> (!field.pf<7 : i32>, !field.pf<7 : i32>)
    %16 = "field.ext_from_coeffs"(%15#0, %15#1) : (!field.pf<7 : i32>, !field.pf<7 : i32>) -> !field.ef<2x!field.pf<7 : i32>, 6 : i32>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "func.func"() <{"function_type" = (!field.pf<7 : i32>, !field.pf<7 : i32, true>, !field.ef<2x!field.pf<7 : i32>, 6 : i32>, !field.ef<3x!field.ef<2x!field.pf<7 : i32>, 6 : i32>, dense<[1, 1]> : tensor<2xi32>>, i32) -> (), "sym_name" = "ops"}>
// CHECK: "field.constant"() <{"value" = 3 : i32}> : () -> !field.pf<7 : i32>
// CHECK: "field.constant"() <{"value" = dense<[1, 2]> : tensor<2xi32>}> : () -> !field.ef<2x!field.pf<7 : i32>, 6 : i32>
// CHECK: "field.bitcast"(%{{.*}}) : (!field.pf<7 : i32>) -> i32
// CHECK: "field.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = 1 : i64}> : (!field.pf<7 : i32>, !field.pf<7 : i32>) -> i1
// CHECK: "field.to_mont"(%{{.*}}) : (!field.pf<7 : i32>) -> !field.pf<7 : i32, true>
// CHECK: "field.from_mont"(%{{.*}}) : (!field.pf<7 : i32, true>) -> !field.pf<7 : i32>
// CHECK: "field.inverse"
// CHECK: "field.double"
// CHECK: "field.square"
// CHECK: "field.negate"
// CHECK: "field.add"
// CHECK: "field.sub"
// CHECK: "field.mul"(%{{.*}}, %{{.*}}) : (!field.ef<2x!field.pf<7 : i32>, 6 : i32>, !field.pf<7 : i32>) -> !field.ef<2x!field.pf<7 : i32>, 6 : i32>
// CHECK: "field.powui"(%{{.*}}, %{{.*}}) : (!field.pf<7 : i32>, i32) -> !field.pf<7 : i32>
// CHECK: "field.powui"(%{{.*}}, %{{.*}}) <{"unroll" = {{false|0 : i1}}}> : (!field.pf<7 : i32>, i32) -> !field.pf<7 : i32>
// CHECK: "field.ext_to_coeffs"(%{{.*}}) : (!field.ef<2x!field.pf<7 : i32>, 6 : i32>) -> (!field.pf<7 : i32>, !field.pf<7 : i32>)
// CHECK: "field.ext_from_coeffs"(%{{.*}}, %{{.*}}) : (!field.pf<7 : i32>, !field.pf<7 : i32>) -> !field.ef<2x!field.pf<7 : i32>, 6 : i32>
