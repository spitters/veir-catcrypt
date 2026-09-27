// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// Two RNS limbs, N = 8; storage i64 (omitted) unless given, basis coeff (omitted) unless eval.
!R = !ring.rq<[12289, 40961], 8 : i32>
!Rhat = !ring.rq<[12289, 40961], 8 : i32, eval>
!R3 = !ring.rq<[12289, 40961, 65537], 8 : i32>
!Rs = !ring.rq<[3329], 8 : i32, i32, eval>
"builtin.module"() ({
  "func.func"() <{function_type = (!R, !Rhat, !R3, !Rs, tensor<2x8xi64>, tensor<8x!field.pf<12289 : i64>>, tensor<8x!field.pf<40961 : i64>>) -> (), sym_name = "ops"}> ({
  ^bb0(%r: !R, %h: !Rhat, %r3: !R3, %s: !Rs, %t: tensor<2x8xi64>, %l0: tensor<8x!field.pf<12289 : i64>>, %l1: tensor<8x!field.pf<40961 : i64>>):
    %0 = "ring.from_tensor"(%t) : (tensor<2x8xi64>) -> !R
    %1 = "ring.to_tensor"(%r) : (!R) -> tensor<2x8xi64>
    %2 = "ring.from_limbs"(%l0, %l1) : (tensor<8x!field.pf<12289 : i64>>, tensor<8x!field.pf<40961 : i64>>) -> !Rhat
    %3:2 = "ring.to_limbs"(%h) : (!Rhat) -> (tensor<8x!field.pf<12289 : i64>>, tensor<8x!field.pf<40961 : i64>>)
    %4 = "ring.automorphism"(%r) <{exponent = 5 : i64}> : (!R) -> !R
    %5 = "ring.rescale"(%r3) : (!R3) -> !R
    %6 = "ring.add"(%r, %0) : (!R, !R) -> !R
    %7 = "ring.sub"(%r, %0) : (!R, !R) -> !R
    %8 = "ring.negate"(%r) : (!R) -> !R
    %9 = "ring.mul"(%h, %2) : (!Rhat, !Rhat) -> !Rhat
    %10 = "ring.base_convert"(%r) : (!R) -> !R3
    %11 = "ring.mul"(%s, %s) : (!Rs, !Rs) -> !Rs
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "func.func"() <{"function_type" = (!ring.rq<[12289, 40961], 8 : i32>, !ring.rq<[12289, 40961], 8 : i32, eval>, !ring.rq<[12289, 40961, 65537], 8 : i32>, !ring.rq<[3329], 8 : i32, i32, eval>, tensor<2x8xi64>, tensor<8x!field.pf<12289 : i64>>, tensor<8x!field.pf<40961 : i64>>) -> (), "sym_name" = "ops"}>
// CHECK: "ring.from_tensor"(%{{.*}}) : (tensor<2x8xi64>) -> !ring.rq<[12289, 40961], 8 : i32>
// CHECK: "ring.to_tensor"(%{{.*}}) : (!ring.rq<[12289, 40961], 8 : i32>) -> tensor<2x8xi64>
// CHECK: "ring.from_limbs"(%{{.*}}, %{{.*}}) : (tensor<8x!field.pf<12289 : i64>>, tensor<8x!field.pf<40961 : i64>>) -> !ring.rq<[12289, 40961], 8 : i32, eval>
// CHECK: "ring.to_limbs"(%{{.*}}) : (!ring.rq<[12289, 40961], 8 : i32, eval>) -> (tensor<8x!field.pf<12289 : i64>>, tensor<8x!field.pf<40961 : i64>>)
// CHECK: "ring.automorphism"(%{{.*}}) <{"exponent" = 5 : i64}> : (!ring.rq<[12289, 40961], 8 : i32>) -> !ring.rq<[12289, 40961], 8 : i32>
// CHECK: "ring.rescale"(%{{.*}}) : (!ring.rq<[12289, 40961, 65537], 8 : i32>) -> !ring.rq<[12289, 40961], 8 : i32>
// CHECK: "ring.add"
// CHECK: "ring.sub"
// CHECK: "ring.negate"
// CHECK: "ring.mul"(%{{.*}}, %{{.*}}) : (!ring.rq<[12289, 40961], 8 : i32, eval>, !ring.rq<[12289, 40961], 8 : i32, eval>) -> !ring.rq<[12289, 40961], 8 : i32, eval>
// CHECK: "ring.base_convert"(%{{.*}}) : (!ring.rq<[12289, 40961], 8 : i32>) -> !ring.rq<[12289, 40961, 65537], 8 : i32>
// CHECK: "ring.mul"(%{{.*}}, %{{.*}}) : (!ring.rq<[3329], 8 : i32, i32, eval>, !ring.rq<[3329], 8 : i32, i32, eval>) -> !ring.rq<[3329], 8 : i32, i32, eval>
