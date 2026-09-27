// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// The source doubles as the destination, as in the CatCrypt lowering of `bitReverse`.
"builtin.module"() ({
  "func.func"() <{function_type = (tensor<16xi64>, tensor<4x8xi32>) -> (), sym_name = "ops"}> ({
  ^bb0(%v: tensor<16xi64>, %m: tensor<4x8xi32>):
    %0 = "tensor_ext.bit_reverse"(%v, %v) <{dimension = 0 : i64}> : (tensor<16xi64>, tensor<16xi64>) -> tensor<16xi64>
    %1 = "tensor_ext.bit_reverse"(%m, %m) <{dimension = 1 : i64}> : (tensor<4x8xi32>, tensor<4x8xi32>) -> tensor<4x8xi32>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "tensor_ext.bit_reverse"(%{{.*}}, %{{.*}}) <{"dimension" = 0 : i64}> : (tensor<16xi64>, tensor<16xi64>) -> tensor<16xi64>
// CHECK: "tensor_ext.bit_reverse"(%{{.*}}, %{{.*}}) <{"dimension" = 1 : i64}> : (tensor<4x8xi32>, tensor<4x8xi32>) -> tensor<4x8xi32>
