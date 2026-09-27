// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// The maximum degree is written without a type; it is an i64 attribute and prints as such.
"builtin.module"() ({
  "func.func"() <{function_type = (!poly.polynomial<!field.pf<7 : i32>, 3>, tensor<4x!field.pf<7 : i32>>) -> (), sym_name = "ops"}> ({
  ^bb0(%p: !poly.polynomial<!field.pf<7 : i32>, 3>, %t: tensor<4x!field.pf<7 : i32>>):
    %0 = "poly.to_tensor"(%p) : (!poly.polynomial<!field.pf<7 : i32>, 3>) -> tensor<4x!field.pf<7 : i32>>
    %1 = "poly.from_tensor"(%t) : (tensor<4x!field.pf<7 : i32>>) -> !poly.polynomial<!field.pf<7 : i32>, 3 : i64>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "func.func"() <{"function_type" = (!poly.polynomial<!field.pf<7 : i32>, 3 : i64>, tensor<4x!field.pf<7 : i32>>) -> (), "sym_name" = "ops"}>
// CHECK: "poly.to_tensor"(%{{.*}}) : (!poly.polynomial<!field.pf<7 : i32>, 3 : i64>) -> tensor<4x!field.pf<7 : i32>>
// CHECK: "poly.from_tensor"(%{{.*}}) : (tensor<4x!field.pf<7 : i32>>) -> !poly.polynomial<!field.pf<7 : i32>, 3 : i64>
