// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// y^2 = x^3 + 3 over F_7 with G = (1, 2); -x^2 + y^2 = 1 + 2x^2y^2 over F_13 with G = (2, 4).
!pf = !field.pf<7 : i32>
!affine = !elliptic_curve.affine<#elliptic_curve.sw<0 : i32, 3 : i32, (1 : i32, 2 : i32)> : !field.pf<7 : i32>>
!jacobian = !elliptic_curve.jacobian<#elliptic_curve.sw<0 : i32, 3 : i32, (1 : i32, 2 : i32)> : !field.pf<7 : i32>>
!xyzz = !elliptic_curve.xyzz<#elliptic_curve.sw<0 : i32, 3 : i32, (1 : i32, 2 : i32)> : !field.pf<7 : i32>>
!ed_affine = !elliptic_curve.ed_affine<#elliptic_curve.te<12 : i32, 2 : i32, (2 : i32, 4 : i32)> : !field.pf<13 : i32>>
!ed_extended = !elliptic_curve.ed_extended<#elliptic_curve.te<12 : i32, 2 : i32, (2 : i32, 4 : i32)> : !field.pf<13 : i32>>
"builtin.module"() ({
  "func.func"() <{function_type = (!pf, !affine, !jacobian, !xyzz, !ed_affine, !ed_extended, tensor<4x!pf>, tensor<4x!affine>) -> (), sym_name = "ops"}> ({
  ^bb0(%s: !pf, %a: !affine, %j: !jacobian, %x: !xyzz, %ea: !ed_affine, %ee: !ed_extended, %ss: tensor<4x!pf>, %ps: tensor<4x!affine>):
    %0 = "elliptic_curve.constant"() <{coords = [[1 : i32, 2 : i32]]}> : () -> !affine
    %1 = "elliptic_curve.from_coords"(%s, %s) : (!pf, !pf) -> !affine
    %2:3 = "elliptic_curve.to_coords"(%j) : (!jacobian) -> (!pf, !pf, !pf)
    %3 = "elliptic_curve.is_zero"(%j) : (!jacobian) -> i1
    %4 = "elliptic_curve.add"(%j, %a) : (!jacobian, !affine) -> !jacobian
    %5 = "elliptic_curve.sub"(%x, %x) : (!xyzz, !xyzz) -> !xyzz
    %6 = "elliptic_curve.negate"(%a) : (!affine) -> !affine
    %7 = "elliptic_curve.double"(%a) : (!affine) -> !jacobian
    %8 = "elliptic_curve.scalar_mul"(%s, %j) : (!pf, !jacobian) -> !jacobian
    %9 = "elliptic_curve.cmp"(%j, %4) <{predicate = 0 : i64}> : (!jacobian, !jacobian) -> i1
    %10 = "elliptic_curve.msm"(%ss, %ps) <{degree = 2 : i32, parallel}> : (tensor<4x!pf>, tensor<4x!affine>) -> !xyzz
    %11 = "elliptic_curve.msm"(%ss, %ps) <{degree = 2 : i32, windowBits = 4 : i32}> : (tensor<4x!pf>, tensor<4x!affine>) -> !jacobian
    %12 = "elliptic_curve.pairing_check"(%ps, %ps) : (tensor<4x!affine>, tensor<4x!affine>) -> i1
    %13 = "elliptic_curve.convert_point_type"(%j) : (!jacobian) -> !xyzz
    %14 = "elliptic_curve.bitcast"(%a) : (!affine) -> tensor<2x!pf>
    %15 = "elliptic_curve.add"(%ee, %ee) : (!ed_extended, !ed_extended) -> !ed_extended
    %16 = "elliptic_curve.convert_point_type"(%ea) : (!ed_affine) -> !ed_extended
    %17 = "elliptic_curve.double"(%ee) : (!ed_extended) -> !ed_extended
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "func.func"() <{"function_type" = (!field.pf<7 : i32>, !elliptic_curve.affine<#elliptic_curve.sw<0 : i32, 3 : i32, (1 : i32, 2 : i32)> : !field.pf<7 : i32>>, !elliptic_curve.jacobian<{{.*}}>, !elliptic_curve.xyzz<{{.*}}>, !elliptic_curve.ed_affine<#elliptic_curve.te<12 : i32, 2 : i32, (2 : i32, 4 : i32)> : !field.pf<13 : i32>>, !elliptic_curve.ed_extended<{{.*}}>, tensor<4x!field.pf<7 : i32>>, tensor<4x!elliptic_curve.affine<{{.*}}>>) -> (), "sym_name" = "ops"}>
// CHECK: "elliptic_curve.constant"() <{"coords" = {{\[\[}}1 : i32, 2 : i32]]}> : () -> !elliptic_curve.affine<{{.*}}>
// CHECK: "elliptic_curve.from_coords"(%{{.*}}, %{{.*}}) : (!field.pf<7 : i32>, !field.pf<7 : i32>) -> !elliptic_curve.affine<{{.*}}>
// CHECK: "elliptic_curve.to_coords"(%{{.*}}) : (!elliptic_curve.jacobian<{{.*}}>) -> (!field.pf<7 : i32>, !field.pf<7 : i32>, !field.pf<7 : i32>)
// CHECK: "elliptic_curve.is_zero"(%{{.*}}) : (!elliptic_curve.jacobian<{{.*}}>) -> i1
// CHECK: "elliptic_curve.add"(%{{.*}}, %{{.*}}) : (!elliptic_curve.jacobian<{{.*}}>, !elliptic_curve.affine<{{.*}}>) -> !elliptic_curve.jacobian<{{.*}}>
// CHECK: "elliptic_curve.sub"
// CHECK: "elliptic_curve.negate"
// CHECK: "elliptic_curve.double"(%{{.*}}) : (!elliptic_curve.affine<{{.*}}>) -> !elliptic_curve.jacobian<{{.*}}>
// CHECK: "elliptic_curve.scalar_mul"(%{{.*}}, %{{.*}}) : (!field.pf<7 : i32>, !elliptic_curve.jacobian<{{.*}}>) -> !elliptic_curve.jacobian<{{.*}}>
// CHECK: "elliptic_curve.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = 0 : i64}>
// CHECK: "elliptic_curve.msm"(%{{.*}}, %{{.*}}) <{{.*}}"parallel"{{.*}} : (tensor<4x!field.pf<7 : i32>>, tensor<4x!elliptic_curve.affine<{{.*}}>>) -> !elliptic_curve.xyzz<{{.*}}>
// CHECK: "elliptic_curve.msm"(%{{.*}}, %{{.*}}) <{{.*}}"windowBits" = 4 : i32
// CHECK: "elliptic_curve.pairing_check"(%{{.*}}, %{{.*}}) : (tensor<4x!elliptic_curve.affine<{{.*}}>>, tensor<4x!elliptic_curve.affine<{{.*}}>>) -> i1
// CHECK: "elliptic_curve.convert_point_type"(%{{.*}}) : (!elliptic_curve.jacobian<{{.*}}>) -> !elliptic_curve.xyzz<{{.*}}>
// CHECK: "elliptic_curve.bitcast"(%{{.*}}) : (!elliptic_curve.affine<{{.*}}>) -> tensor<2x!field.pf<7 : i32>>
// CHECK: "elliptic_curve.add"(%{{.*}}, %{{.*}}) : (!elliptic_curve.ed_extended<{{.*}}>, !elliptic_curve.ed_extended<{{.*}}>) -> !elliptic_curve.ed_extended<{{.*}}>
// CHECK: "elliptic_curve.convert_point_type"(%{{.*}}) : (!elliptic_curve.ed_affine<{{.*}}>) -> !elliptic_curve.ed_extended<{{.*}}>
// CHECK: "elliptic_curve.double"(%{{.*}}) : (!elliptic_curve.ed_extended<{{.*}}>) -> !elliptic_curve.ed_extended<{{.*}}>
