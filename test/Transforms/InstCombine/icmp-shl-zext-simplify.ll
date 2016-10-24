; RUN: opt %s -instcombine -S | FileCheck %s

define i1 @icmp_ugt_32(i64) {
; CHECK-LABEL: @icmp_ugt_32
; CHECK-NEXT: icmp ne i32 %0, 0
; CHECK-NEXT: ret
  %c = shl nuw i64 %0, 32
  %d = icmp ugt i64 %c, 4294967295
  ret i1 %d
}

define i1 @icmp_ule_64(i128) {
; CHECK-LABEL: @icmp_ule_64
; CHECK-NEXT: icmp eq i64 %0, 0
; CHECK-NEXT: ret
  %c = shl nuw i128 %0, 64
  %d = icmp ule i128 %c, 18446744073709551615
  ret i1 %d
}

define i1 @icmp_ugt_16(i64) {
; CHECK-LABEL: @icmp_ugt_16
; CHECK-NEXT: icmp ugt i16 %0, 15
; CHECK-NEXT: ret
  %c = shl nuw i64 %0, 16
  %d = icmp ugt i64 %c, 1048575 ; 0x0f_ffff
  ret i1 %d
}

define <2 x i1> @icmp_ule_i64x2(<2 x i64>) {
  %c = shl nuw <2 x i64> %0, <i64 16, i64 16>
  %d = icmp ule <2 x i64> %c, <i64 65535, i64 65535>
  ret <2 x i1> %d
}
