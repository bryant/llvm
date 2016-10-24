; RUN: opt %s -instcombine -S | FileCheck %s

define i32 @icmp_ugt_16(i16) {
; CHECK-LABEL: @icmp_ugt_16
; CHECK-NEXT: icmp ne i16 %0, 0
; CHECK-NEXT: zext
; CHECK-NEXT: ret
  %b = zext i16 %0 to i64
  %c = shl i64 %b, 16
  %d = icmp ugt i64 %c, 65535
  %rv = zext i1 %d to i32
  ret i32 %rv
}

define i32 @icmp_ule_16(i16) {
; CHECK-LABEL: @icmp_ule_16
; CHECK-NEXT: icmp eq i16 %0, 0
; CHECK-NEXT: zext
; CHECK-NEXT: ret
  %b = zext i16 %0 to i64
  %c = shl i64 %b, 16
  %d = icmp ule i64 %c, 65535
  %rv = zext i1 %d to i32
  ret i32 %rv
}

define i32 @icmp_ugt_32(i32) {
; CHECK-LABEL: @icmp_ugt_32
; CHECK-NEXT: icmp ne i32 %0, 0
; CHECK-NEXT: zext
; CHECK-NEXT: ret
  %b = zext i32 %0 to i64
  %c = shl i64 %b, 32
  %d = icmp ugt i64 %c, 4294967295
  %rv = zext i1 %d to i32
  ret i32 %rv
}

define i32 @icmp_ule_32(i32) {
; CHECK-LABEL: @icmp_ule_32
; CHECK-NEXT: icmp eq i32 %0, 0
; CHECK-NEXT: zext
; CHECK-NEXT: ret
  %b = zext i32 %0 to i64
  %c = shl i64 %b, 32
  %d = icmp ule i64 %c, 4294967295
  %rv = zext i1 %d to i32
  ret i32 %rv
}

define i32 @icmp_ugt_64(i64) {
; CHECK-LABEL: @icmp_ugt_64
; CHECK-NEXT: icmp ne i64 %0, 0
; CHECK-NEXT: zext
; CHECK-NEXT: ret
  %b = zext i64 %0 to i128
  %c = shl i128 %b, 64
  %d = icmp ugt i128 %c, 18446744073709551615
  %rv = zext i1 %d to i32
  ret i32 %rv
}

define i32 @icmp_ule_64(i64) {
; CHECK-LABEL: @icmp_ule_64
; CHECK-NEXT: icmp eq i64 %0, 0
; CHECK-NEXT: zext
; CHECK-NEXT: ret
  %b = zext i64 %0 to i128
  %c = shl i128 %b, 64
  %d = icmp ule i128 %c, 18446744073709551615
  %rv = zext i1 %d to i32
  ret i32 %rv
}
