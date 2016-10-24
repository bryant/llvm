; RUN: llc -O3 -mtriple=x86_64 < %s | FileCheck %s

define i32 @nonzero(i32) {
; CHECK-LABEL: nonzero
  %b = zext i32 %0 to i64
  %c = shl i64 %b, 32
  %d = icmp ugt i64 %c, 4294967295
  %rv = zext i1 %d to i32
; CHECK-DAG: testl %edi, %edi
  ret i32 %rv
}
