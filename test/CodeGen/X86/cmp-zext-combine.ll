; RUN: llc -march=x86-64 < %s | FileCheck %s

define i32 @nonzero(i32) {
; CHECK-LABEL: nonzero:
; CHECK-NEXT:    xorl %eax, %eax
; CHECK-NEXT:    testl %edi, %edi
; CHECK-NEXT:    setne %al
; CHECK-NEXT:    retq
  %b = zext i32 %0 to i64
  %c = shl i64 %b, 32
  %d = icmp ugt i64 %c, 4294967295
  %rv = zext i1 %d to i32
  ret i32 %rv
}
