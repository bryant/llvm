; RUN: llc -march=x86-64 < %s | FileCheck %s

define i32 @nonzero32(i32) {
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

define i32 @nonzero64(i64) {
; CHECK-LABEL: nonzero:
; CHECK-NEXT:    xorl %eax, %eax
; CHECK-NEXT:    shrq $32, %rdi
; CHECK-NEXT:    setne %al
; CHECK-NEXT:    retq
  %b = zext i64 %0 to i128
  %c = shl i128 %b, 64
  %d = icmp ugt i128 %c, 18446744073709551615
  %rv = zext i1 %d to i32
  ret i32 %rv
}
