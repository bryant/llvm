; RUN: llc < %s -O0 -march=x86 -o - | FileCheck %s

define i1 @f(i64*, i64, i64) {
; CHECK-LABEL: f
; CHECK: cmpxchg8b
; CHECK-NEXT: sete
; CHECK-NEXT: movzbl
  %a = cmpxchg i64* %0, i64 %1, i64 %2 seq_cst seq_cst
  %b = extractvalue { i64, i1 } %a, 1
  %c = zext i1 %b to i32
  call void asm sideeffect "", "r"(i32 %c)
  ret i1 %b
}
