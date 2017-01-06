; RUN: opt -basicaa -aa-eval -disable-output %s 2>/dev/null

declare {}* @llvm.invariant.start(i64, i8* nocapture) nounwind readonly
declare void @llvm.invariant.end({}*, i64, i8* nocapture) nounwind

; Previously caused getModRefInfo to retrieve a MemoryLocation for an invalid
; argument to the intrinsic.
define void @tests.invariant.start.end() {
  %a = alloca i8
  %i = call {}* @llvm.invariant.start(i64 1, i8* %a)
  call void @llvm.invariant.end({}* %i, i64 1, i8* %a)
  ret void
}
