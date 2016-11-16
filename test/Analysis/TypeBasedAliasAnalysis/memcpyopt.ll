; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt -S -tbaa -basicaa -memcpyopt -instcombine < %s | FileCheck %s
; RUN: opt -S -tbaa -basicaa -memcpyopt-mssa -instcombine < %s | FileCheck %s --check-prefix=MCO-MSSA

target datalayout = "e-p:64:64:64"

; The second memcpy is redundant and can be deleted. There's an intervening store, but
; it has a TBAA tag which declares that it is unrelated.

define void @foo(i8* nocapture %p, i8* nocapture %q, i8* nocapture %s) nounwind {
; CHECK-LABEL: @foo(
; CHECK-NEXT:    tail call void @llvm.memcpy.p0i8.p0i8.i64(i8* %p, i8* %q, i64 16, i32 1, i1 false), !tbaa !0
; CHECK-NEXT:    store i8 2, i8* %s, align 1, !tbaa !3
; CHECK-NEXT:    ret void
;
; MCO-MSSA-LABEL: @foo(
; MCO-MSSA-NEXT:    tail call void @llvm.memcpy.p0i8.p0i8.i64(i8* %p, i8* %q, i64 16, i32 1, i1 false), !tbaa !0
; MCO-MSSA-NEXT:    store i8 2, i8* %s, align 1, !tbaa !3
; MCO-MSSA-NEXT:    ret void
;
  tail call void @llvm.memcpy.p0i8.p0i8.i64(i8* %p, i8* %q, i64 16, i32 1, i1 false), !tbaa !2
  store i8 2, i8* %s, align 1, !tbaa !1
  tail call void @llvm.memcpy.p0i8.p0i8.i64(i8* %q, i8* %p, i64 16, i32 1, i1 false), !tbaa !2
  ret void
}

declare void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture, i8* nocapture, i64, i32, i1) nounwind

!0 = !{!"tbaa root", null}
!1 = !{!3, !3, i64 0}
!2 = !{!4, !4, i64 0}
!3 = !{!"A", !0}
!4 = !{!"B", !0}
