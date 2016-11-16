; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt < %s -memcpyopt -mldst-motion -gvn -S | FileCheck %s
; RUN: opt < %s -memcpyopt-mssa -mldst-motion -gvn -S | FileCheck %s --check-prefix=MCO-MSSA

declare void @check(i8)

declare void @write(i8* %res)

define void @test1() {
; CHECK-LABEL: @test1(
; CHECK-NEXT:    [[TMP1:%.*]] = alloca [10 x i8]
; CHECK-NEXT:    [[TMP2:%.*]] = bitcast [10 x i8]* [[TMP1]] to i8*
; CHECK-NEXT:    call void @write(i8* [[TMP2]])
; CHECK-NEXT:    [[TMP3:%.*]] = load i8, i8* [[TMP2]]
; CHECK-NEXT:    call void @check(i8 [[TMP3]])
; CHECK-NEXT:    ret void
;
; MCO-MSSA-LABEL: @test1(
; MCO-MSSA-NEXT:    [[TMP1:%.*]] = alloca [10 x i8]
; MCO-MSSA-NEXT:    [[TMP2:%.*]] = bitcast [10 x i8]* [[TMP1]] to i8*
; MCO-MSSA-NEXT:    call void @write(i8* [[TMP2]])
; MCO-MSSA-NEXT:    [[TMP3:%.*]] = load i8, i8* [[TMP2]]
; MCO-MSSA-NEXT:    call void @check(i8 [[TMP3]])
; MCO-MSSA-NEXT:    ret void
;
  %1 = alloca [10 x i8]
  %2 = bitcast [10 x i8]* %1 to i8*
  call void @write(i8* %2)
  %3 = load i8, i8* %2

  call void @check(i8 %3)

  ret void
}

