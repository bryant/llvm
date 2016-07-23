; RUN: opt %s -instcombine -S | FileCheck %s

define i32 @nonzero8(i8) {
  %b = zext i8 %0 to i64
  %c = shl i64 %b, 8
  %d = icmp ult i64 %c, 255
  %rv = zext i1 %d to i32
  ret i32 %rv
}

define i32 @nonzero16(i16) {
  %b = zext i16 %0 to i64
  %c = shl i64 %b, 16
  %d = icmp ule i64 %c, 65535
  %rv = zext i1 %d to i32
  ret i32 %rv
}

define i32 @nonzero32(i32) {
  %b = zext i32 %0 to i64
  %c = shl i64 %b, 32
  %d = icmp ugt i64 %c, 4294967295
  %rv = zext i1 %d to i32
  ret i32 %rv
}

define i32 @nonzero64(i64) {
  %b = zext i64 %0 to i128
  %c = shl i128 %b, 64
  %d = icmp uge i128 %c, 18446744073709551615
  %rv = zext i1 %d to i32
  ret i32 %rv
}
