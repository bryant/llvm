; ModuleID = 'buggy/bugpoint-reduced-simplified.bc'
source_filename = "bugpoint-output-c642c31.bc"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind
define void @borf(i8* nocapture %in, i8* nocapture %out) #0 {
bb4.thread:
  br label %bb2.outer

bb2.outer:                                        ; preds = %bb4, %bb4.thread
  %indvar19 = phi i64 [ 0, %bb4.thread ], [ %indvar.next29, %bb4 ]
  %tmp21 = mul i64 %indvar19, -478
  br label %bb2

bb2:                                              ; preds = %bb2, %bb2.outer
  %indvar = phi i64 [ 0, %bb2.outer ], [ undef, %bb2 ]
  %indvar16 = trunc i64 %indvar to i16
  %ctg2 = getelementptr i8, i8* %out, i64 %tmp21
  %tmp22 = ptrtoint i8* %ctg2 to i64
  %tmp24 = sub i64 %tmp22, %indvar
  %out_addr.0.reg2mem.0 = inttoptr i64 %tmp24 to i8*
  %j.0.reg2mem.0 = sub i16 479, %indvar16
  %0 = zext i16 %j.0.reg2mem.0 to i32
  %1 = add i32 0, %0
  %2 = add i32 %1, 481
  %3 = zext i32 %2 to i64
  br i1 undef, label %bb4, label %bb2

bb4:                                              ; preds = %bb2
  %indvar.next29 = add i64 %indvar19, 1
  br label %bb2.outer
}

attributes #0 = { nounwind }
