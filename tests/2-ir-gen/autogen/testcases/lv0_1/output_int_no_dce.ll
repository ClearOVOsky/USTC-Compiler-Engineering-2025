; ModuleID = 'cminus'
source_filename = "/home/clearsky/lab2/USTC-Compiler-Engineering-2025/tests/2-ir-gen/autogen/testcases/lv0_1/output_int.cminus"

declare i32 @input()

declare void @output(i32)

declare void @outputFloat(float)

declare void @neg_idx_except()

define void @main() {
label_entry:
  call void @output(i32 1234)
  ret void
}
