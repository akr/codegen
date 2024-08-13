Require Import codegen.codegen.

Load "ascii_api.v".

CodeGen HeaderFile "ascii.h".
CodeGen SourceFile "ascii.c".

CodeGen HeaderSnippet "prologue" "
#ifdef ASCII_H
".

CodeGen HeaderSnippet "func_impls" "
#define ascii_bit0(a) (((a) & 0x01) != 0)
#define ascii_bit1(a) (((a) & 0x02) != 0)
#define ascii_bit2(a) (((a) & 0x04) != 0)
#define ascii_bit3(a) (((a) & 0x08) != 0)
#define ascii_bit4(a) (((a) & 0x10) != 0)
#define ascii_bit5(a) (((a) & 0x20) != 0)
#define ascii_bit6(a) (((a) & 0x40) != 0)
#define ascii_bit7(a) (((a) & 0x80) != 0)
#define ascii_cstr(b0, b1, b2, b3, b4, b5, b6, b7) \
  (((b0)     ) | ((b1) << 1) | ((b2) << 2) | ((b3) << 3) | \
   ((b4) << 4) | ((b5) << 5) | ((b6) << 6) | ((b7) << 7))
".

CodeGen Snippet "prologue" "#include ""ascii.h""".

CodeGen HeaderSnippet "epilogue" "#endif /* ASCII_H */".
CodeGen GenerateFile.
