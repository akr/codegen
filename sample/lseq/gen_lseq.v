Require Import lseq.

Require Import codegen.codegen.

Set CodeGen IndImpAutoLinear.

CodeGen BorrowFunc borrow_lseq_bool.

CodeGen SourceFile "lseq.c".
CodeGen HeaderFile "lseq.h".

CodeGen HeaderSnippet "prologue" "#ifndef LSEQ_H".
CodeGen HeaderSnippet "prologue" "#define LSEQ_H".

CodeGen Snippet "prologue" "#include ""lseq.h""".

CodeGen IndType bool => "bool" swfunc "" with
| true => constant "true" case ""
| false => constant "false" case "0".

CodeGen HeaderSnippet "prologue" "
#include <stdbool.h> /* for bool, true and false */
".

CodeGen IndType nat => "nat" swfunc "" with
| O => constant "0" case "0"
| S => primitive "nat_succ" case "" accessor "nat_pred".

CodeGen HeaderSnippet "prologue" "
#include <stdint.h>
typedef uint64_t nat;
".

CodeGen Snippet "prologue" "
#define nat_succ(n) ((n)+1)
#define nat_pred(n) ((n)-1)
".

CodeGen Primitive Nat.add => "nat_add".
CodeGen Primitive Nat.sub => "nat_sub".
CodeGen Primitive Nat.mul => "nat_mul".
CodeGen Primitive Nat.div => "nat_div".
CodeGen Primitive Nat.modulo => "nat_mod".
CodeGen Primitive Nat.double => "nat_double".
CodeGen Primitive Nat.div2 => "nat_div2".
CodeGen Primitive Nat.testbit => "nat_testbit".
CodeGen Primitive Nat.shiftl => "nat_shiftl".
CodeGen Primitive Nat.shiftr => "nat_shiftr".
CodeGen Primitive Nat.land => "nat_land".
CodeGen Primitive Nat.lor => "nat_lor".
CodeGen Primitive Nat.ldiff => "nat_ldiff".
CodeGen Primitive Nat.lxor => "nat_lxor".
CodeGen Primitive Nat.eqb => "nat_eqb".
CodeGen Primitive Nat.leb => "nat_leb".
CodeGen Primitive Nat.ltb => "nat_ltb".

CodeGen Snippet "prologue" "
#define nat_add(x,y) ((x) + (y))
#define nat_sub(x,y) ((x) - (y))
#define nat_mul(x,y) ((x) * (y))
#define nat_div(x,y) ((x) / (y))
#define nat_mod(x,y) ((x) % (y))
#define nat_double(x) ((x) << 1)
#define nat_div2(x) ((x) >> 1)
#define nat_testbit(x,y) (((x) >> (y)) & 1)
#define nat_shiftl(x,y) ((x) << (y))
#define nat_shiftr(x,y) ((x) >> (y))
#define nat_land(x,y) ((x) & (y))
#define nat_lor(x,y) ((x) | (y))
#define nat_ldiff(x,y) ((x) & ~(y))
#define nat_lxor(x,y) ((x) ^ (y))
#define nat_eqb(x,y) ((x) == (y))
#define nat_leb(x,y) ((x) <= (y))
#define nat_ltb(x,y) ((x) < (y))
".

CodeGen IndType lseq bool => "lseq_bool" swfunc "lseq_bool_sw" with
| lnil => primitive "lseq_bool_nil" case "lseq_bool_nil_tag"
| lcons => primitive "lseq_bool_cons" case "lseq_bool_cons_tag" accessor "lseq_bool_head" "lseq_bool_tail".
CodeGen IndImp lseq bool
  where heap on
  where static off
  where output_type_decls current_header
  where output_type_impls current_header
  where output_func_decls current_header
  where output_func_impls current_source
  where prefix "lseqbool".

CodeGen HeaderSnippet "prologue" "
#include <stdlib.h> /* for NULL, malloc(), abort() */
".

CodeGen Func @lseq_consume bool => "lseq_consume_bool" where static off.

CodeGen IndType bseq bool => "lseq_bool" swfunc "lseq_bool_sw" with
| bnil => case "lseq_bool_nil_tag"
| bcons => case "lseq_bool_cons_tag" accessor "lseq_bool_head" "lseq_bool_tail".


CodeGen Func @lncons bool => "lncons_bool" where static off.
CodeGen Func @lnseq bool => "lnseq_bool" where static off.

CodeGen Func @bhead bool => "bhead_bool" where static off.
CodeGen Func @lbehead bool => "lbehead_bool" where static off.
CodeGen Func @blast bool => "blast_bool" where static off.
CodeGen Func @lbelast bool => "lbelast_bool" where static off.

CodeGen Func @bsize bool => "bsize_bool" where static off.

CodeGen Func @bnth bool => "bnth_bool" where static off.
CodeGen Func @lset_nth bool => "lset_nth_bool" where static off.

CodeGen Func @bnilp bool => "bnilp_bool" where static off.

CodeGen Func @lmask bool => "lmask_bool" where static off.
CodeGen Func @lcat bool => "lcat_bool" where static off.
CodeGen Func @blcat bool => "blcat_bool" where static off.

CodeGen Func @ltake bool => "ltake_bool" where static off.
CodeGen Func @ldrop bool => "ldrop_bool" where static off.
CodeGen Func @bdrop bool => "bdrop_bool" where static off.
CodeGen Func @lrot bool => "lrot_bool" where static off.
CodeGen Func @lrotr bool => "lrotr_bool" where static off.

CodeGen Func @lcatrev bool => "lcatrev_bool" where static off.
CodeGen Func @lrev bool => "lrev_bool" where static off.
CodeGen Func @bcatrev bool => "bcatrev_bool" where static off.
CodeGen Func @brev bool => "brev_bool" where static off.

CodeGen HeaderSnippet "epilogue" "#endif /* LSEQ_H */".

(* Print CodeGen Inductive. *)

CodeGen GenerateFile.
