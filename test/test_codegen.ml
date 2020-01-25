open OUnit2

let escape_coq_str (str : string) : string =
  let buf = Buffer.create (String.length str + 2) in
  Buffer.add_char buf '"';
  String.iter
    (fun ch ->
      match ch with
      | '"' -> Buffer.add_string buf "\"\""
      | _ -> Buffer.add_char buf ch)
    str;
  Buffer.add_char buf '"';
  Buffer.contents buf

let escape_C_str (str : string) : string =
  let buf = Buffer.create (String.length str + 2) in
  Buffer.add_char buf '"';
  String.iter
    (fun ch ->
      match ch with
      | ' ' .. '!' -> Buffer.add_char buf ch
      | '"' -> Buffer.add_string buf "\\\""
      | '#' .. '[' -> Buffer.add_char buf ch
      | '\\'-> Buffer.add_string buf "\\\\"
      | ']' .. '~' -> Buffer.add_char buf ch
      | _ -> Buffer.add_string buf (Printf.sprintf "\\%03o\n" (Char.code ch)))
      (* We don't use hexadecimal-escape-sequence because it accepts
       * more than two hexadecimal-digit and it is difficult to escape
       * a character before a hexadecimal-digit.
       * e.g. If escape_C_str ("\xff" ^ "0") generates "\\xff0",
       * it is interpreted as the character 0xff0 in C string literal. *)
    str;
  Buffer.add_char buf '"';
  Buffer.contents buf

(* "q-char-sequence" *)
let quote_C_header (str : string) =
  let buf = Buffer.create (String.length str + 2) in
  Buffer.add_char buf '"';
  String.iter
    (fun ch ->
      match ch with
      | '\n' -> failwith "quoted C header name cannot contain a newline"
      | '"' -> failwith "quoted C header name cannot contain a double quote"
      | _ -> Buffer.add_char buf ch)
    str;
  Buffer.add_char buf '"';
  Buffer.contents buf

let write_file (fn : string) (content : string) : unit =
  let ch = open_out fn in
  output_string ch content;
  close_out ch

let search_topdir () : string option =
  let rec f d =
    let fn = d ^ "/Makefile.coq.conf" in
    if Sys.file_exists fn then
      Some d
    else if d = "/" then
      None
    else
      f (Filename.dirname d)
  in
  f (Sys.getcwd ())

let cc : string =
  match Sys.getenv_opt "CC" with
  | Some v -> v
  | None -> "gcc"

let coqc : string =
  match Sys.getenv_opt "COQC" with
  | Some v -> v
  | None -> "coqc"

let topdir_opt : string option = search_topdir ()

let coq_opts : string list =
  match topdir_opt with
  | Some topdir -> ["-Q"; topdir ^ "/theories"; "codegen"; "-I"; topdir ^ "/src"]
  | None -> []

let min_indent (str : string) : int =
  let min = ref (String.length str + 1) in
  let indent = ref (Some 0) in
  String.iter
    (fun ch ->
      match ch with
      | '\n' -> indent := Some 0
      | ' ' ->
          (match !indent with
          | None -> ()
          | Some n -> indent := Some (n+1))
      | _ ->
          (match !indent with
          | None -> ()
          | Some n ->
              (indent := None;
              if n < !min then min := n)))
    str;
  if String.length str < !min then
    0
  else
    !min

let delete_n_indent (n : int) (str : string) : string =
  let buf = Buffer.create (String.length str) in
  let indent = ref (Some 0) in
  String.iter
    (fun ch ->
      match ch with
      | '\n' -> Buffer.add_char buf ch; indent := Some 0
      | ' ' ->
          (match !indent with
          | Some i ->
              if i < n then
                indent := Some (i + 1)
              else
                (Buffer.add_char buf ch; indent := None)
          | None -> Buffer.add_char buf ch)
      | _ ->
          (Buffer.add_char buf ch; indent := None))
    str;
  Buffer.contents buf

let delete_indent (str : string) : string =
  delete_n_indent (min_indent str) str

let add_n_indent (n : int) (str : string) : string =
  let buf = Buffer.create (String.length str) in
  let line_head = ref true in
  let indent = String.make n ' ' in
  String.iter
    (fun ch ->
      match ch with
      | '\n' -> Buffer.add_char buf ch; line_head := true
      | _ ->
          (if !line_head then
            Buffer.add_string buf indent;
            line_head := false);
          Buffer.add_char buf ch)
    str;
  Buffer.contents buf

let make_temp_dir (prefix : string) (suffix : string) : string =
  let rec f () =
    let fn = Filename.temp_file prefix suffix in
    Unix.unlink fn; (* because Filename.temp_file generates a regular file *)
    try
      Unix.mkdir fn 0o700;
      fn
    with Unix.Unix_error (e,_,_) as exn ->
      if e = Unix.EEXIST then
        f ()
      else
        raise exn
  in
  Unix.handle_unix_error f ()

let codegen_test_template (ctx : test_ctxt)
    (coq_commands : string)
    (c_body : string) : unit =
  let d =
    match Sys.getenv_opt "CODEGEN_SAVE_TMP" with
    | Some _ -> make_temp_dir "codegen-test" ""
    | None -> bracket_tmpdir ~prefix:"codegen-test" ctx
  in
  let src_fn = d ^ "/src.v" in
  let gen_fn = d ^ "/gen.c" in
  let main_fn = d ^ "/main.c" in
  let exe_fn = d ^ "/exe" in
  write_file src_fn
    ("From codegen Require codegen.\n" ^
    delete_indent coq_commands ^ "\n" ^
    "CodeGen EndFile " ^ (escape_coq_str gen_fn) ^ ".\n");
  write_file main_fn
    ("#include <assert.h>\n" ^
    "#include " ^ (quote_C_header gen_fn) ^ "\n" ^
    "int main(int argc, char *argv[]) {\n" ^
    add_n_indent 2 (delete_indent c_body) ^ "\n" ^
    "}\n");
  assert_command ctx coqc (List.append coq_opts [src_fn]);
  assert_command ctx cc ["-o"; exe_fn; main_fn];
  assert_command ctx exe_fn []

let bool_src = {|
      CodeGen Inductive Type bool => "bool".
      CodeGen Inductive Match bool => ""
      | true => "default"
      | false => "case 0".
      CodeGen Constant true => "true".
      CodeGen Constant false => "false".

      CodeGen Snippet "
      #include <stdbool.h> /* for bool, true and false */
      ".
|}

let nat_src = {|
      CodeGen Inductive Type nat => "nat".
      CodeGen Inductive Match nat => ""
      | O => "case 0"
      | S => "default" "nat_pred".
      CodeGen Constant O => "0".
      CodeGen Primitive S => "nat_succ".

      CodeGen Snippet "
      #include <stdint.h>
      typedef uint64_t nat;
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
      CodeGen Snippet "
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
      ".
|}

let list_bool_src = {|
      CodeGen Inductive Type list bool => "list_bool".
      CodeGen Inductive Match list bool => "list_bool_is_nil"
      | nil => "default"
      | cons => "case 0" "list_bool_head" "list_bool_tail".
      CodeGen Constant nil bool => "((list_bool)NULL)".
      CodeGen Primitive cons bool => "list_bool_cons".

      CodeGen Snippet "
      #include <stdlib.h> /* for NULL, malloc(), abort() */

      struct list_bool_struct;
      typedef struct list_bool_struct *list_bool;
      struct list_bool_struct {
        bool head;
        list_bool tail;
      };

      static inline bool list_bool_is_nil(list_bool s) { return s == NULL; }
      static inline bool list_bool_head(list_bool s) { return s->head; }
      static inline list_bool list_bool_tail(list_bool s) { return s->tail; }
      static inline list_bool list_bool_cons(bool v, list_bool s) {
        list_bool ret = malloc(sizeof(struct list_bool_struct));
        if (ret == NULL) abort();
        ret->head = v;
        ret->tail = s;
        return ret;
      }
      ".
|}

let list_nat_src = {|
      CodeGen Inductive Type list nat => "list_nat".
      CodeGen Inductive Match list nat => "list_nat_is_nil"
      | nil => "default"
      | cons => "case 0" "list_nat_head" "list_nat_tail".
      CodeGen Constant nil nat => "((list_nat)NULL)".
      CodeGen Primitive cons nat => "list_nat_cons".

      CodeGen Snippet "
      #include <stdlib.h> /* for NULL, malloc(), abort() */
      #include <stdbool.h> /* for bool */
      struct list_nat_struct;
      typedef struct list_nat_struct *list_nat;
      struct list_nat_struct {
        nat head;
        list_nat tail;
      };
      static inline bool list_nat_is_nil(list_nat s) { return s == NULL; }
      static inline nat list_nat_head(list_nat s) { return s->head; }
      static inline list_nat list_nat_tail(list_nat s) { return s->tail; }
      static inline list_nat list_nat_cons(nat v, list_nat s) {
        list_nat ret = malloc(sizeof(struct list_nat_struct));
        if (ret == NULL) abort();
        ret->head = v;
        ret->tail = s;
        return ret;
      }
      ".
|}

let test_mono_id_bool (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Definition mono_id_bool (b : bool) := b.
      CodeGen Function mono_id_bool => "mono_id_bool".
    |}) {|
      assert(mono_id_bool(true) == true);
      assert(mono_id_bool(false) == false);
    |}

let test_mono_id_mybool (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    ({|
      Inductive mybool : Set := mytrue : mybool | myfalse : mybool.
      CodeGen Inductive Type mybool => "mybool".
      CodeGen Inductive Match mybool => ""
      | mytrue => "default"
      | myfalse => "case 0".
      CodeGen Constant mytrue => "mytrue".
      CodeGen Constant myfalse => "myfalse".
      CodeGen Snippet "
      typedef int mybool;
      #define mytrue 1
      #define myfalse 0
      ".
      Definition mono_id_mybool (b : mybool) := b.
      CodeGen Function mono_id_mybool => "mono_id_mybool".
    |}) {|
      assert(mono_id_mybool(mytrue) == mytrue);
      assert(mono_id_mybool(myfalse) == myfalse);
    |}

let test_mybool_true (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    ({|
      Inductive mybool : Set := mytrue : mybool | myfalse : mybool.
      CodeGen Inductive Type mybool => "mybool".
      CodeGen Inductive Match mybool => ""
      | mytrue => "default"
      | myfalse => "case 0".
      CodeGen Constant mytrue => "mytrue".
      CodeGen Constant myfalse => "myfalse".
      CodeGen Snippet "
      typedef int mybool;
      #define mytrue 1
      #define myfalse 0
      ".
      Definition mybool_true (b : mybool) := mytrue.
      CodeGen Function mybool_true => "mybool_true".
    |}) {|
      assert(mybool_true(mytrue) == mytrue);
      assert(mybool_true(myfalse) == mytrue);
    |}

let test_mono_id_bool_omit_cfunc_name (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Definition mono_id_bool (b : bool) := b.
      CodeGen Function mono_id_bool.
    |}) {|
      assert(mono_id_bool(true) == true);
      assert(mono_id_bool(false) == false);
    |}

let test_nat_add_rec (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ {|
      Fixpoint my_add_rec (m n : nat) : nat :=
        match m with
        | O => n
        | S m' => S (my_add_rec m' n)
        end.
      CodeGen Function my_add_rec.
    |}) {|
      assert(my_add_rec(2,3) == 5);
    |}

let test_nat_add_iter (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ {|
      Fixpoint my_add_iter (m n : nat) : nat :=
        match m with
        | O => n
        | S m' => my_add_iter m' (S n)
        end.
      CodeGen Function my_add_iter.
    |}) {|
      assert(my_add_iter(2,3) == 5);
    |}

let test_list_bool (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ list_bool_src ^ {|
      Definition is_nil (s : list bool) :=
        match s with
        | nil => true
        | cons _ _ => false
        end.
      CodeGen Function is_nil.
    |}) {|
      #define cons(h,t) list_bool_cons(h,t)
      assert(is_nil(NULL));
      assert(!is_nil(cons(true, NULL)));
    |}

let test_list_bool_length (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ list_bool_src ^
    {|
      Fixpoint length (s : list bool) : nat :=
        match s with
        | nil => 0
        | cons x s' => S (length s')
        end.
      CodeGen Function length.
    |}) {|
      #define cons(h,t) list_bool_cons(h,t)
      assert(length(NULL) == 0);
      assert(length(cons(1, NULL)) == 1);
      assert(length(cons(1, cons(2, NULL))) == 2);
    |}

let test_sum (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ list_nat_src ^
    {|
      Fixpoint sum (s : list nat) : nat :=
        match s with
        | nil => 0
        | cons x s' => x + sum s'
        end.
      CodeGen Function sum.
    |}) {|
      #define cons(h,t) list_nat_cons(h,t)
      assert(sum(NULL) == 0);
      assert(sum(cons(1, NULL)) == 1);
      assert(sum(cons(1, cons(2, NULL))) == 3);
    |}

let test_nil_nat (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ list_nat_src ^
    {|
      Definition nil_nat := @nil nat.
      CodeGen Function nil_nat.
    |}) {|
      list_nat s = nil_nat();
      assert(s == NULL);
    |}

let test_singleton_list (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^ list_nat_src ^
    {|
      Definition singleton_list (n : nat) : list nat := cons n nil.
      CodeGen Function singleton_list.
    |}) {|
      #define is_nil(s) list_nat_is_nil(s)
      #define head(s) list_nat_head(s)
      #define tail(s) list_nat_tail(s)
      #define cons(h,t) list_nat_cons(h,t)
      list_nat s = singleton_list(42);
      assert(!is_nil(s));
      assert(head(s) == 42);
      assert(is_nil(tail(s)));
    |}

let test_map_succ (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^ list_nat_src ^
    {|
      Require Import List.
      Definition map_succ (s : list nat) : list nat :=
        map S s.
      CodeGen Global Inline map.
      CodeGen Function map_succ.
    |}) {|
      #define is_nil(s) list_nat_is_nil(s)
      #define head(s) list_nat_head(s)
      #define tail(s) list_nat_tail(s)
      #define cons(h,t) list_nat_cons(h,t)
      assert(is_nil(map_succ(NULL)));
      assert(head(map_succ(cons(1, NULL))) == 2);
    |}

let suite : OUnit2.test =
  "TestCodeGen" >::: [
    "test_mono_id_bool" >:: test_mono_id_bool;
    "test_mono_id_bool_omit_cfunc_name" >:: test_mono_id_bool_omit_cfunc_name;
    "test_mono_id_mybool" >:: test_mono_id_mybool;
    "test_mybool_true" >:: test_mybool_true;
    "test_nat_add_rec" >:: test_nat_add_rec;
    "test_nat_add_iter" >:: test_nat_add_iter;
    "test_list_bool" >:: test_list_bool;
    "test_sum" >:: test_sum;
    "test_nil_nat" >:: test_nil_nat;
    "test_singleton_list" >:: test_singleton_list;
    (*"test_map_succ" >:: test_map_succ;*)
  ]

let () =
  run_test_tt_main suite
