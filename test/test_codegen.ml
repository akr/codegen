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
    "CodeGen GenerateFile " ^ (escape_coq_str gen_fn) ^ ".\n");
  write_file main_fn
    ("#include <assert.h>\n" ^
    "#include " ^ (quote_C_header gen_fn) ^ "\n" ^
    "int main(int argc, char *argv[]) {\n" ^
    add_n_indent 2 (delete_indent c_body) ^ "\n" ^
    "}\n");
  assert_command ctx coqc (List.append coq_opts [src_fn]);
  assert_command ctx cc ["-o"; exe_fn; main_fn];
  assert_command ctx exe_fn []

let assert_coq_exit
    ~(exit_code : Unix.process_status)
    ~(regexp_in_output : Str.regexp option)
    (ctx : test_ctxt)
    (coq_commands : string) : unit =
  let d =
    match Sys.getenv_opt "CODEGEN_SAVE_TMP" with
    | Some _ -> make_temp_dir "codegen-test" ""
    | None -> bracket_tmpdir ~prefix:"codegen-test" ctx
  in
  let src_fn = d ^ "/src.v" in
  let gen_fn = d ^ "/gen.c" in
  write_file src_fn
    ("From codegen Require codegen.\n" ^
    delete_indent coq_commands ^ "\n" ^
    "CodeGen GenerateFile " ^ (escape_coq_str gen_fn) ^ ".\n");
  let foutput stream =
    let buf = Buffer.create 0 in
    Stream.iter (Buffer.add_char buf) stream;
    let text = Buffer.contents buf in
    match regexp_in_output with
    | None -> ()
    | Some expected ->
        try
          ignore (Str.search_forward expected text 0);
          assert_bool "expected regexp found" true
        with Not_found ->
          assert_bool "expected regexp not found" false
  in
  assert_command
    ~exit_code:exit_code
    ~use_stderr:true
    ~foutput:foutput
    ~ctxt:ctx
    coqc (List.append coq_opts [src_fn])

let assert_coq_success
    ?(regexp_in_output : Str.regexp option)
    (ctx : test_ctxt)
    (coq_commands : string) : unit =
  assert_coq_exit
    ~exit_code:(Unix.WEXITED 0)
    ~regexp_in_output:regexp_in_output
    ctx
    coq_commands

let assert_coq_failure
    ?(regexp_in_output : Str.regexp option)
    (ctx : test_ctxt)
    (coq_commands : string) : unit =
  assert_coq_exit
    ~exit_code:(Unix.WEXITED 1)
    ~regexp_in_output:regexp_in_output
    ctx
    coq_commands

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
      CodeGen Primitive Nat.eqb => "nat_eqb".
      CodeGen Primitive Nat.leb => "nat_leb".
      CodeGen Primitive Nat.ltb => "nat_ltb".
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
      #define nat_eqb(x,y) ((x) == (y))
      #define nat_leb(x,y) ((x) <= (y))
      #define nat_ltb(x,y) ((x) < (y))
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

let test_tail_rel (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Definition mono_id_bool (b : bool) := b.
      CodeGen Function mono_id_bool => "mono_id_bool".
    |}) {|
      assert(mono_id_bool(true) == true);
      assert(mono_id_bool(false) == false);
    |}

let test_tail_constructor_bool (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Definition constructor_true : bool := true.
      Definition constructor_false : bool := false.
      CodeGen Function constructor_true.
      CodeGen Function constructor_false.
    |}) {|
      assert(constructor_true() == true);
      assert(constructor_false() == false);
    |}

let test_tail_constructor_args (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Inductive bool_pair : Set := bpair : bool -> bool -> bool_pair.
      CodeGen Inductive Type bool_pair => "bool_pair".
      CodeGen Inductive Match bool_pair => ""
      | bpair => "default" "bool_pair_fst" "bool_pair_snd".
      CodeGen Primitive bpair => "bpair".

      CodeGen Snippet "
      typedef int bool_pair;
      #define bpair(a,b) (((a) << 1) | (b))
      #define bool_pair_fst(x) ((x) >> 1)
      #define bool_pair_snd(x) ((x) & 1)
      ".

      Definition call_bpair a b : bool_pair := bpair a b.
      CodeGen Function call_bpair.
    |}) {|
      assert(call_bpair(false, false) == 0);
      assert(call_bpair(false, true) == 1);
      assert(call_bpair(true, false) == 2);
      assert(call_bpair(true, true) == 3);
    |}

let test_tail_constant_bool (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      CodeGen Snippet "
      bool my_true(void) { return true; }
      bool my_false(void) { return false; }
      ".
      Definition my_true := true.
      Definition my_false := false.
      CodeGen Primitive my_true.
      CodeGen Primitive my_false.
      Definition constant_true : bool := my_true.
      Definition constant_false : bool := my_false.
      CodeGen Function constant_true.
      CodeGen Function constant_false.
    |})
    {|
      assert(constant_true() == true);
      assert(constant_false() == false);
    |}

let test_tail_constant_args (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      CodeGen Primitive negb.
      CodeGen Snippet "#define negb(b) (!(b))".
      Definition call_negb (b : bool) : bool := negb b.
      CodeGen Function call_negb.
    |}) {|
      assert(call_negb(false) == true);
      assert(call_negb(true) == false);
    |}

let test_tail_match_bool (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Definition f (b : bool) :=
        match b with
        | true => false
        | false => true
        end.
      CodeGen Function f => "f".
    |}) {|
      assert(f(true) == false);
      assert(f(false) == true);
    |}

let test_tail_match_nat (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^ {|
      Definition f (n : nat) :=
        match n with
        | O => false
        | S n' => true
        end.
      CodeGen Function f => "f".
    |}) {|
      assert(f(0) == false);
      assert(f(1) == true);
    |}

let test_tail_match_singleton (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Inductive singleton : Set := C : bool -> singleton.
      CodeGen Inductive Type singleton => "singleton".
      CodeGen Inductive Match singleton => ""
      | C => "unused-case-label" "access".
      CodeGen Snippet "
      typedef bool singleton;
      #define access(s) s
      ".
      Definition f (x : singleton) := match x with C y => y end.
      CodeGen Function f => "f".
    |}) {|
      assert(f(true) == true);
      assert(f(false) == false);
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

let test_pair_bool_bool (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      CodeGen Inductive Type bool*bool => "pair_bool_bool".
      CodeGen Inductive Match bool*bool => ""
      | pair => "" "pair_bool_bool_fst" "pair_bool_bool_snd".
      CodeGen Primitive pair bool bool => "make_pair_bool_bool".
      CodeGen Snippet "
      typedef struct {
        bool fst;
        bool snd;
      } pair_bool_bool;
      #define make_pair_bool_bool(fst, snd) ((pair_bool_bool){ (fst), (snd) })
      #define pair_bool_bool_fst(x) ((x).fst)
      #define pair_bool_bool_snd(x) ((x).snd)
      ".
      Definition fst_pair (v : bool * bool) := match v with pair x y => x end.
      Definition snd_pair (v : bool * bool) := match v with pair x y => y end.
      CodeGen Function fst_pair.
      CodeGen Function snd_pair.
    |}) {|
      pair_bool_bool v = make_pair_bool_bool(true, false);
      assert(fst_pair(v) == true);
      assert(snd_pair(v) == false);
      v = make_pair_bool_bool(false, true);
      assert(fst_pair(v) == false);
      assert(snd_pair(v) == true);
    |}

let test_pair_2bool_bool (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      CodeGen Inductive Type bool*bool => "pair_bool_bool".
      CodeGen Inductive Match bool*bool => ""
      | pair => "" "pair_bool_bool_fst" "pair_bool_bool_snd".
      CodeGen Primitive pair bool bool => "make_pair_bool_bool".

      CodeGen Inductive Type bool*bool*bool => "pair_2bool_bool".
      CodeGen Inductive Match bool*bool*bool => ""
      | pair => "" "pair_2bool_bool_fst" "pair_2bool_bool_snd".
      CodeGen Primitive pair (bool*bool) bool => "make_pair_2bool_bool".

      CodeGen Snippet "
      typedef struct { bool fst; bool snd; } pair_bool_bool;
      #define make_pair_bool_bool(fst, snd) ((pair_bool_bool){ (fst), (snd) })
      #define pair_bool_bool_fst(x) ((x).fst)
      #define pair_bool_bool_snd(x) ((x).snd)
      typedef struct { pair_bool_bool fst; bool snd; } pair_2bool_bool;
      #define make_pair_2bool_bool(fst, snd) ((pair_2bool_bool){ (fst), (snd) })
      #define pair_2bool_bool_fst(x) ((x).fst)
      #define pair_2bool_bool_snd(x) ((x).snd)
      ".
      Definition fst_pair (v : bool * bool * bool) := match v with pair x y => x end.
      Definition snd_pair (v : bool * bool * bool) := match v with pair x y => y end.
      CodeGen Function fst_pair.
      CodeGen Function snd_pair.
    |}) {|
      pair_2bool_bool v;
      v = make_pair_2bool_bool(make_pair_bool_bool(true, false), true);
      assert(fst_pair(v).fst == true);
      assert(fst_pair(v).snd == false);
      assert(snd_pair(v) == true);
      v = make_pair_2bool_bool(make_pair_bool_bool(false, true), false);
      assert(fst_pair(v).fst == false);
      assert(fst_pair(v).snd == true);
      assert(snd_pair(v) == false);
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
    (bool_src ^ nat_src ^ list_bool_src ^
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

let test_add3 (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition add3 (n : nat) : nat := 3 + n.
      CodeGen Global Inline Nat.add.
      CodeGen Function add3.
    |}) {|
      assert(add3(4) == 7);
    |}

let test_mul3 (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition mul3 (n : nat) : nat := 3 * n.
      CodeGen Global Inline Nat.mul.
      CodeGen Function mul3.
    |}) {|
      assert(mul3(4) == 12);
    |}

let test_even_odd (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^
    {|
      Fixpoint even (n : nat) : bool :=
        match n with
        | O => true
        | S n' => odd n'
        end
      with odd (n : nat) : bool :=
        match n with
        | O => false
        | S n' => even n'
        end.

      CodeGen Global Inline even.
      Definition even3 := even 3.
      CodeGen Function even.
      CodeGen Function odd.
      CodeGen Function even3.
    |}) {|
      assert(even(0) == true);
      assert(even(1) == false);
      assert(even(2) == true);
      assert(even(3) == false);
      assert(even(4) == true);
      assert(odd(0) == false);
      assert(odd(1) == true);
      assert(odd(2) == false);
      assert(odd(3) == true);
      assert(odd(4) == false);
      assert(even3() == false);
    |}

let test_inner_fix_even_odd_1 (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^
    {|
      Definition even n :=
        (fix even n :=
          match n with
          | O => true
          | S n' => odd n'
          end
        with odd n :=
          match n with
          | O => false
          | S n' => even n'
          end
        for even) n.
      CodeGen Function even.
    |}) {|
      assert(even(0) == true);
      assert(even(1) == false);
      assert(even(2) == true);
      assert(even(3) == false);
      assert(even(4) == true);
    |}

let test_inner_fix_even_odd_2 (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^
    {|
      Definition even n :=
        (fix odd n :=
          match n with
          | O => false
          | S n' => even n'
          end
        with even n :=
          match n with
          | O => true
          | S n' => odd n'
          end
        for even) n.
      CodeGen Function even.
    |}) {|
      assert(even(0) == true);
      assert(even(1) == false);
      assert(even(2) == true);
      assert(even(3) == false);
      assert(even(4) == true);
    |}

let test_app_let (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition foo := (let x := 1 in Nat.add x) 2.
      CodeGen Function foo.
    |}) {|
      assert(foo() == 3);
    |}

let test_app_match (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^
    {|
      Definition add_or_sub b n :=
        (match b with
        | true => Nat.add 10
        | false => Nat.sub 10
        end) n.
      CodeGen Function add_or_sub.
    |}) {|
      assert(add_or_sub(true, 1) == 11);
      assert(add_or_sub(true, 2) == 12);
      assert(add_or_sub(false, 1) == 9);
      assert(add_or_sub(false, 2) == 8);
    |}

let test_cast (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition nat_id (n : nat) : nat := (n : nat) + 0.
      CodeGen Function nat_id.
    |}) {|
      assert(nat_id(4) == 4);
    |}

let test_delta_fun_constant (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition add (a b : nat) : nat := let f := Nat.add in f a b.
      CodeGen Function add.
    |}) {|
      assert(add(2,3) == 5);
    |}

let test_delta_fun_constructor (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition succ (n : nat) : nat := let f := S in f n.
      CodeGen Function succ.
    |}) {|
      assert(succ(2) == 3);
    |}

let test_delta_fun_lambda (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition succ (n : nat) : nat := let f x := S x in f n.
      CodeGen Function succ.
    |}) {|
      assert(succ(2) == 3);
    |}

(* test_delta_fun_rel *)
(* test_delta_fun_fix *)

(* codegen removes TestRecord type completely at reduction.
   So, no inductive type cofiguration required for TestRecord. *)
let test_reduce_proj (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Set Primitive Projections.
      Record TestRecord (par:nat) : Set := mk { f0 : nat; f1 : nat }.
      Definition f0_mk a b : nat := f0 10 (mk 10 a b).
      Definition f1_mk a b : nat := f1 10 (mk 10 a b).
      CodeGen Function f0_mk.
      CodeGen Function f1_mk.
    |}) {|
      assert(f0_mk(7, 8) == 7);
      assert(f1_mk(7, 8) == 8);
    |}

let test_deeply_nested_match (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Require Import List.
      Fixpoint f (s : list bool) : nat :=
        match s with
        | nil => 0
        | cons true (cons true (cons true (cons true rest))) => f rest
        | cons _ rest => f rest
        end.
      CodeGen Function f (repeat true 0) => "f0".
      CodeGen Function f (repeat true 10) => "f10".
    |}) {|
      assert(f0() == 0);
      assert(f10() == 0);
    |}

let test_let_add (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition add3 (a b c : nat) : nat :=
        let ab := a + b in
        ab + c.
      CodeGen Function add3.
    |}) {|
      assert(add3(1,2,3) == 6);
    |}

(* gen_assign Case *)
let test_let_match (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^
    {|
      Definition tst (b : bool) : bool :=
        let not_b := match b with true => false | false => true end in
        match not_b with true => false | false => true end.
      CodeGen Function tst.
    |}) {|
      assert(tst(true) == true);
      assert(tst(false) == false);
    |}

(* gen_assign LetIn *)
let test_let_match_let (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^
    {|
      Definition tst (b : bool) : nat :=
        let n := match b with true => let z := O in S z | false => O end in
        S n.
      CodeGen Function tst.
    |}) {|
      assert(tst(false) == 1);
      assert(tst(true) == 2);
    |}

let test_add_tailrec (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Fixpoint add (a b : nat) : nat :=
        match a with
        | O => b
        | S a' => add a' (S b)
        end.
      CodeGen Function add.
    |}) {|
      assert(add(0,0) == 0);
      assert(add(0,1) == 1);
      assert(add(1,0) == 1);
      assert(add(1,1) == 2);
    |}

let test_add_nontailrec (ctx : test_ctxt) : unit =
  assert_coq_success ctx
    (nat_src ^
    {|
      Fixpoint add (a b : nat) : nat :=
        match a with
        | O => b
        | S a' => S (add a' b)
        end.
      CodeGen Function add.
    |})

let test_tail_fix_double (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition dbl (n : nat) : nat :=
        (fix add (a b : nat) : nat :=
          match a with
          | O => b
          | S a' => S (add a' b)
          end) n n.
      CodeGen Function dbl.
    |}) {|
      assert(dbl(0) == 0);
      assert(dbl(1) == 2);
    |}

let test_nth (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^ list_nat_src ^
    {|
      Require Import List.
      CodeGen Function nth nat => "nth".
    |}) {|
      #define is_nil(s) list_nat_is_nil(s)
      #define head(s) list_nat_head(s)
      #define tail(s) list_nat_tail(s)
      #define cons(h,t) list_nat_cons(h,t)
      #define list3(v1, v2, v3) cons(v1, cons(v2, cons(v3, NULL)))
      list_nat s = list3(1,2,3);
      assert(nth(0, s, 999) == 1);
      assert(nth(1, s, 999) == 2);
      assert(nth(2, s, 999) == 3);
      assert(nth(3, s, 999) == 999);
    |}

let test_rev_append (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^ list_nat_src ^
    {|
      Require Import List.
      CodeGen Function nth nat => "nth".
      CodeGen Function rev_append nat => "rev_append".
    |}) {|
      #define is_nil(s) list_nat_is_nil(s)
      #define head(s) list_nat_head(s)
      #define tail(s) list_nat_tail(s)
      #define cons(h,t) list_nat_cons(h,t)
      #define list3(v1, v2, v3) cons(v1, cons(v2, cons(v3, NULL)))
      list_nat s1 = list3(1,2,3);
      list_nat s2 = list3(4,5,6);
      list_nat s3 = rev_append(s1, s2);
      assert(nth(0, s3, 999) == 3);
      assert(nth(1, s3, 999) == 2);
      assert(nth(2, s3, 999) == 1);
      assert(nth(3, s3, 999) == 4);
      assert(nth(4, s3, 999) == 5);
      assert(nth(5, s3, 999) == 6);
      assert(nth(6, s3, 999) == 999);
    |}

(* nested fix-term *)
let test_merge (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^ list_nat_src ^
    {|
      Require Import List.
      Definition merge :=
        fix f (s1 : list nat) :=
          fix g (s2 : list nat) :=
            fun s =>
              match s1 with
              | nil => rev_append s2 s
              | cons v1 s1' =>
                  match s2 with
                  | nil => rev_append s1 s
                  | cons v2 s2' =>
                      if Nat.ltb v1 v2 then
                        f s1' s2 (cons v1 s)
                      else
                        g s2' (cons v2 s)
                  end
              end.
      CodeGen Function nth nat => "nth".
      CodeGen Function rev_append nat => "rev_append".
      CodeGen Function merge.
    |}) {|
      #define is_nil(s) list_nat_is_nil(s)
      #define head(s) list_nat_head(s)
      #define tail(s) list_nat_tail(s)
      #define cons(h,t) list_nat_cons(h,t)
      #define list4(v1, v2, v3, v4) cons(v1, cons(v2, cons(v3, cons(v4, NULL))))
      list_nat s1 = list4(0,2,8,10);
      list_nat s2 = list4(1,4,5,20);
      list_nat s3 = merge(s1, s2, NULL);
      assert(nth(0, s3, 999) == 20);
      assert(nth(1, s3, 999) == 10);
      assert(nth(2, s3, 999) == 8);
      assert(nth(3, s3, 999) == 5);
      assert(nth(4, s3, 999) == 4);
      assert(nth(5, s3, 999) == 2);
      assert(nth(6, s3, 999) == 1);
      assert(nth(7, s3, 999) == 0);
      assert(nth(8, s3, 999) == 999);
    |}

(* nested fix-term *)
let test_sum_nested_fix (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^ list_nat_src ^
    {|
      Require Import List.
      Definition sum (s : list nat) (n : nat) : nat :=
        (fix f (s : list nat) :=
          fix g (m : nat) :=
            fun (n : nat) =>
              match m with
              | O =>
                  match s with
                  | nil => n
                  | cons v s' => f s' v n
                  end
              | S m' => g m' (S n)
              end) s 0 n.
      (*Compute sum (1 :: 2 :: 3 :: 4 :: nil) 0.*)
      CodeGen Function sum.
    |}) {|
      #define is_nil(s) list_nat_is_nil(s)
      #define head(s) list_nat_head(s)
      #define tail(s) list_nat_tail(s)
      #define cons(h,t) list_nat_cons(h,t)
      #define list4(v1, v2, v3, v4) cons(v1, cons(v2, cons(v3, cons(v4, NULL))))
      list_nat s = list4(1,2,3,4);
      assert(sum(s, 0) == 10);
    |}

(* gen_assign Fix, multiple loops *)
let test_add_at_non_tail_position (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^
    {|
      Require Import List.
      Definition f a b c :=
        let ab :=
          (fix add1 x y :=
            match x with
            | O => y
            | S x' => add1 x' (S y)
            end) a b
        in
        (fix add2 x y :=
          match x with
          | O => y
          | S x' => add2 x' (S y)
          end) ab c.
      CodeGen Function f.
    |}) {|
      assert(f(1, 2, 3) == 6);
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

let test_fully_dynamic_func_with_partapp_name (ctx : test_ctxt) : unit =
  assert_coq_success ctx
    (nat_src ^
    {|
      Definition add1 := Nat.add 1.
      CodeGen Function add1 => add1_p add1_s.
      Print add1_p.
      Fail Print add1_s.
      CodeGen Specialize "add1".
      Print add1_s.
    |})

let test_specialization_at_get_ctnt_type_body_from_cfunc (ctx : test_ctxt) : unit =
  assert_coq_success ctx
    (bool_src ^
    {|
      CodeGen Inductive Type bool*bool => "pair_bool_bool".
      CodeGen Inductive Match bool*bool => ""
      | pair => "" "pair_bool_bool_fst" "pair_bool_bool_snd".

      Definition swap {A B : Type} (p : A * B) := let (a, b) := p in (b, a).
      Definition swap_bb p := @swap bool bool p.
      CodeGen Function swap_bb.
      CodeGen Gen "swap_bb".
    |})

let test_mftest (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Fixpoint mftest (n : nat) :=
	match n with
	| O => O
	| S nn => mftest2 nn
	end
      with mftest2 n :=
	match n with
	| O => O
	| S nn => mftest3 nn + 1
	end
      with mftest3 n :=
	match n with
	| O => O
	| S nn => mftest nn
	end.
      CodeGen Function mftest.
    |}) {|
      assert(mftest(0) == 0);
      assert(mftest(1) == 0);
      assert(mftest(2) == 1);
      assert(mftest(3) == 1);
      assert(mftest(4) == 1);
      assert(mftest(5) == 2);
    |}

let suite : OUnit2.test =
  "TestCodeGen" >::: [
    "test_tail_rel" >:: test_tail_rel;
    "test_tail_constructor_bool" >:: test_tail_constructor_bool;
    "test_tail_constructor_args" >:: test_tail_constructor_args;
    "test_tail_constant_bool" >:: test_tail_constant_bool;
    "test_tail_constant_args" >:: test_tail_constant_args;
    "test_tail_match_bool" >:: test_tail_match_bool;
    "test_tail_match_nat" >:: test_tail_match_nat;
    "test_tail_match_singleton" >:: test_tail_match_singleton;
    "test_mono_id_bool" >:: test_mono_id_bool;
    "test_mono_id_bool_omit_cfunc_name" >:: test_mono_id_bool_omit_cfunc_name;
    "test_mono_id_mybool" >:: test_mono_id_mybool;
    "test_mybool_true" >:: test_mybool_true;
    "test_pair_bool_bool" >:: test_pair_bool_bool;
    "test_pair_2bool_bool" >:: test_pair_2bool_bool;
    "test_nat_add_rec" >:: test_nat_add_rec;
    "test_nat_add_iter" >:: test_nat_add_iter;
    "test_list_bool" >:: test_list_bool;
    "test_list_bool_length" >:: test_list_bool_length;
    "test_sum" >:: test_sum;
    "test_add3" >:: test_add3;
    "test_mul3" >:: test_mul3;
    "test_even_odd" >:: test_even_odd;
    "test_inner_fix_even_odd_1" >:: test_inner_fix_even_odd_1;
    "test_inner_fix_even_odd_2" >:: test_inner_fix_even_odd_2;
    "test_app_let" >:: test_app_let;
    "test_app_match" >:: test_app_match;
    "test_cast" >:: test_cast;
    "test_delta_fun_constant" >:: test_delta_fun_constant;
    "test_delta_fun_constructor" >:: test_delta_fun_constructor;
    "test_delta_fun_lambda" >:: test_delta_fun_lambda;
    "test_reduce_proj" >:: test_reduce_proj;
    "test_nil_nat" >:: test_nil_nat;
    "test_singleton_list" >:: test_singleton_list;
    "test_deeply_nested_match" >:: test_deeply_nested_match;
    "test_let_add" >:: test_let_add;
    "test_let_match" >:: test_let_match;
    "test_let_match_let" >:: test_let_match_let;
    "test_add_tailrec" >:: test_add_tailrec;
    "test_add_nontailrec" >:: test_add_nontailrec;
    "test_map_succ" >:: test_map_succ;
    "test_tail_fix_double" >:: test_tail_fix_double;
    "test_nth" >:: test_nth;
    "test_rev_append" >:: test_rev_append;
    "test_merge" >:: test_merge;
    "test_sum_nested_fix" >:: test_sum_nested_fix;
    "test_add_at_non_tail_position" >:: test_add_at_non_tail_position;
    "test_fully_dynamic_func_with_partapp_name" >:: test_fully_dynamic_func_with_partapp_name;
    "test_specialization_at_get_ctnt_type_body_from_cfunc" >:: test_specialization_at_get_ctnt_type_body_from_cfunc;
    "test_mftest" >:: test_mftest;
  ]

let () =
  run_test_tt_main suite
