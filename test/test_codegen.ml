open OUnit2

let ounit_path (ctx : test_ctxt) =
  String.concat ":"
    (List.rev
      (List.map
        (fun n ->
          (match n with
          | OUnitTest.ListItem i -> string_of_int i
          | OUnitTest.Label s -> s))
        ctx.path))

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

let read_file (fn : string) : string =
  let ch = open_in fn in
  let result = really_input_string ch (in_channel_length ch) in
  close_in ch;
  result

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

let cc_opts : string list =
  match Sys.getenv_opt "CFLAGS" with
  | Some v -> List.filter (fun s -> s <> "") (String.split_on_char ' ' v)
  | None -> ["-Werror=unused-label"]

let coqc : string =
  match Sys.getenv_opt "COQC" with
  | Some v -> v
  | None -> "coqc"

let topdir_opt : string option = search_topdir ()

let coq_opts : string list =
  (match topdir_opt with
  | Some topdir -> ["-Q"; topdir ^ "/theories"; "codegen"; "-I"; topdir ^ "/src"]
  | None -> []) @
  ["-bt"]

let expand_tab (str : string) : string =
  let add_spaces buf n =
    for i = 1 to n do
      Buffer.add_char buf ' '
    done
  in
  let buf = Buffer.create (String.length str) in
  let col = ref 0 in
  String.iter
    (fun ch ->
      match ch with
      | '\n' -> Buffer.add_char buf ch; col := 0
      | '\t' -> let n = (8 - (!col mod 8)) in add_spaces buf n; col := !col + n
      | _ -> Buffer.add_char buf ch; col := !col + 1)
    str;
    Buffer.contents buf

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

(*
We don't like usual string literal for regexp because it needs too many backslashes.
OCaml has quoted string {|...|} for no backslash-escapes.
But Str.regexp does not recognize escaped newline character, {|\n|} or "\\n".
So, we define regexp function here to convert escaped control characters to
bare control characters.
*)
let regexp s =
  let n = String.length s in
  let buf = Buffer.create n in
  let rec f i =
    if i < n then
      let c = s.[i] in
      match c with
      | '\\' -> found_backslash (i+1)
      | _ -> Buffer.add_char buf c; f (i+1)
  and found_backslash i =
    if i < n then
      let c = s.[i] in
      match c with
      | 'a' -> Buffer.add_char buf '\x07'; f (i+1)
      | 't' -> Buffer.add_char buf '\t'; f (i+1)
      | 'n' -> Buffer.add_char buf '\n'; f (i+1)
      | 'v' -> Buffer.add_char buf '\x0B'; f (i+1)
      | 'f' -> Buffer.add_char buf '\x0C'; f (i+1)
      | 'r' -> Buffer.add_char buf '\r'; f (i+1)
      | 'e' -> Buffer.add_char buf '\x1B'; f (i+1)
      | 'x' -> found_backslash_x (i+1)
      | _ -> Buffer.add_char buf '\\'; Buffer.add_char buf c; f (i+1)
    else
      Buffer.add_char buf '\\'
  and found_backslash_x i =
    if i+1 < n then
      let c1 = s.[i] in
      let c2 = s.[i+1] in
      match c1, c2 with
      | ('0'..'9' | 'A'..'F' | 'a'..'f'), ('0'..'9' | 'A'..'F' | 'a'..'f') ->
          let hex = Bytes.of_string "0xHH" in
          Bytes.set hex 2 c1;
          Bytes.set hex 3 c2;
          Buffer.add_char buf (Char.chr (int_of_string (Bytes.to_string hex)))
      | _, _ -> Buffer.add_char buf '\\'; Buffer.add_char buf 'x'; f i
    else
      Buffer.add_char buf '\\'; Buffer.add_char buf 'x'; f i
  in
  f 0;
  Str.regexp (Buffer.contents buf)

let my_temp_dir (ctx : test_ctxt) : string =
  match Sys.getenv_opt "CODEGEN_SAVE_TMP" with
  | Some _ -> make_temp_dir "codegen-test" ""
  | None -> bracket_tmpdir ~prefix:"codegen-test" ctx

type test_goal = UntilCoq | UntilCC | UntilExe

let make_foutput regexp seq =
  let buf = Buffer.create 0 in
  (try
    Seq.iter (Buffer.add_char buf) seq
  with End_of_file ->
    ());
  let text = Buffer.contents buf in
  try
    ignore (Str.search_forward regexp text 0);
    assert_bool "expected regexp found" true
  with Not_found ->
    assert_bool "expected regexp not found" false

let codegen_test_template
    ?(goal : test_goal = UntilExe)
    ?(coq_exit_code : Unix.process_status option)
    ?(coq_output_regexp : Str.regexp option)
    ?(generated_code_regexp : Str.regexp option)
    ?(generated_code_regexp_not : Str.regexp option)
    ?(modify_generated_source : (string -> string) option)
    ?(resolve_dependencies : bool = true)
    ?(mutual_recursion_detection : bool = true)
    ?(cc_exit_code : Unix.process_status option)
    ?(main_toplevel_defs : string option)
    (ctx : test_ctxt)
    (coq_commands : string)
    (c_body : string) : unit =
  let d = my_temp_dir ctx in
  let test_path = ounit_path ctx in
  let src_fn = d ^ "/src.v" in
  let gen_fn = d ^ "/gen.c" in
  let main_fn = d ^ "/main.c" in
  let exe_fn = d ^ "/exe" in
  write_file src_fn
    ("(* " ^ test_path ^ " *)\n" ^
    "From codegen Require codegen.\n" ^
    "CodeGen SourceFile \"gen.c\".\n" ^
    "CodeGen Snippet " ^ (escape_coq_str ("/* " ^ test_path ^ " */\n")) ^ ".\n" ^
    delete_indent (expand_tab coq_commands) ^ "\n" ^
    "CodeGen GenerateFile" ^
    (if resolve_dependencies then "" else " DisableDependencyResolver") ^
    (if mutual_recursion_detection then "" else " DisableMutualRecursionDetection") ^
    ".\n");
  write_file main_fn
    ("/* " ^ test_path ^ " */\n" ^
    "#include <stdlib.h> /* for EXIT_SUCCESS, abort and malloc */\n" ^
    "#include <assert.h>\n" ^
    "#include \"gen.c\"\n" ^
    delete_indent (expand_tab (Stdlib.Option.value main_toplevel_defs ~default:"")) ^ "\n" ^
    "int main(int argc, char *argv[]) {\n" ^
    add_n_indent 2 (delete_indent (expand_tab c_body)) ^ "\n" ^
    "  return EXIT_SUCCESS;\n" ^
    "}\n");
  let coq_foutput = Option.map make_foutput coq_output_regexp in
  assert_command
    ~chdir:d
    ~ctxt:ctx
    ?exit_code:coq_exit_code
    ~use_stderr:true
    ?foutput:coq_foutput
    coqc (List.append coq_opts [src_fn]);
  (match generated_code_regexp with
  | None -> ()
  | Some regexp ->
      let ch = open_in gen_fn in
      let text = really_input_string ch (in_channel_length ch) in
      close_in ch;
      try
        ignore (Str.search_forward regexp text 0);
        assert_bool "regexp matched expectedly" true
      with Not_found ->
        assert_bool "regexp not matched unexpectedly" false);
  (match generated_code_regexp_not with
  | None -> ()
  | Some regexp ->
      let ch = open_in gen_fn in
      let text = really_input_string ch (in_channel_length ch) in
      close_in ch;
      try
        ignore (Str.search_forward regexp text 0);
        assert_bool "regexp matched unexpectedly" false
      with Not_found ->
        assert_bool "regexp not matched expectedly" true);
  (match modify_generated_source with
  | None -> ()
  | Some f ->
      write_file gen_fn (f (read_file gen_fn)));
  match goal with
  | UntilCoq -> ()
  | UntilCC ->
      assert_command ~ctxt:ctx ?exit_code:cc_exit_code cc (cc_opts @ ["-o"; exe_fn; main_fn]);
  | UntilExe ->
      assert_command ~ctxt:ctx ?exit_code:cc_exit_code cc (cc_opts @ ["-o"; exe_fn; main_fn]);
      assert_command ~ctxt:ctx exe_fn []

let template_coq_success
    ?(coq_output_regexp : Str.regexp option)
    (ctx : test_ctxt)
    (coq_commands : string) : unit =
  codegen_test_template ~goal:UntilCoq
    ~coq_exit_code:(Unix.WEXITED 0)
    ?coq_output_regexp
    ctx coq_commands ""

let unit_src = {|
      CodeGen InductiveType unit => "void".
|}

let bool_src = {|
      CodeGen InductiveType bool => "bool".
      CodeGen InductiveMatch bool => ""
      | true => "default"
      | false => "case 0".
      CodeGen Constant true => "true".
      CodeGen Constant false => "false".

      CodeGen Snippet "
      #include <stdbool.h> /* for bool, true and false */
      ".
|}

let bool_paren_src = {|
      CodeGen InductiveType bool => "bool (" ")". (* redundant parenthesis *)
      CodeGen InductiveMatch bool => ""
      | true => "default"
      | false => "case 0".
      CodeGen Constant true => "true".
      CodeGen Constant false => "false".
      CodeGen Snippet "
      #include <stdbool.h> /* for bool, true and false */
      ".
|}

let nat_src = {|
      CodeGen InductiveType nat => "nat".
      CodeGen InductiveMatch nat => ""
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
      CodeGen InductiveType list bool => "list_bool".
      CodeGen InductiveMatch list bool => "list_bool_is_nil"
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
      static inline bool list_bool_eq(list_bool s1, list_bool s2) {
        while (s1 && s2) {
          if (s1->head != s2->head) return false;
          s1 = s1->tail;
          s2 = s2->tail;
        }
        return !(s1 || s2);
      }

      ".
|}

let list_nat_src = {|
      CodeGen InductiveType list nat => "list_nat".
      CodeGen InductiveMatch list nat => "list_nat_is_nil"
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
      CodeGen Func mono_id_bool => "mono_id_bool".
    |}) {|
      assert(mono_id_bool(true) == true);
      assert(mono_id_bool(false) == false);
    |}

let test_tail_constructor_bool (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Definition constructor_true : bool := true.
      Definition constructor_false : bool := false.
      CodeGen Func constructor_true.
      CodeGen Func constructor_false.
    |}) {|
      assert(constructor_true() == true);
      assert(constructor_false() == false);
    |}

let test_tail_constructor_args (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Inductive bool_pair : Set := bpair : bool -> bool -> bool_pair.
      CodeGen InductiveType bool_pair => "bool_pair".
      CodeGen InductiveMatch bool_pair => ""
      | bpair => "default" "bool_pair_fst" "bool_pair_snd".
      CodeGen Primitive bpair => "bpair".

      CodeGen Snippet "
      typedef int bool_pair;
      #define bpair(a,b) (((a) << 1) | (b))
      #define bool_pair_fst(x) ((x) >> 1)
      #define bool_pair_snd(x) ((x) & 1)
      ".

      Definition call_bpair a b : bool_pair := bpair a b.
      CodeGen Func call_bpair.
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
      CodeGen Func constant_true.
      CodeGen Func constant_false.
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
      CodeGen Func call_negb.
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
      CodeGen Func f => "f".
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
      CodeGen Func f => "f".
    |}) {|
      assert(f(0) == false);
      assert(f(1) == true);
    |}

let test_tail_match_singleton (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Inductive singleton : Set := C : bool -> singleton.
      CodeGen InductiveType singleton => "singleton".
      CodeGen InductiveMatch singleton => ""
      | C => "unused-case-label" "access".
      CodeGen Snippet "
      typedef bool singleton;
      #define access(s) s
      ".
      Definition f (x : singleton) := match x with C y => y end.
      CodeGen Func f => "f".
    |}) {|
      assert(f(true) == true);
      assert(f(false) == false);
    |}

let test_mono_id_bool (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Definition mono_id_bool (b : bool) := b.
      CodeGen Func mono_id_bool => "mono_id_bool".
    |}) {|
      assert(mono_id_bool(true) == true);
      assert(mono_id_bool(false) == false);
    |}

let test_mono_id_mybool (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    ({|
      Inductive mybool : Set := mytrue : mybool | myfalse : mybool.
      CodeGen InductiveType mybool => "mybool".
      CodeGen InductiveMatch mybool => ""
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
      CodeGen Func mono_id_mybool => "mono_id_mybool".
    |}) {|
      assert(mono_id_mybool(mytrue) == mytrue);
      assert(mono_id_mybool(myfalse) == myfalse);
    |}

let test_mybool_true (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    ({|
      Inductive mybool : Set := mytrue : mybool | myfalse : mybool.
      CodeGen InductiveType mybool => "mybool".
      CodeGen InductiveMatch mybool => ""
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
      CodeGen Func mybool_true => "mybool_true".
    |}) {|
      assert(mybool_true(mytrue) == mytrue);
      assert(mybool_true(myfalse) == mytrue);
    |}

let test_mono_id_bool_omit_cfunc_name (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Definition mono_id_bool (b : bool) := b.
      CodeGen Func mono_id_bool.
    |}) {|
      assert(mono_id_bool(true) == true);
      assert(mono_id_bool(false) == false);
    |}

let test_pair_bool_bool (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      CodeGen InductiveType bool*bool => "pair_bool_bool".
      CodeGen InductiveMatch bool*bool => ""
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
      CodeGen Func fst_pair.
      CodeGen Func snd_pair.
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
      CodeGen InductiveType bool*bool => "pair_bool_bool".
      CodeGen InductiveMatch bool*bool => ""
      | pair => "" "pair_bool_bool_fst" "pair_bool_bool_snd".
      CodeGen Primitive pair bool bool => "make_pair_bool_bool".

      CodeGen InductiveType bool*bool*bool => "pair_2bool_bool".
      CodeGen InductiveMatch bool*bool*bool => ""
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
      CodeGen Func fst_pair.
      CodeGen Func snd_pair.
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
      CodeGen Func my_add_rec.
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
      CodeGen Func my_add_iter.
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
      CodeGen Func is_nil.
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
      CodeGen Func length.
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
      CodeGen Func sum.
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
      CodeGen Func nil_nat.
    |}) {|
      list_nat s = nil_nat();
      assert(s == NULL);
    |}

let test_singleton_list (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^ list_nat_src ^
    {|
      Definition singleton_list (n : nat) : list nat := cons n nil.
      CodeGen Func singleton_list.
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
      CodeGen GlobalInline Nat.add.
      CodeGen Func add3.
    |}) {|
      assert(add3(4) == 7);
    |}

let test_mul3 (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition mul3 (n : nat) : nat := 3 * n.
      CodeGen GlobalInline Nat.mul.
      CodeGen Func mul3.
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
      CodeGen GlobalInline even.
      Definition even3 := even 3.
      CodeGen Func even.
      CodeGen Func odd.
      CodeGen Func even3.
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

let test_even_odd_label_primary (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    ~generated_code_regexp:(Str.regexp "entry_even:")
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
      CodeGen Func even.
      CodeGen Func odd.
    |}) {|
      assert(even(0) == true);
      assert(even(1) == false);
      assert(odd(0) == false);
      assert(odd(1) == true);
    |}

let test_even_odd_label_sibling (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    ~generated_code_regexp:(Str.regexp "entry_odd:")
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
      CodeGen Func even.
      CodeGen Func odd.
    |}) {|
      assert(even(0) == true);
      assert(even(1) == false);
      assert(odd(0) == false);
      assert(odd(1) == true);
    |}

let test_even_odd_count (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^
    {|
      CodeGen Snippet "
      static int even_count = 0;
      static int odd_count = 0;
      ".
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
      CodeGen Func even.
      CodeGen Func odd.
    |})
    ~modify_generated_source:
      (fun s ->
        let s = Str.replace_first
          (regexp {|^bool[ \n]even\(.*\n\(\([^}\n].*\)\n\)*}\n\)|})
          ("bool tmp_even\\1" ^
           "bool even(nat n) { even_count++; return tmp_even(n); }\n")
          s
        in
        let s = Str.replace_first
          (regexp {|^bool[ \n]odd\(.*\n\(\([^}\n].*\)\n\)*}\n\)|})
          ("bool tmp_odd\\1" ^
           "bool odd(nat n) { odd_count++; return tmp_odd(n); }\n")
          s
        in
        s)
    {|
      assert(even(3) == false);
      /* tail recursion elimination avoids calls except the first one */
      assert(even_count == 1);
      assert(odd_count == 0);
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
      CodeGen Func even.
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
      CodeGen Func even.
    |}) {|
      assert(even(0) == true);
      assert(even(1) == false);
      assert(even(2) == true);
      assert(even(3) == false);
      assert(even(4) == true);
    |}

let test_two_even (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^
    {|
      Definition even1 :=
        fix even (n : nat) : bool :=
          match n with | O => true | S m => odd m end
        with odd (m : nat) : bool :=
          match m with | O => false | S n => even n end
        for even.
      Definition even2 :=
        fix even (n : nat) : bool :=
          match n with | O => true | S m => odd m end
        with odd (m : nat) : bool :=
          match m with | O => false | S n => even n end
        for even.
      CodeGen Func even1.
      CodeGen Func even2.
    |}) {|
      assert(even1(0) == true);
      assert(even1(1) == false);
      assert(even1(2) == true);
      assert(even1(3) == false);
      assert(even1(4) == true);
      assert(even2(0) == true);
      assert(even2(1) == false);
      assert(even2(2) == true);
      assert(even2(3) == false);
      assert(even2(4) == true);
    |}

let test_two_even_two_odd (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^
    {|
      Fixpoint even1 (n : nat) : bool :=
        match n with | O => true | S m => odd1 m end
      with odd1 (m : nat) : bool :=
        match m with | O => false | S n => even1 n end.
      Fixpoint even2 (n : nat) : bool :=
        match n with | O => true | S m => odd2 m end
      with odd2 (m : nat) : bool :=
        match m with | O => false | S n => even2 n end.
      CodeGen Func even1.
      CodeGen Func even2.
      CodeGen Func odd1.
      CodeGen Func odd2.
    |}) {|
      assert(even1(0) == true);
      assert(even1(1) == false);
      assert(even1(2) == true);
      assert(even1(3) == false);
      assert(even1(4) == true);
      assert(even2(0) == true);
      assert(even2(1) == false);
      assert(even2(2) == true);
      assert(even2(3) == false);
      assert(even2(4) == true);
      assert(odd1(0) == false);
      assert(odd1(1) == true);
      assert(odd1(2) == false);
      assert(odd1(3) == true);
      assert(odd1(4) == false);
      assert(odd2(0) == false);
      assert(odd2(1) == true);
      assert(odd2(2) == false);
      assert(odd2(3) == true);
      assert(odd2(4) == false);
    |}

let test_app_let (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition foo := (let x := 1 in Nat.add x) 2.
      CodeGen Func foo.
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
      CodeGen Func add_or_sub.
    |}) {|
      assert(add_or_sub(true, 1) == 11);
      assert(add_or_sub(true, 2) == 12);
      assert(add_or_sub(false, 1) == 9);
      assert(add_or_sub(false, 2) == 8);
    |}

let test_let_app_match (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^
    {|
      Definition f a b :=
        let g := Nat.add in
        (match tt with tt => g end) a b.
      CodeGen Func f.
    |}) {|
      assert(f(0, 0) == 0);
      assert(f(0, 1) == 1);
      assert(f(1, 0) == 1);
      assert(f(1, 1) == 2);
      assert(f(4, 7) == 11);
    |}

let test_cast (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition nat_id (n : nat) : nat := (n : nat) + 0.
      CodeGen Func nat_id.
    |}) {|
      assert(nat_id(4) == 4);
    |}

let bool_matchcount_src = {|
      CodeGen InductiveType bool => "bool".
      CodeGen InductiveMatch bool => "sw_bool"
      | true => "default"
      | false => "case 0".
      CodeGen Constant true => "true".
      CodeGen Constant false => "false".

      CodeGen Snippet "
      #include <stdbool.h> /* for bool, true and false */
      static int bool_match_count = 0;
      #define sw_bool(x) ((bool_match_count++), (x))
      ".
|}

let test_beta_var_presimp (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_matchcount_src ^ nat_src ^
    {|
      Definition f (b : bool) : nat :=
        let g := (fun (b2 : bool) => if b2 then Nat.add else Nat.sub) b in
        g 1 1 + g 2 2.
      CodeGen Func f.
    |}) {|
      assert(f(true) == 6);
      assert(bool_match_count == 2);
      assert(f(false) == 0);
      assert(bool_match_count == 4);
    |}

let test_matchapp_before_reduction (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_matchcount_src ^ nat_src ^
    {|
      (* conditional of z must be reduced at compile-time *)
      Definition f (x:bool) :=
        let y := true in
        (if x then
          fun z:bool => if z then 0 else 1
        else
          fun z:bool => if z then 2 else 3) y.
      CodeGen Func f.
    |}) {|
      assert(f(true) == 0);
      assert(bool_match_count == 1);
      assert(f(false) == 2);
      assert(bool_match_count == 2);
    |}

let test_delta_fun_constant (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition add (a b : nat) : nat := let f := Nat.add in f a b.
      CodeGen Func add.
    |}) {|
      assert(add(2,3) == 5);
    |}

let test_delta_fun_constructor (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition succ (n : nat) : nat := let f := S in f n.
      CodeGen Func succ.
    |}) {|
      assert(succ(2) == 3);
    |}

let test_delta_fun_lambda (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition succ (n : nat) : nat := let f x := S x in f n.
      CodeGen Func succ.
    |}) {|
      assert(succ(2) == 3);
    |}

let test_delta_fun_nested_let (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^
    {|
      Definition f (x : nat) :=
        let f := S in
        let one := f 0 in
        match one with
        | O => false
        | S _ => true
        end.
      CodeGen Func f.
    |}) {|
      assert(f(0) == true);
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
      Record TestRecord (par:Type) : Set := mk { f0 : nat; f1 : nat }.
      Definition f0_mk a b : nat := f0 bool (mk bool a b).
      Definition f1_mk a b : nat := f1 bool (mk bool a b).
      CodeGen Func f0_mk.
      CodeGen Func f1_mk.
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
      CodeGen Func f (repeat true 0) => "f0".
      CodeGen Func f (repeat true 10) => "f10".
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
      CodeGen Func add3.
    |}) {|
      assert(add3(1,2,3) == 6);
    |}

(* gen_head Case *)
let test_let_match (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^
    {|
      Definition tst (b : bool) : bool :=
        let not_b := match b with true => false | false => true end in
        match not_b with true => false | false => true end.
      CodeGen Func tst.
    |}) {|
      assert(tst(true) == true);
      assert(tst(false) == false);
    |}

(* gen_head LetIn *)
let test_let_match_let (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^
    {|
      Definition tst (b : bool) : nat :=
        let n := match b with true => let z := O in S z | false => O end in
        S n.
      CodeGen Func tst.
    |}) {|
      assert(tst(false) == 1);
      assert(tst(true) == 2);
    |}

(* gen_head LetIn, cargs != [] *)
let test_let_match_let_nonempty_cargs (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^
    {|
      Definition f x y :=
        let v :=
          match x with
          | true => let z := 1 in Nat.add z
          | false => let z := 2 in Nat.add z
          end y
        in
        v.
      CodeGen Func f.
    |}) {|
      assert(f(true, 3) == 4);
      assert(f(false, 3) == 5);
    |}

let test_let_unused_is_not_specialized (ctx : test_ctxt) : unit =
  template_coq_success ctx
    {|
      Definition f a b := let unused := Nat.pow 3 3 in Nat.add a b.
      CodeGen Gen f.
      Fail Print CodeGen Specialization Nat.pow.
    |}

let test_let_only_used_in_static_is_not_specialized (ctx : test_ctxt) : unit =
  template_coq_success ctx
    {|
      Definition f a :=
        let only_used_in_static := Nat.mul 2 3 in
        Nat.add only_used_in_static a.
      CodeGen StaticArgs Nat.add s d.
      CodeGen Gen f.
      Fail Print CodeGen Specialization Nat.mul.
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
      CodeGen Func add.
    |}) {|
      assert(add(0,0) == 0);
      assert(add(0,1) == 1);
      assert(add(1,0) == 1);
      assert(add(1,1) == 2);
    |}

let test_add_nontailrec (ctx : test_ctxt) : unit =
  template_coq_success ctx
    (nat_src ^
    {|
      Fixpoint add (a b : nat) : nat :=
        match a with
        | O => b
        | S a' => S (add a' b)
        end.
      CodeGen Func add.
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
      CodeGen Func dbl.
    |}) {|
      assert(dbl(0) == 0);
      assert(dbl(1) == 2);
    |}

let test_nth (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^ list_nat_src ^
    {|
      Require Import List.
      CodeGen Func nth nat => "nth".
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
      CodeGen Func nth nat => "nth".
      CodeGen Func rev_append nat => "rev_append".
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
      CodeGen Func nth nat => "nth".
      CodeGen Func rev_append nat => "rev_append".
      CodeGen Func merge.
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

let test_merge_nontailrec (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^ list_nat_src ^
    {|
      Require Import List.
      Definition merge_nontailrec :=
        fix f (s1 : list nat) :=
          fix g (s2 : list nat) :=
            match s1 with
            | nil => s2
            | cons v1 s1' =>
                match s2 with
                | nil => s1
                | cons v2 s2' =>
                    if Nat.ltb v1 v2 then
                      cons v1 (f s1' s2)
                    else
                      cons v2 (g s2')
                end
            end.
      CodeGen Func nth nat => "nth".
      CodeGen Func merge_nontailrec.
    |}) {|
      #define is_nil(s) list_nat_is_nil(s)
      #define head(s) list_nat_head(s)
      #define tail(s) list_nat_tail(s)
      #define cons(h,t) list_nat_cons(h,t)
      #define list4(v1, v2, v3, v4) cons(v1, cons(v2, cons(v3, cons(v4, NULL))))
      list_nat s1 = list4(0,2,8,10);
      list_nat s2 = list4(1,4,5,20);
      list_nat s3 = merge_nontailrec(s1, s2);
      assert(nth(0, s3, 999) == 0);
      assert(nth(1, s3, 999) == 1);
      assert(nth(2, s3, 999) == 2);
      assert(nth(3, s3, 999) == 4);
      assert(nth(4, s3, 999) == 5);
      assert(nth(5, s3, 999) == 8);
      assert(nth(6, s3, 999) == 10);
      assert(nth(7, s3, 999) == 20);
      assert(nth(8, s3, 999) == 999);
    |}

let test_ackermann (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Fixpoint ack m :=
        fix ackm n :=
          match m with
          | 0 => S n
          | S m' =>
            match n with
            | 0 => ack m' 1
            | S n' => ack m' (ackm n')
            end
          end.
      CodeGen Func ack.
    |}) {|
      assert(ack(0, 0) == 1);
      assert(ack(0, 1) == 2);
      assert(ack(0, 2) == 3);
      assert(ack(0, 3) == 4);
      assert(ack(1, 0) == 2);
      assert(ack(1, 1) == 3);
      assert(ack(1, 2) == 4);
      assert(ack(1, 3) == 5);
      assert(ack(2, 0) == 3);
      assert(ack(2, 1) == 5);
      assert(ack(2, 2) == 7);
      assert(ack(2, 3) == 9);
      assert(ack(3, 0) == 5);
      assert(ack(3, 1) == 13);
      assert(ack(3, 2) == 29);
      assert(ack(3, 3) == 61);
    |}

let test_ackermann_plus1 (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Fixpoint ack m :=
        fix ackm n :=
          match m with
          | 0 => S n
          | S m' =>
            match n with
            | 0 => ack m' 1
            | S n' => ack m' (ackm n')
            end
          end.
      Definition f x y := let z := ack x y in S z.
      CodeGen GlobalInline ack.
      CodeGen Func f.
    |}) {|
      assert(f(0, 0) == 2);
      assert(f(0, 1) == 3);
      assert(f(0, 2) == 4);
      assert(f(0, 3) == 5);
      assert(f(1, 0) == 3);
      assert(f(1, 1) == 4);
      assert(f(1, 2) == 5);
      assert(f(1, 3) == 6);
      assert(f(2, 0) == 4);
      assert(f(2, 1) == 6);
      assert(f(2, 2) == 8);
      assert(f(2, 3) == 10);
      assert(f(3, 0) == 6);
      assert(f(3, 1) == 14);
      assert(f(3, 2) == 30);
      assert(f(3, 3) == 62);
    |}

let test_uphalf (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Fixpoint half (n : nat) : nat := match n with O => n | S n' => uphalf n' end
      with uphalf (n : nat) : nat := match n with O => n | S n' => S (half n') end.
      CodeGen Func half.
      CodeGen Func uphalf.
    |}) {|
      assert(half(0) == 0);
      assert(half(1) == 0);
      assert(half(2) == 1);
      assert(half(3) == 1);
      assert(half(4) == 2);
      assert(half(5) == 2);
      assert(half(6) == 3);
      assert(half(7) == 3);
      assert(half(8) == 4);
      assert(half(9) == 4);
      assert(uphalf(0) == 0);
      assert(uphalf(1) == 1);
      assert(uphalf(2) == 1);
      assert(uphalf(3) == 2);
      assert(uphalf(4) == 2);
      assert(uphalf(5) == 3);
      assert(uphalf(6) == 3);
      assert(uphalf(7) == 4);
      assert(uphalf(8) == 4);
      assert(uphalf(9) == 5);
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
      CodeGen Func sum.
    |}) {|
      #define is_nil(s) list_nat_is_nil(s)
      #define head(s) list_nat_head(s)
      #define tail(s) list_nat_tail(s)
      #define cons(h,t) list_nat_cons(h,t)
      #define list4(v1, v2, v3, v4) cons(v1, cons(v2, cons(v3, cons(v4, NULL))))
      list_nat s = list4(1,2,3,4);
      assert(sum(s, 0) == 10);
    |}

(* gen_head Fix, single tail recursive loop *)
(* The fix-term must be translated to a loop.
  Thus, the address of "a" in the stack will be preserved.
  If the invocation of fix-term is translated as function call,
  The address of "a" is changed because the fix-term has
  individual stack frame.
 *)
let test_add_at_non_tail_position1 (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^
    {|
      Require Import List.
      Definition checkaddr (n : nat) : nat := 0.
      CodeGen Snippet "static nat checkaddr_imp(nat *);".
      CodeGen Snippet "#define checkaddr(x) checkaddr_imp(&x)".
      Definition f a b c :=
        let ab :=
          (fix add1 x y :=
            match x with
            | O => y
            | S x' => add1 x' (S y + checkaddr a)
            end) a b
        in
        ab + c + checkaddr a.
      CodeGen Primitive checkaddr => "checkaddr".
      CodeGen Func f.
    |})
    ~main_toplevel_defs:{|
      static nat *pointer = NULL;
      static nat checkaddr_imp(nat *p) {
        if (pointer == NULL)
          pointer = p;
        else
          assert(p == pointer);
        return 0;
      }
    |}
    {|
      assert(f(1, 2, 3) == 6);
    |}

(* gen_head Fix, multiple loops *)
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
      CodeGen Func f.
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
      CodeGen GlobalInline map.
      CodeGen Func map_succ.
    |}) {|
      #define is_nil(s) list_nat_is_nil(s)
      #define head(s) list_nat_head(s)
      #define tail(s) list_nat_tail(s)
      #define cons(h,t) list_nat_cons(h,t)
      assert(is_nil(map_succ(NULL)));
      assert(head(map_succ(cons(1, NULL))) == 2);
    |}

let test_fully_dynamic_func_with_presimp_name (ctx : test_ctxt) : unit =
  template_coq_success ctx
    (nat_src ^
    {|
      Definition add1 := Nat.add 1.
      CodeGen Func add1 => add1_p add1_s.
      Print add1_p.
      Fail Print add1_s.
      CodeGen SimplifyFunction "add1".
      Print add1_s.
    |})

let test_specialized_func_with_presimp_name (ctx : test_ctxt) : unit =
  template_coq_success ctx
    (nat_src ^
    {|
      Definition myadd := Nat.add.
      CodeGen Func myadd 1 => myadd1 myadd1_s.
      Print myadd1.
      Fail Print myadd1_s.
      CodeGen SimplifyFunction "myadd1".
      Print myadd1_s.
    |})

let test_specialization_at_get_ctnt_type_body_from_cfunc (ctx : test_ctxt) : unit =
  template_coq_success ctx
    (bool_src ^
    {|
      CodeGen InductiveType bool*bool => "pair_bool_bool".
      CodeGen InductiveMatch bool*bool => ""
      | pair => "" "pair_bool_bool_fst" "pair_bool_bool_snd".
      Definition swap {A B : Type} (p : A * B) := let (a, b) := p in (b, a).
      Definition swap_bb p := @swap bool bool p.
      CodeGen Func swap_bb.
      CodeGen Gen "swap_bb".
    |})

let test_letin_in_constructor_type (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] constructor type contains let-in:")
    ctx
    {|
      Inductive TestInd := TestConstructor : forall (x := 0) (y : nat), TestInd.
      Definition f (v : TestInd) :=
        match v with
        | TestConstructor x y => x
        end.
      CodeGen Gen f. (* should fail *)
    |} {| |}

let test_arguments_contain_sort (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ {|
      Definition zero (T : Type) := 0.
      Definition f (n : nat) := zero Type.
      CodeGen Func f.
    |}) {|
      assert(f(10) == 0);
    |}

let test_arguments_contain_prod (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ {|
      Definition zero (T : Type) := 0.
      Definition f (n : nat) := zero (nat -> nat).
      CodeGen Func f.
    |}) {|
      assert(f(10) == 0);
    |}

let test_arguments_contain_ind (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ {|
      Definition zero (T : Type) := 0.
      Definition f (n : nat) := zero nat.
      CodeGen Func f.
    |}) {|
      assert(f(10) == 0);
    |}

let test_command_gen_qualid (ctx : test_ctxt) : unit =
  template_coq_success ctx
    (bool_src ^
    {|
      Definition id_bool (x : bool) : bool := x.
      CodeGen Gen id_bool.
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
      CodeGen Func mftest.
    |}) {|
      assert(mftest(0) == 0);
      assert(mftest(1) == 0);
      assert(mftest(2) == 1);
      assert(mftest(3) == 1);
      assert(mftest(4) == 1);
      assert(mftest(5) == 2);
    |}

let test_multifunc_different_return_types (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^
    {|
      CodeGen Snippet "
      /* mybool is incompatible with uint64_t unlike bool.*/
      typedef struct { int b; } mybool;
      #define mytrue ((mybool){ 1 })
      #define myfalse ((mybool){ 0 })
      ".
      Inductive mybool : Set := mytrue | myfalse.
      Definition f (n : nat) : mybool :=
        let
          y := (fix g (n : nat) : nat :=
                match n with
                | O => O
                | S m => S (g m)
                end) n
        in
        match y with
        | O => myfalse
        | S _ => mytrue
        end.
      CodeGen Func f.
      CodeGen InductiveType mybool => "mybool".
      CodeGen Constant mytrue => "mytrue".
      CodeGen Constant myfalse => "myfalse".
    |}) {|
      assert(f(0).b == 0);
      assert(f(1).b == 1);
      assert(f(2).b == 1);
    |}

let test_multifunc_noargument (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition f0 := 0.
      Definition f1 :=
        let g := fix id_nat x :=
                  match x with
                  | O => O
                  | S y => S (id_nat y)
                  end
        in
        S (g f0).
      CodeGen Func f0.
      CodeGen Func f1.
    |}) {|
      assert(f0() == 0);
      assert(f1() == 1);
    |}

let forest_src = {|
      (* This example is taken from Coq reference manual *)
      Inductive tree : Set :=
      | node : forest -> tree
      with forest : Set :=
      | emptyf : forest
      | consf : tree -> forest -> forest.

      CodeGen Snippet "
      #include <stdlib.h> /* for NULL, malloc(), abort() */

      struct tree_st {
        struct forest_st *f;
      };

      struct forest_st {
        /* constructed by consf constructor */
        struct tree_st *t;
        struct forest_st *f;
      };

      typedef struct tree_st *tree; /* NULL is invalid */
      typedef struct forest_st *forest; /* NULL means emptyf constructor */

      tree node(forest f)
      {
        tree t;
        if ((t = malloc(sizeof(*t))) == NULL) { abort(); }
        t->f = f;
        return t;
      }

      #define emptyf NULL

      forest consf(tree t, forest f)
      {
        forest ret;
        if ((ret = malloc(sizeof(*ret))) == NULL) { abort(); }
        ret->t = t;
        ret->f = f;
        return ret;
      }

      #define node_get_member_0(n) ((n)->f)

      #define sw_forest(f) ((f) != NULL)
      #define emptyf_tag 0
      #define consf_tag 1
      #define consf_get_member_0(c) ((c)->t)
      #define consf_get_member_1(c) ((c)->f)
      ".
|}

let test_mutual_sizet_sizef (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ forest_src ^
    {|
      Fixpoint sizet (t:tree) : nat :=
        let (f) := t in S (sizef f)
      with sizef (f:forest) : nat :=
        match f with
        | emptyf => O
        | consf t f => plus (sizet t) (sizef f)
        end.
      CodeGen Func sizet.
      CodeGen Func sizef.
    |}) {|
      forest f0 = emptyf;
      tree t1 = node(f0);
      forest f1 = consf(t1, f0);
      forest f2 = consf(t1, f1);
      assert(sizef(f0) == 0);
      assert(sizet(t1) == 1);
      assert(sizef(f1) == 1);
      assert(sizef(f2) == 2);
    |}

(*
  test dedup by counting calls of sizet and sizef.
  If dedup doesn't work, calling sizef doesn't cause calling sizet.
  In such case, assert(sizet_count == 2) will fail.
*)
let test_mutual_sizet_sizef_dedup (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ forest_src ^
    {|
      CodeGen Snippet "
      static int sizet_count = 0;
      static int sizef_count = 0;
      ".
      Fixpoint sizet (t:tree) : nat :=
        let (f) := t in S (sizef f)
      with sizef (f:forest) : nat :=
        match f with
        | emptyf => O
        | consf t f => plus (sizet t) (sizef f)
        end.
      CodeGen Func sizet.
      CodeGen Func sizef.
    |})
    ~modify_generated_source:
      (fun s ->
        (*print_string src;*)
        let s = Str.replace_first
          (regexp {|^nat[ \n]sizet\(.*\n\(\([^}\n].*\)\n\)*}\n\)|})
          ("nat tmp_sizet\\1" ^
           "nat sizet(tree t) { sizet_count++; return tmp_sizet(t); }\n")
          s
        in
        let s = Str.replace_first
          (regexp {|^nat[ \n]sizef\(.*\n\(\([^}\n].*\)\n\)*}\n\)|})
          ("nat tmp_sizef\\1" ^
           "nat sizef(forest f) { sizef_count++; return tmp_sizef(f); }\n")
          s
        in
        s)
    {|
      forest f0 = emptyf;
      tree t1 = node(f0);
      forest f1 = consf(t1, f0);
      forest f2 = consf(t1, f1);
      assert(sizef(f2) == 2);
      assert(sizet_count == 2);
      assert(sizef_count == 5);
    |}

let test_mutual_sizet_sizef_nodedup (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    ~mutual_recursion_detection:false
    (nat_src ^ forest_src ^
    {|
      CodeGen Snippet "
      static int sizet_count = 0;
      static int sizef_count = 0;
      ".
      Fixpoint sizet (t:tree) : nat :=
        let (f) := t in S (sizef f)
      with sizef (f:forest) : nat :=
        match f with
        | emptyf => O
        | consf t f => plus (sizet t) (sizef f)
        end.
      CodeGen Func sizet.
      CodeGen Func sizef.
    |})
    ~modify_generated_source:
      (fun s ->
        (*print_string src;*)
        let s = Str.replace_first
          (regexp {|^nat[ \n]sizet\(.*\n\(\([^}\n].*\)\n\)*}\n\)|})
          ("nat tmp_sizet\\1" ^
           "nat sizet(tree t) { sizet_count++; return tmp_sizet(t); }\n")
          s
        in
        let s = Str.replace_first
          (regexp {|^nat[ \n]sizef\(.*\n\(\([^}\n].*\)\n\)*}\n\)|})
          ("nat tmp_sizef\\1" ^
           "nat sizef(forest f) { sizef_count++; return tmp_sizef(f); }\n")
          s
        in
        s)
    {|
      forest f0 = emptyf;
      tree t1 = node(f0);
      forest f1 = consf(t1, f0);
      forest f2 = consf(t1, f1);
      assert(sizef(f2) == 2);
      assert(sizet_count == 0); /* sizet is not called because a private version of sizet is generated for sizef. */
      assert(sizef_count == 5);
    |}

let test_mutual_static1 (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Fixpoint idnat1 n :=
        match n with
        | O => O
        | S m => S (idnat2 m)
        end
      with idnat2 n :=
        match n with
        | O => O
        | S m => S (idnat1 m)
        end.
      CodeGen Snippet "extern nat idnat1(nat v1_n);".
      CodeGen Func idnat1.
      CodeGen StaticFunc idnat2.
      CodeGen Snippet "static nat idnat2(nat v1_n);".
    |})
    {|
      assert(idnat1(3) == 3);
      assert(idnat2(4) == 4);
    |}

let test_mutual_static2 (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Fixpoint idnat1 n :=
        match n with
        | O => O
        | S m => S (idnat2 m)
        end
      with idnat2 n :=
        match n with
        | O => O
        | S m => S (idnat1 m)
        end.
      CodeGen Snippet "extern nat idnat2(nat v1_n);".
      CodeGen StaticFunc idnat1.
      CodeGen Func idnat2.
      CodeGen Snippet "static nat idnat1(nat v1_n);".
    |})
    {|
      assert(idnat1(3) == 3);
      assert(idnat2(4) == 4);
    |}

let test_mutual_fix_outer_noninlinable_fix_must_be_noninlinable (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition f x y :=
        let z :=
          (fix g (m : nat) { struct m } :=
            fix h (n : nat) { struct n } :=
              match n with
              | O => m
              | S n' => S (h n')
              end) x y
        in
        S z.
      CodeGen Func f.
    |})
    {|
      assert(f(10,0) == 11);
      assert(f(20,1) == 22);
      assert(f(30,2) == 33);
    |}

let test_nested_fix_must_have_consistent_arguments (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition f x y :=
	let g :=
	  fix g (m : nat) {struct m} :=
	  fix h (n : nat) {struct n} :=
	  match n with
	  | O => O
	  | S n' => S (h n')
	  end
	in
	S (g x y).
      CodeGen Func f.
    |})
    {|
      assert(f(10,0) == 1);
      assert(f(20,1) == 2);
      assert(f(30,2) == 3);
    |}

let test_nongoto_fixterm_at_nontail (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition f x :=
        let a :=
          (fix g y :=
            match y with
            | O => 0
            | S z => x + g z
            end) x
        in
        S a.
      CodeGen Func f.
    |}) {|
      assert(f(0) == 1);
      assert(f(1) == 2);
      assert(f(2) == 5);
      assert(f(3) == 10);
      assert(f(4) == 17);
      assert(f(5) == 26);
    |}

let test_nongoto_fixterm_in_gotoonly_fixterm_at_nontail (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition f a b c :=
        let d :=
          (fix g x y z :=
            match x with
            | O =>
              (fix h u v :=
                match u with
                | O => v
                | S u' => S (h u' v)
                end) y z
            | S x' =>
              g x' (S y) z
            end) a b c
        in
        S d.
      CodeGen Func f.
    |}) {|
      assert(f(1,2,3) == 7);
      assert(f(4,5,6) == 16);
      assert(f(7,8,9) == 25);
    |}

let test_useless_fixterm_at_nontail (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition f x :=
        let a :=
          (fix g (y : nat) := 0) x
        in
        S a.
      CodeGen Func f.
    |}) {|
      assert(f(0) == 1);
      assert(f(1) == 1);
    |}

let test_extra_arguments (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition test_extra_arguments (a b c d e : nat) :=
        let y :=
          (fix g x :=
            match x with
            | O => a + c + e
            | S x' => g x'
            end) b
        in
        S y.
      CodeGen Func test_extra_arguments.
    |}) {|
      assert(test_extra_arguments(1,2,3,4,5) == 10);
    |}

let test_extra_arguments_nested_exarg_used (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition test_extra_arguments_nested_exarg_used (a b c d e : nat) :=
        let y :=
          (fix g x :=
            match x with
            | O => a + c
            | S x' =>
              let z :=
                (fix h u :=
                  match u with
                  | O => e
                  | S u' => g x' + h u'
                  end) x'
              in
              z + g x'
            end) b
        in
        S y.
      CodeGen Func test_extra_arguments_nested_exarg_used.
    |}) {|
      assert(test_extra_arguments_nested_exarg_used(1,2,3,4,5) == 24);
    |}

let test_extra_arguments_nested_exarg_unused (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition test_extra_arguments_nested_exarg_unused (a b c d e : nat) :=
        let y :=
          (fix g x :=
            match x with
            | O => a + c
            | S x' =>
              let z :=
                (fix h u :=
                  match u with
                  | O => e
                  | S u' => h u'
                  end) x'
              in
              z + g x'
            end) b
        in
        S y.
      CodeGen Func test_extra_arguments_nested_exarg_unused.
    |}) {|
      assert(test_extra_arguments_nested_exarg_unused(1,2,3,4,5) == 15);
    |}

let test_unused_argument (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition f :=
        fun (a : nat) =>
        fix f (x : nat) :=
          match x with
          | O => 0
          | S y => S (f y)
          end.
      CodeGen Func f.
    |}) {|
      assert(f(100, 0) == 0);
      assert(f(100, 1) == 1);
      assert(f(100, 2) == 2);
      assert(f(100, 3) == 3);
    |}

let test_inner_fixfunc_goto_exarg_fixfunc (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition f :=
        fun (a : nat) =>
        fun (b : nat) =>
        fix f (x : nat) :=
          match x with
          | O => 0
          | S y => let z :=
                     (fix g (u : nat) := match u with
                                         | O => adda y
                                         | S v => S (g v)
                                         end) y
                   in z + f y
          end
        with adda (u : nat) :=
          a + u
        for f.
      CodeGen Func f.
    |}) {|
      assert(f(1, 2, 3) == 9);
    |}

let test_parallel_assignment (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Fixpoint f (x y z : nat) :=
        match x with
        | O => y
        | S x' => f x' z y
        end.
      CodeGen Func f.
    |}) {|
      assert(f(0, 1, 2) == 1);
      assert(f(1, 1, 2) == 2);
      assert(f(2, 1, 2) == 1);
      assert(f(3, 1, 2) == 2);
      assert(f(4, 1, 2) == 1);
      assert(f(5, 1, 2) == 2);
    |}

let test_unused_fixfunc_in_internal_fixterm (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Fixpoint f (n : nat) := 0
      with g (n : nat) := 0.
      CodeGen Func f.
    |}) {|
      assert(f(0) == 0);
    |}

let test_unused_fixfunc_in_external_fixterm (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Definition f a :=
        let gh := fix g x :=
                    (fix h y n :=
                      match y with
                      | O =>
                        match x with
                        | O => n
                        | S x2 => g x2 x (S n)
                        end
                      | S y2 => h y2 (S n)
                      end)
                  with dummy y := match y with O => 1 | S y2 => dummy y2 end
                  for g
        in
        S (gh a 0 0).
      CodeGen Func f.
    |}) {|
      assert(f(0) == 1);
      assert(f(1) == 3);
      assert(f(2) == 6);
      assert(f(3) == 10);
      assert(f(4) == 15);
    |}

let test_primitive_projection (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^
    {|
      CodeGen Snippet "
      typedef struct { bool fst; bool snd; } bool_pair;
      #define make_bool_pair(fst, snd) ((bool_pair){ (fst), (snd) })
      #define bool_pair_fst(x) ((x).fst)
      #define bool_pair_snd(x) ((x).snd)
      ".

      Set Primitive Projections. (* enables Proj *)
      Record bool_pair : Set := make_bool_pair { member1 : bool; member2 : bool }.

      CodeGen InductiveType bool_pair => "bool_pair".
      CodeGen InductiveMatch bool_pair => ""
      | make_bool_pair => "" "bool_pair_fst" "bool_pair_snd".
      CodeGen Primitive make_bool_pair => "make_bool_pair".

      Definition make (x y : bool) := make_bool_pair x y.
      Definition bbfst (x : bool_pair) := member1 x.
      Definition bbsnd (x : bool_pair) := member2 x.
      CodeGen Func make.
      CodeGen Func bbfst.
      CodeGen Func bbsnd.
    |}) {|
      assert(make(true,true).fst == true); assert(make(true,true).snd == true);
      assert(make(true,false).fst == true); assert(make(true,false).snd == false);
      assert(make(false,true).fst == false); assert(make(false,true).snd == true);
      assert(make(false,false).fst == false); assert(make(false,false).snd == false);
      assert(bbfst(make(true,true)) == true); assert(bbsnd(make(true,true)) == true);
      assert(bbfst(make(true,false)) == true); assert(bbsnd(make(true,false)) == false);
      assert(bbfst(make(false,true)) == false); assert(bbsnd(make(false,true)) == true);
      assert(bbfst(make(false,false)) == false); assert(bbsnd(make(false,false)) == false);
    |}

let test_primitive_projection_nontail (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^
    {|
      CodeGen Snippet "
      typedef struct { bool fst; bool snd; } bool_pair;
      #define make_bool_pair(fst, snd) ((bool_pair){ (fst), (snd) })
      #define bool_pair_fst(x) ((x).fst)
      #define bool_pair_snd(x) ((x).snd)
      ".

      Set Primitive Projections. (* enables Proj *)
      Record bool_pair : Set := make_bool_pair { member1 : bool; member2 : bool }.

      CodeGen InductiveType bool_pair => "bool_pair".
      CodeGen InductiveMatch bool_pair => ""
      | make_bool_pair => "" "bool_pair_fst" "bool_pair_snd".
      CodeGen Primitive make_bool_pair => "make_bool_pair".

      Definition make (x y : bool) := make_bool_pair x y.
      Definition bbfst (x : bool_pair) := let y := member1 x in id y.
      Definition bbsnd (x : bool_pair) := let y := member2 x in id y.
      CodeGen Func id bool.
      CodeGen Func make.
      CodeGen Func bbfst.
      CodeGen Func bbsnd.
    |}) {|
      assert(make(true,true).fst == true); assert(make(true,true).snd == true);
      assert(make(true,false).fst == true); assert(make(true,false).snd == false);
      assert(make(false,true).fst == false); assert(make(false,true).snd == true);
      assert(make(false,false).fst == false); assert(make(false,false).snd == false);
      assert(bbfst(make(true,true)) == true); assert(bbsnd(make(true,true)) == true);
      assert(bbfst(make(true,false)) == true); assert(bbsnd(make(true,false)) == false);
      assert(bbfst(make(false,true)) == false); assert(bbsnd(make(false,true)) == true);
      assert(bbfst(make(false,false)) == false); assert(bbsnd(make(false,false)) == false);
    |}

let test_matchapp_twoarg (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (unit_src ^ bool_src ^ nat_src ^ {|
      Definition n_of_bn (b : bool) (n : nat) : nat := n.
      Definition f (c : bool) (b : bool) (n : nat) :=
        match c with
        | true => fun (n2 : nat) (b2 : bool) => S (n_of_bn b2 n2)
        | false => fun (n2 : nat) (b2 : bool) => S (S (n_of_bn b2 n2))
        end n b.
      CodeGen Func f.
    |}) {|
    assert(f(true, true, 10) == 11);
    assert(f(false, false, 20) == 22);
    |}

(*
"Move Match Argument" transformation must be applied multiply.
"Move Match Argument" phase moves "x" into branches of conditional.
S-reductions (zeta-app) moves "x" into the body of let-in.
Since match-expression (if-expression) and let-ins are nested,
two "Move Match Argument" are required to transform the term.
(and additional one to check "Move Match Argument" doesn't change the term.)
*)
let test_matchapp_multiple_phases (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ nat_src ^ {|
      Definition f (b1 b2 : bool) (x y z1 z2 z3 z4 : nat) : nat :=
        (if b1 then
          let y := S y in
          if b2 then
            fun x => x + y + z1
          else
            fun x => x + y + z2
        else
          let y := S y in
          if b2 then
            fun x => x + y + z3
          else
            fun x => x + y + z4) x.
      CodeGen Func f.
    |}) {|
    assert(f(true, true, 100, 19, 1, 2, 3, 4) == 121);
    assert(f(true, false, 100, 19, 1, 2, 3, 4) == 122);
    assert(f(false, true, 100, 19, 1, 2, 3, 4) == 123);
    assert(f(false, false, 100, 19, 1, 2, 3, 4) == 124);
    |}

(*
This test needs to transform
(match m with ... | C args => br | ... end n) to
(match m with ... | C args => br n | ... end)
where m is a decreasing argument of the outer fixpoint.
codegen verify
  (match m with ... | C args => br | ... end n) =
  (match m with ... | C args => br n | ... end).
But it doesn't verify
  (fun (n : nat) => fix g (m : nat) : nat :=
    (match m with ... | C args => br | ... end n)) =
  (fun (n : nat) => fix g (m : nat) : nat :=
    (match m with ... | C args => br n | ... end)).
Because the verification needs induction which is difficult to automate.
(Above description assumes functional_extensionality.)
*)
let test_matchapp_and_fix (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ {|
      Definition f (n : nat) :=
        fix g (m : nat) : nat :=
        match m with
        | O => fun n => n
        | S m' => fun n => g m'
        end n.
      CodeGen Func f.
    |}) {|
    assert(f(10, 5) == 10);
    |}

let test_auto_ind_type (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^
    {|
      CodeGen Snippet "typedef bool mybool;".
      Inductive mybool : Set := mytrue : mybool | myfalse : mybool.
      Definition id_mybool (x : mybool) : mybool := x.
      CodeGen Func id_mybool.
    |}) {|
      assert(id_mybool(true) == true);
      assert(id_mybool(false) == false);
    |}

let test_auto_ind_match_cstrlabel (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^
    {|
      CodeGen Snippet "
      typedef bool mybool;
      #define sw_mybool(x) (x)
      #define mytrue_tag true
      #define myfalse_tag false
      ".
      Inductive mybool : Set := mytrue : mybool | myfalse : mybool.
      Definition bool_of_mybool (x : mybool) :=
        match x with
        | mytrue => true
        | myfalse => false
        end.
      CodeGen Func bool_of_mybool.
    |}) {|
      assert(bool_of_mybool(true) == true);
      assert(bool_of_mybool(false) == false);
    |}

let test_auto_ind_match_cstrmember (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Inductive bool_pair : Set := bpair : bool -> bool -> bool_pair.
      CodeGen Snippet "
      typedef int bool_pair;
      #define bpair(a,b) (((a) << 1) | (b))
      #define bpair_get_member_0(x) ((x) >> 1)
      #define bpair_get_member_1(x) ((x) & 1)
      ".
      Definition bbfst (x : bool_pair) := match x with bpair a b => a end.
      Definition bbsnd (x : bool_pair) := match x with bpair a b => b end.
      CodeGen Func bbfst.
      CodeGen Func bbsnd.
    |}) {|
      assert(bbfst(0) == 0); assert(bbsnd(0) == 0);
      assert(bbfst(1) == 0); assert(bbsnd(1) == 1);
      assert(bbfst(2) == 1); assert(bbsnd(2) == 0);
      assert(bbfst(3) == 1); assert(bbsnd(3) == 1);
    |}

let test_auto_ind_type_with_arg (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^
    {|
      CodeGen Primitive pair bool bool => "pair".
      CodeGen Snippet "
      typedef int prod_bool_bool;
      #define pair(a,b) (((a) << 1) | (b))
      #define pair_get_member_0(x) ((x) >> 1)
      #define pair_get_member_1(x) ((x) & 1)
      ".
      Definition mypair (x y : bool) : bool*bool := (x, y).
      CodeGen Func mypair.
    |}) {|
      assert(mypair(false, false) == 0);
      assert(mypair(false, true) == 1);
      assert(mypair(true, false) == 2);
      assert(mypair(true, true) == 3);
    |}

let test_auto_ind_match_cstrlabel_with_arg (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^
    {|
      CodeGen Snippet "
      typedef int option_bool;
      enum option_bool_tag { None_bool_tag, Some_bool_tag };
      #define sw_option_bool(x) ((enum option_bool_tag)((x) & 1))
      #define Some_bool_get_member_0(x) ((bool)((x) >> 1))
      ".
      Definition value_of_optionbool (default : bool) (x : option bool) :=
        match x with
        | Some x => x
        | None => default
        end.
      CodeGen Func value_of_optionbool.
    |}) {|
      assert(value_of_optionbool(true, 0) == true);
      assert(value_of_optionbool(true, 1) == false);
      assert(value_of_optionbool(true, 3) == true);
      assert(value_of_optionbool(false, 0) == false);
      assert(value_of_optionbool(false, 1) == false);
      assert(value_of_optionbool(false, 3) == true);
    |}

let test_auto_ind_match_cstrmember_with_arg (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      CodeGen Snippet "
      typedef int prod_bool_bool;
      #define bpair(a,b) (((a) << 1) | (b))
      enum { pair_bool_bool_tag };
      #define sw_prod_bool_bool(x) pair_bool_bool_tag
      #define pair_bool_bool_get_member_0(x) ((x) >> 1)
      #define pair_bool_bool_get_member_1(x) ((x) & 1)
      ".
      Definition bbfst (x : bool*bool) := match x with (a,b) => a end.
      Definition bbsnd (x : bool*bool) := match x with (a,b) => b end.
      CodeGen Func bbfst.
      CodeGen Func bbsnd.
    |}) {|
      assert(bbfst(0) == 0); assert(bbsnd(0) == 0);
      assert(bbfst(1) == 0); assert(bbsnd(1) == 1);
      assert(bbfst(2) == 1); assert(bbsnd(2) == 0);
      assert(bbfst(3) == 1); assert(bbsnd(3) == 1);
    |}

let test_auto_const (ctx : test_ctxt) : unit =
  codegen_test_template
    ~resolve_dependencies:false
    ctx
    (nat_src ^ {|
      CodeGen Snippet "#define one() 1".
      Definition one := 1.
      Definition add1 x := x + one.
      CodeGen Func add1.
    |}) {|
      assert(add1(0) == 1);
      assert(add1(1) == 2);
      assert(add1(2) == 3);
    |}

let test_auto_construct (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    ({|
      CodeGen Snippet "
      typedef int nat;
      #define O() 0
      #define S(x) ((x)+1)
      ".
      Definition one := 1.
      CodeGen Func one.
    |}) {|
      assert(one() == 1);
    |}

let test_auto_nat_fold (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ {|
      Definition nat_fold (A : Type) (f : A -> nat -> A) :=
        fix nat_fold (n : nat) (a0 : A) : A :=
          match n with
          | O => a0
          | S m => nat_fold m (f a0 m)
          end.
      Definition sum_plus_one (n : nat) : nat :=
        S (nat_fold nat Nat.add n 0).
      CodeGen AutoArgs nat_fold.
      CodeGen Func nat_fold nat => "nat_fold".
      CodeGen Func sum_plus_one.
    |}) {|
      assert(sum_plus_one(3) == 4);
    |}

let test_option_bool_struct (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^
    {|
      CodeGen InductiveType option bool => "option_bool".
      CodeGen InductiveMatch option bool => "sw_option_bool"
      | None => "default"
      | Some => "case option_bool_Some" "option_bool_Some_member1".
      CodeGen Primitive None bool => "None_bool".
      CodeGen Primitive Some bool => "Some_bool".
      CodeGen Snippet "
      enum enum_option_bool { option_bool_None, option_bool_Some };
      typedef struct {
        enum enum_option_bool tag;
        union {
          struct {
            bool member1;
          } Some;
        } as;
      } option_bool;
      #define None_bool() ((option_bool){ option_bool_None, })
      #define Some_bool(member1) ((option_bool){ option_bool_Some, { .Some = { member1 }}})
      #define sw_option_bool(x) ((x).tag)
      #define option_bool_Some_member1(x) ((x).as.Some.member1)
      ".
      Definition value_of_optionbool (default : bool) (x : option bool) :=
        match x with
        | Some x => x
        | None => default
        end.
      CodeGen Func value_of_optionbool.
    |}) {|
      assert(value_of_optionbool(true, None_bool()) == true);
      assert(value_of_optionbool(true, Some_bool(false)) == false);
      assert(value_of_optionbool(true, Some_bool(true)) == true);
      assert(value_of_optionbool(false, None_bool()) == false);
      assert(value_of_optionbool(false, Some_bool(false)) == false);
      assert(value_of_optionbool(false, Some_bool(true)) == true);
    |}

let test_reduceeta_makes_single_function (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    ~generated_code_regexp_not:(Str.regexp "^codegen_functions_mycat_bool")
    (bool_src ^ list_bool_src ^
    {|
      Definition mycat {T : Type} :=
        fix mycat (s1 s2 : list T) : list T :=
          match s1 with
          | nil => s2
          | cons x s => cons x (mycat s s2)
          end.
      CodeGen Func mycat bool => "mycat_bool".
    |}) {|
      #define cons(h,t) list_bool_cons(h,t)
      list_bool s1 = cons(true,(cons(false,NULL)));
      list_bool s2 = cons(false,(cons(true,NULL)));
      list_bool s3 = cons(true,(cons(false,cons(false,(cons(true,NULL))))));
      assert(list_bool_eq(s3, mycat_bool(s1,s2)));
    |}

let test_multiple_primitives_shares_cfunc (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^
    {|
      Fixpoint myadd (m n : nat) :=
        match n with
        | O => m
        | S n' => myadd (S m) n'
        end.
      Definition f a b := a + b.
      Definition g a b := myadd a b.
      (* CodeGen Primitive Nat.add => "nat_add". *) (* nat_src contains this *)
      CodeGen Primitive myadd => "nat_add".
      CodeGen Func f.
      CodeGen Func g.
    |}) {|
      assert(f(2,3) == 5);
      assert(g(2,3) == 5);
    |}

let test_indimp_bool (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Inductive yesno : Set := yes : yesno | no : yesno.
      Definition yesno_of_bool (b : bool) : yesno :=
        match b with
        | true => yes
        | false => no
        end.
      Definition bool_of_yesno (y : yesno) : bool :=
        match y with
        | yes => true
        | no => false
        end.
      Definition id_bool (b : bool) : bool :=
        bool_of_yesno (yesno_of_bool b).
      CodeGen IndImp yesno.
      CodeGen Func yesno_of_bool.
      CodeGen Func bool_of_yesno.
      CodeGen Func id_bool.
    |}) {|
      assert(id_bool(true) == true);
      assert(id_bool(false) == false);
    |}

let test_indimp_bool_pair (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Inductive yn : Set := yes : yn | no : yn.
      Inductive ynpair : Set := yn2 : bool -> bool -> ynpair.
      Definition ynpair_of_boolpair (bb : bool * bool) : ynpair :=
        match bb with
        | (true, true) => yn2 true true
        | (true, false) => yn2 true false
        | (false, true) => yn2 false true
        | (false, false) => yn2 false false
        end.
      Definition boolpair_of_ynpair (yy : ynpair) : bool * bool :=
        match yy with
        | yn2 true true => (true, true)
        | yn2 true false => (true, false)
        | yn2 false true => (false, true)
        | yn2 false false => (false, false)
        end.
      Definition id_boolpair (bb : bool * bool) : bool * bool :=
        boolpair_of_ynpair (ynpair_of_boolpair bb).
      CodeGen InductiveType bool*bool => "prod_bool_bool".
      CodeGen InductiveMatch bool*bool => ""
      | pair => "" "pair_bool_bool_fst" "pair_bool_bool_snd".
      CodeGen Primitive pair bool bool => "pair_bool_bool".
      CodeGen Snippet "
      typedef int prod_bool_bool;
      #define pair_bool_bool(a,b) (((a) << 1) | (b))
      #define pair_bool_bool_fst(x) ((x) >> 1)
      #define pair_bool_bool_snd(x) ((x) & 1)
      ".
      CodeGen IndImp yn.
      CodeGen IndImp ynpair.
      CodeGen Func ynpair_of_boolpair.
      CodeGen Func boolpair_of_ynpair.
      CodeGen Func id_boolpair.
    |}) {|
      assert(id_boolpair(0) == 0);
      assert(id_boolpair(1) == 1);
      assert(id_boolpair(2) == 2);
      assert(id_boolpair(3) == 3);
    |}

let test_indimp_parametric_pair (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Inductive yn : Set := yes : yn | no : yn.
      Inductive ynpair (A B : Set) : Set := yn2 : A -> B -> ynpair A B.
      Definition ynpair_of_boolpair (bb : bool * bool) : ynpair bool bool :=
        match bb with
        | (true, true) => yn2 bool bool true true
        | (true, false) => yn2 bool bool true false
        | (false, true) => yn2 bool bool false true
        | (false, false) => yn2 bool bool false false
        end.
      Definition boolpair_of_ynpair (yy : ynpair bool bool) : bool * bool :=
        match yy with
        | yn2 _ _ true true => (true, true)
        | yn2 _ _ true false => (true, false)
        | yn2 _ _ false true => (false, true)
        | yn2 _ _ false false => (false, false)
        end.
      Definition id_boolpair (bb : bool * bool) : bool * bool :=
        boolpair_of_ynpair (ynpair_of_boolpair bb).
      CodeGen InductiveType bool*bool => "prod_bool_bool".
      CodeGen InductiveMatch bool*bool => ""
      | pair => "" "pair_bool_bool_fst" "pair_bool_bool_snd".
      CodeGen Primitive pair bool bool => "pair_bool_bool".
      CodeGen Snippet "
      typedef int prod_bool_bool;
      #define pair_bool_bool(a,b) (((a) << 1) | (b))
      #define pair_bool_bool_fst(x) ((x) >> 1)
      #define pair_bool_bool_snd(x) ((x) & 1)
      ".
      CodeGen IndImp yn.
      CodeGen IndImp (ynpair bool bool).
      CodeGen Func ynpair_of_boolpair.
      CodeGen Func boolpair_of_ynpair.
      CodeGen Func id_boolpair.
    |}) {|
      assert(id_boolpair(0) == 0);
      assert(id_boolpair(1) == 1);
      assert(id_boolpair(2) == 2);
      assert(id_boolpair(3) == 3);
    |}

let test_indimp_option_bool (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Inductive myoption (T : Type) : Type := MySome : T -> myoption T | MyNone : myoption T.
      Definition myopt_of_opt (ob : option bool) : myoption bool :=
        match ob with
        | Some true => MySome bool true
        | Some false => MySome bool false
        | None => MyNone bool
        end.
      Definition opt_of_myopt (mb : myoption bool) : option bool :=
        match mb with
        | MySome _ true => Some true
        | MySome _ false => Some false
        | MyNone _ => None
        end.
      Definition id_option_bool (ob : option bool) : option bool :=
        opt_of_myopt (myopt_of_opt ob).
      CodeGen InductiveType option bool => "option_bool".
      CodeGen InductiveMatch option bool => "sw_option_bool"
      | Some => "default" "option_bool_get_some"
      | None => "case 0".
      CodeGen Primitive Some bool => "some_bool".
      CodeGen Constant None bool => "none_bool".
      CodeGen Snippet "
      typedef int option_bool;
      #define sw_option_bool(x) ((x) & 1)
      #define option_bool_get_some(x) ((bool)((x) >> 1))
      #define some_bool(x) (((x) << 1) | 1)
      #define none_bool 0
      ".
      CodeGen IndImp (myoption bool).
      CodeGen Func myopt_of_opt.
      CodeGen Func opt_of_myopt.
      CodeGen Func id_option_bool.
    |}) {|
      assert(id_option_bool(0) == 0);
      assert(id_option_bool(1) == 1);
      assert(id_option_bool(3) == 3);
    |}

let test_indimp_record (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Record bool2 : Set := mkbool2 { bool2_x : bool; bool2_y : bool }.
      Definition bool2_of_boolpair (bb : bool * bool) : bool2 :=
        match bb with
        | (true, true) => mkbool2 true true
        | (true, false) => mkbool2 true false
        | (false, true) => mkbool2 false true
        | (false, false) => mkbool2 false false
        end.
      Definition boolpair_of_bool2 (b2 : bool2) : bool * bool :=
        match b2 with
        | mkbool2 true true => (true, true)
        | mkbool2 true false => (true, false)
        | mkbool2 false true => (false, true)
        | mkbool2 false false => (false, false)
        end.
      Definition id_boolpair (bb : bool * bool) : bool * bool :=
        boolpair_of_bool2 (bool2_of_boolpair bb).
      CodeGen InductiveType bool*bool => "prod_bool_bool".
      CodeGen InductiveMatch bool*bool => ""
      | pair => "" "pair_bool_bool_fst" "pair_bool_bool_snd".
      CodeGen Primitive pair bool bool => "pair_bool_bool".
      CodeGen Snippet "
      typedef int prod_bool_bool;
      #define pair_bool_bool(a,b) (((a) << 1) | (b))
      #define pair_bool_bool_fst(x) ((x) >> 1)
      #define pair_bool_bool_snd(x) ((x) & 1)
      ".
      CodeGen IndImp bool2.
      CodeGen Func bool2_of_boolpair.
      CodeGen Func boolpair_of_bool2.
      CodeGen Func id_boolpair.
    |}) {|
      assert(id_boolpair(0) == 0);
      assert(id_boolpair(1) == 1);
      assert(id_boolpair(2) == 2);
      assert(id_boolpair(3) == 3);
    |}

let test_indimp_nat (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ {|
      Inductive mynat : Set := myO : mynat | myS : mynat -> mynat.
      Fixpoint mynat_of_nat (n : nat) : mynat :=
        match n with
        | O => myO
        | S m => myS (mynat_of_nat m)
        end.
      Fixpoint nat_of_mynat (n : mynat) : nat :=
        match n with
        | myO => O
        | myS m => S (nat_of_mynat m)
        end.
      Definition id_nat n := nat_of_mynat (mynat_of_nat n).
      CodeGen IndImp mynat.
      CodeGen Func mynat_of_nat.
      CodeGen Func nat_of_mynat.
      CodeGen Func id_nat.
    |}) {|
      assert(id_nat(0) == 0);
      assert(id_nat(1) == 1);
      assert(id_nat(2) == 2);
      assert(id_nat(3) == 3);
    |}

let test_indimp_mutual (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ list_bool_src ^
    {|
      Inductive even_list : Set :=
      | even_nil : even_list
      | even_cons : bool -> odd_list -> even_list
      with odd_list : Set :=
      | odd_cons : bool -> even_list -> odd_list.
      Fixpoint list_of_even_list (el : even_list) : list bool :=
        match el with
        | even_nil => nil
        | even_cons b ol => cons b (list_of_odd_list ol)
        end
      with list_of_odd_list (ol : odd_list) : list bool :=
        match ol with
        | odd_cons b el => cons b (list_of_even_list el)
        end.
      Fixpoint even_list_of_list (l : list bool) : even_list :=
        match l with
        | nil => even_nil
        | cons b nil => even_cons b (odd_cons false even_nil)
        | cons b1 (cons b2 l2) => even_cons b1 (odd_cons b2 (even_list_of_list l2))
        end.
      Fixpoint odd_list_of_list (l : list bool) : odd_list :=
        match l with
        | nil => odd_cons false even_nil
        | cons b nil => odd_cons b even_nil
        | cons b1 (cons b2 l2) => odd_cons b1 (even_cons b2 (odd_list_of_list l2))
        end.
      Definition id_list_even (l : list bool) : list bool :=
        list_of_even_list (even_list_of_list l).
      Definition id_list_odd (l : list bool) : list bool :=
        list_of_odd_list (odd_list_of_list l).
      CodeGen IndImp even_list.
      CodeGen Func list_of_even_list.
      CodeGen Func list_of_odd_list.
      CodeGen Func even_list_of_list.
      CodeGen Func odd_list_of_list.
      CodeGen Func id_list_even.
      CodeGen Func id_list_odd.
    |}) {|
      #define cons(h,t) list_bool_cons(h,t)
      list_bool s = NULL;
      assert(list_bool_eq(s, id_list_even(s)));
      s = cons(false, s);
      assert(list_bool_eq(s, id_list_odd(s)));
      s = cons(true, s);
      assert(list_bool_eq(s, id_list_even(s)));
      s = cons(true, s);
      assert(list_bool_eq(s, id_list_odd(s)));
    |}

let test_header_snippet (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCC ctx
    {|
      CodeGen HeaderFile "foo.h".
      CodeGen HeaderSnippet "static void foo(void) {}".
      CodeGen Snippet "#include ""foo.h""".
    |} {|
      foo();
    |}

let test_prototype (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCC ctx
    (* If the prototype for id_bool is not generated, id_bool is implicitly declared as int id_bool() in f.
       It conflicts with the actual definition: bool id_bool(bool v1_x).
       The conflicts causes an error in C compilation.
       So, this test examines that the prototype declaration exists. *)
    (bool_src ^
    {|
      CodeGen HeaderFile "foo.h".
      CodeGen Snippet "#include ""foo.h""".
      CodeGen Snippet "void f(void) { id_bool(true); }".
      CodeGen Func id bool => "id_bool".
    |}) {|
    |}

let test_monocheck_failure (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] monomorphism check failed: let-in type must be monomorphic:") ctx
    ({|
      Definition f (z : Empty_set) (n : nat) : nat :=
        let T : Type := match z with end in
        (fix h (T : Type) (n : nat) := n) T n.
      CodeGen Func f.
    |}) {| |}

let boolbox_src = {|
      Inductive boolbox : Set := BoolBox : bool -> boolbox.
      Definition boolbox_dealloc (x : boolbox) : unit := tt.
      CodeGen Linear boolbox.
      CodeGen InductiveType boolbox => "boolbox".
      CodeGen InductiveMatch boolbox => ""
      | BoolBox => "" "boolbox_get".
      CodeGen Deallocator boolbox => "boolbox_dealloc".
      CodeGen Primitive BoolBox => "boolbox_alloc".
      CodeGen Primitive boolbox_dealloc => "boolbox_dealloc".

      CodeGen Snippet "
      typedef bool *boolbox;

      static char boolbox_log_buffer[1000];
      static char *boolbox_log_next = boolbox_log_buffer;

      static inline boolbox boolbox_alloc(bool b) {
        *boolbox_log_next++ = 'a';
        boolbox ret = malloc(sizeof(bool));
        if (ret == NULL) abort();
        *ret = b;
        return ret;
      }

      static inline bool boolbox_get(boolbox x) {
        *boolbox_log_next++ = 'g';
        return *x;
      }

      static inline void boolbox_dealloc(boolbox x) {
        *boolbox_log_next++ = 'd';
        free(x);
      }
      ".
|}

let test_linear_types (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ctx
    ({|
      Inductive L : Type := CL : L.
      Inductive M : Type := CM : L -> M.

      CodeGen Linear L.

      CodeGen TestUnrestrictedType Type.
      CodeGen TestUnrestrictedType nat -> nat.
      CodeGen TestUnrestrictedType nat.
      CodeGen TestUnrestrictedType list nat.

      CodeGen TestLinearType L.
      CodeGen TestLinearType M.
      CodeGen TestLinearType list L.
    |}) {| |}

let test_linear_novar (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] linear argument not consumed:") ctx
    (unit_src ^ bool_src ^ boolbox_src ^
    {|
      Definition f (x : boolbox) := tt.
      CodeGen Func f.
    |}) {| |}

let test_linear_twovar (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] linear variables used multiply in arguments:") ctx
    (unit_src ^ bool_src ^ boolbox_src ^
    {|
      Definition f (x : boolbox) := (x,x).
      CodeGen Func f.
    |}) {| |}

let test_linear_inconsistent_reference_in_match (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] match-branches uses linear variables inconsistently:") ctx
    (unit_src ^ bool_src ^ boolbox_src ^
    {|
      Definition f (x : boolbox) (b : bool) :=
        match b with
        | true => x
        | false => BoolBox true
        end.
      CodeGen Func f.
    |}) {| |}

let test_linear_reference_in_fix (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] linear argument outside of fix-term:") ctx
    (unit_src ^ bool_src ^ boolbox_src ^
    {|
      Definition f (x : boolbox) :=
        fix g (n : nat) := x.
      CodeGen Func f.
    |}) {| |}

let test_linear_dellet (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (unit_src ^ bool_src ^ boolbox_src ^
    {|
      Definition f (x : boolbox) :=
        let unused := boolbox_dealloc x in
        true.
      CodeGen Func f.
    |}) {|
      assert(f(boolbox_alloc(true)) == true);
      assert(boolbox_log_next - boolbox_log_buffer > 0);
      assert(boolbox_log_buffer[0] == 'a');
      assert(boolbox_log_next - boolbox_log_buffer > 1);
      assert(boolbox_log_buffer[1] == 'd');
      assert(boolbox_log_next - boolbox_log_buffer == 2);
    |}

let test_linear_dellet_match (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (unit_src ^ bool_src ^ boolbox_src ^
    {|
      Definition f (x : boolbox) (u : unit) :=
        let unused := match u with tt => boolbox_dealloc x end in
        true.
      CodeGen Func f.
    |}) {|
      assert(f(boolbox_alloc(true)) == true);
      assert(boolbox_log_next - boolbox_log_buffer > 0);
      assert(boolbox_log_buffer[0] == 'a');
      assert(boolbox_log_next - boolbox_log_buffer > 1);
      assert(boolbox_log_buffer[1] == 'd');
      assert(boolbox_log_next - boolbox_log_buffer == 2);
    |}

let test_linear_match_with_deallocator (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (unit_src ^ bool_src ^ boolbox_src ^
    {|
      Definition f (x : boolbox) : bool :=
        match x with
        | BoolBox b => b
        end.
      CodeGen Func f.
    |}) {|
      assert(f(boolbox_alloc(true)) == true);
      assert(f(boolbox_alloc(false)) == false);
      assert(boolbox_log_next - boolbox_log_buffer > 0); assert(boolbox_log_buffer[0] == 'a');
      assert(boolbox_log_next - boolbox_log_buffer > 1); assert(boolbox_log_buffer[1] == 'g');
      assert(boolbox_log_next - boolbox_log_buffer > 2); assert(boolbox_log_buffer[2] == 'd');
      assert(boolbox_log_next - boolbox_log_buffer > 3); assert(boolbox_log_buffer[3] == 'a');
      assert(boolbox_log_next - boolbox_log_buffer > 4); assert(boolbox_log_buffer[4] == 'g');
      assert(boolbox_log_next - boolbox_log_buffer > 5); assert(boolbox_log_buffer[5] == 'd');
      assert(boolbox_log_next - boolbox_log_buffer == 6);
    |}

let test_linear_match_without_deallocator (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (unit_src ^ bool_src ^ boolbox_src ^
    {|
      CodeGen InductiveType boolbox*boolbox => "pair_boolbox_boolbox".
      CodeGen InductiveMatch boolbox*boolbox => ""
      | pair => "" "pair_boolbox_boolbox_fst" "pair_boolbox_boolbox_snd".
      CodeGen Primitive pair boolbox boolbox => "make_pair_boolbox_boolbox".
      CodeGen Snippet "
      typedef struct {
        boolbox fst;
        boolbox snd;
      } pair_boolbox_boolbox;
      #define make_pair_boolbox_boolbox(fst, snd) ((pair_boolbox_boolbox){ (fst), (snd) })
      #define pair_boolbox_boolbox_fst(x) ((x).fst)
      #define pair_boolbox_boolbox_snd(x) ((x).snd)
      ".
      Definition f (xy : boolbox*boolbox) : bool :=
        match xy with
        | pair (BoolBox x) (BoolBox y) => x
        end.
      CodeGen Func f.
    |})
    {|
      pair_boolbox_boolbox p = make_pair_boolbox_boolbox(boolbox_alloc(true), boolbox_alloc(false));
      assert(boolbox_log_next - boolbox_log_buffer == 2);
      assert(boolbox_log_buffer[0] == 'a');
      assert(boolbox_log_buffer[1] == 'a');
      assert(f(p) == true);
      assert(boolbox_log_next - boolbox_log_buffer == 5);
      assert(boolbox_log_buffer[2] == 'g');
      assert(boolbox_log_buffer[3] == 'd');
      assert(boolbox_log_buffer[4] == 'd');
    |}

let test_downward_simple (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] function returns downward value:") ctx
    (bool_src ^
    {|
      Inductive D : Set := C.
      Definition f (x : bool) : D := C.
      CodeGen Downward D.
      CodeGen Func f.
    |}) {| |}

let test_downward_in_pair (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] function returns downward value:") ctx
    (bool_src ^
    {|
      Inductive D : Set := C.
      Definition f (x : bool) : (bool * D) := (x, C).
      CodeGen Downward D.
      CodeGen Func f.
    |}) {| |}

let test_downward_fixfunc (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] fixpoint function returns downward value:") ctx
    ({|
      Inductive D : Set := C0 : D | C1 : D -> D.
      Definition f (n : nat) : nat :=
	let d :=
	  (fix g (m : nat) : D :=
	    match m with
	    | O => C0
	    | S m' => C1 (g m')
	    end) n
	in
	match d with
	| C0 => 0
	| C1 _ => 1
	end.
      CodeGen Downward D.
      CodeGen Func f.
    |}) {| |}

let test_downward_indirect_cycle (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Inductive T := C1 : T | C2 : (T*T) -> T.
      Definition f (x : T)  := x.
      CodeGen Snippet "
        typedef struct T_struct *T;
        typedef struct prod_T_T_struct {
          T member1;
          T member2;
        } prod_T_T;
        struct T_struct { prod_T_T member; };
        #define C1() NULL
        static inline T C2(prod_T_T arg) {
          T ret;
          if ((ret = malloc(sizeof(*ret))) == NULL) abort();
          ret->member = arg;
          return ret;
        }
        static inline prod_T_T pair_T_T(T arg1, T arg2) {
          return (struct prod_T_T_struct){ arg1, arg2 };
        }
      ".
      CodeGen InductiveType T => "T".
      CodeGen Func f.
    |}) {|
      T x1 = C1();
      T x2 = C2(pair_T_T(C1(),C1()));
      assert(f(x1) == x1);
      assert(f(x2) == x2);
    |}

let test_borrowcheck_constructor (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ctx
    ({|
      CodeGen TestBorrowCheck fun (x : nat) => 0.
    |}) {| |}

let test_borrowcheck_constant (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ctx
    ({|
      Definition c := 0.
      CodeGen TestBorrowCheck fun (n : nat) => c.
    |}) {| |}

let test_borrowcheck_linear_id (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ctx
    ({|
      Inductive L : Set := LC.
      CodeGen Linear L.
      CodeGen TestBorrowCheck fun (x : L) => x.
    |}) {| |}

let test_borrowcheck_invalid_linearity_linear_arg_out_of_fix (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] linear argument outside of fix-term:") ctx
    ({|
      Inductive L : Set := LC.
      CodeGen Linear L.
      CodeGen TestBorrowCheck
	fun (x : L) =>
        fix f (n : nat) := match n with O => O | S m => let x := f m in S x end.
    |}) {| |}

let test_borrowcheck_invalid_linearity_lambda (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] linear argument not consumed:") ctx
    ({|
      Inductive L : Set := LC.
      CodeGen Linear L.
      CodeGen TestBorrowCheck
	fun (x : L) =>
	0.
    |}) {| |}

let test_borrowcheck_invalid_linearity_free_linear_var_in_lambda (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] function cannot refer free linear variables:") ctx
    ({|
      Inductive L : Set := LC.
      CodeGen Linear L.
      CodeGen TestBorrowCheck
	fun (u : unit) (x : L) =>
	  let f := fun (u : unit) => x in
	  f u.
    |}) {| |}

let test_borrowcheck_invalid_linearity_letin (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] linear variable not consumed:") ctx
    ({|
      Inductive L : Set := LC.
      CodeGen Linear L.
      CodeGen TestBorrowCheck
	fun (u : unit) =>
	let x := LC in
	0.
    |}) {| |}

let test_borrowcheck_invalid_linearity_dealloc_twice (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] linear variables consumed multiply:") ctx
    ({|
      Inductive L : Set := LC.
      Definition dealloc (x : L) : unit := tt.
      CodeGen Linear L.
      CodeGen TestBorrowCheck
	fun (x : L) =>
	let y := dealloc x in
	let z := dealloc x in
	0.
    |}) {| |}

let test_borrowcheck_invalid_linearity_arguments (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] linear variables used multiply in arguments:") ctx
    ({|
      Inductive L : Set := LC.
      Definition twoarg (x y : L) : nat := 0.
      CodeGen Linear L.
      CodeGen TestBorrowCheck
	fun (x : L) => twoarg x x.
    |}) {| |}

let test_borrowcheck_invalid_linearity_match_item (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] linear match-item is used in match-branch:") ctx
    ({|
      Inductive L : Set := LC.
      CodeGen Linear L.
      CodeGen TestBorrowCheck
	fun (x : L) =>
	match x with
	| LC => x
	end.
    |}) {| |}

let test_borrowcheck_invalid_linearity_match_branches (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] match-branches uses linear variables inconsistently:") ctx
    ({|
      Inductive L : Set := LC.
      CodeGen Linear L.
      CodeGen TestBorrowCheck
	fun (b : bool) (x : L) =>
	match b with
	| true => x
	| false => LC
	end.
    |}) {| |}

let test_borrowcheck_invalid_linearity_match_member (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] linear member not consumed:") ctx
    ({|
      Inductive lseq (A : Type) : Type :=
      | lnil : lseq A
      | lcons : A -> lseq A -> lseq A.
      Arguments lnil {_}.
      Arguments lcons {_} _ _.
      CodeGen Linear lseq bool.
      CodeGen TestBorrowCheck
	fun (x : lseq bool) =>
	match x with
	| lnil => 0
	| lcons v y => 0
	end.
    |}) {| |}

let test_borrowcheck_indirect_cycle (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_src ^ {|
      Inductive L := LC1 : L | LC2 : (L*L) -> L.
      Inductive B := BC1 : B | BC2 : (B*B) -> B.
      Fixpoint borrow (l : L) : B :=
        match l with
        | LC1 => BC1
        | LC2 (x,y) => BC2 (borrow x, borrow y)
        end.
      Definition f (b : B) : bool :=
        match b with
        | BC1 => true
        | BC2 _ => false
        end.
      CodeGen BorrowFunc borrow.
      CodeGen Snippet "
        typedef struct L_struct *L;
        typedef struct prod_L_L_struct {
          L member1;
          L member2;
        } prod_L_L;
        struct L_struct { prod_L_L member; };
        #define LC1() NULL
        static inline L LC2(prod_L_L arg) {
          L ret;
          if ((ret = malloc(sizeof(*ret))) == NULL) abort();
          ret->member = arg;
          return ret;
        }
        static inline prod_L_L pair_L_L(L arg1, L arg2) {
          return (struct prod_L_L_struct){ arg1, arg2 };
        }
        #define sw_L(l) ((l) == NULL)
        #define LC2_tag 0
      ".
      CodeGen InductiveType L => "L".
      CodeGen InductiveMatch L => "sw_L" | LC1 => "default" | LC2 => "case 0" "L_member".
      CodeGen InductiveType B => "L".
      CodeGen InductiveMatch B => "sw_L" | BC1 => "default" | BC2 => "case 0" "L_member".
      CodeGen Func f.
    |}) {|
      assert(f(LC1()) == true);
      assert(f(LC2(pair_L_L(LC1(),LC1()))) == false);
    |}

let test_borrowcheck_simple_borrow (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ctx
    ({|
      Inductive L : Set := LC.
      Inductive B : Set := BC.
      Definition dealloc (x : L) : unit := tt.
      Definition borrow (x : L) : B := BC.
      CodeGen BorrowFunc borrow.
      CodeGen TestBorrowCheck
        fun (x : L) =>
        let b := borrow x in
        let _ := dealloc x in
        0.
    |}) {| |}

let test_borrowcheck_proj (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ctx
    ({|
      Inductive L : Set := LC.
      Inductive B : Set := BC.
      Definition dealloc (x : L) : unit := tt.
      Definition borrow (x : L) : B := BC.
      Set Primitive Projections.
      Record TestRecord : Set := mk { f0 : B; f1 : nat }.
      CodeGen BorrowFunc borrow.
      CodeGen TestBorrowCheck
        fun (n : nat) (x : L) =>
        let b := borrow x in
        let d := mk b n in
        let e := f1 d in
        let _ := dealloc x in
        e.
    |}) {| |}

let test_borrowcheck_lambda_out_of_fix (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ctx
    ({|
      Inductive lseq (A : Type) : Type :=
      | lnil : lseq A
      | lcons : A -> lseq A -> lseq A.
      Arguments lnil {_}.
      Arguments lcons {_} _ _.
      CodeGen Linear lseq bool.
      CodeGen TestBorrowCheck
        fun (n : nat) =>
        fix f (l : lseq bool) :=
        match l with
        | lnil => n
        | lcons b l' => f l'
        end.
    |}) {| |}

let test_borrowcheck_lambda_closure (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] linear variable and its borrowed value are used inconsistently in let-in:") ctx
    ({|
      Inductive L : Set := LC.
      Inductive B : Set := BC.
      Definition dealloc (x : L) : unit := tt.
      Definition borrow (x : L) : B := BC.
      CodeGen BorrowFunc borrow.
      CodeGen TestBorrowCheck
        fun (n : nat) (x : L) =>
        let b := borrow x in
        let f := fun (m : nat) => b in
        let r := f n in
        let _ := dealloc x in
        r.
    |}) {| |}

let test_borrowcheck_fix_closure (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] linear variable and its borrowed value are used inconsistently in let-in:") ctx
    ({|
      Inductive L : Set := LC.
      Inductive B : Set := BC.
      Definition dealloc (x : L) : unit := tt.
      Definition borrow (x : L) : B := BC.
      CodeGen BorrowFunc borrow.
      CodeGen TestBorrowCheck
        fun (n : nat) (x : L) =>
        let b := borrow x in
        let f := fix g (m : nat) := match m with O => b | S m' => g m' end in
        let r := f n in
        let _ := dealloc x in
        r.
    |}) {| |}

let test_borrowcheck_invalid_borrow_used_after_dealloc (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] linear variable and its borrowed value are used inconsistently in let-in:") ctx
    ({|
      Inductive L : Set := LC.
      Inductive B : Set := BC.
      Definition dealloc (x : L) : unit := tt.
      Definition borrow (x : L) : B := BC.
      CodeGen BorrowFunc borrow.
      CodeGen TestBorrowCheck
        fun (x : L) =>
        let b := borrow x in
        let _ := dealloc x in
        b.
    |}) {| |}

let test_borrowcheck_invalid_borrow_application (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] linear variable and its borrowed value are used both in an application:") ctx
    ({|
      Inductive L : Set := LC.
      Inductive B : Set := BC.
      Definition dealloc (x : L) : unit := tt.
      Definition borrow (x : L) : B := BC.
      CodeGen BorrowFunc borrow.
      Definition g (x : L) (b : B) := tt.
      CodeGen TestBorrowCheck
	fun (x : L) =>
	  let b := borrow x in
	  g x b.
    |}) {| |}

let test_borrowcheck_invalid_borrow_match (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] linear variable and its borrowed value are used inconsistently in match:") ctx
    ({|
      Inductive L : Set := LC.
      Inductive B : Set := BC.
      Definition dealloc (x : L) : unit := tt.
      Definition borrow (x : L) : B := BC.
      CodeGen BorrowFunc borrow.
      CodeGen TestBorrowCheck
	fun (x : L) =>
	let b := borrow x in
	match x with
	| LC => b
	end.
    |}) {| |}

let test_borrowcheck_invalid_borrow_proj (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] linear variable and its borrowed value are used inconsistently in let-in:") ctx
    ({|
      Inductive L : Set := LC.
      Inductive B : Set := BC.
      Set Primitive Projections.
      Record TestRecord : Set := mk { f0 : B }.
      Definition dealloc (x : L) : unit := tt.
      Definition borrow (x : L) : B := BC.
      CodeGen BorrowFunc borrow.
      CodeGen TestBorrowCheck
        fun (n : nat) (x : L) =>
        let b := borrow x in
        let d := mk b in
        let e := f0 d in
        let _ := dealloc x in
        e.
    |}) {| |}

let test_borrowcheck_list_bool_has_true (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ctx
    ({|
      Inductive lseq (A : Type) : Type :=
      | lnil : lseq A
      | lcons : A -> lseq A -> lseq A.
      Arguments lnil {_}.
      Arguments lcons {_} _ _.
      Definition lcons_bool (b : bool) (l : lseq bool) := lcons b l.
      Fixpoint borrow_lseq_bool (l : lseq bool) : list bool :=
	match l with
	| lnil => nil
	| lcons x l' => cons x (borrow_lseq_bool l')
	end.
      Fixpoint dealloc_lseq_bool (l : lseq bool) : unit :=
	match l with
	| lnil => tt
	| lcons x l' => dealloc_lseq_bool l'
	end.
      CodeGen BorrowFunc borrow_lseq_bool.
      CodeGen TestBorrowCheck
	fun (l : lseq bool) =>
	let l' := borrow_lseq_bool l in
	let has_true :=
	  (fix loop (bs : list bool) : bool :=
	    match bs with
	    | nil => false
	    | cons b bs' => if b then true else loop bs'
	    end) l'
	in
	let _ := dealloc_lseq_bool l in
	has_true.
    |}) {| |}

let test_borrowcheck_invalid_borrow_in_match (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] linear variable and its borrowed value are used inconsistently in let-in:") ctx
    ({|
      Inductive L : Set := LC.
      Inductive B : Set := BC.
      Definition dealloc (x : L) : unit := tt.
      Definition borrow (x : L) : B := BC.
      CodeGen BorrowFunc borrow.
      CodeGen TestBorrowCheck
	fun (u : unit) (x : L) =>
	let b := match u with tt => borrow x end in
	let _ := dealloc x in
	b.
    |}) {| |}

let test_borrowcheck_invalid_borrow_mutual (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] linear variable and its borrowed value are used inconsistently in let-in:") ctx
    ({|
      (* This example is taken from Coq reference manual *)
      Inductive tree : Set :=
      | node : forest -> tree
      with forest : Set :=
      | emptyf : forest
      | consf : tree -> forest -> forest.
      Definition dealloc_tree (t : tree) : unit := tt.
      Inductive btree : Set :=
      | bnode : bforest -> btree
      with bforest : Set :=
      | bemptyf : bforest
      | bconsf : btree -> bforest -> bforest.
      Fixpoint borrow_tree t :=
        match t with
        | node f => bnode (borrow_forest f)
        end
      with borrow_forest f :=
        match f with
        | emptyf => bemptyf
        | consf t f => bconsf (borrow_tree t) (borrow_forest f)
        end.
      CodeGen BorrowFunc borrow_tree.
      CodeGen TestBorrowCheck
        fun (t : tree) =>
        let bt := borrow_tree t in
        match bt with
        | bnode bf => let _ := dealloc_tree t in bf
        end.
    |}) {| |}

let test_borrowcheck_borrow_constructor (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] constructor of borrow type used:") ctx
    ({|
      Inductive L : Set := LC.
      Inductive B : Set := BC.
      Definition dealloc (x : L) : unit := tt.
      Definition borrow (x : L) : B := BC.
      CodeGen BorrowFunc borrow.
      CodeGen TestBorrowCheck
	fun (n : nat) => BC.
    |}) {| |}

let test_borrowcheck_borrow_nested_match (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] linear variable and its borrowed value are used inconsistently in let-in:") ctx
    ({|
      Inductive L := LC.
      Inductive B := BC.
      Definition dealloc (l : L) : unit := match l with LC => tt end.
      Definition borrow (l : L) : B := BC.
      Inductive Box1 := box1 : B -> Box1.
      Inductive Box2 := box2 : Box1 -> Box2.
      Definition id_box2 (x : Box2) := x.
      Definition f (l : L) :=
        let b := borrow l in
        let b1 := box1 b in
        let b2 := box2 b1 in
        let b3 := id_box2 b2 in
        let b' := match b3 with
                  | box2 b4 =>
                      match b4 with
                      | box1 b5 => b5
                      end
                  end in
        let _ := dealloc l in
        b'.
      CodeGen BorrowFunc borrow.
      CodeGen Func f.
    |}) {| |}

let test_borrowcheck_borrow_and_linear (ctx : test_ctxt) : unit =
  codegen_test_template ~goal:UntilCoq ~coq_exit_code:(Unix.WEXITED 1)
    ~coq_output_regexp:(Str.regexp_string "[codegen] couldn't find borrow types from borrow function:") ctx
    ({|
      Definition borrow (n : nat) : nat := n.
      Fixpoint consume (n: nat) : unit :=
        match n with
        | O => tt
        | S m => consume m
        end.
      CodeGen Linear nat.
      CodeGen BorrowType nat.
      CodeGen BorrowFunc borrow.
      Definition f (n : nat) :=
        let m := borrow n in
        let _ := consume m in
        consume n.
      CodeGen Func f.
    |}) {| |}

let test_void_tail (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (unit_src ^ bool_src ^ {|
      CodeGen Snippet "void f(bool);".
      Definition f (b : bool) : unit := tt.
      CodeGen Func f.
    |})
    {| |}

let test_void_head (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (unit_src ^ bool_src ^ {|
      CodeGen Snippet "void f(bool);".
      Definition f (b : bool) : unit :=
	let x := tt in
	match b with
	| true => x
	| false => x
	end.
      CodeGen Func f.
    |})
    {| |}

let test_void_mutual (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (unit_src ^ bool_src ^ nat_src ^ {|
      CodeGen Snippet "void f(nat);".
      CodeGen Snippet "static nat constant_zero(void) { return 0; }".
      CodeGen Snippet "static void ignore_nat(nat v1_x) { return; }".
      Definition ignore_nat (x : nat) : unit := tt.
      Definition constant_zero (x : unit) : nat := 0.
      Fixpoint f (n : nat) : unit :=
        match n with
        | O => tt
        | S m => let x := g m in ignore_nat x
        end
      with g (n : nat) : nat :=
        match n with
        | O => 0
        | S m => let x := f m in constant_zero x
        end.
      CodeGen Primitive ignore_nat.
      CodeGen Primitive constant_zero.
      CodeGen Func f.
    |})
    {| |}

let test_void_empty_args (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (unit_src ^ nat_src ^ {|
      Definition f (u : unit) : nat :=
        let z := O in
        let n := match u with
                 | tt => z
                 end
        in
        (fix g (n : nat) : nat :=
          match n with
          | O => O
          | S m => S (g m)
          end) n.
      CodeGen Func f.
    |})
    {|
      assert(f() == 0);
    |}

let test_void_head_tt_var (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (unit_src ^ bool_src ^ nat_src ^ {|
      CodeGen Snippet "nat f(bool);".
      Definition constant_zero (x : unit) : nat := 0.
      Definition f (b : bool) (u0 : unit) : nat :=
        let u :=
          match b with
          | true => tt (* We don't define tt in C but tt is usable because codegen omit void constructor *)
          | false => u0 (* void variable reference is also omitted *)
          end
        in
        constant_zero u.
      CodeGen Func f.
    |})
    {| |}

let test_void_tail_tt_var (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (unit_src ^ bool_src ^ nat_src ^ {|
      CodeGen Snippet "void f(bool);".
      Definition f (b : bool) (u0 : unit) : unit :=
        match b with
        | true => tt (* We don't define tt in C but tt is usable because codegen omit void constructor *)
        | false => u0 (* void variable reference is also omitted *)
        end.
      CodeGen Func f.
    |})
    {| |}

let test_void_head_proj (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (unit_src ^ bool_src ^ nat_src ^ {|
      Set Primitive Projections.
      Record TestRecord : Set := mk { umem : unit; nmem : nat }.
      Definition constant_zero (x : unit) : nat := 0.
      Definition f (x : TestRecord) : nat :=
        let x := umem x in
        constant_zero x.
      CodeGen InductiveType TestRecord => "TestRecord".
      CodeGen InductiveMatch TestRecord => ""
      | mk => "" "TestRecord_umem" "TestRecord_nmem".
      CodeGen Linear TestRecord.
      CodeGen Deallocator TestRecord => "dealloc_TestRecord".
      CodeGen Snippet "typedef int TestRecord;".
      CodeGen Snippet "int dealloc_called = 0;".
      CodeGen Snippet "#define TestRecord_umem(x) (abort(x))".
      CodeGen Snippet "#define TestRecord_nmem(x) (x)".
      CodeGen Snippet "#define dealloc_TestRecord(x) ((void)(dealloc_called++))".
      CodeGen Snippet "static nat constant_zero(void) { return 0; }".
      CodeGen Primitive constant_zero.
      CodeGen Func f.
    |})
    {|
      f(0);
      assert(dealloc_called == 1);
    |}

let test_void_tail_proj (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (unit_src ^ bool_src ^ nat_src ^ {|
      Set Primitive Projections.
      Record TestRecord : Set := mk { umem : unit; nmem : nat }.
      Definition f (x : TestRecord) : unit := umem x.
      CodeGen InductiveType TestRecord => "TestRecord".
      CodeGen InductiveMatch TestRecord => ""
      | mk => "" "TestRecord_umem" "TestRecord_nmem".
      CodeGen Linear TestRecord.
      CodeGen Deallocator TestRecord => "dealloc_TestRecord".
      CodeGen Snippet "typedef int TestRecord;".
      CodeGen Snippet "int dealloc_called = 0;".
      CodeGen Snippet "#define TestRecord_umem(x) (abort(x))".
      CodeGen Snippet "#define TestRecord_nmem(x) (x)".
      CodeGen Snippet "#define dealloc_TestRecord(x) ((void)(dealloc_called++))".
      CodeGen Func f.
    |})
    {|
      f(0);
      assert(dealloc_called == 1);
    |}

let test_inductivetype_twoarg_bool_paren (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (bool_paren_src ^ {|
      Definition f (b : bool) := b.
      CodeGen Func f.
    |}) {|
      assert(f(true) == true);
      assert(f(false) == false);
    |}

let test_closure_call_at_tail_position (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ {|
      Definition f (g : nat -> nat) x := g x.
      CodeGen Func f.
    |})
    ~main_toplevel_defs:{|
      struct closure_f_tag { uint64_t (*func)(uint64_t, void*); uint64_t m; };
      uint64_t g(uint64_t n, void *closure) {
        struct closure_f_tag *c = closure;
        return n + c->m + 100;
      }
    |}
    {|
      struct closure_f_tag c = { g, 20 };
      assert(f(&c.func, 3) == 123);
    |}

let test_closure_call_at_head_position (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ {|
      Definition f (g : nat -> nat) x := S (g x).
      CodeGen Func f.
    |})
    ~main_toplevel_defs:{|
      struct closure_f_tag { uint64_t (*func)(uint64_t, void*); uint64_t m; };
      uint64_t g(uint64_t n, void *closure) {
        struct closure_f_tag *c = closure;
        return n + c->m + 100;
      }
    |}
    {|
      struct closure_f_tag c = { g, 70 };
      assert(f(&c.func, 3) == 174);
    |}

let test_closure_generation_by_lambda (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ {|
      Definition call (f : nat -> nat -> nat) (x y : nat) : nat := f x y.
      Definition f a b c d :=
        let g x y := a * 5 + b * 4 + x * 3 + y * 2 + 1 in
        call g c d.
      CodeGen Func call.
      CodeGen Func f.
    |})
    {|
      assert(f(1,2,3,4) == 31);
      assert(f(4000,300,20,1) == 21263);
    |}

let test_closure_generation_by_fix_tailrec (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ {|
      Definition call (g : nat -> nat) (n : nat) : nat := g n.
      Definition f a b :=
        let g :=
          fix g n :=
            match n with
            | O => b
            | S m => g m
            end
        in
        call g a.
      CodeGen Func call.
      CodeGen Func f.
    |})
    {|
      assert(f(1,2) == 2);
    |}

let test_closure_generation_by_fix_nontailrec (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ {|
      Definition call (g : nat -> nat) (n : nat) : nat := g n.
      Definition f a b :=
        let g :=
          fix g n :=
            match n with
            | O => b
            | S m => S (g m)
            end
        in
        call g a.
      CodeGen Func call.
      CodeGen Func f.
    |})
    {|
      assert(f(1,2) == 3);
    |}

let test_closure_generation_by_fix_tailrec_multi (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ {|
      Definition call (g : nat -> nat) (n : nat) : nat := g n.
      Definition f a b :=
        let g :=
          fix g1 n :=
            match n with
            | O => b
            | S m => g2 m
            end
          with g2 n :=
            match n with
            | O => b
            | S m => g1 m
            end
          for g1
        in
        call g a.
      CodeGen Func call.
      CodeGen Func f.
    |})
    {|
      assert(f(1,2) == 2);
    |}

let test_closure_generation_by_fix_nontailrec_multi (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ {|
      Definition call (g : nat -> nat) (n : nat) : nat := g n.
      Definition f a b :=
        let g :=
          fix g1 n :=
            match n with
            | O => b
            | S m => S (g2 m)
            end
          with g2 n :=
            match n with
            | O => b
            | S m => S (g1 m)
            end
          for g1
        in
        call g a.
      CodeGen Func call.
      CodeGen Func f.
    |})
    {|
      assert(f(1,2) == 3);
    |}

(*
  The function body of g was generated twice.
  One for closure and one for recursion.
  The label entry_fixfunc2_h was generated twice which cause compilation error.
*)
let test_closure_generation_and_non_inlinable_fix_at_head_position (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ {|
      Definition call (g : nat -> nat) (n : nat) : nat := g n.
      Definition f a b :=
        let g :=
          fix g n :=
            match n with
            | O => (fix h p := match p with O => b | S p' => h p' end) b
            | S m => S (g m)
            end
        in
        call g a.
      CodeGen Func call.
      CodeGen Func f.
    |})
    {|
      assert(f(1,2) == 3);
    |}

let test_closure_argument_disables_tail_recursion_elimination (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ {|
      (* The invocation of g is tail recursion.
         But it cannot translate to goto because
         the stack-allocated closure, hh, is overwrtten.  *)
      Fixpoint g (n : nat) (h : nat -> nat) (acc : nat) :=
        match n with
        | O => acc
        | S m =>
            let hh x := n + x in
            g m hh (acc + h n)
        end.
      Definition f x :=
        g x (fun y => y + x) 0.
      CodeGen Func g.
      CodeGen Func f.
    |})
    {|
      assert(f(0) == 0);
      assert(f(1) == 2);
      assert(f(2) == 7);
      assert(f(3) == 14);
    |}

let test_closure_generated_from_fixfunc_argument (ctx : test_ctxt) : unit =
  codegen_test_template ctx
    (nat_src ^ {|
      Definition call (f : nat -> nat -> nat) (x y : nat) := f x y.
      Fixpoint add m n :=
        match m with
        | O => n
        | S m' => call add m' (S n)
        end.
      CodeGen Func call.
      CodeGen Func add.
    |})
    {|
      assert(add(1,2) == 3);
      assert(add(7,1) == 8);
    |}

let suite : OUnit2.test =
  "TestCodeGen" >::: [
    "test_command_gen_qualid" >:: test_command_gen_qualid;
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
    "test_even_odd_label_primary" >:: test_even_odd_label_primary;
    "test_even_odd_label_sibling" >:: test_even_odd_label_sibling;
    "test_even_odd_count" >:: test_even_odd_count;
    "test_inner_fix_even_odd_1" >:: test_inner_fix_even_odd_1;
    "test_inner_fix_even_odd_2" >:: test_inner_fix_even_odd_2;
    "test_two_even" >:: test_two_even;
    "test_two_even_two_odd" >:: test_two_even_two_odd;
    "test_app_let" >:: test_app_let;
    "test_app_match" >:: test_app_match;
    "test_let_app_match" >:: test_let_app_match;
    "test_cast" >:: test_cast;
    "test_beta_var_presimp" >:: test_beta_var_presimp;
    "test_matchapp_before_reduction" >:: test_matchapp_before_reduction;
    "test_delta_fun_constant" >:: test_delta_fun_constant;
    "test_delta_fun_constructor" >:: test_delta_fun_constructor;
    "test_delta_fun_lambda" >:: test_delta_fun_lambda;
    "test_delta_fun_nested_let" >:: test_delta_fun_nested_let;
    "test_reduce_proj" >:: test_reduce_proj;
    "test_nil_nat" >:: test_nil_nat;
    "test_singleton_list" >:: test_singleton_list;
    "test_deeply_nested_match" >:: test_deeply_nested_match;
    "test_let_add" >:: test_let_add;
    "test_let_match" >:: test_let_match;
    "test_let_match_let" >:: test_let_match_let;
    "test_let_match_let_nonempty_cargs" >:: test_let_match_let_nonempty_cargs;
    "test_let_unused_is_not_specialized" >:: test_let_unused_is_not_specialized;
    "test_let_only_used_in_static_is_not_specialized" >:: test_let_only_used_in_static_is_not_specialized;
    "test_add_tailrec" >:: test_add_tailrec;
    "test_add_nontailrec" >:: test_add_nontailrec;
    "test_map_succ" >:: test_map_succ;
    "test_tail_fix_double" >:: test_tail_fix_double;
    "test_nth" >:: test_nth;
    "test_rev_append" >:: test_rev_append;
    "test_merge" >:: test_merge;
    "test_merge_nontailrec" >:: test_merge_nontailrec;
    "test_ackermann" >:: test_ackermann;
    "test_ackermann_plus1" >:: test_ackermann_plus1;
    "test_uphalf" >:: test_uphalf;
    "test_sum_nested_fix" >:: test_sum_nested_fix;
    "test_add_at_non_tail_position1" >:: test_add_at_non_tail_position1;
    "test_add_at_non_tail_position" >:: test_add_at_non_tail_position;
    "test_fully_dynamic_func_with_presimp_name" >:: test_fully_dynamic_func_with_presimp_name;
    "test_specialized_func_with_presimp_name" >:: test_specialized_func_with_presimp_name;
    "test_specialization_at_get_ctnt_type_body_from_cfunc" >:: test_specialization_at_get_ctnt_type_body_from_cfunc;
    "test_letin_in_constructor_type" >:: test_letin_in_constructor_type;
    "test_arguments_contain_sort" >:: test_arguments_contain_sort;
    "test_arguments_contain_prod" >:: test_arguments_contain_prod;
    "test_arguments_contain_ind" >:: test_arguments_contain_ind;
    "test_mftest" >:: test_mftest;
    "test_multifunc_different_return_types" >:: test_multifunc_different_return_types;
    "test_multifunc_noargument" >:: test_multifunc_noargument;
    "test_mutual_sizet_sizef" >:: test_mutual_sizet_sizef;
    "test_mutual_sizet_sizef_dedup" >:: test_mutual_sizet_sizef_dedup;
    "test_mutual_sizet_sizef_nodedup" >:: test_mutual_sizet_sizef_nodedup;
    "test_mutual_static1" >:: test_mutual_static1;
    "test_mutual_static2" >:: test_mutual_static2;
    "test_mutual_fix_outer_noninlinable_fix_must_be_noninlinable" >:: test_mutual_fix_outer_noninlinable_fix_must_be_noninlinable;
    "test_nested_fix_must_have_consistent_arguments" >:: test_nested_fix_must_have_consistent_arguments;
    "test_nongoto_fixterm_at_nontail" >:: test_nongoto_fixterm_at_nontail;
    "test_nongoto_fixterm_in_gotoonly_fixterm_at_nontail" >:: test_nongoto_fixterm_in_gotoonly_fixterm_at_nontail;
    "test_useless_fixterm_at_nontail" >:: test_useless_fixterm_at_nontail;
    "test_extra_arguments" >:: test_extra_arguments;
    "test_extra_arguments_nested_exarg_used" >:: test_extra_arguments_nested_exarg_used;
    "test_extra_arguments_nested_exarg_unused" >:: test_extra_arguments_nested_exarg_unused;
    "test_unused_argument" >:: test_unused_argument;
    "test_inner_fixfunc_goto_exarg_fixfunc" >:: test_inner_fixfunc_goto_exarg_fixfunc;
    "test_parallel_assignment" >:: test_parallel_assignment;
    "test_unused_fixfunc_in_internal_fixterm" >:: test_unused_fixfunc_in_internal_fixterm;
    "test_unused_fixfunc_in_external_fixterm" >:: test_unused_fixfunc_in_external_fixterm;
    "test_primitive_projection" >:: test_primitive_projection;
    "test_primitive_projection_nontail" >:: test_primitive_projection_nontail;
    "test_matchapp_twoarg" >:: test_matchapp_twoarg;
    "test_matchapp_multiple_phases" >:: test_matchapp_multiple_phases;
    "test_matchapp_and_fix" >:: test_matchapp_and_fix;
    "test_auto_ind_type" >:: test_auto_ind_type;
    "test_auto_ind_match_cstrlabel" >:: test_auto_ind_match_cstrlabel;
    "test_auto_ind_match_cstrmember" >:: test_auto_ind_match_cstrmember;
    "test_auto_ind_type_with_arg" >:: test_auto_ind_type_with_arg;
    "test_auto_ind_match_cstrlabel_with_arg" >:: test_auto_ind_match_cstrlabel_with_arg;
    "test_auto_ind_match_cstrmember_with_arg" >:: test_auto_ind_match_cstrmember_with_arg;
    "test_auto_const" >:: test_auto_const;
    "test_auto_construct" >:: test_auto_construct;
    "test_auto_nat_fold" >:: test_auto_nat_fold;
    "test_option_bool_struct" >:: test_option_bool_struct;
    "test_reduceeta_makes_single_function" >:: test_reduceeta_makes_single_function;
    "test_multiple_primitives_shares_cfunc" >:: test_multiple_primitives_shares_cfunc;
    "test_indimp_bool" >:: test_indimp_bool;
    "test_indimp_bool_pair" >:: test_indimp_bool_pair;
    "test_indimp_parametric_pair" >:: test_indimp_parametric_pair;
    "test_indimp_option_bool" >:: test_indimp_option_bool;
    "test_indimp_record" >:: test_indimp_record;
    "test_indimp_nat" >:: test_indimp_nat;
    "test_indimp_mutual" >:: test_indimp_mutual;
    "test_header_snippet" >:: test_header_snippet;
    "test_prototype" >:: test_prototype;
    "test_monocheck_failure" >:: test_monocheck_failure;
    "test_linear_types" >:: test_linear_types;
    "test_linear_novar" >:: test_linear_novar;
    "test_linear_twovar" >:: test_linear_twovar;
    "test_linear_inconsistent_reference_in_match" >:: test_linear_inconsistent_reference_in_match;
    "test_linear_reference_in_fix" >:: test_linear_reference_in_fix;
    "test_linear_dellet" >:: test_linear_dellet;
    "test_linear_dellet_match" >:: test_linear_dellet_match;
    "test_linear_match_with_deallocator" >:: test_linear_match_with_deallocator;
    "test_linear_match_without_deallocator" >:: test_linear_match_without_deallocator;
    "test_downward_simple" >:: test_downward_simple;
    "test_downward_in_pair" >:: test_downward_in_pair;
    "test_downward_fixfunc" >:: test_downward_fixfunc;
    "test_downward_indirect_cycle" >:: test_downward_indirect_cycle;
    "test_borrowcheck_constructor" >:: test_borrowcheck_constructor;
    "test_borrowcheck_constant" >:: test_borrowcheck_constant;
    "test_borrowcheck_linear_id" >:: test_borrowcheck_linear_id;
    "test_borrowcheck_invalid_linearity_linear_arg_out_of_fix" >:: test_borrowcheck_invalid_linearity_linear_arg_out_of_fix;
    "test_borrowcheck_invalid_linearity_lambda" >:: test_borrowcheck_invalid_linearity_lambda;
    "test_borrowcheck_invalid_linearity_free_linear_var_in_lambda" >:: test_borrowcheck_invalid_linearity_free_linear_var_in_lambda;
    "test_borrowcheck_invalid_linearity_letin" >:: test_borrowcheck_invalid_linearity_letin;
    "test_borrowcheck_invalid_linearity_dealloc_twice" >:: test_borrowcheck_invalid_linearity_dealloc_twice;
    "test_borrowcheck_invalid_linearity_arguments" >:: test_borrowcheck_invalid_linearity_arguments;
    "test_borrowcheck_invalid_linearity_match_item" >:: test_borrowcheck_invalid_linearity_match_item;
    "test_borrowcheck_invalid_linearity_match_branches" >:: test_borrowcheck_invalid_linearity_match_branches;
    "test_borrowcheck_invalid_linearity_match_member" >:: test_borrowcheck_invalid_linearity_match_member;
    "test_borrowcheck_indirect_cycle" >:: test_borrowcheck_indirect_cycle;
    "test_borrowcheck_simple_borrow" >:: test_borrowcheck_simple_borrow;
    "test_borrowcheck_proj" >:: test_borrowcheck_proj;
    "test_borrowcheck_lambda_out_of_fix" >:: test_borrowcheck_lambda_out_of_fix;
    "test_borrowcheck_lambda_closure" >:: test_borrowcheck_lambda_closure;
    "test_borrowcheck_fix_closure" >:: test_borrowcheck_fix_closure;
    "test_borrowcheck_invalid_borrow_used_after_dealloc" >:: test_borrowcheck_invalid_borrow_used_after_dealloc;
    "test_borrowcheck_invalid_borrow_application" >:: test_borrowcheck_invalid_borrow_application;
    "test_borrowcheck_invalid_borrow_match" >:: test_borrowcheck_invalid_borrow_match;
    "test_borrowcheck_invalid_borrow_proj" >:: test_borrowcheck_invalid_borrow_proj;
    "test_borrowcheck_list_bool_has_true" >:: test_borrowcheck_list_bool_has_true;
    "test_borrowcheck_invalid_borrow_in_match" >:: test_borrowcheck_invalid_borrow_in_match;
    "test_borrowcheck_invalid_borrow_mutual" >:: test_borrowcheck_invalid_borrow_mutual;
    "test_borrowcheck_borrow_constructor" >:: test_borrowcheck_borrow_constructor;
    "test_borrowcheck_borrow_nested_match" >:: test_borrowcheck_borrow_nested_match;
    "test_borrowcheck_borrow_and_linear" >:: test_borrowcheck_borrow_and_linear;
    "test_void_tail" >:: test_void_tail;
    "test_void_head" >:: test_void_head;
    "test_void_mutual" >:: test_void_mutual;
    "test_void_empty_args" >:: test_void_empty_args;
    "test_void_head_tt_var" >:: test_void_head_tt_var;
    "test_void_tail_tt_var" >:: test_void_tail_tt_var;
    "test_void_head_proj" >:: test_void_head_proj;
    "test_void_tail_proj" >:: test_void_tail_proj;
    "test_inductivetype_twoarg_bool_paren" >:: test_inductivetype_twoarg_bool_paren;
    "test_closure_call_at_tail_position" >:: test_closure_call_at_tail_position;
    "test_closure_call_at_head_position" >:: test_closure_call_at_tail_position;
    "test_closure_generation_by_lambda" >:: test_closure_generation_by_lambda;
    "test_closure_generation_by_fix_tailrec" >:: test_closure_generation_by_fix_tailrec;
    "test_closure_generation_by_fix_nontailrec" >:: test_closure_generation_by_fix_nontailrec;
    "test_closure_generation_by_fix_tailrec_multi" >:: test_closure_generation_by_fix_tailrec_multi;
    "test_closure_generation_by_fix_nontailrec_multi" >:: test_closure_generation_by_fix_nontailrec_multi;
    "test_closure_generation_and_non_inlinable_fix_at_head_position" >:: test_closure_generation_and_non_inlinable_fix_at_head_position;
    "test_closure_argument_disables_tail_recursion_elimination" >:: test_closure_argument_disables_tail_recursion_elimination;
    "test_closure_generated_from_fixfunc_argument" >:: test_closure_generated_from_fixfunc_argument;
  ]

let () =
  run_test_tt_main suite
