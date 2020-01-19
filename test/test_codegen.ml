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

let delete_indent (str : string) : string =
  let buf = Buffer.create (String.length str + 2) in
  let line_head = ref true in
  String.iter
    (fun ch ->
      match ch with
      | '\n' -> Buffer.add_char buf ch; line_head := true
      | ' ' | '\t' -> if not !line_head then Buffer.add_char buf ch
      | _ -> Buffer.add_char buf ch; line_head := false)
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
    (c_preamble : string)
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
    (delete_indent c_preamble ^ "\n" ^
    "#include <assert.h>\n" ^
    "#include " ^ (quote_C_header gen_fn) ^ "\n" ^
    "int main(int argc, char *argv[]) {\n" ^
    delete_indent c_body ^ "\n" ^
    "}\n");
  assert_command ctx coqc (List.append coq_opts [src_fn]);
  assert_command ctx cc ["-o"; exe_fn; main_fn];
  assert_command ctx exe_fn []

let test_mono_id_bool (ctx : test_ctxt) =
  codegen_test_template ctx
    {|
      Definition mono_id_bool (b : bool) := b.
      CodeGen Instance mono_id_bool => "mono_id_bool".
    |} {|
      #include <stdlib.h>
      #include <stdbool.h>
    |} {|
      assert(mono_id_bool(true) == true);
      assert(mono_id_bool(false) == false);
    |}

let test_mono_id_bool_omit_cfunc_name (ctx : test_ctxt) =
  codegen_test_template ctx
    {|
      Definition mono_id_bool (b : bool) := b.
      CodeGen Instance mono_id_bool.
    |} {|
      #include <stdlib.h>
      #include <stdbool.h>
    |} {|
      assert(mono_id_bool(true) == true);
      assert(mono_id_bool(false) == false);
    |}

let test_nat_add (ctx : test_ctxt) =
  codegen_test_template ctx
    {|
      CodeGen Inductive Type nat => "uint64_t".
      CodeGen Inductive Constructor nat
      | O => "0"
      | S => "succ".
      CodeGen Inductive Match nat => ""
      | O => "case 0"
      | S => "default" "pred".
      CodeGen Instance Nat.add.
    |} {|
      #include <stdlib.h>
      #include <stdint.h>
      #define succ(n) ((n)+1)
      #define pred(n) ((n)-1)
    |} {|
      assert(add(2,3) == 5);
    |}

let suite =
  "TestCodeGen" >::: [
    "test_mono_id_bool" >:: test_mono_id_bool;
    "test_mono_id_bool_omit_cfunc_name" >:: test_mono_id_bool_omit_cfunc_name;
    "test_nat_add" >:: test_nat_add;
  ]

let () =
  run_test_tt_main suite
