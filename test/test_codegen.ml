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

let concat_lines (lines : string list) : string =
  if lines = [] then
    ""
  else
    String.concat "\n" lines ^ "\n"

let codegen_test_template ?(dir : string option) (test_ctxt : test_ctxt)
    (coq_commands : string list)
    (c_preamble : string list)
    (c_body : string list) : unit =
  let d =
    match dir with
    | Some d -> Unix.mkdir d 0o700; d
    | None -> bracket_tmpdir ~prefix:"codegen-test" test_ctxt
  in
  let src_fn = d ^ "/src.v" in
  let gen_fn = d ^ "/gen.c" in
  let main_fn = d ^ "/main.c" in
  let exe_fn = d ^ "/exe" in
  write_file src_fn
    ("From codegen Require codegen.\n" ^
    concat_lines coq_commands ^
    "CodeGen EndFile " ^ (escape_coq_str gen_fn) ^ ".\n");
  write_file main_fn
    (concat_lines c_preamble ^
    "#include " ^ (quote_C_header gen_fn) ^ "\n" ^
    "int main(int argc, char *argv[]) {\n" ^
    concat_lines c_body ^
    "}\n");
  assert_command test_ctxt coqc (List.append coq_opts [src_fn]);
  assert_command test_ctxt cc ["-o"; exe_fn; main_fn];
  assert_command test_ctxt exe_fn []

let test_mono_id_bool (test_ctxt : test_ctxt) =
  codegen_test_template test_ctxt (* ~dir:"/tmp/debug" *)
    ["Definition mono_id_bool (b : bool) := b.";
     "CodeGen Instance mono_id_bool => \"mono_id_bool\".";]
    ["#include <stdlib.h>";
     "#include <stdbool.h>";]
    ["if (mono_id_bool(true) != true) abort();";
     "if (mono_id_bool(false) != false) abort();";]

let test_mono_id_bool_omit_cfunc_name (test_ctxt : test_ctxt) =
  codegen_test_template test_ctxt (* ~dir:"/tmp/debug" *)
    ["Definition mono_id_bool (b : bool) := b.";
     "CodeGen Instance mono_id_bool.";]
    ["#include <stdlib.h>";
     "#include <stdbool.h>";]
    ["if (mono_id_bool(true) != true) abort();";
     "if (mono_id_bool(false) != false) abort();";]

let suite =
  "TestCodeGen" >::: [
    "test_mono_id_bool" >:: test_mono_id_bool;
    "test_mono_id_bool_omit_cfunc_name" >:: test_mono_id_bool_omit_cfunc_name;
  ]

let () =
  run_test_tt_main suite
