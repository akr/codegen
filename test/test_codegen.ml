open OUnit

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
let quote_C_header str =
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

(* As far as the given file name is not modifiable and not movable
 * by other users,
 * like one created with make_temp_dir under /tmp which has sticky bit,
 * simple recursive deletion is safe.  *)
let remove_dir_rec (fn : string) : unit =
  let rec f fn =
    let s = Unix.lstat fn in
    if s.st_kind <> Unix.S_DIR then
      Unix.unlink fn
    else
      (let d = Unix.opendir fn in
      let rec g () =
        let n = Unix.readdir d in
        (if n <> "." && n <> ".." then
          f (fn ^ "/" ^ n));
        g ()
      in
      (try
        g ()
      with End_of_file ->
        ());
      Unix.rmdir fn)
  in
  Unix.handle_unix_error f fn

let try_finally f x g =
  let y =
    try
      f x
    with exn ->
      (g (); raise exn)
  in
  g ();
  y

let with_temp_dir prefix suffix body =
  let d = make_temp_dir prefix suffix in
  try_finally
    (fun () -> body d) ()
    (fun () -> remove_dir_rec d)

let with_temp_dir_noremove prefix suffix body =
  let d = make_temp_dir prefix suffix in
  body d

let write_file (fn : string) (content : string) : unit =
  let ch = open_out fn in
  output_string ch content;
  close_out ch

let search_topdir () : string =
  let rec f d =
    let fn = d ^ "/Makefile.coq.conf" in
    if Sys.file_exists fn then
      d
    else if d = "/" then
      failwith "Makefile.coq.conf not found"
    else
      f (Filename.dirname d)
  in
  f (Sys.getcwd ())

let test_mono_id_bool () =
  let topdir = search_topdir () in
  let coq_opts = ["-Q"; topdir ^ "/theories"; "codegen"; "-I"; topdir ^ "/src"] in
  with_temp_dir "codegen-test" "" (fun d ->
    let src_fn = d ^ "/src.v" in
    let gen_fn = d ^ "/gen.c" in
    let main_fn = d ^ "/main.c" in
    let exe_fn = d ^ "/exe" in
    write_file src_fn
      ("From codegen Require codegen.\n" ^
      "Definition mono_id_bool (b : bool) := b.\n" ^
      "CodeGen Instance mono_id_bool => " ^ (escape_coq_str "mono_id_bool") ^ ".\n" ^
      "CodeGen GenFile " ^ (escape_coq_str gen_fn) ^ " " ^ (escape_coq_str "mono_id_bool") ^ ".\n");
    write_file main_fn
      ("#include <stdlib.h>\n" ^
      "#include <stdbool.h>\n" ^
      "#include " ^ (quote_C_header gen_fn) ^ "\n" ^
      "int main(int argc, char *argv[]) {\n" ^
      "  if (mono_id_bool(true) != true) abort();\n" ^
      "  if (mono_id_bool(false) != false) abort();\n" ^
      "}\n");
    assert_command "coqc" (List.append coq_opts [src_fn]);
    assert_command "gcc" ["-o"; exe_fn; main_fn];
    assert_command exe_fn [])

let suite =
  "TestCodeGen" >::: [
    "test_mono_id_bool" >:: test_mono_id_bool
  ]

let () =
  ignore (run_test_tt_main suite)
