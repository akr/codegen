(*
Copyright (C) 2016- National Institute of Advanced Industrial Science and Technology (AIST)

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 2.1 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
*)

open Names
open Pp
open CErrors
open Constr
open EConstr

open State

exception CodeGenError of string

let array_rev a =
  let n = Array.length a in
  Array.init n (fun i -> a.(n - i - 1))

let array_map2 f a1 a2 =
  if Array.length a1 <> Array.length a2 then
    invalid_arg "Array.map2: arrays must have the same length";
  Array.mapi (fun i -> f a1.(i)) a2

let array_map3 (f : 'a -> 'b -> 'c -> 'd) (a : 'a array) (b : 'b array) (c : 'c array) : 'd array =
  let n = Array.length a in
  if Array.length b <> n then raise (Invalid_argument "array_map3");
  if Array.length c <> n then raise (Invalid_argument "array_map3");
  Array.init n (fun i -> f a.(i) b.(i) c.(i))

let array_iter2 f a1 a2 =
  if Array.length a1 <> Array.length a2 then
    invalid_arg "Array.iter2: arrays must have the same length";
  Array.iteri (fun i -> f a1.(i)) a2

let array_iter3 f a1 a2 a3 =
  if Array.length a1 <> Array.length a2 || Array.length a1 <> Array.length a3 then
    invalid_arg "Array.iter3: arrays must have the same length";
  Array.iteri (fun i -> f a1.(i) a2.(i)) a3

let array_for_all f a =
  try Array.iter (fun x -> if f x then () else raise Exit) a; true
  with Exit -> false

let array_exists f a =
  try Array.iter (fun x -> if f x then raise Exit) a; false
  with Exit -> true

(* map from right to left *)
let array_map_right f a =
  let n = Array.length a in
  if n = 0 then
    [||]
  else
    let vlast = f a.(n-1) in
    let result = Array.make n vlast in
    for i = n-2 downto 0 do
      result.(i) <- f a.(i)
    done;
    result

let array_fold_right_map f a e =
  let eref = ref e in
  let a' = array_map_right
    (fun v -> let (v',e') = f v !eref in eref := e'; v')
    a
  in
  (a', !eref)

let array_find_index_opt (p : 'a -> bool) (ary : 'a array) : int option =
  let len = Array.length ary in
  let rec aux i =
    if len <= i then
      None
    else if p (Array.get ary i) then
      Some i
    else
      aux (i + 1)
  in
  aux 0

let array_copy_set (ary : 'a array) (i : int) (v : 'a) : 'a array =
  let ret = Array.copy ary in
  Array.set ret i v;
  ret

let array_find_index (p : 'a -> bool) (ary : 'a array) : int =
  match array_find_index_opt p ary with
  | None -> raise Not_found
  | Some i -> i

let array_combine (a1 : 'a array) (a2 : 'b array) : ('a * 'b) array =
  Array.map2 (fun x y -> (x,y)) a1 a2

let array_flatten (v : 'a array array) : 'a array =
  let nonempty = ref 0 in
  let total = ref 0 in
  for i = 0 to Array.length v - 1 do
    let w = v.(i) in
    let l = Array.length w in
    (if l <> 0 then nonempty := i);
    total := !total + l
  done;
  if !total = 0 then
    [||]
  else
    let u = Array.make !total v.(!nonempty).(0) in
    let k = ref 0 in
    for i = 0 to Array.length v - 1 do
      let w = v.(i) in
      for j = 0 to Array.length w - 1 do
        u.(!k) <- w.(j);
        k := !k + 1
      done
    done;
    u

let rec ncons n x s =
  if n = 0 then
    s
  else
    x :: (ncons (n-1) x s)

let rec list_find_index pred l =
  match l with
  | [] -> raise Not_found
  | v :: rest ->
      if pred v then
        0
      else
        1 + (list_find_index pred rest)

let string_of_name name =
  match name with
  | Name.Name id -> Id.to_string id
  | Name.Anonymous -> "_"

let iota_ary (m : int) (n : int) : int array =
  Array.init n (fun i -> m + i)

let iota_list (m : int) (n : int) : int list =
  Array.to_list (iota_ary m n)

let rec array_option_exists_rec p a n i =
  if n <= i then
    None
  else
    let v = p a.(i) in
    match v with
    | None -> array_option_exists_rec p a n (i+1)
    | Some _ -> v

let shortcut_option_or o f =
  match o with
  | None -> f ()
  | Some _ -> o

let array_option_exists p a =
  array_option_exists_rec p a (Array.length a) 0

let int_pred i = i - 1
let int_succ i = i + 1

let merge_range (r1 : (int*int) option) (r2 : (int*int) option) : (int*int) option =
  match r1 with
  | None -> r2
  | Some (min1,max1) ->
      match r2 with
      | None -> r1
      | Some (min2,max2) ->
          Some ((min min1 min2), (max max1 max2))

let merge_range3 (r1 : (int*int) option) (r2 : (int*int) option) (r3 : (int*int) option) : (int*int) option =
  merge_range (merge_range r1 r2) r3

let (+++) d1 d2 =
  if Pp.ismt d1 then
    d2
  else if Pp.ismt d2 then
    d1
  else
    d1 ++ Pp.spc () ++ d2

let pp_sjoin_ary (ary : Pp.t array) : Pp.t =
  Array.fold_left
    (fun pp elt -> pp +++ elt)
    (mt ())
    ary

let pp_sjoin_list (l : Pp.t list) : Pp.t =
  List.fold_left
    (fun pp elt -> pp +++ elt)
    (mt ())
    l

let pp_join_ary sep ary =
  if Array.length ary = 0 then
    mt ()
  else
    Array.fold_left
      (fun pp elt -> pp ++ sep ++ elt)
      ary.(0)
      (Array.sub ary 1 (Array.length ary - 1))

let pp_join_list sep l =
  match l with
  | [] ->
    mt ()
  | elt :: rest ->
    List.fold_left
      (fun pp elt -> pp ++ sep ++ elt)
      elt
      rest

let pp_prejoin_ary sep ary =
  Array.fold_left
    (fun pp elt -> pp ++ sep ++ elt)
    (mt ())
    ary

let pp_prejoin_list sep l =
  List.fold_left
    (fun pp elt -> pp ++ sep ++ elt)
    (mt ())
    l

let pp_postjoin_ary sep ary =
  Array.fold_left
    (fun pp elt -> if ismt elt then pp else pp ++ elt ++ sep)
    (mt ())
    ary

let pp_postjoin_list sep l =
  List.fold_left
    (fun pp elt -> pp ++ elt ++ sep)
    (mt ())
    l

let new_env_with_rels (env : Environ.env) : Environ.env =
  let n = Environ.nb_rel env in
  let r = ref (Global.env ()) in
  for i = n downto 1 do
    r := Environ.push_rel (Environ.lookup_rel i env) (!r)
  done;
  !r

let rec decompose_lam_n_env (env : Environ.env) (sigma : Evd.evar_map) (n : int) (term : EConstr.t) : (Environ.env * EConstr.t) =
  if n = 0 then
    (env, term)
  else
    match EConstr.kind sigma term with
    | Lambda (x,t,e) ->
        let decl = Context.Rel.Declaration.LocalAssum (x, t) in
        let env2 = EConstr.push_rel decl env in
        decompose_lam_n_env env2 sigma (n-1) e
    | _ ->
      user_err (str "[codegen:bug:decompose_lam_n_env] unexpected non-lambda term: " ++ Printer.pr_econstr_env env sigma term)

let numargs_of_type (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : int =
  (*Feedback.msg_debug (Pp.str "[codegen] numargs_of_type arg: " ++ Printer.pr_econstr_env env sigma t);*)
  let t = Reductionops.nf_all env sigma t in
  (*Feedback.msg_debug (Pp.str "[codegen] numargs_of_type nf_all: " ++ Printer.pr_econstr_env env sigma t);*)
  let (args, result_type) = decompose_prod sigma t in
  List.length args

let numargs_of_exp (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : int =
  (*Feedback.msg_debug (Pp.str "[codegen] numargs_of_exp arg: " ++ Printer.pr_econstr_env env sigma term);*)
  let t = Retyping.get_type_of env sigma term in
  (*Feedback.msg_debug (Pp.str "[codegen] numargs_of_exp t=" ++ Printer.pr_econstr_env env sigma t);*)
  numargs_of_type env sigma t

let out_punivs : 'a EConstr.puniverses -> 'a = fst

let rec mangle_term_buf (env : Environ.env) (sigma : Evd.evar_map) (buf : Buffer.t) (ty : EConstr.t) : unit =
  (*Feedback.msg_debug (Pp.str "mangle_term_buf:" +++ Printer.pr_econstr_env env sigma ty);*)
  match EConstr.kind sigma ty with
  | Ind iu ->
      let (mutind, i) = out_punivs iu in
      let mutind_body = Environ.lookup_mind mutind env in
      let s = Id.to_string mutind_body.Declarations.mind_packets.(i).Declarations.mind_typename in
      Buffer.add_string buf s
  | Construct cu ->
      let ((mutind, i), j) = out_punivs cu in
      let mutind_body = Environ.lookup_mind mutind env in
      let oneind_body = mutind_body.Declarations.mind_packets.(i) in
      let s = Id.to_string oneind_body.Declarations.mind_consnames.(j) in
      Buffer.add_string buf s
  | App (f, argsary) ->
      mangle_term_buf env sigma buf f;
      Array.iter (fun arg -> Buffer.add_char buf '_'; mangle_term_buf env sigma buf arg) argsary
  | Prod (x, t, b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      mangle_term_buf env sigma buf t;
      Buffer.add_string buf "_to_";
      mangle_term_buf env2 sigma buf b
  | Rel i -> user_err (Pp.str "[codegen] mangle_term_buf:rel:" +++ Printer.pr_econstr_env env sigma ty)
  | Var name -> user_err (Pp.str "[codegen] mangle_term_buf:var:")
  | Meta i -> user_err (Pp.str "[codegen] mangle_term_buf:meta:")
  | Evar (ekey, termary) -> user_err (Pp.str "[codegen] mangle_term_buf:evar:")
  | Sort s -> user_err (Pp.str "[codegen] mangle_term_buf:sort:")
  | Cast (expr, kind, ty) -> user_err (Pp.str "[codegen] mangle_term_buf:cast:")
  | Lambda (name, ty, body) -> user_err (Pp.str "[codegen] mangle_term_buf:lambda:")
  | LetIn (name, expr, ty, body) -> user_err (Pp.str "[codegen] mangle_term_buf:letin:")
  | Const cu -> user_err (Pp.str "[codegen] mangle_term_buf:const:" ++ Pp.spc () ++ Printer.pr_econstr_env env sigma ty)
  | Case (ci, tyf, iv, expr, brs) -> user_err (Pp.str "[codegen] mangle_term_buf:case:")
  | Fix ((ia, i), (nameary, tyary, funary)) -> user_err (Pp.str "[codegen] mangle_term_buf:fix:")
  | CoFix (i, (nameary, tyary, funary)) -> user_err (Pp.str "[codegen] mangle_term_buf:cofix:")
  | Proj (proj, expr) -> user_err (Pp.str "[codegen] mangle_term_buf:proj:")
  | Int n -> user_err (Pp.str "[codegen] mangle_term_buf:int:")
  | Float n -> user_err (Pp.str "[codegen] mangle_term_buf:float:")
  | Array _ -> user_err (Pp.str "[codegen] mangle_term_buf:array:")

let mangle_term (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.t) : string =
  let buf = Buffer.create 0 in
  mangle_term_buf env sigma buf ty;
  Buffer.contents buf

let squeeze_white_spaces (str : string) : string =
  let buf = Buffer.create 0 in
  let after_space = ref true in
  String.iter
    (fun ch ->
      match ch with
      |' '|'\t'|'\n' ->
          if not !after_space then
            Buffer.add_char buf ' ';
          after_space := true
      | _ ->
          Buffer.add_char buf ch;
          after_space := false)
    str;
  let n = Buffer.length buf in
  if 0 < n && Buffer.nth buf (n - 1) = ' ' then
    Buffer.truncate buf (n - 1 );
  Buffer.contents buf

let c_id str =
  let buf = Buffer.create 0 in
  String.iter
    (fun ch ->
      match ch with
      |'_'|'0'..'9'|'A'..'Z'|'a'..'z' -> Buffer.add_char buf ch
      | _ -> Buffer.add_char buf '_')
    str;
  Buffer.contents buf

exception Invalid_as_C_identifier

let valid_c_id_p (str : string) : bool =
  let n = String.length str in
  if n = 0 then
    false
  else
    match str.[0] with
    |'_'|'A'..'Z'|'a'..'z' ->
        (try
          for i = 1 to n-1 do
            match str.[i] with
            |'_'|'0'..'9'|'A'..'Z'|'a'..'z' -> ()
            |_ -> raise Invalid_as_C_identifier
          done;
          true
        with Invalid_as_C_identifier -> false)
    | _ -> false

let check_c_id (str : string) : unit =
  if valid_c_id_p str then
    ()
  else
    user_err (Pp.str "[codegen] invalid C name:" ++ Pp.spc () ++ Pp.str str)

let escape_as_coq_string str =
  let buf = Buffer.create (String.length str + 2) in
  Buffer.add_char buf '"';
  String.iter
    (fun ch ->
      match ch with
      |'"' -> Buffer.add_string buf "\"\""
      |_ -> Buffer.add_char buf ch)
    str;
  Buffer.add_char buf '"';
  Buffer.contents buf

let detect_recursive_functions (ctnt_i : Constant.t) : (int * Constant.t option array) option =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let modpath = KerName.modpath (Constant.canonical ctnt_i) in
  match Global.body_of_constant Library.indirect_accessor ctnt_i with
  | None -> user_err (Pp.str "[codegen] couldn't obtain the definition of" ++ Pp.spc () ++
                      Printer.pr_constant env ctnt_i)
  | Some (def_i,_,_) ->
      let def_i = EConstr.of_constr def_i in
      let (ctx_rel_i, body_i) = decompose_lam_assum sigma def_i in
      match EConstr.kind sigma body_i with
      | Constr.Fix ((ia, i), (nary, tary, fary)) ->
          let ctnt_ary =
            Array.mapi (fun j nm ->
              if j = i then
                Some ctnt_i
              else
                let nm = Context.binder_name nm in
                match nm with
                | Name.Anonymous -> None
                | Name.Name id ->
                    let label = Label.of_id id in
                    let ctnt_j = Constant.make1 (KerName.make modpath label) in
                    try
                      match Global.body_of_constant Library.indirect_accessor ctnt_j with
                      | None -> None
                      | Some (def_j,_,_) ->
                          let def_j = EConstr.of_constr def_j in
                          let body_j' = mkFix ((ia, j), (nary, tary, fary)) in
                          let def_j' = it_mkLambda_or_LetIn body_j' ctx_rel_i in
                          if EConstr.eq_constr sigma def_j def_j' then
                            Some ctnt_j
                          else
                            None
                    with Not_found -> None)
            nary
          in
          Some (i, ctnt_ary)
      | _ -> None

let rec compose_prod (l : (Name.t Context.binder_annot * EConstr.t) list) (b : EConstr.t) : EConstr.t =
  match l with
  | [] -> b
  | (v, e) :: l' -> compose_prod l' (mkProd (v,e,b))

let rec free_variables_rec (sigma : Evd.evar_map) (numlocal : int) (fv : bool array) (term : EConstr.t) : unit =
  match EConstr.kind sigma term with
  | Var _ | Meta _ | Sort _ | Ind _ | Int _ | Float _ | Array _
  | Const _ | Construct _ -> ()
  | Rel i ->
      if numlocal < i then
        fv.(i-numlocal-1) <- true
  | Evar (ev, es) ->
      List.iter (free_variables_rec sigma numlocal fv) es
  | Proj (proj, e) ->
      free_variables_rec sigma numlocal fv e
  | Cast (e,ck,t) ->
      free_variables_rec sigma numlocal fv e;
      free_variables_rec sigma numlocal fv t
  | App (f, args) ->
      free_variables_rec sigma numlocal fv f;
      Array.iter (free_variables_rec sigma numlocal fv) args
  | LetIn (x,e,t,b) ->
      free_variables_rec sigma numlocal fv e;
      free_variables_rec sigma numlocal fv t;
      free_variables_rec sigma (numlocal+1) fv b
  | Case (ci, p, iv, item, branches) ->
      free_variables_rec sigma numlocal fv p;
      free_variables_rec sigma numlocal fv item;
      Array.iter (free_variables_rec sigma numlocal fv) branches
  | Prod (x,t,b) | Lambda (x,t,b) ->
      free_variables_rec sigma numlocal fv t;
      free_variables_rec sigma (numlocal+1) fv b
  | Fix (_, (nary, tary, fary)) | CoFix (_, (nary, tary, fary)) ->
      Array.iter (free_variables_rec sigma numlocal fv) tary;
      let numlocal2 = numlocal + Array.length fary in
      Array.iter (free_variables_rec sigma numlocal2 fv) fary

(* nb_rel + nb_local should be Environ.nb_rel env *)
let free_variables_without (sigma : Evd.evar_map) (nb_rel : int) (nb_local : int) (term : EConstr.t) : bool array =
  let fv = Array.make nb_rel false in
  free_variables_rec sigma nb_local fv term;
  fv

(* nb_rel should be Environ.nb_rel env *)
let free_variables (sigma : Evd.evar_map) (nb_rel : int) (term : EConstr.t) : bool array =
  free_variables_without sigma nb_rel 0 term

let constr_name (sigma : Evd.evar_map) (term : EConstr.t) : string =
  match EConstr.kind sigma term with
  | Rel _ -> "Rel"
  | Var _ -> "Var"
  | Meta _ -> "Meta"
  | Evar _ -> "Evar"
  | Sort _ -> "Sort"
  | Cast _ -> "Cast"
  | Prod _ -> "Prod"
  | Lambda _ -> "Lambda"
  | LetIn _ -> "LetIn"
  | App _ -> "App"
  | Const _ -> "Const"
  | Ind _ -> "Ind"
  | Construct _ -> "Construct"
  | Case _ -> "Case"
  | Fix _ -> "Fix"
  | CoFix _ -> "CoFix"
  | Proj _ -> "Proj"
  | Int _ -> "Int"
  | Float _ -> "Float"
  | Array _ -> "Array"

let constr_expr_cstr_name (c : Constrexpr.constr_expr) =
  match CAst.with_val (fun x -> x) c with
  | Constrexpr.CRef _ -> "CRef"
  | Constrexpr.CFix _ -> "CFix"
  | Constrexpr.CCoFix _ -> "CCoFix"
  | Constrexpr.CProdN _ -> "CProdN"
  | Constrexpr.CLambdaN _ -> "CLambdaN"
  | Constrexpr.CLetIn _ -> "CLetIn"
  | Constrexpr.CAppExpl _ -> "CAppExpl"
  | Constrexpr.CApp _ -> "CApp"
  | Constrexpr.CRecord _ -> "CRecord"
  | Constrexpr.CCases _ -> "CCases"
  | Constrexpr.CLetTuple _ -> "CLetTuple"
  | Constrexpr.CIf _ -> "CIf"
  | Constrexpr.CHole _ -> "CHole"
  | Constrexpr.CPatVar _ -> "CPatVar"
  | Constrexpr.CEvar _ -> "CEvar"
  | Constrexpr.CSort _ -> "CSort"
  | Constrexpr.CCast _ -> "CCast"
  | Constrexpr.CNotation _ -> "CNotation"
  | Constrexpr.CGeneralization _ -> "CGeneralization"
  | Constrexpr.CPrim _ -> "CPrim"
  | Constrexpr.CDelimiters _ -> "CDelimiters"
  | Constrexpr.CArray _ -> "CArray"

let global_gensym ?(prefix : string = "g") () : string =
  let n = !gensym_id in
  gensym_id := n + 1;
  prefix ^ string_of_int n

let global_gensym_with_id (id : Id.t) : string =
  global_gensym () ^ "_" ^ (c_id (Id.to_string id))
