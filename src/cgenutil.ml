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

module IntSet = Set.Make(Int)

open Names
open CErrors
open Constr
open EConstr

open State

let abort (x : 'a) : 'a = assert false

exception CodeGenError of string

let int_find_opt (p : int -> bool) ?(start : int = 0) (n : int) : int option =
  let rec aux i =
    if i < n then
      if p (start + i) then
        Some (start + i)
      else
        aux (i + 1)
    else
      None
  in
  aux 0

let int_find_map (f : int -> 'a option) ?(start : int = 0) (n : int) : 'a option =
  let rec aux i =
    if i < n then
      let opt = f (start + i) in
      match opt with
      | None -> aux (i + 1)
      | Some _ -> opt
    else
      None
  in
  aux 0

let int_find_i_map (f : int -> 'a option) ?(start : int = 0) (n : int) : (int * 'a) option =
  let rec aux i =
    if i < n then
      let opt = f (start + i) in
      match opt with
      | None -> aux (i + 1)
      | Some v -> Some (start + i, v)
    else
      None
  in
  aux 0

let array_rev a =
  let n = Array.length a in
  Array.init n (fun i -> a.(n - i - 1))

let array_firstn (n : int) (ary : 'a array) : 'a array =
  Array.sub ary 0 n

let array_skipn (n : int) (ary : 'a array) : 'a array =
  Array.sub ary n (Array.length ary - n)

let array_map2 f a1 a2 =
  if Array.length a1 <> Array.length a2 then
    invalid_arg "Array.map2: arrays must have the same length";
  Array.mapi (fun i -> f a1.(i)) a2

let array_map3 (f : 'a -> 'b -> 'c -> 'd) (a : 'a array) (b : 'b array) (c : 'c array) : 'd array =
  let n = Array.length a in
  if Array.length b <> n then raise (Invalid_argument "array_map3");
  if Array.length c <> n then raise (Invalid_argument "array_map3");
  Array.init n (fun i -> f a.(i) b.(i) c.(i))

let array_map4 (f : 'a -> 'b -> 'c -> 'd -> 'e) (a : 'a array) (b : 'b array) (c : 'c array) (d : 'd array) : 'e array =
  let n = Array.length a in
  if Array.length b <> n then raise (Invalid_argument "array_map4");
  if Array.length c <> n then raise (Invalid_argument "array_map4");
  if Array.length d <> n then raise (Invalid_argument "array_map4");
  Array.init n (fun i -> f a.(i) b.(i) c.(i) d.(i))

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

let array_find_map (f : 'a -> 'b option) (s : 'a array) : 'b option =
  let n = Array.length s in
  let rec aux i =
    if i < n then
      let v = f s.(i) in
      match v with
      | None -> aux (i+1)
      | Some _ -> v
    else
      None
  in
  aux 0

let array_find_map2 (f : 'a -> 'b -> 'c option) (s1 : 'a array) (s2 : 'b array) : 'c option =
  let n = Array.length s1 in
  if n <> Array.length s2 then
    raise (Invalid_argument "array_find_map2: arrays must have the same length");
  let rec aux i =
    if i < n then
      let v = f s1.(i) s2.(i) in
      match v with
      | None -> aux (i+1)
      | Some _ -> v
    else
      None
  in
  aux 0

let array_find_map_i (p : int -> 'a -> 'b option) (ary : 'a array) : (int * 'b) option =
  let len = Array.length ary in
  let rec aux i =
    if len <= i then
      None
    else
      match p i ary.(i) with
      | None -> aux (i + 1)
      | Some v -> Some (i, v)
  in
  aux 0

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
    else if p ary.(i) then
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

let ncons n x s = CList.addn n x s

let rec ntimes n f v =
  if n = 0 then
    v
  else
    ntimes (n-1) f (f v)

let list_prepend_map_rev (f : 'a -> 'b) (l1 : 'a list) (l2 : 'b list) : 'b list =
  let rec aux l1 result =
    match l1 with
    | [] -> result
    | e :: rest -> aux rest ((f e) :: result)
  in
  aux l1 []

let list_prepend_mapi_rev (f : int -> 'a -> 'b) (l1 : 'a list) (l2 : 'b list) : 'b list =
  let rec aux i l1 result =
    match l1 with
    | [] -> result
    | e :: rest -> aux (i+1) rest ((f i e) :: result)
  in
  aux 0 l1 []

let rec list_rev_map_append (f : 'a -> 'b) (l1 : 'a list) (l2 : 'b list) : 'b list =
  match l1 with
  | [] -> l2
  | e :: rest -> list_rev_map_append f rest ((f e) :: l2)

let rec list_map_append (f : 'a -> 'b) (l1 : 'a list) (l2 : 'b list) : 'b list =
  match l1 with
  | [] -> l2
  | e :: rest -> (f e) :: list_map_append f rest l2

let rec list_find_index pred l =
  match l with
  | [] -> raise Not_found
  | v :: rest ->
      if pred v then
        0
      else
        1 + (list_find_index pred rest)

let list_filter_map2 (f : 'a -> 'b -> 'c option) (xs : 'a list) (ys : 'b list) : 'c list =
  List.fold_right2
    (fun x y s ->
      match f x y with
      | None -> s
      | Some z -> z :: s)
    xs ys []

let list_filter_none (s : 'a option list) : 'a list =
  List.fold_right
    (fun opt s ->
      match opt with
      | None -> s
      | Some x -> x :: s)
    s []

let seq_map2 (f : 'a -> 'b -> 'c) (xs : 'a Seq.t) (ys : 'b Seq.t) () : 'c Seq.node =
  let rec r xs ys () =
    match xs (), ys () with
    | Seq.Nil, Seq.Nil -> Seq.Nil
    | Seq.Cons (x, xs), Seq.Cons (y, ys) -> Seq.Cons (f x y, r xs ys)
    | _ -> raise (Invalid_argument "seq_map2")
  in
  r xs ys ()

let seq_mapi (f : int -> 'a -> 'b) (s : 'a Seq.t) () : 'b Seq.node =
  let rec r i s () =
    match s () with
    | Seq.Nil -> Seq.Nil
    | Seq.Cons (x, xs) -> Seq.Cons (f i x, r (i+1) xs)
  in
  r 0 s ()

let seq_flat_map2 (f : 'a -> 'b -> 'c Seq.t) (xs : 'a Seq.t) (ys : 'b Seq.t) () : 'c Seq.node =
  let rec r xs ys () =
    match xs (), ys () with
    | Seq.Nil, Seq.Nil -> Seq.Nil
    | Seq.Cons (x, xs), Seq.Cons (y,ys) -> Seq.append (f x y) (r xs ys) ()
    | _ -> raise (Invalid_argument "seq_flat_map2")
  in
  r xs ys ()

let seq_flat_mapi (f : int -> 'a -> 'b Seq.t) (s : 'a Seq.t) () : 'b Seq.node =
  let rec r i s () =
    match s () with
    | Seq.Nil -> Seq.Nil
    | Seq.Cons (x, xs) -> Seq.append (f i x) (r (i+1) xs) ()
  in
  r 0 s ()

let seq_flat_map2_i (f : int -> 'a -> 'b -> 'c Seq.t) (xs : 'a Seq.t) (ys : 'b Seq.t) () : 'c Seq.node =
  let rec r i xs ys () =
    match xs (), ys () with
    | Seq.Nil, Seq.Nil -> Seq.Nil
    | Seq.Cons (x, xs), Seq.Cons (y,ys) -> Seq.append (f i x y) (r (i+1) xs ys) ()
    | _ -> raise (Invalid_argument "seq_flat_map2_i")
  in
  r 0 xs ys ()

let rec concat_list_seq (l : 'a Seq.t list) : 'a Seq.t =
  match l with
  | [] -> Seq.empty
  | s :: rest -> Seq.append s (concat_list_seq rest)

let concat_array_seq (ary : 'a Seq.t array) : 'a Seq.t =
  let r = ref Seq.empty in
  for i = Array.length ary - 1 downto 0 do
    r := Seq.append ary.(i) !r
  done;
  !r

let unique_string_list (ss : string list) : string list =
  let h = Hashtbl.create 0 in
  List.filter
    (fun s ->
      if Hashtbl.mem h s then
        false
      else
        (Hashtbl.add h s true;
        true))
    ss

let quote_coq_string (s : string) : string =
  let buf = Buffer.create (String.length s + 2) in
  let rec f i =
    match String.index_from_opt s i '"' with
    | None ->
        Buffer.add_substring buf s i (String.length s - i)
    | Some j ->
        Buffer.add_substring buf s i (j - i);
        Buffer.add_string buf "\"\"";
        f (j+1)
  in
  Buffer.add_char buf '"';
  f 0;
  Buffer.add_char buf '"';
  Buffer.contents buf

let expand_tab (str : string) : string =
  let add_spaces buf n =
    for i = 1 to n do
      ignore i;
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

let id_of_name (name : Name.t) : Id.t =
  match name with
  | Name.Anonymous -> user_err (Pp.str "[codegen:bug] id_of_name require non-anonymous Name")
  | Name.Name id -> id

let id_of_annotated_name (name : Name.t Context.binder_annot) : Id.t =
  id_of_name (Context.binder_name name)

let str_of_name (name : Name.t) : string =
  match name with
  | Name.Anonymous -> user_err (Pp.str "[codegen] str_of_name with anonymous name")
  | Name.Name id -> Id.to_string id

let str_of_annotated_name (name : Name.t Context.binder_annot) : string =
  str_of_name (Context.binder_name name)

let str_of_name_permissive (name : Name.t) : string =
  match name with
  | Name.Anonymous -> "_"
  | Name.Name id -> Id.to_string id

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

let merge_range_ary (ranges : (int*int) option array) : (int*int) option =
  Array.fold_left
    (fun acc r -> merge_range acc r)
    None ranges

let intset_union_ary (sets : IntSet.t array) : IntSet.t =
  let result = ref IntSet.empty in
  for i = 0 to Array.length sets - 1 do
    result := IntSet.union !result sets.(i)
  done;
  !result

let (++) = Pp.app

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
    (Pp.mt ())
    ary

let pp_sjoin_list (l : Pp.t list) : Pp.t =
  List.fold_left
    (fun pp elt -> pp +++ elt)
    (Pp.mt ())
    l

let pp_sjoinmap_ary (f : 'a -> Pp.t) (ary : 'a array) : Pp.t =
  Array.fold_left
    (fun pp elt -> pp +++ f elt)
    (Pp.mt ())
    ary

let pp_sjoinmap_list (f : 'a -> Pp.t) (l : 'a list) : Pp.t =
  List.fold_left
    (fun pp elt -> pp +++ f elt)
    (Pp.mt ())
    l

let pp_join_ary (sep : Pp.t) (ary : Pp.t array) : Pp.t =
  if Array.length ary = 0 then
    Pp.mt ()
  else
    Array.fold_left
      (fun pp elt -> pp ++ sep ++ elt)
      ary.(0)
      (Array.sub ary 1 (Array.length ary - 1))

let pp_join_list (sep : Pp.t) (l : Pp.t list) : Pp.t =
  match l with
  | [] ->
    Pp.mt ()
  | elt :: rest ->
    List.fold_left
      (fun pp elt -> pp ++ sep ++ elt)
      elt
      rest

let pp_joinmap_ary (sep : Pp.t) (f : 'a -> Pp.t) (ary : 'a array) : Pp.t =
  if Array.length ary = 0 then
    Pp.mt ()
  else
    Array.fold_left
      (fun pp elt -> pp ++ sep ++ f elt)
      (f ary.(0))
      (Array.sub ary 1 (Array.length ary - 1))

let pp_joinmap_list (sep : Pp.t) (f : 'a -> Pp.t) (l : 'a list) : Pp.t =
  match l with
  | [] ->
    Pp.mt ()
  | elt :: rest ->
    List.fold_left
      (fun pp elt -> pp ++ sep ++ f elt)
      (f elt)
      rest

let pp_prejoin_ary sep ary =
  Array.fold_left
    (fun pp elt -> pp ++ sep ++ elt)
    (Pp.mt ())
    ary

let pp_prejoin_list sep l =
  List.fold_left
    (fun pp elt -> pp ++ sep ++ elt)
    (Pp.mt ())
    l

let pp_postjoin_ary sep ary =
  Array.fold_left
    (fun pp elt -> if Pp.ismt elt then pp else pp ++ elt ++ sep)
    (Pp.mt ())
    ary

let pp_postjoin_list sep l =
  List.fold_left
    (fun pp elt -> pp ++ elt ++ sep)
    (Pp.mt ())
    l

let hbrace (pp : Pp.t) : Pp.t =
  Pp.h (Pp.str "{" +++ pp ++ Pp.brk (1,-2) ++ Pp.str "}")

let hovbrace (pp : Pp.t) : Pp.t =
  Pp.hv 2 (Pp.str "{" +++ pp ++ Pp.brk (1,-2) ++ Pp.str "}")

let vbrace (pp : Pp.t) : Pp.t =
  Pp.v 2 (Pp.str "{" +++ pp ++ Pp.brk (1,-2) ++ Pp.str "}")

let msg_info_hov pp =
  Feedback.msg_info (Pp.hov 2 pp)

let msg_debug_hov pp =
  Feedback.msg_debug (Pp.hov 2 pp)

let user_err_hov pp = user_err (Pp.hov 2 pp)

let format_deep (pp : Pp.t) : string =
  let buf = Buffer.create 0 in
  let fmt = Format.formatter_of_buffer buf in
  Format.pp_set_max_boxes fmt max_int;
  Pp.pp_with fmt pp;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

let pr_deep (pp : Pp.t) : Pp.t =
  Pp.str (format_deep pp)

let rec is_monomorphic_type (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.t) : bool =
  match EConstr.kind sigma ty with
  | Prod (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      is_monomorphic_type env sigma t &&
      is_monomorphic_type env2 sigma b
  | Ind _ -> true
  | App (f,args) when isInd sigma f -> true
  | Rel _ -> true (* type variable *)
  | _ -> false

let new_env_with_rels (env : Environ.env) : Environ.env =
  let n = Environ.nb_rel env in
  let r = ref (Global.env ()) in
  for i = n downto 1 do
    r := Environ.push_rel (Environ.lookup_rel i env) (!r)
  done;
  !r

let decompose_appvect (sigma : Evd.evar_map) (term : EConstr.t) : (EConstr.t * EConstr.t array) =
  match EConstr.kind sigma term with
  | App (f,args) -> (f,args)
  | _ -> (term, [||])

let decompose_lam_upto_n (env : Environ.env) (sigma : Evd.evar_map) (n : int) (term : EConstr.t) : (Name.t Context.binder_annot * EConstr.t) list * EConstr.t =
  let rec aux n fargs term =
    if n <= 0 then
      (fargs, term)
    else
      match EConstr.kind sigma term with
      | Lambda (x,t,e) ->
          aux (n-1) ((x,t)::fargs) e
      | _ ->
          (fargs, term)
  in
  aux n [] term

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
      user_err (Pp.str "[codegen:bug:decompose_lam_n_env] unexpected non-lambda term:" +++ Printer.pr_econstr_env env sigma term)

let numargs_of_type (env : Environ.env) (sigma : Evd.evar_map) (t : EConstr.types) : int =
  (*Feedback.msg_debug (Pp.str "[codegen] numargs_of_type arg:" +++ Printer.pr_econstr_env env sigma t);*)
  let t = Reductionops.nf_all env sigma t in
  (*Feedback.msg_debug (Pp.str "[codegen] numargs_of_type nf_all:" +++ Printer.pr_econstr_env env sigma t);*)
  let (args, result_type) = decompose_prod sigma t in
  List.length args

let numargs_of_exp (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : int =
  (*Feedback.msg_debug (Pp.str "[codegen] numargs_of_exp arg:" +++ Printer.pr_econstr_env env sigma term);*)
  let t = Retyping.get_type_of env sigma term in
  (*Feedback.msg_debug (Pp.str "[codegen] numargs_of_exp t=" ++ Printer.pr_econstr_env env sigma t);*)
  numargs_of_type env sigma t

let out_punivs : 'a EConstr.puniverses -> 'a = fst

let inductive_abstract_constructor_type_relatively_to_inductive_types_context_nflc (ntypes : int) (mutind : MutInd.t) (nf_lc : Constr.rel_context * Constr.types) : Constr.rel_context * Constr.types =
  let (ctx, t) = nf_lc in
  let t = Term.it_mkProd_or_LetIn t ctx in
  let t = Inductive.abstract_constructor_type_relatively_to_inductive_types_context ntypes mutind t in
  Term.decompose_prod_assum t

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
      let j0 = j - 1 in
      (*(if j < 1 then user_err (Pp.str "[codegen] too small j=" ++ Pp.int j));
      (if Array.length oneind_body.Declarations.mind_consnames < j then user_err (Pp.str "[codegen] too big j=" ++ Pp.int j));*)
      let s = Id.to_string oneind_body.Declarations.mind_consnames.(j0) in
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
  | Const cu -> user_err (Pp.str "[codegen] mangle_term_buf:const:" +++ Printer.pr_econstr_env env sigma ty)
  | Case (ci,u,pms,p,iv,c,bl) -> user_err (Pp.str "[codegen] mangle_term_buf:case:")
  | Fix ((ks, j), (nary, tary, fary)) -> user_err (Pp.str "[codegen] mangle_term_buf:fix:")
  | CoFix (i, (nary, tary, fary)) -> user_err (Pp.str "[codegen] mangle_term_buf:cofix:")
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
    user_err (Pp.str "[codegen] invalid C name:" +++ Pp.str str)

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

let rec compose_prod (l : (Name.t Context.binder_annot * EConstr.t) list) (b : EConstr.t) : EConstr.t =
  match l with
  | [] -> b
  | (v, e) :: l' -> compose_prod l' (mkProd (v,e,b))

let rec free_variables_rec (sigma : Evd.evar_map) (numlocal : int) (fv : bool array) (term : EConstr.t) : unit =
  match EConstr.kind sigma term with
  | Rel i ->
      if numlocal < i then
        fv.(i-numlocal-1) <- true
  | _ ->
      Termops.fold_constr_with_binders sigma Stdlib.Int.succ
        (fun numlocal u e -> free_variables_rec sigma numlocal fv e)
        numlocal () term

(* nb_rel + nb_local should be Environ.nb_rel env *)
let free_variables_without (env : Environ.env) (sigma : Evd.evar_map) (nb_rel : int) (nb_local : int) (term : EConstr.t) : bool array =
  let fv = Array.make nb_rel false in
  free_variables_rec sigma nb_local fv term;
  fv

let free_variables_bool_ary (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : bool array =
  free_variables_without env sigma (Environ.nb_rel env) 0 term

(* set of de Bruijn indexes of free variables *)
let free_variables_index_set (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : IntSet.t =
  let fv = free_variables_bool_ary env sigma term in
  let r = ref IntSet.empty in
  for i = 0 to Array.length fv - 1 do
    if fv.(i) then
      r := IntSet.add (i + 1) !r
  done;
  !r

(* range of de Bruijn indexes of free variables *)
let free_variables_index_range (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : (int * int) option =
  let fv = free_variables_bool_ary env sigma term in
  let r = ref None in
  for i = 0 to Array.length fv - 1 do
    if fv.(i) then
      r := merge_range !r (Some (i+1,i+1))
  done;
  !r

(* set of de Bruijn levels of free variables *)
let free_variables_level_set ?(without : int = 0) (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : IntSet.t =
  let nb_rel = Environ.nb_rel env in
  let fv = free_variables_without env sigma (nb_rel - without) without term in
  let r = ref IntSet.empty in
  for i = 0 to Array.length fv - 1 do
    if fv.(i) then
      r := IntSet.add (nb_rel - (i + 1)) !r
  done;
  !r

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
  | Constrexpr.CProj _ -> "CProj"
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

let str_cast_kind (k : cast_kind) : string =
  match k with
  | VMcast -> "<:"
  | NATIVEcast -> "<<:"
  | DEFAULTcast -> ":"

let pr_raw_econstr (sigma : Evd.evar_map) (term : EConstr.t) : Pp.t =
  let open Declarations in
  let env0 = Global.env () in
  let rec aux relnames term =
    match EConstr.kind sigma term with
    | Rel i ->
        (match List.nth_opt relnames (i-1) with
        | Some name -> Name.print name
        | None -> Pp.str "Rel") ++
        Pp.str "[" ++ Pp.int i ++ Pp.str "]"
    | Var id -> Pp.str "Var[" ++ Id.print id ++ Pp.str "]"
    | Meta _ -> Pp.str "Meta"
    | Evar _ -> Pp.str "Evar"
    | Sort s -> Printer.pr_sort sigma (ESorts.kind sigma s)
    | Cast (e,k,t) ->
        Pp.hov 2 (
          Pp.str "(" ++
          aux relnames e +++
          Pp.str (str_cast_kind k) +++
          aux relnames t)
    | Prod (x, t, b) ->
        let n = Context.binder_name x in
        Pp.hov 2 (
          Pp.str "(forall" +++
          Pp.str "(" ++
          Name.print n +++
          Pp.str ":" +++
          aux relnames t ++
          Pp.str ")," +++
          aux (n::relnames) b ++
          Pp.str ")")
    | Lambda (x, t, b) ->
        let n = Context.binder_name x in
        Pp.hov 2 (
          Pp.str "(fun" +++
          Pp.str "(" ++
          Name.print n +++
          Pp.str ":" +++
          aux relnames t ++
          Pp.str ")," +++
          aux (n::relnames) b ++
          Pp.str ")")
    | LetIn (x, e, t, b) ->
        let n = Context.binder_name x in
        Pp.hov 2 (
          Pp.str "(let" +++
          Name.print n +++
          Pp.str ":" +++
          aux relnames t +++
          Pp.str ":=" +++
          aux relnames e +++
          Pp.str "in" +++
          aux (n::relnames) b ++
          Pp.str ")")
    | App (f, args) ->
        Pp.hov 2 (
          Pp.str "(" ++
          aux relnames f +++
          pp_sjoinmap_ary (aux relnames) args ++
          Pp.str ")")
    | Const (cnst, univ) -> Constant.print cnst
    | Ind ((mutind, ind_index), univ) ->
        let mind_body = Environ.lookup_mind mutind env0 in
        let oind_body = mind_body.mind_packets.(ind_index) in
        Id.print oind_body.mind_typename
    | Construct (((mutind, ind_index), cons_index), univ) ->
        let mind_body = Environ.lookup_mind mutind env0 in
        let oind_body = mind_body.mind_packets.(ind_index) in
        Id.print oind_body.mind_consnames.(cons_index-1)
    | Case (ci, u, pms, mpred, iv, item, bl) ->
        let (mutind, ind_index) = ci.ci_ind in
        let mind_body = Environ.lookup_mind mutind env0 in
        let oind_body = mind_body.mind_packets.(ind_index) in
        Pp.hov 2 (
          Pp.str "(match" +++
          aux relnames item +++
          Pp.str "with" +++
          pp_sjoinmap_ary
            (fun i ->
              let consname = oind_body.mind_consnames.(i) in
              let (nas, b) = bl.(i) in
              let nas = Array.map Context.binder_name nas in
              Pp.hov 2 (
                Pp.str "|" +++
                Id.print consname +++
                pp_sjoinmap_ary Name.print nas +++
                Pp.str "=>" +++
                aux (List.append (CArray.rev_to_list nas) relnames) b))
            (iota_ary 0 (Array.length oind_body.mind_consnames)) ++
          Pp.str ")")
    | Fix ((ks, j), (nary, tary, fary)) ->
        let nary = Array.map Context.binder_name nary in
        let relnames2 = List.append (CArray.rev_to_list nary) relnames in (* xxx: check reverse or not *)
        Pp.hov 2 (
          Pp.str "(fix" +++
          pp_sjoinmap_ary
            (fun i ->
              let n = nary.(i) in
              let t = tary.(i) in
              let f = fary.(i) in
              let k = ks.(i) in
              Pp.str "(" ++
              Name.print n ++
              Pp.str "/" ++
              Pp.int k +++
              Pp.str ":" +++
              aux relnames t +++
              Pp.str ":=" +++
              aux relnames2 f ++
              Pp.str ")")
            (iota_ary 0 (Array.length nary)) +++
          Pp.str "for" +++
          Name.print nary.(j) ++
          Pp.str ")")
    | CoFix (j, (nary, tary, fary)) ->
        let nary = Array.map Context.binder_name nary in
        let relnames2 = List.append (CArray.rev_to_list nary) relnames in (* xxx: check reverse or not *)
        Pp.hov 2 (
          Pp.str "(cofix" +++
          pp_sjoinmap_ary
            (fun i ->
              let n = nary.(i) in
              let t = tary.(i) in
              let f = fary.(i) in
              Pp.str "(" ++
              Name.print n +++
              Pp.str ":" +++
              aux relnames t +++
              Pp.str ":=" +++
              aux relnames2 f ++
              Pp.str ")")
            (iota_ary 0 (Array.length nary)) +++
          Pp.str "for" +++
          Name.print nary.(j) ++
          Pp.str ")")
    | Proj (proj, e) ->
        Pp.hov 2 (
          Pp.str "(Proj" ++
          Projection.print proj +++
          aux relnames e ++
          Pp.str ")")
    | Int _ -> Pp.str "Int"
    | Float _ -> Pp.str "Float"
    | Array _ -> Pp.str "Array"
  in
  aux [] term

