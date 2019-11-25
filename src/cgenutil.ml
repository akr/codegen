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

exception CodeGenError of string

let array_rev a =
  let n = Array.length a in
  Array.init n (fun i -> a.(n - i - 1))

let array_map2 f a1 a2 =
  if Array.length a1 <> Array.length a2 then
    invalid_arg "Array.map2: arrays must have the same length";
  Array.mapi (fun i -> f a1.(i)) a2

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

let iota_ary m n =
  Array.init n (fun i -> m + i)

let iota_list m n =
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

let rec mangle_type_buf_short buf ty =
  match Constr.kind ty with
  | Constr.Ind iu ->
      let (mutind, i) = Univ.out_punivs iu in
      let env = Global.env () in
      let mutind_body = Environ.lookup_mind mutind env in
      Buffer.add_string buf (Id.to_string mutind_body.Declarations.mind_packets.(i).Declarations.mind_typename)
  | Constr.App (f, argsary) ->
      mangle_type_buf_short buf f;
      Array.iter (fun arg -> Buffer.add_char buf '_'; mangle_type_buf_short buf arg) argsary
  | Constr.Prod (name, ty, body) ->
      mangle_type_buf_short buf ty;
      Buffer.add_string buf "_to_";
      mangle_type_buf_short buf body
  | Constr.Rel i -> raise (CodeGenError "mangle_type_buf_short:rel")
  | Constr.Var name -> raise (CodeGenError "mangle_type_buf_short:var")
  | Constr.Meta i -> raise (CodeGenError "mangle_type_buf_short:meta")
  | Constr.Evar (ekey, termary) -> raise (CodeGenError "mangle_type_buf_short:evar")
  | Constr.Sort s -> raise (CodeGenError "mangle_type_buf_short:sort")
  | Constr.Cast (expr, kind, ty) -> raise (CodeGenError "mangle_type_buf_short:cast")
  | Constr.Lambda (name, ty, body) -> raise (CodeGenError "mangle_type_buf_short:lambda")
  | Constr.LetIn (name, expr, ty, body) -> raise (CodeGenError "mangle_type_buf_short:letin")
  | Constr.Const cu -> raise (CodeGenError "mangle_type_buf_short:const")
  | Constr.Construct cu -> raise (CodeGenError "mangle_type_buf_short:construct")
  | Constr.Case (ci, tyf, expr, brs) -> raise (CodeGenError "mangle_type_buf_short:case")
  | Constr.Fix ((ia, i), (nameary, tyary, funary)) -> raise (CodeGenError "mangle_type_buf_short:fix")
  | Constr.CoFix (i, (nameary, tyary, funary)) -> raise (CodeGenError "mangle_type_buf_short:cofix")
  | Constr.Proj (proj, expr) -> raise (CodeGenError "mangle_type_buf_short:proj")
  | Constr.Int n -> raise (CodeGenError "mangle_type_buf_short:int")

let mangle_type_buf buf ty =
  mangle_type_buf_short buf ty

let mangle_type ty =
  let buf = Buffer.create 0 in
  mangle_type_buf buf ty;
  Buffer.contents buf

type cstr_config = {
  coq_cstr : Id.t;
  c_cstr : string option;
  c_caselabel : string; (* meaningful if c_swfnc is not None *)
  c_accessors : string array (* meaningful if c_swfnc is not None *)
}

type ind_config = {
  coq_type : Constr.t;
  c_type : string;
  c_swfunc : string option;
  cstr_configs : cstr_config array
}

type ind_cstr_caselabel_accessors = Id.t * string * string list

type s_or_d = SorD_S | SorD_D

let pr_s_or_d sd =
  match sd with
  | SorD_S -> Pp.str "s"
  | SorD_D -> Pp.str "d"

let drop_trailing_d sd_list =
  List.fold_right (fun sd l -> match (sd,l) with (SorD_D,[]) -> [] | _ -> sd :: l) sd_list []

type id_or_underscore = Id.t option
type constr_or_underscore = Constrexpr.constr_expr option

type sp_instance_names = {
  spi_cfunc_name : string option;
  spi_partapp_id : Id.t option;
  spi_specialized_id : Id.t option
}

