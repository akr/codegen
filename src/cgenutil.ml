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
open Globnames
open Pp
open CErrors
open Goptions

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

let array_for_all f a =
  try Array.iter (fun x -> if f x then () else raise Exit) a; true
  with Exit -> false

let array_exists f a =
  try Array.iter (fun x -> if f x then raise Exit) a; false
  with Exit -> true

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
  match Term.kind_of_term ty with
  | Term.Ind iu ->
      let (mutind, i) = Univ.out_punivs iu in
      let ((evd : Evd.evar_map), (env : Environ.env)) = Lemmas.get_current_context () in
      let mutind_body = Environ.lookup_mind mutind env in
      Buffer.add_string buf (Id.to_string mutind_body.Declarations.mind_packets.(i).Declarations.mind_typename)
  | Term.App (f, argsary) ->
      mangle_type_buf_short buf f;
      Array.iter (fun arg -> Buffer.add_char buf '_'; mangle_type_buf_short buf arg) argsary
  | Term.Prod (name, ty, body) ->
      mangle_type_buf_short buf ty;
      Buffer.add_string buf "_to_";
      mangle_type_buf_short buf body
  | Term.Rel i -> raise (CodeGenError "mangle_type_buf_short:rel")
  | Term.Var name -> raise (CodeGenError "mangle_type_buf_short:var")
  | Term.Meta i -> raise (CodeGenError "mangle_type_buf_short:meta")
  | Term.Evar (ekey, termary) -> raise (CodeGenError "mangle_type_buf_short:evar")
  | Term.Sort s -> raise (CodeGenError "mangle_type_buf_short:sort")
  | Term.Cast (expr, kind, ty) -> raise (CodeGenError "mangle_type_buf_short:cast")
  | Term.Lambda (name, ty, body) -> raise (CodeGenError "mangle_type_buf_short:lambda")
  | Term.LetIn (name, expr, ty, body) -> raise (CodeGenError "mangle_type_buf_short:letin")
  | Term.Const cu -> raise (CodeGenError "mangle_type_buf_short:const")
  | Term.Construct cu -> raise (CodeGenError "mangle_type_buf_short:construct")
  | Term.Case (ci, tyf, expr, brs) -> raise (CodeGenError "mangle_type_buf_short:case")
  | Term.Fix ((ia, i), (nameary, tyary, funary)) -> raise (CodeGenError "mangle_type_buf_short:fix")
  | Term.CoFix (i, (nameary, tyary, funary)) -> raise (CodeGenError "mangle_type_buf_short:cofix")
  | Term.Proj (proj, expr) -> raise (CodeGenError "mangle_type_buf_short:proj")

let rec mangle_type_buf buf ty =
  mangle_type_buf_short buf ty

let mangle_type ty =
  let buf = Buffer.create 0 in
  mangle_type_buf buf ty;
  Buffer.contents buf

