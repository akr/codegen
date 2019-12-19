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

let out_punivs : 'a EConstr.puniverses -> 'a = fst

let rec mangle_type_buf (buf : Buffer.t) (ty : EConstr.t) : unit =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  match EConstr.kind sigma ty with
  | Constr.Ind iu ->
      let (mutind, i) = out_punivs iu in
      let env = Global.env () in
      let mutind_body = Environ.lookup_mind mutind env in
      Buffer.add_string buf (Id.to_string mutind_body.Declarations.mind_packets.(i).Declarations.mind_typename)
  | Constr.App (f, argsary) ->
      mangle_type_buf buf f;
      Array.iter (fun arg -> Buffer.add_char buf '_'; mangle_type_buf buf arg) argsary
  | Constr.Prod (name, ty, body) ->
      mangle_type_buf buf ty;
      Buffer.add_string buf "_to_";
      mangle_type_buf buf body
  | Constr.Rel i -> user_err (Pp.str "mangle_type_buf:rel:")
  | Constr.Var name -> user_err (Pp.str "mangle_type_buf:var:")
  | Constr.Meta i -> user_err (Pp.str "mangle_type_buf:meta:")
  | Constr.Evar (ekey, termary) -> user_err (Pp.str "mangle_type_buf:evar:")
  | Constr.Sort s -> user_err (Pp.str "mangle_type_buf:sort:")
  | Constr.Cast (expr, kind, ty) -> user_err (Pp.str "mangle_type_buf:cast:")
  | Constr.Lambda (name, ty, body) -> user_err (Pp.str "mangle_type_buf:lambda:")
  | Constr.LetIn (name, expr, ty, body) -> user_err (Pp.str "mangle_type_buf:letin:")
  | Constr.Const cu -> user_err (Pp.str "mangle_type_buf:const:" ++ Pp.spc () ++ Printer.pr_econstr_env env sigma ty)
  | Constr.Construct cu -> user_err (Pp.str "mangle_type_buf:construct:")
  | Constr.Case (ci, tyf, expr, brs) -> user_err (Pp.str "mangle_type_buf:case:")
  | Constr.Fix ((ia, i), (nameary, tyary, funary)) -> user_err (Pp.str "mangle_type_buf:fix:")
  | Constr.CoFix (i, (nameary, tyary, funary)) -> user_err (Pp.str "mangle_type_buf:cofix:")
  | Constr.Proj (proj, expr) -> user_err (Pp.str "mangle_type_buf:proj:")
  | Constr.Int n -> user_err (Pp.str "mangle_type_buf:int:")

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
    user_err (Pp.str "invalid C name:" ++ Pp.spc () ++ Pp.str str)

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

let mangle_type (ty : EConstr.t) : string =
  let buf = Buffer.create 0 in
  mangle_type_buf buf ty;
  Buffer.contents buf

let rec count_evars (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : int =
  match EConstr.kind sigma term with
  | Constr.Rel _ | Constr.Var _ | Constr.Meta _ | Constr.Sort _ | Constr.Ind _
  | Constr.Int _ | Constr.Const _ | Constr.Construct _ -> 0
  | Constr.Evar _ -> 1
  | Constr.Proj (proj, e) -> count_evars env sigma e
  | Constr.Cast (e,ck,t) -> count_evars env sigma e + count_evars env sigma t
  | Constr.App (f, args) ->
      count_evars env sigma f +
      Array.fold_left (fun n arg -> n + count_evars env sigma arg) 0 args
  | Constr.LetIn (x,e,t,b) ->
      let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
      let env2 = EConstr.push_rel decl env in
      let ne = count_evars env sigma e in
      let nt = count_evars env sigma t in
      let nb = count_evars env2 sigma b in
      ne + nt + nb
  | Constr.Case (ci, p, item, branches) ->
      let np = count_evars env sigma p in
      let nitem = count_evars env sigma item in
      let nbranches = Array.fold_left (fun n arg -> n + count_evars env sigma arg) 0 branches in
      np + nitem + nbranches
  | Constr.Prod (x,t,b) | Constr.Lambda (x,t,b) ->
      let decl = Context.Rel.Declaration.LocalAssum (x, t) in
      let env2 = EConstr.push_rel decl env in
      let nt = count_evars env sigma t in
      let nb = count_evars env2 sigma b in
      nt + nb
  | Constr.Fix ((_, _), ((nameary, tary, fary) as prec))
  | Constr.CoFix (_, ((nameary, tary, fary) as prec)) ->
      let env2 = EConstr.push_rec_types prec env in
      let ntary = Array.fold_left (fun n ty -> n + count_evars env sigma ty) 0 tary in
      let nfary = Array.fold_left (fun n f -> n + count_evars env2 sigma f) 0 fary in
      ntary + nfary

let abstract_evars (env : Environ.env) (sigma : Evd.evar_map) (term : EConstr.t) : EConstr.t =
  let nb_rel_env0 = Environ.nb_rel env in
  let nevars = count_evars env sigma term in
  let nextrel = ref 0 in
  let etypes = ref [] in
  let rec aux1 env term =
    match EConstr.kind sigma term with
    | Constr.Rel _ | Constr.Var _ | Constr.Meta _ | Constr.Sort _ | Constr.Ind _
    | Constr.Int _ | Constr.Const _ | Constr.Construct _ -> term
    | Constr.Evar _ ->
        let ety = Retyping.get_type_of env sigma term in
        let ety = Reductionops.nf_all env sigma ety in
        (if not (EConstr.Vars.closed0 sigma ety) then
          user_err (Pp.str "type is not a closed term:" ++ Pp.spc () ++ Printer.pr_econstr_env env sigma ety));
        (if Evarutil.has_undefined_evars sigma ety then
          user_err (Pp.str "type of a hole contains a existential variable:" ++ Pp.spc() ++
            Printer.pr_econstr_env env sigma term ++
            Pp.spc () ++ Pp.str ":" ++ Pp.spc () ++
            Printer.pr_econstr_env env sigma ety));
        let i = !nextrel in
        nextrel := i + 1;
        etypes := ety :: !etypes;
        EConstr.mkRel (Environ.nb_rel env - nb_rel_env0 + nevars - i)
    | Constr.Proj (proj, e) -> EConstr.mkProj (proj, aux1 env e)
    | Constr.Cast (e,ck,t) -> EConstr.mkCast (aux1 env e, ck, aux1 env t)
    | Constr.App (f, args) ->
        let f' = aux1 env f in
        let args' = Array.map (aux1 env) args in (* assume left-to-right *)
        EConstr.mkApp (f', args')
    | Constr.LetIn (x,e,t,b) ->
        let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
        let env2 = EConstr.push_rel decl env in
        let e' = aux1 env e in
        let t' = aux1 env t in
        let b' = aux1 env2 b in
        EConstr.mkLetIn (x,e',t',b')
    | Constr.Case (ci, p, item, branches) ->
        let p' = aux1 env p in
        let item' = aux1 env item in
        let branches' = Array.map (aux1 env) branches in
        EConstr.mkCase (ci, p', item', branches')
    | Constr.Prod (x,t,b) ->
        let decl = Context.Rel.Declaration.LocalAssum (x, t) in
        let env2 = EConstr.push_rel decl env in
        let t' = aux1 env t in
        let b' = aux1 env2 b in
        EConstr.mkProd (x,t',b')
    | Constr.Lambda (x,t,b) ->
        let decl = Context.Rel.Declaration.LocalAssum (x, t) in
        let env2 = EConstr.push_rel decl env in
        let t' = aux1 env t in
        let b' = aux1 env2 b in
        EConstr.mkLambda (x,t',b')
    | Constr.Fix ((ia, i), ((nary, tary, fary) as prec)) ->
        let env2 = EConstr.push_rec_types prec env in
        let tary' = Array.map (aux1 env) tary in
        let fary' = Array.map (aux1 env2) fary in
        EConstr.mkFix ((ia, i), (nary, tary', fary'))
    | Constr.CoFix (i, ((nary, tary, fary) as prec)) ->
        let env2 = EConstr.push_rec_types prec env in
        let tary' = Array.map (aux1 env) tary in
        let fary' = Array.map (aux1 env2) fary in
        EConstr.mkCoFix (i, (nary, tary', fary'))
  in
  let rec aux2 etypes term =
    match etypes with
    | [] -> term
    | ety :: etypes' ->
        let x = Context.annotR (Namegen.named_hd env sigma ety Name.Anonymous) in
        aux2 etypes' (EConstr.mkLambda (x, ety, term))
  in
  let term = EConstr.Vars.lift nevars term in
  let term = aux2 !etypes (aux1 env term) in
  ignore (Typing.type_of env sigma term); (* (@eq_refl nat _ : @eq nat _ _) should be rejected *)
  term

let detect_recursive_functions (ctnt_i : Constant.t) : (int * Constant.t option array) option =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let modpath = KerName.modpath (Constant.canonical ctnt_i) in
  match Global.body_of_constant ctnt_i with
  | None -> user_err (Pp.str "couldn't obtain the definition of" ++ Pp.spc () ++
                      Printer.pr_constant env ctnt_i)
  | Some (def_i,_) ->
      let def_i = EConstr.of_constr def_i in
      let (ctx_rel_i, body_i) = EConstr.decompose_lam_assum sigma def_i in
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
                      match Global.body_of_constant ctnt_j with
                      | None -> None
                      | Some (def_j,_) ->
                          let def_j = EConstr.of_constr def_j in
                          let body_j' = EConstr.mkFix ((ia, j), (nary, tary, fary)) in
                          let def_j' = EConstr.it_mkLambda_or_LetIn body_j' ctx_rel_i in
                          if EConstr.eq_constr sigma def_j def_j' then
                            Some ctnt_j
                          else
                            None
                    with Not_found -> None)
            nary
          in
          Some (i, ctnt_ary)
      | _ -> None

let constr_name (sigma : Evd.evar_map) (term : EConstr.t) : string =
  match EConstr.kind sigma term with
  | Constr.Rel _ -> "Rel"
  | Constr.Var _ -> "Var"
  | Constr.Meta _ -> "Meta"
  | Constr.Evar _ -> "Evar"
  | Constr.Sort _ -> "Sort"
  | Constr.Cast _ -> "Cast"
  | Constr.Prod _ -> "Prod"
  | Constr.Lambda _ -> "Lambda"
  | Constr.LetIn _ -> "LetIn"
  | Constr.App _ -> "App"
  | Constr.Const _ -> "Const"
  | Constr.Ind _ -> "Ind"
  | Constr.Construct _ -> "Construct"
  | Constr.Case _ -> "Case"
  | Constr.Fix _ -> "Fix"
  | Constr.CoFix _ -> "CoFix"
  | Constr.Proj _ -> "Proj"
  | Constr.Int _ -> "Int"

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

