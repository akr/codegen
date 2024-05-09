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

let array_find_opt (f : 'a -> bool) (ary : 'a array) : 'a option =
  match int_find_opt (fun i -> f ary.(i)) (Array.length ary) with
  | None -> None
  | Some i -> Some ary.(i)

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

let array_count_sub (p : 'a -> bool) (ary : 'a array) (i : int) (n : int) : int =
  let rec aux i n acc =
    if n <= 0 then
      acc
    else
      if p ary.(i) then
        aux (i+1) (n-1) (acc+1)
      else
        aux (i+1) (n-1) acc
  in
  aux i n 0

let array_count (p : 'a -> bool) (ary : 'a array) (i : int) (n : int) : int = array_count_sub p ary 0 (Array.length ary)

let boolarray_count_sub (ary : bool array) (i : int) (n : int) : int =
  let rec aux i n acc =
    if n <= 0 then
      acc
    else
      if ary.(i) then
        aux (i+1) (n-1) (acc+1)
      else
        aux (i+1) (n-1) acc
  in
  aux i n 0

let boolarray_count (ary : bool array) : int =
  boolarray_count_sub ary 0 (Array.length ary)

let array_filter_with (filter : bool array)
    ?(result_length = boolarray_count filter)
    (ary : 'a array) : 'a array =
  let n = Array.length ary in
  if Array.length filter <> n then
    invalid_arg "array_filter_with";
  if CArray.is_empty ary then
    begin
      if result_length <> 0 then
        invalid_arg "array_filter_with(result_length)";
      [||]
    end
  else
    begin
      let result = Array.make result_length ary.(0) in
      let j = ref 0 in
      for i = 0 to n-1 do
        if filter.(i) then
          begin
            (if result_length <= !j then
              invalid_arg "array_filter_with(result_length)");
            result.(!j) <- ary.(i);
            j := !j + 1;
          end
      done;
      if result_length <> !j then
        invalid_arg "array_filter_with(result_length)";
      result
    end

let ncons n x s = CList.addn n x s

let rec ntimes n f v =
  if n = 0 then
    v
  else
    ntimes (n-1) f (f v)

let rcons s v =
  List.append s [v]

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

let list_find_suffix (f : 'a -> bool) (l : 'a list) : 'a list =
  let rec aux l =
    match l with
    | [] -> raise Not_found
    | x :: l' -> if f x then l else aux l'
  in
  aux l

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

let intset_union_list (sets : IntSet.t list) : IntSet.t =
  intset_union_ary (Array.of_list sets)

let intset_union3 (set1 : IntSet.t) (set2 : IntSet.t) (set3 : IntSet.t) : IntSet.t =
  IntSet.union (IntSet.union set1 set2) set3

let idset_union_list (s : Id.Set.t list) =
  List.fold_left Id.Set.union Id.Set.empty s

let idset_union_ary (ary : Id.Set.t array) =
  Array.fold_left Id.Set.union Id.Set.empty ary

let stringset_union_list (s : StringSet.t list) : StringSet.t =
  List.fold_left StringSet.union StringSet.empty s

let reachable (start : IntSet.t) (edge : int -> IntSet.t) : IntSet.t =
  let rec loop q result =
    match IntSet.choose_opt q with
    | Some i ->
        let q = IntSet.remove i q in
        let nexts = edge i in
        let q = IntSet.union q (IntSet.diff nexts result) in
        let result = IntSet.union nexts result in
        loop q result
    | None ->
        result
  in
  loop start start

type unionfind_t = int array

let unionfind_make (n : int) : unionfind_t =
  Array.init n (fun i -> i)

let rec unionfind_find (u : unionfind_t) (i : int) : int =
  if u.(i) = i then
    i
  else
    let j = unionfind_find u u.(i) in
    u.(i) <- j;
    j

(* We don't consider the rank (depth) here.
   It may make the algorithm slower but
   it makes us possible to guarantee that the representative is smallest element. *)
let unionfind_union (u : unionfind_t) (i : int) (j : int) : unit =
  let i = unionfind_find u i in
  let j = unionfind_find u j in
  if i < j then
    u.(j) <- i
  else if j < i then
    u.(i) <- j

let unionfind_sets (u : unionfind_t) : int list list =
  let n = Array.length u in
  let sets = Array.make n [] in
  for i = n-1 downto 0 do
    let j = unionfind_find u i in
    sets.(j) <- i :: sets.(j)
  done;
  let result = ref [] in
  for i = n-1 downto 0 do
    if not (CList.is_empty sets.(i)) then
      result := sets.(i) :: !result
  done;
  !result

let idset_of_array (ary : Id.t array) : Id.Set.t =
  Array.fold_right Id.Set.add ary Id.Set.empty

let idmap_of_list (bindings : (Id.t * 'a) list) : 'a Id.Map.t =
  List.fold_left
    (fun m (id, v) -> Id.Map.add id v m)
    Id.Map.empty
    bindings

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

let msg_info_v pp =
  Feedback.msg_info (Pp.v 2 pp)

let msg_debug_v pp =
  Feedback.msg_debug (Pp.v 2 pp)

let format_deep (pp : Pp.t) : string =
  let buf = Buffer.create 0 in
  let fmt = Format.formatter_of_buffer buf in
  Format.pp_set_max_boxes fmt max_int;
  Pp.pp_with fmt pp;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

let pr_deep (pp : Pp.t) : Pp.t =
  Pp.str (format_deep pp)

let disjoint_id_map_union (m1 : 'a Id.Map.t) (m2 : 'a Id.Map.t) : 'a Id.Map.t =
  Id.Map.union
    (fun id b1 b2 -> user_err (Pp.str "[codegen:bug] unexpected duplicated variable name:" +++ Id.print id))
    m1 m2

let disjoint_id_map_union_ary (ms : 'a Id.Map.t array) : 'a Id.Map.t =
  Array.fold_left
    (fun m0 m1 ->
      disjoint_id_map_union m0 m1)
    Id.Map.empty ms

let disjoint_id_map_union_list (ms : 'a Id.Map.t list) : 'a Id.Map.t =
  List.fold_left
    (fun m0 m1 ->
      disjoint_id_map_union m0 m1)
    Id.Map.empty ms

let env_push_assum (env : Environ.env) (x : Names.Name.t Context.binder_annot) (t : EConstr.types) : Environ.env =
  let decl = Context.Rel.Declaration.LocalAssum (x, t) in
  let env2 = EConstr.push_rel decl env in
  env2

(* assums is a list of (name,type).
  The innermost assumption is first.  *)
let env_push_assums (env : Environ.env) (assums : (Names.Name.t Context.binder_annot * EConstr.types) list) : Environ.env =
  let ctx = List.map (fun (x,t) -> Context.Rel.Declaration.LocalAssum (x,t)) assums in
  let env2 = EConstr.push_rel_context ctx env in
  env2

let env_push_def (env : Environ.env) (x : Names.Name.t Context.binder_annot) (e : EConstr.t) (t : EConstr.types) : Environ.env =
  let decl = Context.Rel.Declaration.LocalDef (x, e, t) in
  let env2 = EConstr.push_rel decl env in
  env2

(* defs is a list of (name,exp,type).
  The innermost definition is first.  *)
let env_push_defs (env : Environ.env) (defs : (Names.Name.t Context.binder_annot * EConstr.t * EConstr.types) list) : Environ.env =
  let ctx = List.map (fun (x,e,t) -> Context.Rel.Declaration.LocalDef (x,e,t)) defs in
  let env2 = EConstr.push_rel_context ctx env in
  env2

let env_push_fix (env : Environ.env) (prec : (EConstr.t, EConstr.t) Constr.prec_declaration) : Environ.env =
  let env2 = push_rec_types prec env in
  env2

let is_monomorphic_type (env : Environ.env) (sigma : Evd.evar_map) (ty : EConstr.t) : bool =
  let rec aux env ty =
    match EConstr.kind sigma ty with
    | Prod (x,t,b) ->
        let env2 = env_push_assum env x t in
        aux env t &&
        aux env2 b
    | Ind _ -> true
    | App (f,args) when isInd sigma f ->
        Array.for_all (aux env) args
    | _ -> false
  in
  aux env ty

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
        let env2 = env_push_assum env x t in
        decompose_lam_n_env env2 sigma (n-1) e
    | _ ->
      user_err (Pp.str "[codegen:bug:decompose_lam_n_env] unexpected non-lambda term:" +++ Printer.pr_econstr_env env sigma term)

(* The innermost let binding is appeared first in the result:
  Here, "exp" means AST of exp, not string.

    decompose_lets
      "let x : nat := 0 in
       let y : nat := 1 in
       let z : nat := 2 in
      body"

  returns

    ([("z","2","nat"); ("y","1","nat"); ("x","0","nat")], "body")

  This order of bindings is same as Constr.rel_context used by
  Environ.push_rel_context.
*)
let decompose_lets (sigma : Evd.evar_map) (term : EConstr.t) : (Name.t Context.binder_annot * EConstr.t * EConstr.types) list * EConstr.t =
  let rec aux term defs =
    match EConstr.kind sigma term with
    | LetIn (x, e, ty, b) ->
        aux b ((x, e, ty) :: defs)
    | _ -> (defs, term)
  in
  aux term []

let rec compose_lets (defs : (Name.t Context.binder_annot * EConstr.t * EConstr.types) list) (body : EConstr.t) : EConstr.t =
  match defs with
  | [] -> body
  | (x,e,ty) :: rest ->
      compose_lets rest (mkLetIn (x, e, ty, body))

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

let nf_interp_constr (env : Environ.env) (sigma : Evd.evar_map) (t : Constrexpr.constr_expr) : Evd.evar_map * EConstr.t =
  let (sigma, t) = Constrintern.interp_constr_evars env sigma t in
  let t = Reductionops.nf_all env sigma t in
  (sigma, t)

let nf_interp_type (env : Environ.env) (sigma : Evd.evar_map) (t : Constrexpr.constr_expr) : Evd.evar_map * EConstr.t =
  let (sigma, t) = Constrintern.interp_type_evars env sigma t in
  let t = Reductionops.nf_all env sigma t in
  (sigma, t)

let out_punivs : 'a EConstr.puniverses -> 'a = fst

let inductive_abstract_constructor_type_relatively_to_inductive_types_context_nflc (ntypes : int) (mutind : MutInd.t) (nf_lc : Constr.rel_context * Constr.types) : Constr.rel_context * Constr.types =
  let (ctx, t) = nf_lc in
  let t = Term.it_mkProd_or_LetIn t ctx in
  let t = Inductive.abstract_constructor_type_relatively_to_inductive_types_context ntypes mutind t in
  Term.decompose_prod_decls t

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
      let env2 = env_push_assum env x t in
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
  | Proj (proj, r, expr) -> user_err (Pp.str "[codegen] mangle_term_buf:proj:")
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
      EConstr.fold_with_binders sigma Stdlib.Int.succ
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
  | Constrexpr.CGenarg _ -> "CGenarg"
  | Constrexpr.CGenargGlob _ -> "CGenargGlob"

let global_gensym ?(prefix : string = "g") () : string =
  let n = !gensym_id in
  gensym_id := n + 1;
  prefix ^ string_of_int n

let global_gensym_with_string (s : string) : string =
  global_gensym () ^ "_" ^ s

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
    | Proj (proj, r, e) ->
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

let check_convertible (phase : string) (env : Environ.env) (sigma : Evd.evar_map) (t1 : EConstr.t) (t2 : EConstr.t) : unit =
  if Reductionops.is_conv env sigma t1 t2 then
    ()
  else
    user_err (Pp.v 2 (Pp.hov 0 (Pp.str "[codegen] translation inconvertible:" +++ Pp.str phase) ++
      Pp.fnl () ++
      Printer.pr_econstr_env env sigma t1 ++ Pp.fnl () ++
      Pp.str "=/=>" ++ Pp.fnl () ++
      Printer.pr_econstr_env env sigma t2))

let show_goals () : unit Proofview.tactic =
  Proofview.Goal.enter begin fun g ->
    let env = Proofview.Goal.env g in
    let sigma = Proofview.Goal.sigma g in
    let concl = Proofview.Goal.concl g in
    Feedback.msg_debug (Pp.str "[codegen] goal:" +++ Printer.pr_econstr_env env sigma concl);
    Proofview.tclUNIT ()
  end

let lib_ref (env : Environ.env) (sigma : Evd.evar_map) (name : string) : Evd.evar_map * EConstr.t =
  let gr = Coqlib.lib_ref name in
  fresh_global env sigma gr

let exact_term_eq (sigma : Evd.evar_map) (t1 : EConstr.t) (t2 : EConstr.t) : bool =
  let name_equal x1 x2 = Context.eq_annot Names.Name.equal x1 x2 in
  let instance_equal u1 u2 = UVars.Instance.equal (EInstance.kind sigma u1) (EInstance.kind sigma u2) in
  let rec eq t1 t2 =
    match EConstr.kind sigma t1, EConstr.kind sigma t2 with
    | Rel n1, Rel n2 -> Int.equal n1 n2
    | Meta m1, Meta m2 -> Int.equal m1 m2
    | Var id1, Var id2 -> Id.equal id1 id2
    | Int i1, Int i2 -> Uint63.equal i1 i2
    | Float f1, Float f2 -> Float64.equal f1 f2
    | Sort s1, Sort s2 -> Sorts.equal (ESorts.kind sigma s1) (ESorts.kind sigma s2)
    | Cast (c1,kind1,t1), Cast (c2,kind2,t2) -> kind1 = kind2 && eq c1 c2 && eq t1 t2
    | Prod (x1,t1,c1), Prod (x2,t2,c2) -> name_equal x1 x2 && eq t1 t2 && eq c1 c2
    | Lambda (x1,t1,c1), Lambda (x2,t2,c2) -> name_equal x1 x2 && eq t1 t2 && eq c1 c2
    | LetIn (x1,b1,t1,c1), LetIn (x2,b2,t2,c2) -> name_equal x1 x2 && eq b1 b2 && eq t1 t2 && eq c1 c2
    | App (c1, l1), App (c2, l2) ->
      let len = Array.length l1 in
      Int.equal len (Array.length l2) &&
      eq c1 c2 && CArray.equal eq l1 l2
    | Proj (p1,r1,c1), Proj (p2,r2,c2) -> Projection.CanOrd.equal p1 p2 && eq c1 c2
    | Evar (e1,l1), Evar (e2,l2) -> Evar.equal e1 e2 && SList.equal eq l1 l2
    | Const (c1,u1), Const (c2,u2) ->
      Constant.CanOrd.equal c1 c2 && instance_equal u1 u2
    | Ind (c1,u1), Ind (c2,u2) -> Ind.CanOrd.equal c1 c2 && instance_equal u1 u2
    | Construct (c1,u1), Construct (c2,u2) ->
      Construct.CanOrd.equal c1 c2 && instance_equal u1 u2
    | Case (ci1,u1,pms1,((nas1,p1),sr1),iv1,c1,bl1), Case (ci2,u2,pms2,((nas2,p2),sr2),iv2,c2,bl2) ->
      Ind.CanOrd.equal ci1.ci_ind ci2.ci_ind && instance_equal u1 u2 &&
      CArray.equal eq pms1 pms2 && CArray.equal name_equal nas1 nas2 && eq p1 p2 &&
      eq_invert eq iv1 iv2 &&
      eq c1 c2 &&
      CArray.equal (fun (nas1,bl1) (nas2,bl2) -> CArray.equal name_equal nas1 nas2 && eq bl1 bl2) bl1 bl2
    | Fix ((ln1, i1),(xl1,tl1,bl1)), Fix ((ln2, i2),(xl2,tl2,bl2)) ->
      Int.equal i1 i2 && CArray.equal Int.equal ln1 ln2 &&
      CArray.equal name_equal xl1 xl2 &&
      CArray.equal eq tl1 tl2 && CArray.equal eq bl1 bl2
    | CoFix(ln1,(xl1,tl1,bl1)), CoFix(ln2,(xl2,tl2,bl2)) ->
      Int.equal ln1 ln2 &&
      CArray.equal name_equal xl1 xl2 &&
      CArray.equal eq tl1 tl2 && CArray.equal eq bl1 bl2
    | Array(u1,t1,def1,ty1), Array(u2,t2,def2,ty2) ->
      instance_equal u1 u2 &&
      CArray.equal eq t1 t2 &&
      eq def1 def2 && eq ty1 ty2
    | (Rel _ | Meta _ | Var _ | Sort _ | Cast _ | Prod _ | Lambda _ | LetIn _ | App _
      | Proj _ | Evar _ | Const _ | Ind _ | Construct _ | Case _ | Fix _
      | CoFix _ | Int _ | Float _| Array _), _ -> false
  in
  eq t1 t2

(*
  pp_side_chars analyses Pp.t to detect beginning and ending characters to
  decide inserting a space between C tokens or not.

  For example, we insert a space between (Pp.str "int") and (Pp.str "foo").
  But we don't insert a space between (Pp.str "int *") and (Pp.str "foo").

  Fortunately, variable part in Pp.t is only white spaces, Ppcmd_print_break.
  Thus, the beginning/ending character of a formatted Pp.t can be
  (1) single fixed character generated by Pp.str, or
  (2) single fixed character generated or a whitespace generated by Pp.brk.

  (Ppcmd_force_newline and Ppcmd_comment can be considered as
  Ppcmd_string because they does not generate empty string.)

  Since the white spaces cannot be a part of C token,
  we only need to know the characters generated by Ppcmd_string
  for deciding space requirement between C tokens.

  Thus, pp_side_chars pp = NotEmpty (c1, c2) means
  - formatted pp can start with c1 or a whitespace, and
  - formatted pp can end with c2 or a whitespace.
*)

type pp_sides =
| AlwaysEmpty
| WheteSpaceOrEmpty
| NotEmpty of char * char

let rec pp_side_chars (pp : Pp.t) : pp_sides =
  pp_side_chars_rec (Pp.repr pp)
and pp_side_chars_rec (doc : Pp.doc_view) : pp_sides =
  let open Pp in
  match doc with
  | Ppcmd_empty -> AlwaysEmpty
  | Ppcmd_string str ->
      if CString.is_empty str then
        AlwaysEmpty
      else
        NotEmpty (str.[0], str.[String.length str - 1])
  | Ppcmd_glue pps ->
      (*
        - zero or more AlwaysEmpty, no WheteSpaceOrEmpty, no NotEmpty -> AlwaysEmpty
        - zero or more AlwaysEmpty, one or more WheteSpaceOrEmpty, no NotEmpty -> WheteSpaceOrEmpty
        - zero or more AlwaysEmpty, zero or more WheteSpaceOrEmpty, one or more NotEmpty -> NotEmpty
      *)
      let rec start sides_list =
        match sides_list with
        | [] -> AlwaysEmpty
        | AlwaysEmpty :: rest -> start rest
        | WheteSpaceOrEmpty :: rest -> found_WheteSpaceOrEmpty rest
        | NotEmpty (c1,c2) :: rest -> found_NotEmpty (c1, c2) rest
      and found_WheteSpaceOrEmpty sides_list =
        match sides_list with
        | [] -> WheteSpaceOrEmpty
        | AlwaysEmpty :: rest -> found_WheteSpaceOrEmpty rest
        | WheteSpaceOrEmpty :: rest -> found_WheteSpaceOrEmpty rest
        | NotEmpty (c1,c2) :: rest -> found_NotEmpty (c1, c2) rest
      and found_NotEmpty (c1, c2) sides_list =
        match sides_list with
        | [] -> NotEmpty (c1, c2)
        | AlwaysEmpty :: rest -> found_NotEmpty (c1, c2) rest
        | WheteSpaceOrEmpty :: rest -> found_NotEmpty (c1, c2) rest
        | NotEmpty (c3,c4) :: rest -> found_NotEmpty (c1, c4) rest
      in
      start (List.map pp_side_chars pps)
  | Ppcmd_box (_, pp) -> pp_side_chars pp
  | Ppcmd_tag (_, pp) -> pp_side_chars pp
  | Ppcmd_print_break (nspaces, offset) ->
      if nspaces = 0 then
        WheteSpaceOrEmpty
      else
        NotEmpty (' ', ' ')
  | Ppcmd_force_newline -> NotEmpty (' ', ' ')
  | Ppcmd_comment strs ->
      let strs = List.filter (fun s -> not (CString.is_empty s)) strs in
      (match strs with
      | [] -> AlwaysEmpty
      | s1 :: _ ->
          let s2 = CList.last strs in
          NotEmpty (s1.[0], s2.[String.length s2 - 1]))

let c_needs_space_between_chars (c1 : char) (c2 : char) =
  match c1, c2 with
  | ('0'..'9' | 'a'..'z' | 'A'..'Z' | '_'), ('0'..'9' | 'a'..'z' | 'A'..'Z' | '_') -> true (* identifier, integer-constant, etc. *)
  | 'L', '\'' -> true  (* character-constant: L'c-char-sequence' *)
  | 'L', '"' -> true  (* string-literal: L"s-char-sequence-opt" *)
  | ('0'..'9' | 'a'..'f' | 'A'..'F'), '.' -> true (* fractional-constant, hexadecimal-floating-constant *)
  | '!', '=' -> true (* punctuator != *)
  | '#', '#' -> true (* punctuator ## *)
  | '%', ':' -> true (* punctuator %: *)
  | ':', '%' -> true (* punctuator %:%: *)
  | '%', '=' -> true (* punctuator %= *)
  | '%', '>' -> true (* punctuator %> *)
  | '&', '&' -> true (* punctuator && *)
  | '&', '=' -> true (* punctuator &= *)
  | '*', '=' -> true (* punctuator *= *)
  | '+', '+' -> true (* punctuator ++ *)
  | '+', '=' -> true (* punctuator += *)
  | '-', '-' -> true (* punctuator -- *)
  | '-', '=' -> true (* punctuator -= *)
  | '-', '>' -> true (* punctuator -> *)
  | '.', '.' -> true (* punctuator ... *)
  | '/', '=' -> true (* punctuator /= *)
  | ':', '>' -> true (* punctuator :> *)
  | '<', '%' -> true (* punctuator <% *)
  | '<', ':' -> true (* punctuator <: *)
  | '<', '<' -> true (* punctuator << *)
  | '<', '=' -> true (* punctuator <<=, <= *)
  | '=', '=' -> true (* punctuator == *)
  | '>', '=' -> true (* punctuator >=, >>= *)
  | '>', '>' -> true (* punctuator >> *)
  | '^', '=' -> true (* punctuator ^= *)
  | '|', '=' -> true (* punctuator |= *)
  | '|', '|' -> true (* punctuator || *)
  | _, _ -> false

let c_needs_space_between_tokens (str1 : string) (str2 : string) =
  if CString.is_empty str1 || CString.is_empty str2 then
    false
  else
    c_needs_space_between_chars str1.[String.length str1 - 1] str2.[0]

let str_first_non_white_space_character (s : string) : char option =
  let n = String.length s in
  let rec f i =
    if i < n then
      let c = s.[i] in
      match c with
      | ' ' |
        '\t' |
        '\r' |
        '\n' |
        '\x0B' | (* vertical tab *)
        '\x0C' (* form feed *)
        -> f (i+1)
      | '/' -> found_slash (i+1)
      | _ -> Some c
    else
      None
  and found_slash i =
    if i < n then
      let c = s.[i] in
      match c with
      | '*' -> found_multiline_comment (i+1)
      | '/' -> found_singleline_comment (i+1)
      | _ -> f (i+1)
    else
      None
  and found_multiline_comment i =
    if i < n then
      let c = s.[i] in
      match c with
      | '*' -> found_asterisk_in_multiline_comment (i+1)
      | _ -> found_multiline_comment (i+1)
    else
      None
  and found_asterisk_in_multiline_comment i =
    if i < n then
      let c = s.[i] in
      match c with
      | '/' -> f (i+1)
      | '*' -> found_asterisk_in_multiline_comment (i+1)
      | _ -> found_multiline_comment (i+1)
    else
      None
  and found_singleline_comment i =
    if i < n then
      let c = s.[i] in
      match c with
      | '\n' -> f (i+1)
      | _ -> found_singleline_comment (i+1)
    else
      None
  in
  f 0

let rec pp_first_non_white_space_character (pp : Pp.t) : char option =
  doc_first_non_white_space_character (Pp.repr pp)
and doc_first_non_white_space_character (doc : Pp.doc_view) : char option =
  let open Pp in
  match doc with
  | Ppcmd_empty -> None
  | Ppcmd_string str ->
      str_first_non_white_space_character str
  | Ppcmd_glue pps ->
      List.fold_left
        (fun c_opt pp -> Option.bind c_opt (fun _ -> pp_first_non_white_space_character pp))
        None
        pps
  | Ppcmd_box (_, pp) -> pp_first_non_white_space_character pp
  | Ppcmd_tag (_, pp) -> pp_first_non_white_space_character pp
  | Ppcmd_print_break (nspaces, offset) -> None
  | Ppcmd_force_newline -> None
  | Ppcmd_comment strs ->
      List.fold_left
        (fun c_opt str -> Option.bind c_opt (fun _ -> str_first_non_white_space_character str))
        None
        strs

let compose_c_tokens (strings : string list) : string =
  let rec f ss =
    match ss with
    | [] -> []
    | "" :: rest -> f rest
    | s :: "" :: rest -> f (s :: rest)
    | s :: [] -> [s]
    | s1 :: ((s2 :: _) as rest) ->
        if c_needs_space_between_tokens s1 s2 then
          s1 :: " " :: f rest
        else
          s1 :: f rest
  in
  String.concat "" (f strings)

let simple_c_type (c_type_left : string) : c_typedata =
  { c_type_left=c_type_left; c_type_right="" }

let is_simple_c_type (c_type : c_typedata) =
  CString.is_empty c_type.c_type_right

(*
  We wrap declarator by parenthesis if it start with '*' and
  c_type_right starts with '[' or '('.

  declarator is "prefix identifier postfix" or "prefix ( declarator ) postfix"
  where prefix is zero or more asterisks and
  postfix is zero or more brackets and parenthesis.

  The postfix has stronger precedence over the prefix.

  *foo(int) is parsed as *(foo(int)), not ( *foo)(int).
  Thus, we need a parenthesis as ( *foo)(int) when D is substituted to *foo in D(int).
*)

let compose_c_type (c_type : c_typedata) (declarator_left : string) (declarator_right : string) : c_typedata =
  if str_first_non_white_space_character declarator_left = Some '*' &&
     (let c_opt = str_first_non_white_space_character c_type.c_type_right in
      c_opt = Some '[' || c_opt = Some '(')
  then
    { c_type_left=c_type.c_type_left^"("^declarator_left; c_type_right=declarator_right^")"^c_type.c_type_right }
  else
    { c_type_left=c_type.c_type_left^declarator_left; c_type_right=declarator_right^c_type.c_type_right }

let c_type_pointer_to (c_type : c_typedata) : c_typedata =
  compose_c_type c_type "*" ""

let compose_c_decl (c_type : c_typedata) (declarator : string) : string =
  if str_first_non_white_space_character declarator = Some '*' &&
     (let c_opt = str_first_non_white_space_character c_type.c_type_right in
      c_opt = Some '[' || c_opt = Some '(')
  then
    compose_c_tokens [c_type.c_type_left; "("; declarator; ")"; c_type.c_type_right]
  else
    compose_c_tokens [c_type.c_type_left; declarator; c_type.c_type_right]

let compose_c_abstract_decl (c_type : c_typedata) : string =
  compose_c_tokens [c_type.c_type_left; c_type.c_type_right]

let compose_c_pps (pps : Pp.t list) : Pp.t =
  let rec f left_char pps =
    match pps with
    | [] -> []
    | pp :: rest ->
        (match pp_side_chars pp with
        | AlwaysEmpty -> f left_char rest
        | WheteSpaceOrEmpty -> pp :: (f left_char rest)
        | NotEmpty (c1, c2) ->
            if c_needs_space_between_chars left_char c1 then
              (Pp.spc ()) :: pp :: (f c2 rest)
            else
              pp :: (f c2 rest))
  in
  Pp.seq (f ' ' pps)

let pr_c_decl (c_type : c_typedata) (declarator : Pp.t) : Pp.t =
  if pp_first_non_white_space_character declarator = Some '*' &&
     (let c_opt = str_first_non_white_space_character c_type.c_type_right in
      c_opt = Some '[' || c_opt = Some '(')
  then
    compose_c_pps [Pp.str c_type.c_type_left; Pp.str "("; declarator; Pp.str ")"; Pp.str c_type.c_type_right]
  else
    compose_c_pps [Pp.str c_type.c_type_left; declarator; Pp.str c_type.c_type_right]

let pr_c_abstract_decl (c_type : c_typedata) : Pp.t =
  compose_c_pps [Pp.str c_type.c_type_left; Pp.str c_type.c_type_right]
