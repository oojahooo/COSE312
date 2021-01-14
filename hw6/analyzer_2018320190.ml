open Batteries

(***************)
(*    types    *)
(***************)

type aexp =
  | Int of int
  | Var of T.var
  | Add of aexp * aexp
  | Sub of aexp * aexp
  | Mult of aexp * aexp
  | Div of aexp * aexp
  | Minus of aexp
  | Not of aexp

type cmd =
  | Skip
  | Alloc of T.var * aexp
  | Assign of T.var * aexp
  | Lt of aexp * aexp
  | Le of aexp * aexp
  | Gt of aexp * aexp
  | Ge of aexp * aexp
  | Eq of aexp * aexp
  | 

type block = int * T.instr
and blocks = block list
and edge = int * int
and edges = edge list
and cfg = blocks * edges

type num = NUM of int | INF | NEGINF

let min a b =
  match a, b with
  | NEGINF, _ -> NEGINF
  | _, NEGINF -> NEGINF
  | INF, i -> i
  | i, INF -> i
  | NUM n, NUM m -> if n < m then NUM n else NUM m

let max a b =
  match a, b with
  | INF, _ -> INF
  | _, INF -> INF
  | NEGINF, i -> i
  | i, NEGINF -> i
  | NUM n, NUM m -> if n > m then NUM n else NUM m

let cmpnum a b =
  match a, b with
  | NEGINF, _ -> true
  | _, INF -> true
  | INF, _ -> false
  | _, NEGINF -> false
  | NUM n, NUM m -> n <= m

let numplus a b =
  match a, b with
  | INF, _ -> INF
  | _, INF -> INF
  | NEGINF, _ -> NEGINF
  | _, NEGINF -> NEGINF
  | NUM n, NUM m -> NUM (n + m)

let numneg a =
  match a with
  | INF -> NEGINF
  | NEGINF -> INF
  | NUM n -> NUM (-n)

let nummult a b =
  match a, b with
  | INF, INF -> INF
  | INF, NEGINF -> NEGINF
  | NEGINF, INF -> NEGINF
  | NEGINF, NEGINF -> INF
  | INF, NUM n | NUM n, INF -> if n < 0 then NEGINF else if n = 0 then NUM 0 else INF
  | NEGINF, NUM n | NUM n, NEGINF -> if n < 0 then INF else if n = 0 then NUM 0 else NEGINF
  | NUM n, NUM m -> NUM (n*m)

let min_lst l =
  let fst = List.hd l in
  List.fold_left (fun min n -> if cmpnum min n then min else n) fst l

let max_lst l =
  let fst = List.hd l in
  List.fold_left (fun max n -> if cmpnum max n then n else max) fst l

(****************************)
(* abstract interval, state *)
(****************************)

module AInt = struct
  type t = Bot | INT of num * num
  
  let alpha : int -> t
  = fun n -> INT (n, n)
  
  let order : t -> t -> bool
  = fun s1 s2 ->
    match s1, s2 with
    | Bot, _ -> true
    | _, Bot -> false
    | NUM (l1, u1), NUM (l2, u2) ->
      if cmpnum l2 l1 && cmpnum u1 u2 then true else false

  let lub : t -> t -> t
  = fun s1 s2 ->
    match s1, s2 with
    | Bot, i -> i
    | i, Bot -> i
    | INT (l1, u1), INT (l2, u2) -> INT ((min l1 l2), (max u1 u2))
  
  let glb : t -> t -> t
  = fun s1 s2 ->
    match s1, s2 with
    | Bot, _ -> Bot
    | _, Bot -> Bot
    | INT (l1, u1), INT (l2, u2) ->
      let l = max l1 l2 in
      let u = min u1 u2 in
      if cmpnum l u then INT (l, u) else Bot
  
  let plus : t -> t -> t
  = fun s1 s2 ->
    match s1, s2 with
    | Bot, _ -> Bot
    | _, Bot -> Bot
    | INT (l1, u1), INT (l2, u2) -> INT (numplus l1 l2, numplus u1 u2)

  let neg : t -> t
  = fun s ->
    match s with
    | Bot -> Bot
    | INT (l, u) -> INT (numneg u, numneg l)

  let minus : t -> t -> t
  = fun s1 s2 ->
    match s1, s2 with
    | Bot, _ -> Bot
    | _, Bot -> Bot
    | a, b -> plus a (neg b)

  let mult : t -> t -> t
  = fun s1 s2 ->
    match s1, s2 with
    | Bot, _ -> Bot
    | _, Bot -> Bot
    | INT (l1, u1), INT (l2, u2) ->
      let s = [nummult l1 l2; nummult l1 u2; nummult u1 l2; nummult u1 u2] in
      INT (min_lst s, max_lst s)

  let div : t -> t -> t
  = fun s1 s2 ->
    match s1, s2 with
    | Bot, _ -> Bot
    | _, Bot -> Bot
    | Top, _ -> Top
    | _, Top -> Bot
    | INT (l1, u1), INT (l2, u2) -> Bot
end

module AState = struct
  module Map. Map.Make (struct type t = T.var let compare = compare end)
  type t = AInt.t Map.t
  let bot = Map.empty
  let find x m = try Map.find x m with Not_found -> AInt.Bot
  let update x i m = Map.add x i m
  let update_join x i m -> Map.add x (AInt.lub i (find x m)) m
  let order m1 m2 = Map.for_all (fun k i -> AInt.order i (find k m2)) m1
  let lub m1 m2 = Map.fold (fun k i m -> update_join k i m) m1 m2
end
   
let rec  : T.instr -> AState.t -> AState.t

(***********************************)
(*       Functions for cfg         *)
(***********************************)

let nofb (i, _) = i

let construct_cfg : T.program -> cfg
= fun t ->
  let (_, bls, map) = List.fold_left (
    fun (i, nt, l2pc) (l, inst) ->
      if l = T.dummy_label then (i+1, nt@[(i, inst)], l2pc)
      else (i+1, nt@[(i, inst)], PMap.add l i l2pc)
  ) (0, [], PMap.empty) t in
  let edges = List.fold_left (
    fun e bl ->
      match bl with (i, inst) ->
        (match inst with
         | T.UJUMP l -> e@[(i, nofb (List.nth bls (PMap.find l map)))]
         | T.CJUMP (_, l) | T.CJUMPF (_, l) ->
           e@[(i, nofb (List.nth bls (PMap.find l map))); (i, nofb (List.nth bls (i+1)))]
         | T.HALT -> e
         | _ -> e@[(i, nofb (List.nth bls (i+1)))])
  ) [] bls in
  (bls, edges)

let find_nextblock : cfg -> block -> block list
= fun (bls, edges) (i, _) ->
  List.fold_left (fun ls (b1, b2) -> if b1 = i then (List.nth bls b2)::ls else ls) [] edges

let find_prevblock : cfg -> block -> block list
= fun (bls, edges) (i, _) ->
  List.fold_left (fun ls (b1, b2) -> if b2 = i then (List.nth bls b1)::ls else ls) [] edges

(***************************)
(*    interval analysis    *)
(***************************)

(* for pick in, out set *)
let inset (_, i, _) = i
let outset (_, _, o) = o

let ia : cfg -> 

let verify : S.program -> bool
=fun s_pgm -> true (* TODO *)
