(******************************************)
(* type of control flow gragh, expression *)
(******************************************)

type block = int * T.linstr
and blocks = block list
and edge = int * int
and edges = edge list
and cfg = blocks * edges

module DefSet = Set.Make (
    struct
      type t = T.instr
      let compare = compare
    end)
module VarSet = Set.Make (String)

(* for pick in, out set *)
let inset (_, i, _) = i
let outset (_, _, o) = o

(***********************************)
(*       Functions for cfg         *)
(***********************************)

let nofb (i, _) = i

let construct_cfg : T.program -> cfg
  = fun t ->
  let (_, bls, map) = List.fold_left (
    fun (i, nt, l2pc) (l, inst) ->
      if l = T.dummy_label then (i+1, nt@[(i, (l, inst))], l2pc)
      else (i+1, nt@[(i, (l, inst))], PMap.add l i l2pc)
  ) (0, [], PMap.empty) t in
  let edges = List.fold_left (
    fun e bl ->
      match bl with (i, (_, inst)) ->
        (match inst with
         | T.UJUMP l -> e@[(i, nofb (List.nth bls (PMap.find l map)))]
         | T.CJUMP (_, l) | T.CJUMPF (_, l) ->
           e@[(i, nofb (List.nth bls (PMap.find l map))); (i, nofb (List.nth bls (i+1)))]
         | T.HALT -> e
         | _ -> e@[(i, nofb (List.nth bls (i+1)))])
  ) [] bls in
  (bls, edges)

let remake_pgm : cfg -> T.program
= fun (bls, _) ->
  List.map (fun (_, (l, inst)) -> (l, inst)) bls

let find_nextblock : cfg -> block -> block list
= fun (bls, edges) (i, _) ->
  List.fold_left (fun ls (b1, b2) -> if b1 = i then (List.nth bls b2)::ls else ls) [] edges

let find_prevblock : cfg -> block -> block list
= fun (bls, edges) (i, _) ->
  List.fold_left (fun ls (b1, b2) -> if b2 = i then (List.nth bls b1)::ls else ls) [] edges

(***************************************)
(*    Reaching Definitions Analysis    *)
(***************************************)

let cmp_defset : (block * DefSet.t * DefSet.t) list -> (block * DefSet.t * DefSet.t) list -> bool
= fun rm1 rm2 ->
  List.fold_left2 (
    fun b r1 r2 -> 
      if b then
        match r1, r2 with
        | (b1, in1, out1), (b2, in2, out2) -> b1 = b2 && DefSet.equal in1 in2 && DefSet.equal out1 out2
      else false
  ) true rm1 rm2

let lv_of : T.instr -> T.var option
= fun inst ->
  match inst with 
  | T.ALLOC (x, n) -> Some x
  | T.ASSIGNV (x, bop, y, z) -> Some x
  | T.ASSIGNC (x, bop, y, n) -> Some x
  | T.ASSIGNU (x, uop, y) -> Some x
  | T.COPY (x, y) -> Some x
  | T.COPYC (x, n) -> Some x
  | T.LOAD (x, (a, i)) -> Some x
  | T.READ x -> Some x
  | _ -> None

let map_var_def : blocks -> (T.var, DefSet.t) PMap.t
= fun bls ->
  List.fold_left (
    fun vd (_, (_, inst)) ->
      match lv_of inst with
      | Some x ->
        let vset = try PMap.find x vd with Not_found -> DefSet.empty in
        PMap.add x (DefSet.add inst vset) vd
      | None -> vd
  ) PMap.empty bls

let construct_gen_kill : (T.var, DefSet.t) PMap.t -> T.instr -> (DefSet.t * DefSet.t)
= fun map inst ->
  match inst with
  | T.ALLOC (x, _) | T.READ x
  | T.ASSIGNV (x, _, _, _) | T.ASSIGNC (x, _, _, _) | T.ASSIGNU (x, _, _)
  | T.COPY (x, _) | T.COPYC (x, _) | T.LOAD (x, _) -> (* T.pp [(1, inst)] ; T.pp (DefSet.fold (fun i p -> p@[(0, i)]) (PMap.find x map) []) ; *)
    (DefSet.singleton inst, DefSet.remove inst (PMap.find x map))
  | _ -> (* T.pp [(2, inst)] ; *) (DefSet.empty, DefSet.empty)

let rda_loop : cfg -> (block * DefSet.t * DefSet.t) list -> (block * DefSet.t * DefSet.t) list
= fun (bls, egs) rdamap ->
  let map = map_var_def bls in
  let update ((i, (l, inst)), is, os) =
    let (gen, kill) = construct_gen_kill map inst in (* print_endline (string_of_int i) ; T.pp (DefSet.fold (fun i p -> p@[(0, i)]) (is) []) ; print_endline (string_of_int i) ; List.iter (fun (i, _) -> print_endline (string_of_int i)) (find_prevblock (bls, egs) (i, (l, inst))) ; print_endline "" ; *)
    ((i, (l, inst)),
     List.fold_left (
       fun ds (i, (_, _)) ->  DefSet.union ds (outset (List.nth rdamap i))
     ) DefSet.empty (find_prevblock (bls, egs) (i, (l, inst))),
    DefSet.union gen (DefSet.diff (is) kill))
  in 
  List.map update rdamap

let rec rda_fixed : cfg -> (block * DefSet.t * DefSet.t) list -> (block * DefSet.t * DefSet.t) list
= fun cfg rdamap ->
  let new_rdamap = rda_loop cfg rdamap in
  if cmp_defset new_rdamap rdamap then rdamap else rda_fixed cfg new_rdamap

let rda : cfg -> (block * DefSet.t * DefSet.t) list
= fun (bls, egs) ->
  let rdamap = List.map (fun bl -> (bl, DefSet.empty, DefSet.empty)) bls in
  rda_fixed (bls, egs) rdamap

(***************************************)
(*          Liveness Analysis          *)
(***************************************)

let cmp_varset : (block * VarSet.t * VarSet.t) list -> (block * VarSet.t * VarSet.t) list -> bool
= fun rm1 rm2 ->
  List.fold_left2 (
    fun b r1 r2 -> 
      if b then
        match r1, r2 with
        | (b1, in1, out1), (b2, in2, out2) -> b1 = b2 && VarSet.equal in1 in2 && VarSet.equal out1 out2
      else false
  ) true rm1 rm2

let construct_def_use : T.instr -> (VarSet.t * VarSet.t)
= fun inst ->
  let (def, use) = (VarSet.empty, VarSet.empty) in
  match inst with
  | T.ALLOC (x, n) -> (VarSet.add x def, use)
  | T.ASSIGNV (x, bop, y, z) -> (VarSet.add x def, VarSet.add y (VarSet.add z use))
  | T.ASSIGNC (x, bop, y, n) -> (VarSet.add x def, VarSet.add y use)
  | T.ASSIGNU (x, uop, y) -> (VarSet.add x def, VarSet.add y use)
  | T.COPY (x, y) -> (VarSet.add x def, VarSet.add y use)
  | T.COPYC (x, n) -> (VarSet.add x def, use)
  | T.CJUMP (x, _) -> (def, VarSet.add x use)
  | T.CJUMPF (x, _) -> (def, VarSet.add x use)
  | T.LOAD (x, (a, i)) -> (VarSet.add x def, VarSet.add i (VarSet.add a use))
  | T.STORE ((a, i), x) -> (def, VarSet.add i (VarSet.add a (VarSet.add x use)))
  | T.READ x -> (VarSet.add x def, use)
  | T.WRITE x -> (def, VarSet.add x use)
  | _ -> (def, use)

let lv_loop : cfg -> (block * VarSet.t * VarSet.t) list -> (block * VarSet.t * VarSet.t) list
= fun cfg lvmap ->
  let update ((i, (l, inst)), is, os) =
    let (def, use) = construct_def_use inst in
    ((i, (l, inst)), VarSet.union use (VarSet.diff os def),
     List.fold_left (
       fun vs (i, _) ->
         VarSet.union vs (inset (List.nth lvmap i))) VarSet.empty (find_nextblock cfg (i, (l, inst))))
  in
  List.map update lvmap

let rec lv_fixed : cfg -> (block * VarSet.t * VarSet.t) list -> (block * VarSet.t * VarSet.t) list
= fun cfg lvmap ->
  let new_lvmap = lv_loop cfg lvmap in
  if cmp_varset new_lvmap lvmap then lvmap else lv_fixed cfg new_lvmap

let lv : cfg -> (block * VarSet.t * VarSet.t) list
= fun (bls, egs) ->
  let lvmap = List.map (fun bl -> (bl, VarSet.empty, VarSet.empty)) bls in
  lv_fixed (bls, egs) lvmap

(****************************************)
(*          optimize functions          *)
(****************************************)

let change_label : T.linstr -> (T.label * T.label) -> T.linstr
= fun (label, inst) (old_l, new_l) ->
  match inst with
  | T.UJUMP l when l = old_l -> (label, T.UJUMP new_l)
  | T.CJUMP (x, l) when l = old_l -> (label, T.CJUMP (x, new_l))
  | T.CJUMPF (x, l) when l = old_l -> (label, T.CJUMPF (x, new_l))
  | _ -> (label, inst)

let deadcode_elim : cfg -> cfg
= fun (bls, egs) ->
  let lvmap = lv (bls, egs) in
  let check_dead (i, (l, inst)) =
    let (def, use) = construct_def_use inst in
    if def = (VarSet.inter def (outset (List.nth lvmap i))) then (i, (l, inst)) else (i, (l, T.SKIP))
  in
  (List.map check_dead bls, egs)

let substitute : T.instr -> T.var -> T.var -> T.instr
= fun inst a b ->
  match inst with
  | T.ASSIGNV (x, bop, y, z) ->
    if a = y then if a = z then T.ASSIGNV (x, bop, b, b) else T.ASSIGNV (x, bop, b, z)
    else if a = z then T.ASSIGNV (x, bop, y, b)
    else inst
  | T.ASSIGNC (x, bop, y, n) ->
    if a = y then T.ASSIGNC (x, bop, b, n)
    else inst
  | T.ASSIGNU (x, uop, y) ->
    if a = y then T.ASSIGNU (x, uop, b)
    else inst
  | T.COPY (x, y) ->
    if a = y then T.COPY (x, b)
    else inst
  | T.CJUMP (x, l) ->
    if a = x then T.CJUMP (b, l)
    else inst
  | T.CJUMPF (x, l) ->
    if a = x then T.CJUMPF (b, l)
    else inst
  | T.LOAD (x, (yb, i)) ->
    if a = yb then T.LOAD (x, (b, i))
    else if a = i then T.LOAD (x, (yb, b))
    else inst
  | T.STORE ((yb, i), x) ->
    if a = yb then T.STORE ((b, i), x)
    else if a = i then T.STORE ((yb, b), x)
    else if a = x then T.STORE ((yb, i), b)
    else inst
  | T.WRITE x ->
    if a = x then T.WRITE b
    else inst
  | _ -> inst

let calc_b : T.bop -> int -> int -> int
= fun op n m ->
  match op with
  | T.ADD -> n + m
  | T.SUB -> n - m
  | T.MUL -> n * m
  | T.DIV -> n / m
  | T.LT -> if n < m then 1 else 0
  | T.LE -> if n <= m then 1 else 0
  | T.GT -> if n > m then 1 else 0
  | T.GE -> if n >= m then 1 else 0
  | T.EQ -> if n = m then 1 else 0
  | T.AND -> if n != 0 && m != 0 then 1 else 0
  | T.OR -> if n != 0 || m != 0 then 1 else 0

let calc_u : T.uop -> int -> int
= fun op n ->
  match op with
  | T.MINUS -> (-n)
  | T.NOT -> if n = 0 then 1 else 0

let subc : T.instr -> T.var -> int -> T.instr
= fun inst a m ->
  match inst with
  | T.ASSIGNV (x, bop, y, z) ->
    if a = y then if a = z then T.COPYC (x, calc_b bop m m) else T.ASSIGNV (x, bop, y, z)
    else if a = z then T.ASSIGNC (x, bop, y, m)
    else inst
  | T.ASSIGNC (x, bop, y, n) ->
    if a = y then T.COPYC (x, calc_b bop m n)
    else inst
  | T.ASSIGNU (x, uop, y) ->
    if a = y then T.COPYC (x, calc_u uop m)
    else inst
  | T.COPY (x, y) ->
    if a = y then T.COPYC (x, m)
    else inst
  | T.CJUMP (x, l) ->
    if a = x then if m != 0 then T.UJUMP l else T.SKIP
    else inst
  | T.CJUMPF (x, l) ->
    if a = x then if m = 0 then T.UJUMP l else T.SKIP
    else inst
  | T.LOAD (x, (arr, i)) -> inst
  | T.STORE ((arr, i), x) -> inst
  | T.WRITE x -> inst
  | _ -> raise (Failure "subc")

let prop : cfg -> cfg
= fun (bls, egs) ->
  let map = map_var_def bls in
  let rdamap = rda (bls, egs) in
  let update (i, (l, inst)) =
    let (_, use) = construct_def_use inst in
    let new_inst = VarSet.fold (
        fun used inst -> (* T.pp (DefSet.fold (fun i p -> p@[(0, i)]) (outset (List.nth rdamap 1)) []) ; *)
        let defbl = DefSet.inter (PMap.find used map) (inset (List.nth rdamap i)) in
        let num = DefSet.cardinal defbl in
        if num = 0 then raise (Failure "There is a var not defined")
        else if num > 1 then inst
        else
          match DefSet.choose defbl with
          | COPY (x, y) -> substitute inst x y
          | COPYC (x, n) -> subc inst x n
          | _ -> inst
    ) use inst in
    (i, (l, new_inst))
  in
  (List.map update bls, egs)

let prop_reverse : cfg -> cfg
= fun (bls, egs) ->
  let map = map_var_def bls in
  let rdamap = rda (bls, egs) in
  let update (i, (l, inst)) =
    match inst with
    | T.COPY (x, y) ->
      let defbl = DefSet.inter (PMap.find y map) (inset (List.nth rdamap i)) in
      let num = DefSet.cardinal defbl in
        if num = 0 then raise (Failure "There is a var not defined")
        else if num > 1 then (i, (l, inst))
        else
          (match DefSet.choose defbl with
           | T.ALLOC (x', n) -> (i, (l, T.ALLOC (x, n)))
           | T.ASSIGNV (x', bop, y, z) -> (i, (l, T.ASSIGNV (x, bop, y, z)))
           | T.ASSIGNC (x', bop, y, n) -> (i, (l, T.ASSIGNC (x, bop, y, n)))
           | T.ASSIGNU (x', uop, y) -> (i, (l, T.ASSIGNU (x, uop, y)))
           | T.LOAD (x', (a, yb)) -> (i, (l, T.LOAD (x, (a, yb))))
           | _ -> (i, (l, inst))
          )
    | _ -> (i, (l, inst))
  in
  (List.map update bls, egs)

let remove_skip : T.program -> T.program
= fun t ->
  let skipskip (cl, nt, ll) (l, inst) =
    if cl = T.dummy_label then
      if inst = T.SKIP then (l, nt, ll)
      else (cl, nt@[(l, inst)], ll)
    else if inst = T.SKIP then if l = T.dummy_label then (cl, nt, ll) else (l, nt, ll@[(cl, l)])
    else if l = T.dummy_label then (T.dummy_label, nt@[(cl, inst)], ll)
    else (T.dummy_label, nt@[(l, inst)], ll@[(cl, l)])
  in
  let (_, new_t, l2l) = List.fold_left skipskip (T.dummy_label, [], []) t in
  List.fold_left (
    fun nt ll ->
      List.fold_left (fun nnt linst -> nnt@[(change_label linst ll)]) [] nt
  ) new_t l2l

let optimize : T.program -> T.program
=fun t ->
  (* let test = remove_skip (remake_pgm (prop (deadcode_elim (prop_reverse (deadcode_elim (prop (construct_cfg t))))))) in
  T.pp test ; t *)
  let cfg = construct_cfg t in
  let rec opt_fixed cfg =
    let new_cfg = deadcode_elim (prop_reverse (deadcode_elim (prop cfg))) in
    if new_cfg = cfg then remove_skip (remake_pgm new_cfg) else opt_fixed new_cfg
  in
  opt_fixed cfg
