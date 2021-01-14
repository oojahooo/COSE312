open Batteries

(***************)
(*    types    *)
(***************)

type stmt = ASSIGN of S.lv * S.exp
          | COND of S.exp
          | READ of S.id
          | PRINT of S.exp
          | DECL of S.typ * S.id

type cfg = blocks * edges * entry * final
and blocks = block list
and block = int * stmt
and edges = edge list
and edge = int * int
and entry = block option
and final = blocks

(***************************)
(*    functions for cfg    *)
(***************************)

let blnum = ref 0

let new_bl () = blnum := !blnum + 1 ; blnum

let nofb (i, _) = i

let add_blocks : cfg -> blocks -> cfg
= fun (old_bls, egs, e, f) bls ->
  (old_bls@bls, egs, e, f)

let append_block : (cfg * int) -> stmt -> ((cfg * int) * block)
= fun ((bls, egs, e, f), i) st ->
  let j = new_bl () in
  let bl = (j, st) in
  let entry = if e = None then Some bl else e in
  let eg = if i = 0 then [] else [(i, j)] in
  (((bls@[bl], egs@eg, entry, [bl]), j), bl)

let add_edge : cfg -> (block * block) -> cfg
= fun (bls, egs, e, f) (bl1, bl2) ->
  (bls, egs@[((nofb bl1), (nofb bl2))], e, f)

let get_entry : cfg -> block
= fun (_, _, e, _) ->
  match e with
  | None -> raise (Failure "get_entry")
  | Some b -> b

let neg : S.exp -> S.exp
= fun exp ->
  match exp with
  | NUM n -> if n = 0 then Num 1 else Num 0
  | LV lv -> 

let rec block2cfg : S.program -> cfg
= fun (decls, stmts) ->
  let add_decl cfgn (t, x) = let (ncfgn, _) = append_block cfgn (DECL (t, x)) in ncfgn in
  let (cfg, _) = List.fold_left add_decl (([], [], None, []), 0) decls in
  let add_stmt cfgn st =
    match st with
    | S.ASSIGN (lv, exp) ->
      let (ncfgn, _) = append_block cfgn (ASSIGN (lv, exp)) in ncfgn
    | S.IF (exp, stmt) ->
      let (((bls, egs, e, f), j), tbl) = append_block cfgn (COND exp) in
      let (((bls, egs, e, f), j), fbl) = append_block ((bls, egs, e, f), i) (COND (neg exp))

(***************************)
(*    interval analysis    *)
(***************************)



let verify : S.program -> bool
=fun s_pgm -> true (* TODO *)
