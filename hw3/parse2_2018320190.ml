type symbol = T of string | N of string | Epsilon | End
type production = (symbol * symbol list) list
type cfg = symbol list * symbol list * symbol * production

type dotsymbol = S of symbol | Dot
type item = dotsymbol * dotsymbol list
type state = item BatSet.t
type states = state BatSet.t
type edge = state * symbol * state
type edges = edge BatSet.t
type automaton = state * states * edges

type entry = GOTO of state | SHIFT of state | REDUCE of (symbol * symbol list) | ACC
type parsingtable = (state * symbol, entry) BatMap.t

let rec find_next_item : dotsymbol list -> production -> item BatSet.t
  = fun ds prod ->
  match ds with
  | [] -> raise (Failure "There is no dot symbol")
  | Dot::tl ->
    (
      try
        let b = List.hd tl in
        let prod = List.map (fun (a, xyz) -> (S a, List.map (fun s -> S s) xyz)) prod in
        BatSet.of_list (List.filter_map (fun (s, sl) -> if s = b then Some (s, Dot::sl) else None) prod)
      with (Failure _) -> BatSet.empty
    )
  | _::tl -> find_next_item tl prod

let closure : production -> item BatSet.t -> item BatSet.t
= fun prod is ->
  let rec closure_fixed is =
    let new_is = BatSet.fold (fun (s, ds) newi -> BatSet.union (find_next_item ds prod) newi) is is in
    if BatSet.equal new_is is then is else closure_fixed new_is
  in closure_fixed is

let init_i0 : production -> item -> state
= fun prod i -> closure prod (BatSet.singleton i)

let is_nextto_dot : item -> dotsymbol -> item option
= fun (a, ds) d ->
  let new_ds = List.fold_right
    (
      fun s ns ->
        if s = Dot then
          try
            let e = List.hd ns in
            if e = d then e::Dot::(List.tl ns) else []
          with
            (Failure _) -> []
        else s::ns
    ) ds [] in
  if List.mem Dot new_ds then Some (a, new_ds) else None

let construct_next_state : production -> item BatSet.t -> dotsymbol -> state option
= fun prod is s ->
  let j = BatSet.filter_map (fun i -> is_nextto_dot i s) is in
  if BatSet.is_empty j then None else Some (closure prod j)

let construct_automaton : cfg -> automaton
= fun (nts, ts, ss, prod) ->
  let (e', e) = List.hd prod in
  let i0 = init_i0 prod (S e', Dot::(List.map (fun e -> S e) e)) in
  let t = BatSet.singleton i0 in
  let e = BatSet.empty in
  let symbols = nts@ts in
  let rec construct_automaton_fixed t e =
    let (newt, newe) = BatSet.fold
      (
        fun is (t, e) ->
          List.fold_left
            (
              fun (t, e) x -> 
                let j = construct_next_state prod is (S x) in
                match j with
                | None -> (t, e)
                | Some s -> (BatSet.add s t, BatSet.add (is, x, s) e)
            ) (t, e) symbols
      ) t (t, e) in
    if (BatSet.equal newt t) && (BatSet.equal newe e) then (t, e) else construct_automaton_fixed newt newe
  in let (t, e) = construct_automaton_fixed t e in (i0, t, e)

let add_start_symbol : cfg -> cfg
= fun (nts, ts, ss, prod) ->
  match ss with
  | N s ->
    let s' = N (s ^ "'") in
    let prod = (s', [ss])::prod in
    (s'::nts, ts, s', prod)
  | _ -> raise (Failure "wrong cfg")

exception Not_SLR

let rec first_run : (symbol, symbol BatSet.t) BatMap.t -> production -> (symbol, symbol BatSet.t) BatMap.t
= fun first_table prod ->
  let rec compute ft (x , ys) =
    let (b, result) = List.fold_left (fun (b, rset) y -> 
        let fofy = BatMap.find y ft in
        if b then ((BatSet.mem Epsilon fofy), (BatSet.union rset (BatSet.remove Epsilon fofy)))
        else (b, rset)) (true, (BatMap.find x ft)) ys in
    let result = if b then BatSet.add Epsilon result else result in
    BatMap.update x x result ft
    in
  List.fold_left compute first_table prod

let rec first_fixed : production -> (symbol, symbol BatSet.t) BatMap.t -> (symbol, symbol BatSet.t) BatMap.t
= fun prod first_table ->
  let new_first_table = first_run first_table prod in
  if BatMap.equal (BatSet.equal) new_first_table first_table then new_first_table
  else first_fixed prod new_first_table

let rec first : cfg -> (symbol, symbol BatSet.t) BatMap.t
= fun (nts, ts, ss, prod) ->
  let first_table = List.fold_left (fun bm t -> BatMap.add t (BatSet.singleton t) bm) BatMap.empty ts in
  let first_table = List.fold_left (fun bm n -> BatMap.add n BatSet.empty bm) first_table nts in
  first_fixed prod first_table

let rec first_for_str : (symbol, symbol BatSet.t) BatMap.t -> symbol list -> symbol BatSet.t
= fun first_table xs ->
  let (b, result) = List.fold_left (fun (b, rset) x ->
      let fofx = BatMap.find x first_table in
      if b then ((BatSet.mem Epsilon fofx), (BatSet.union rset (BatSet.remove Epsilon fofx)))
      else (b, rset)) (true, BatSet.empty) xs in
  if b then BatSet.add Epsilon result else result

let rec next : symbol list -> symbol -> symbol list
= fun xs x ->
  match xs with
  | [] -> raise (Failure "There's no symbol")
  | hd::tl ->
    if hd = x then tl
    else next tl x

let rec follow_run : (symbol, symbol BatSet.t) BatMap.t -> (symbol, symbol BatSet.t) BatMap.t -> production -> (symbol, symbol BatSet.t) BatMap.t
= fun follow_table first_table prod->
  let rec compute ft (a, bs) =
    (
      let rec add_b_follow ft bs =
        match bs with
        | [] -> ft
        | b::tl ->
          (
            match b with
            | N s ->
              (
                match next bs b with
                | [] -> BatMap.update b b (BatSet.union (BatMap.find a ft) (BatMap.find b ft)) ft
                | beta ->
                  let fofb = first_for_str first_table beta in
                  let updated_set = BatSet.union (BatSet.remove Epsilon fofb) (BatMap.find b ft) in
                  let updated_set = if BatSet.mem Epsilon fofb then BatSet.union (BatMap.find a ft) updated_set else updated_set in
                  add_b_follow (BatMap.update b b updated_set ft) tl
              )
            | _ -> add_b_follow ft tl
          )
      in add_b_follow ft bs
    ) in
  List.fold_left compute follow_table prod

let rec follow_fixed : production -> (symbol, symbol BatSet.t) BatMap.t -> (symbol, symbol BatSet.t) BatMap.t -> (symbol, symbol BatSet.t) BatMap.t
= fun prod follow_table first_table ->
  let new_follow_table = follow_run follow_table first_table prod in
  if BatMap.equal (BatSet.equal) new_follow_table follow_table then new_follow_table
  else follow_fixed prod new_follow_table first_table

let rec follow : cfg -> (symbol, symbol BatSet.t) BatMap.t -> (symbol, symbol BatSet.t) BatMap.t
= fun (nts, ts, ss, prod) first_table ->
  let follow_table = List.fold_left (fun bm n -> BatMap.add n BatSet.empty bm) BatMap.empty nts in
  let follow_table = BatMap.update ss ss (BatSet.singleton End) follow_table in
  follow_fixed prod follow_table first_table

let item_to_prod : item -> (symbol * symbol list)
= fun it ->
  match it with
  | (S s, sls) -> (s, List.filter_map (fun ds -> match ds with S s -> Some s | Dot -> None) sls)
  | _ -> raise (Failure "wrong item")

let can_reduce : state -> production -> production
= fun i prod ->
  let prod_item = List.map (fun (s, ss) -> (S s, (List.map (fun x -> S x) ss)@[Dot])) prod in
  List.fold_left
    (
      fun result it ->
        if BatSet.mem it i then (item_to_prod it)::result else result
    ) [] prod_item

let construct_parsing_table : cfg -> automaton -> parsingtable
= fun (nts, ts, ss, prod) (i0, sts, egs)->
  let add_entry_from_edge e pt =
    match e with
    | (i, T s, j) -> if BatMap.mem (i, T s) pt then raise Not_SLR else BatMap.add (i, T s) (SHIFT j) pt
    | (i, N s, j) -> if BatMap.mem (i, N s) pt then raise Not_SLR else BatMap.add (i, N s) (GOTO j) pt
    | _ -> raise (Failure "XX")
  in let parsing_table = BatSet.fold add_entry_from_edge egs BatMap.empty in
  let (s', sls) = List.hd prod in
  let first_prod_dot = (S s', (List.map (fun s -> S s) sls)@[Dot]) in
  let first_table = first (nts, ts, ss, prod) in
  let follow_table = follow (nts, ts, ss, prod) first_table in
  let add_entry_from_state i pt =
    let new_pt =
      if BatSet.mem first_prod_dot i then
        if BatMap.mem (i, End) pt then raise Not_SLR else BatMap.add (i, End) ACC pt
      else pt
    in List.fold_left
      (
        fun result p ->
          let follow_A = match p with (a, _) -> BatMap.find a follow_table in
          BatSet.fold
            (
              fun y r ->
                if BatMap.mem (i, y) r then raise Not_SLR else BatMap.add (i, y) (REDUCE p) r
            ) follow_A result
      ) new_pt (can_reduce i (List.tl prod))
  in BatSet.fold add_entry_from_state sts parsing_table

let check_SLR : cfg -> bool
=fun cfg ->
  let cfg = add_start_symbol cfg in
  let automaton = construct_automaton cfg in
  try let _ = construct_parsing_table cfg automaton in () ; true
  with Not_SLR -> false

let rec parse_loop : parsingtable -> state BatStack.t -> symbol list -> bool
= fun parsing_table state_stack sentence ->
  let i = BatStack.top state_stack in
  let input_symbol = List.hd sentence in
  let entry = BatMap.find (i, input_symbol) parsing_table in
  match entry with
  | SHIFT n ->
    BatStack.push n state_stack ;
    parse_loop parsing_table state_stack (List.tl sentence)
  | REDUCE (l, r) ->
    List.iter (fun _ -> let _ = BatStack.pop state_stack in ()) r ;
    let etr = BatMap.find (BatStack.top state_stack, l) parsing_table in
    (
      match etr with
      | GOTO n ->
        BatStack.push n state_stack ;
        parse_loop parsing_table state_stack sentence
      | _ -> raise (Failure "wrong parsing table")
    )
  | ACC -> true
  | _ -> raise (Failure "wrong parsing table")

let parse : cfg -> symbol list -> bool
=fun cfg sentence ->
  let cfg = add_start_symbol cfg in
  let (i0, sts, egs) = construct_automaton cfg in
  let parsing_table = construct_parsing_table cfg (i0, sts, egs) in
  let state_stack = BatStack.create () in
  BatStack.push i0 state_stack ;
  try parse_loop parsing_table state_stack sentence with
  | Not_found -> false
  | Failure _ -> false
