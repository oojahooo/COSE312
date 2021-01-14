type symbol = T of string | N of string | Epsilon | End
type production = (symbol * symbol list) list
type cfg = symbol list * symbol list * symbol * production

let rec first_run : (symbol, symbol BatSet.t) BatMap.t -> production -> (symbol, symbol BatSet.t) BatMap.t
= fun first_table prod ->
  let rec compute ft (x , ys) =
    let (b, result) = List.fold_left (fun (b, rset) y -> 
        let fofy = BatMap.find y ft in
        if b then ((BatSet.mem Epsilon fofy), (BatSet.union rset (BatSet.remove Epsilon fofy)))
        else (b, rset)) (true, (BatMap.find x ft)) ys in
    let result = if b then BatSet.add Epsilon result else result in
    BatMap.update x x result ft in
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

exception Not_LL1

let construct_parsing_table : cfg -> (symbol, (symbol, symbol list) BatMap.t) BatMap.t
= fun (nts, ts, ss, prod) ->
  let first_table = first (nts, ts, ss, prod) in
  let follow_table = follow (nts, ts, ss, prod) first_table in
  let add_prod = fun pt (x, xs) ->
    let fofxs = first_for_str first_table xs in
    let algo1 = BatSet.fold (fun s pt ->
        let mapx = BatMap.find x pt in
        if BatMap.mem s mapx then raise Not_LL1 else BatMap.update x x (BatMap.add s xs mapx) pt
      ) (fofxs) pt in
    let algo2 =
      if BatSet.mem Epsilon fofxs then BatSet.fold (fun s pt ->
          let mapx = BatMap.find x pt in
          if BatMap.mem s mapx then raise Not_LL1 else BatMap.update x x (BatMap.add s xs mapx) pt
        ) (BatMap.find x follow_table) algo1
      else algo1 in
    algo2 in
  let parsing_table = List.fold_left (fun pt nt -> BatMap.add nt (BatMap.empty) pt) BatMap.empty nts in
  List.fold_left add_prod parsing_table prod

let check_LL1 : cfg -> bool
=fun cfg ->
  try let _ = construct_parsing_table cfg in () ; true
  with Not_LL1 -> false

let rec parse_loop : (symbol, (symbol, symbol list) BatMap.t) BatMap.t -> symbol BatStack.t -> symbol list -> bool
= fun parsing_table stack w ->
  match w with
  | [] -> raise (Failure "XX")
  | a::tl ->
    let x = BatStack.pop stack in
    if x = End then a = End
    else
    (
      if x = a then parse_loop parsing_table stack tl
      else
        try
          let slst = BatMap.find a (BatMap.find x parsing_table) in
          let stack = List.fold_right (fun s st -> BatStack.push s st ; st) slst stack in
          parse_loop parsing_table stack w
        with Not_found -> false
    )

let parse : cfg -> symbol list -> bool
=fun cfg sentence ->
  match cfg with (_, _, start_symbol, _) ->
  let parsing_table = construct_parsing_table cfg in
  let stack = BatStack.create () in
  BatStack.push End stack ; BatStack.push start_symbol stack ;
  parse_loop parsing_table stack sentence
