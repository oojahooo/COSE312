let t_num = ref (-1)
let new_t () = t_num := !t_num + 1 ; ".t" ^ (string_of_int (!t_num))

let l_num = ref 0
let new_l () = l_num := !l_num + 1 ; !l_num

let trans_bop e =
  match e with
  | S.ADD _ -> T.ADD
  | S.SUB _ -> T.SUB
  | S.MUL _ -> T.MUL
  | S.DIV _ -> T.DIV
  | S.LT _ -> T.LT
  | S.LE _ -> T.LE
  | S.GT _ -> T.GT
  | S.GE _ -> T.GE
  | S.EQ _ -> T.EQ
  | S.AND _ -> T.AND
  | S.OR _ -> T.OR
  | _ -> raise (Failure "Problem at trans_bop")

let trans_uop e =
  match e with
  | S.MINUS _ -> T.MINUS
  | S.NOT _ -> T.NOT
  | _ -> raise (Failure "Problem at trans_uop")

let rec trans_exp : S.exp -> T.var * (T.linstr list)
=fun exp ->
  match exp with
  | S.NUM n -> let t = new_t () in (t, [(T.dummy_label, T.COPYC (t, n))])
  | S.LV lv ->
    (match lv with
     | S.ID x -> let t = new_t () in (t, [(T.dummy_label, T.COPY (t, x))])
     | S.ARR (x, e) ->
       let (t1, code) = trans_exp e in
       let t2 = new_t () in
       (t2, code@[(T.dummy_label, T.LOAD (t2, (x, t1)))]))
  | S.ADD (e1, e2) | S.SUB (e1, e2) | S.MUL (e1, e2) | S.DIV (e1, e2)
  | S.LT (e1, e2) | S.LE (e1, e2) | S.GT (e1, e2) | S.GE (e1, e2)
  | S.EQ (e1, e2) | S.AND (e1, e2) | S.OR (e1, e2) ->
    let (t1, code1) = trans_exp e1 in
    let (t2, code2) = trans_exp e2 in
    let t3 = new_t () in
    (t3, code1@code2@[(T.dummy_label, T.ASSIGNV (t3, trans_bop exp, t1, t2))])
  | S.MINUS e | S.NOT e ->
    let (t1, code) = trans_exp e in
    let t2 = new_t () in
    (t2, code@[(T.dummy_label, T.ASSIGNU (t2, trans_uop exp, t1))])

and trans_stmt : S.stmt -> T.linstr list
=fun stmt ->
  match stmt with
  | S.ASSIGN (lv, e) ->
    let (t1, code1) = trans_exp e in
    (match lv with
     | S.ID x -> code1@[(T.dummy_label, T.COPY (x, t1))]
     | S.ARR (x, e1) ->
       let (t2, code2) = trans_exp e1 in code2@code1@[(T.dummy_label, T.STORE ((x, t2), t1))])
  | S.IF (e, s1, s2) ->
    let (t, code) = trans_exp e in
    let code_t = trans_stmt s1 in
    let code_f = trans_stmt s2 in
    let (l_t, l_f, l_x) = (new_l (), new_l (), new_l ()) in
    code@
    [(T.dummy_label, T.CJUMP (t, l_t))]@
    [(T.dummy_label, T.UJUMP l_f)]@
    [(l_t, T.SKIP)]@
    code_t@
    [(T.dummy_label, T.UJUMP l_x)]@
    [(l_f, T.SKIP)]@
    code_f@
    [(T.dummy_label, T.UJUMP l_x)]@
    [(l_x, T.SKIP)]
  | S.WHILE (e, s) ->
    let (t, code) = trans_exp e in
    let code_b = trans_stmt s in
    let (l_e, l_x) = (new_l (), new_l ()) in
    [(l_e, T.SKIP)]@
    code@
    [(T.dummy_label, T.CJUMPF (t, l_x))]@
    code_b@
    [(T.dummy_label, T.UJUMP l_e)]@
    [(l_x, T.SKIP)]
  | S.DOWHILE (s, e) -> (trans_stmt s)@(trans_stmt (S.WHILE (e, s)))
  | S.READ x -> [(T.dummy_label, T.READ x)]
  | S.PRINT e -> let (t, code) = trans_exp e in code@[(T.dummy_label, T.WRITE t)]
  | S.BLOCK b -> trans_block b

and trans_decl : S.decl -> T.linstr list
=fun decl ->
  match decl with
  | (S.TINT, x) -> [(T.dummy_label, T.COPYC (x, 0))]
  | (S.TARR n, x) -> [(T.dummy_label, T.ALLOC (x, n))]

and trans_block (decls, stmts) =
  List.fold_left (fun linstrs s -> linstrs@(trans_stmt s))
    (List.fold_left (fun linstrs d -> linstrs@(trans_decl d)) [] decls) stmts

let translate : S.program -> T.program
=fun s -> (trans_block s)@[(T.dummy_label, T.HALT)]
