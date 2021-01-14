open Regex

exception Not_implemented

let rec regex2nfa : Regex.t -> Nfa.t 
=fun regex ->
  let nfa = Nfa.create_new_nfa () in
    match regex with
    | Empty -> nfa
    | Epsilon ->
      let (fs, nfa') = Nfa.create_state nfa in
      Nfa.add_final_state (Nfa.add_epsilon_edge nfa' ((Nfa.get_initial_state nfa'), fs)) fs
    | Alpha a ->
      let (fs, nfa') = Nfa.create_state nfa in
      let is = (Nfa.get_initial_state nfa') in
      let nfa'' = Nfa.add_final_state nfa' fs in
      Nfa.add_edge nfa'' (is, a, fs)
    | OR (r1, r2) ->
      let (nfa1, nfa2) = (regex2nfa r1, regex2nfa r2) in
      let is = Nfa.get_initial_state nfa in
      let (fs, nfa') = Nfa.create_state nfa in
      let nfa'' = Nfa.add_final_state nfa' fs in
      let (is1, fs1) = (Nfa.get_initial_state nfa1, Nfa.get_final_states nfa1) in
      let (is2, fs2) = (Nfa.get_initial_state nfa2, Nfa.get_final_states nfa2) in
      let n_nfa = add_nfa (add_nfa nfa'' nfa1) nfa2 in
      let n_nfa = Nfa.add_epsilon_edge (Nfa.add_epsilon_edge n_nfa (is, is1)) (is, is2) in
      let add_final_edge = fun f nfa -> Nfa.add_epsilon_edge nfa (f, fs) in
      let n_nfa = BatSet.fold add_final_edge fs1 n_nfa in
      BatSet.fold add_final_edge fs2 n_nfa
    | CONCAT (r1, r2) -> 
      let (nfa1, nfa2) = (regex2nfa r1, regex2nfa r2) in
      let is = Nfa.get_initial_state nfa in
      let (fs, nfa') = Nfa.create_state nfa in
      let nfa'' = Nfa.add_final_state nfa' fs in
      let (is1, fs1) = (Nfa.get_initial_state nfa1, Nfa.get_final_states nfa1) in
      let (is2, fs2) = (Nfa.get_initial_state nfa2, Nfa.get_final_states nfa2) in
      let n_nfa = add_nfa (add_nfa nfa'' nfa1) nfa2 in
      let n_nfa = Nfa.add_epsilon_edge n_nfa (is, is1) in
      let n_nfa = BatSet.fold (fun f nfa -> Nfa.add_epsilon_edge nfa (f, is2)) fs1 n_nfa in
      BatSet.fold (fun f nfa -> Nfa.add_epsilon_edge nfa (f, fs)) fs2 n_nfa
    | STAR r1 ->
      let nfa1 = regex2nfa r1 in
      let is = Nfa.get_initial_state nfa in
      let (fs, nfa') = Nfa.create_state nfa in
      let (is1, fs1) = (Nfa.get_initial_state nfa1, Nfa.get_final_states nfa1) in
      let nfa'' = Nfa.add_final_state nfa' fs in
      let n_nfa = add_nfa nfa'' nfa1 in
      let n_nfa = Nfa.add_epsilon_edge (Nfa.add_epsilon_edge n_nfa (is, is1)) (is, fs) in
      let n_nfa = BatSet.fold (fun f nfa -> Nfa.add_epsilon_edge nfa (f, is1)) fs1 n_nfa in
      BatSet.fold (fun f nfa -> Nfa.add_epsilon_edge nfa (f, fs)) fs1 n_nfa

and add_nfa : Nfa.t -> Nfa.t -> Nfa.t
= fun nfa nfa' ->
  Nfa.add_edges (Nfa.add_states nfa (Nfa.get_states nfa')) (Nfa.get_edges nfa')

let rec nfa2dfa : Nfa.t -> Dfa.t
=fun nfa ->
  let d0 = epsilon_closure nfa (BatSet.add (Nfa.get_initial_state nfa) BatSet.empty) in
  let dfa = Dfa.create_new_dfa d0 in
  let d_states = BatSet.add d0 BatSet.empty in
  let worklist = BatSet.add d0 BatSet.empty in
  let edges = BatSet.empty in
  let rec iter_worklist : Dfa.states -> (Dfa.edge BatSet.t) -> Dfa.states -> (Dfa.states * (Dfa.edge BatSet.t))
  = fun d_states edges wlst ->
    if BatSet.is_empty wlst then (d_states, edges)
    else
      let (q, wlst) = BatSet.pop wlst in
      let rec iter_alpha : alphabet -> (Dfa.states * (Dfa.edge BatSet.t) * Dfa.states) -> (Dfa.states * (Dfa.edge BatSet.t) * Dfa.states)
      = fun a (d_states, edges, worklist) ->
        let reach = BatSet.fold (fun s r -> BatSet.union (Nfa.get_next_state nfa s a) r) q BatSet.empty in
        let t = epsilon_closure nfa reach in
        let nd_states = BatSet.add t d_states in
        let n_edge = BatSet.add (q, a, t) edges in
        if BatSet.equal d_states nd_states then (nd_states, n_edge, worklist)
        else let worklist = BatSet.add t worklist in (nd_states, n_edge, worklist)
      in
      let (d_states, edges, wlst) = List.fold_right iter_alpha [A;B] (d_states, edges, wlst) in
      iter_worklist d_states edges wlst
  in
  let (d_states, edges) = iter_worklist d_states edges worklist in
  let dfa = BatSet.fold (fun s d -> Dfa.add_state d s) d_states dfa in
  let dfa = BatSet.fold (fun e d -> Dfa.add_edge d e) edges dfa in
  let dfa = BatSet.fold (fun f d -> if BatSet.is_empty (BatSet.intersect (Nfa.get_final_states nfa) f) then d else Dfa.add_final_state d f) d_states dfa in
  dfa

and epsilon_closure : Nfa.t -> Nfa.states -> Nfa.states
= fun nfa st ->
  let n_st = BatSet.fold (fun s ss -> BatSet.union ss (Nfa.get_next_state_epsilon nfa s)) st st in
  if BatSet.equal n_st st then n_st
  else epsilon_closure nfa n_st
 
(* Do not modify this function *)
let regex2dfa : Regex.t -> Dfa.t
=fun regex -> 
  let nfa = regex2nfa regex in
  let dfa = nfa2dfa nfa in
    dfa

let run_dfa : Dfa.t -> alphabet list -> bool
=fun dfa str ->
  let init_state = Dfa.get_initial_state dfa in
  let f_state = List.fold_left (fun st a -> Dfa.get_next_state dfa st a) init_state str in
  Dfa.is_final_state dfa f_state

