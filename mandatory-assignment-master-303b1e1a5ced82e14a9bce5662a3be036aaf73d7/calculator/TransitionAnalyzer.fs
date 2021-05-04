module TransitionAnalyzer
open System
#load "SignAnalyzer.fs"
open SignAnalyzer

(*
 * TODO: use the semantics function in combination with evaluate_expr and evaluate_bool
 * in the interpreter file to implement the reach1 function. 
 *)

let print_and_format state

let semantics command =
    match command with
    | VarAssign(x,y)   -> runner pg_structure (interpret_var x (evaluate_expr y vars arrs) vars) arrs node1 node_final (steps-1)
    | ArrAssign(x,y,z) -> runner pg_structure vars (interpret_arr x (Convert.ToInt32(evaluate_expr y vars arrs)) (evaluate_expr z vars arrs) arrs) node1 node_final (steps-1)
    | Test(x)          -> runner pg_structure vars arrs node1 node_final (steps-1)
    | Skip             -> runner pg_structure vars arrs node1 node_final (steps-1)

let rec reach1 pg_structure state =


let rec reachable_stuck_states pg_structure visited to_explore limit counter =
    let state = pop_queue to_explore
    if state.isSome && counter < limit then 
        let s,to_explore_xs = state.Value
        if not (List.contains s visited) then
            let reached = reach1 pg_structure s
            if List.isEmpty (reached) then
                print_and_format s
            reachable_stuck_states pg_structure (s::visited) (to_explore_xs@reached) limit (counter+1)
        else
            reachable_stuck_states pg_structure visited to_explore_xs limit (counter+1)
