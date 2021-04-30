module SecurityAnalyzer
open System

//
//General duplicate remover: removes duplicates from list if any
//

let rec remove_duplicates_helper list resulting_list =
    match list with
    | x::xs when List.contains x resulting_list -> remove_duplicates_helper xs resulting_list
    | x::xs                                     -> remove_duplicates_helper xs (x::resulting_list)
    | []                                        -> resulting_list
    | _                                         -> failwith "Duplicate removal error"

let rec remove_duplicates list =
    remove_duplicates_helper list []

//
//Finds all outgoing edges from a node
//

let rec outgoing_edges pg_structure node =
    match pg_structure with
    | (node0,node1,action)::pgss when node0 = node -> (node0,node1,action)::(outgoing_edges pgss node)
    | (node0,node1,action)::pgss                   -> (outgoing_edges pgss node)
    | []                                           -> []
    | _                                            -> failwith "Error outgoing_edges error"

//
//returns true if an element is contained in a list
//

let rec element_contained_in_list element element_list =
    match element_list with
    | x::xs when x = element -> true
    | x::xs                  -> element_contained_in_list element xs
    | []                     -> false

//
//removes the outgoing edges from a list if they have already been visited
//

let rec remove_visited_from_outgoing outgoing_list visited_list =
    match outgoing_list with
    | (node0,node1,action)::xs when element_contained_in_list node1 visited_list -> remove_visited_from_outgoing xs visited_list
    | x::xs                                                                      -> x::(remove_visited_from_outgoing xs visited_list)
    | []                                                                         -> []

//
//arithmetic and boolean evaluation as copied from the other files
//

let rec evaluate_expr expr =
    match expr with
    | Num(x)            -> []
    | Var(x)            -> x::[]
    | Times(x,y)        -> (evaluate_expr x)@(evaluate_expr y)
    | Div(x,y)          -> (evaluate_expr x)@(evaluate_expr y)
    | Plus(x,y)         -> (evaluate_expr x)@(evaluate_expr y)
    | Minus(x,y)        -> (evaluate_expr x)@(evaluate_expr y)
    | Pow(x,y)          -> (evaluate_expr x)@(evaluate_expr y)
    | Uminus(x)         -> (evaluate_expr x)
    | ArrIndex(x,y)     -> [x]@(evaluate_expr y)

let rec evaluate_bool bool =
    match bool with
    | True              -> []
    | False             -> []
    | Band(x,y)         -> (evaluate_bool x)@(evaluate_bool y)
    | Bor(x,y)          -> (evaluate_bool x)@(evaluate_bool y)
    | And(x,y)          -> (evaluate_bool x)@(evaluate_bool y)
    | Or(x,y)           -> (evaluate_bool x)@(evaluate_bool y)
    | Equal(x,y)        -> (evaluate_expr x)@(evaluate_expr y)
    | Nequal(x,y)       -> (evaluate_expr x)@(evaluate_expr y)
    | Not(x)            -> (evaluate_bool x)
    | GreaterEqual(x,y) -> (evaluate_expr x)@(evaluate_expr y)
    | SmallerEqual(x,y) -> (evaluate_expr x)@(evaluate_expr y)
    | Greater(x,y)      -> (evaluate_expr x)@(evaluate_expr y)
    | Smaller(x,y)      -> (evaluate_expr x)@(evaluate_expr y)

//
//Logic part that determines how each variable affects each other according to the edge action, and updates the actual flow accordingly
//

let rec insert_flows var var_list =
    match var_list with
    | x::xs -> (x,var)::(insert_flows var xs)
    | []    -> []

let update_flow_var var value actual_flow =
    remove_duplicates ((insert_flows var (evaluate_expr value))@actual_flow)

let update_flow_arr var index value actual_flow =
    remove_duplicates ((insert_flows var (evaluate_expr value))@(insert_flows var (evaluate_expr index))@actual_flow)

let update_conditionals test conditionals =
    remove_duplicates ((evaluate_bool test)@conditionals)

let update_memory memory action =
    match action,memory with
    | VarAssign(x,y),(actual_flow,conditionals)   -> ((update_flow_var x y actual_flow),conditionals)
    | ArrAssign(x,y,z),(actual_flow,conditionals) -> ((update_flow_arr x y z actual_flow),conditionals)
    | Test(x),(actual_flow,conditionals)          -> (actual_flow,(update_conditionals x conditionals))
    | Skip,_                                      -> memory

//
//Searcher and brancher that finds all possible paths to final node, but only passing throuch each loop once
//

let rec searcher pg_structure visited memory current_node final_node =
    let outgoing_list = remove_visited_from_outgoing (outgoing_edges pg_structure current_node) visited
    if current_node = final_node then
        memory
    else if outgoing_list.Length > 1 then
        remove_duplicates (branch_search pg_structure visited memory current_node final_node outgoing_list)
    else if outgoing_list.Length = 1 then
        remove_duplicates (branch_search pg_structure (current_node::visited) memory current_node final_node outgoing_list)
    else
        memory
and branch_search pg_structure visited memory current_node final_node outgoing_list =
    match outgoing_list with
    | (node0,node1,action)::xs -> (searcher pg_structure visited (update_memory memory action) node1 final_node)@(branch_search pg_structure visited memory current_node final_node xs)
    | []                       -> []

//memory is a tuple structure of actual_flow and conditionals: memory = (actual_flow,conditionals)
let searcher_initializer pg_structure start_node final_node =
    searcher pg_structure [] ([],[]) start_node final_node