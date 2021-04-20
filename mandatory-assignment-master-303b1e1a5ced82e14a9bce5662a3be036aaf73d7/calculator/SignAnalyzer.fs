module SignAnalyzer
open System

//let mutable counter = 0

let pg_structure input node0 node1 det =
  let mutable counter = 0
  let rec finished input =
    match input with
      | ConditionCmd(x,y) -> Not(x)
      | Brack(x,y) -> And((finished x),(finished y))
  let rec helper input node0 node1 =
      //guarded commands
      match input with
        | ConditionCmd(x,y)   -> counter <- counter + 1
                                 (node0, counter, Test(x))::(edges y counter node1)
        | Brack(x,y)          -> (helper x node0 node1)@(helper y node0 node1)
  and edges input node0 node1 =
      //commands
      match input with
        | VarAssignCmd(x,y)   -> (node0, node1, VarAssign(x,y))::[]
        | ArrAssignCmd(x,y,z) -> (node0, node1, ArrAssign(x,y,z))::[]
        | IfCmd(x)            -> helper x node0 node1
        | DoCmd(x)            -> [(node0, node1, Test(finished x))]@(helper x node0 node0)
        | SkipCmd             -> (node0, node1, Skip)::[]
        | Scolon(x,y)         -> counter <- counter + 1
                                 (edges x node0 counter)@(edges y counter node1)
  let rec cmd input node0 node1 =
    match input with
    | IfCmd(x) -> let E,d = gc x node0 node1 False
                  E
    | DoCmd(x) -> let E,d = gc x node0 node0 False
                  E@[(node0, node1, Test(Not(d)))]
    | x -> edges x node0 node1
  and gc input node0 node1 d =
    match input with
    | Brack(x,y) -> let (E1,d1) = gc x node0 node1 d
                    let (E2,d2) = gc y node0 node1 d1
                    (E1@E2, d2)
    | ConditionCmd(b,C) -> counter <- counter + 1
                           let E = edges C counter node1
                           ([(node0, counter, Test(And(b,Not(d))))]@E, Or(b,d))
  if det then
    (cmd input node0 node1)
  else
    (edges input node0 node1)

let rec update_memory difference_list mem node =
    match mem with
    | (n,vars)::mems when n = node -> (n,difference_list@vars)::mems
    | (n,vars)::mems               -> (n,vars)::(update_memory difference_list mems node)
    | _                            -> failwith "Memory update error"

let rec node_power_sets mem node =
    match mem with
    | (n,vars)::mems when n = node -> vars
    | (n,vars)::mems               -> node_power_sets mems node
    | _                            -> failwith "Error node_power_sets error"

let rec evaluate_var var mem =
    match mem with
    | (v,vars)::mems when v = var -> vars
    | (v,vars)::mems              -> evaluate_var var mems
    | _                           -> failwith "Variable evaluation error"

let rec remove_duplicates_helper power_sets power_result =
    match power_sets with
    | x::xs when List.contains x power_result -> remove_duplicates_helper xs power_result
    | x::xs                                   -> remove_duplicates_helper xs (x::power_result)
    | []                                      -> power_result
    | _                                       -> failwith "Duplicate removal error"

let rec remove_duplicates power_sets =
    remove_duplicates_helper power_sets []

//returns all values of a variable in memory for a given node (all combinations)
(*
let rec evaluate_var var mem node =
    match mem with
    | (n,vars)::mems when n = node  -> extract_value var vars []
    | (n,vars)::mems                -> evaluate_var var mems node
    | _                             -> failwith "Variable evaluation error"

let rec extract_value var vars results =
    match vars with
    | tuples::vs when List.contains (sub_extract_value var tuples) results -> extract_value var vs results
    | tuples::vs                                                           -> extract_value var vs (results@(sub_extract_value var tuples))
    | []                                                                   -> results
    | _                                                                    -> failwith "Array extraction error"

let rec sub_extract_value var tuples = 
    match tuples with
    | (name,values)::tupless when name = var -> values
    | tuple::tupless                         -> sub_extract_value var tupless
    | []                                     -> []
    | _                                      -> failwith "Array sub-extraction error"

let rec evaluate_arr arr index arr_list =
    match arr_list with
    | (a,xs)::ys when a = arr -> extract_value xs index
    | (a,xs)::ys              -> evaluate_arr arr index ys
    | _                       -> failwith "Array evaluation error"

*)

let evaluate_plus x y =
    match x,y with 
    | MinusSign,MinusSign -> MinusSign::[]
    | MinusSign,ZeroSign  -> MinusSign::[]
    | MinusSign,PlusSign  -> MinusSign::ZeroSign::PlusSign::[]
    | ZeroSign,MinusSign  -> MinusSign::[]
    | ZeroSign,ZeroSign   -> ZeroSign::[]
    | ZeroSign,PlusSign   -> PlusSign::[]
    | PlusSign,MinusSign  -> MinusSign::ZeroSign::PlusSign::[]
    | PlusSign,ZeroSign   -> PlusSign::[]
    | PlusSign,PlusSign   -> PlusSign::[]
    | _                   -> failwith "Evaluation of type evaluate_plus error"

let evaluate_minus x y =
    match x,y with 
    | MinusSign,MinusSign -> MinusSign::ZeroSign::PlusSign::[]
    | MinusSign,ZeroSign  -> MinusSign::[]
    | MinusSign,PlusSign  -> MinusSign::[]
    | ZeroSign,MinusSign  -> PlusSign::[]
    | ZeroSign,ZeroSign   -> ZeroSign::[]
    | ZeroSign,PlusSign   -> MinusSign::[]
    | PlusSign,MinusSign  -> PlusSign::[]
    | PlusSign,ZeroSign   -> PlusSign::[]
    | PlusSign,PlusSign   -> MinusSign::ZeroSign::PlusSign::[]
    | _                   -> failwith "Evaluation of type evaluate_minus error"

let evaluate_times x y =
    match x,y with 
    | MinusSign,MinusSign -> PlusSign::[]
    | MinusSign,ZeroSign  -> ZeroSign::[]
    | MinusSign,PlusSign  -> MinusSign::[]
    | ZeroSign,MinusSign  -> ZeroSign::[]
    | ZeroSign,ZeroSign   -> ZeroSign::[]
    | ZeroSign,PlusSign   -> ZeroSign::[]
    | PlusSign,MinusSign  -> MinusSign::[]
    | PlusSign,ZeroSign   -> ZeroSign::[]
    | PlusSign,PlusSign   -> PlusSign::[]
    | _                   -> failwith "Evaluation of type evaluate_times error"

let evaluate_division x y =
    match x,y with 
    | MinusSign,MinusSign -> PlusSign::[]
    | MinusSign,ZeroSign  -> []
    | MinusSign,PlusSign  -> MinusSign::[]
    | ZeroSign,MinusSign  -> ZeroSign::[]
    | ZeroSign,ZeroSign   -> []
    | ZeroSign,PlusSign   -> ZeroSign::[]
    | PlusSign,MinusSign  -> MinusSign::[]
    | PlusSign,ZeroSign   -> []
    | PlusSign,PlusSign   -> PlusSign::[]
    | _                   -> failwith "Evaluation of type evaluate_division error"

let evaluate_pow x y =
    match x,y with 
    | MinusSign,MinusSign -> MinusSign::PlusSign::[]
    | MinusSign,ZeroSign  -> PlusSign::[]
    | MinusSign,PlusSign  -> MinusSign::PlusSign::[]
    | ZeroSign,MinusSign  -> []
    | ZeroSign,ZeroSign   -> PlusSign::[]
    | ZeroSign,PlusSign   -> []
    | PlusSign,MinusSign  -> PlusSign::[]
    | PlusSign,ZeroSign   -> PlusSign::[]
    | PlusSign,PlusSign   -> PlusSign::[]
    | _                   -> failwith "Evaluation of type evaluate_pow error"

let evaluate_uminus x =
    match x with 
    | MinusSign -> PlusSign::[]
    | ZeroSign  -> ZeroSign::[]
    | PlusSign  -> MinusSign::[]
    | _         -> failwith "Evaluation of type evaluate_uminus error"

let evaluate_sign x =
    match x with 
    | 0.0            -> ZeroSign::[]
    | x when x<0.0   -> MinusSign::[]
    | x when x>0.0   -> PlusSign::[]
    | _              -> failwith "Evaluation of type evaluate_sign error"

let evaluate_equal x y =
    match x,y with 
    | MinusSign,MinusSign -> true
    | MinusSign,ZeroSign  -> false
    | MinusSign,PlusSign  -> false
    | ZeroSign,MinusSign  -> false
    | ZeroSign,ZeroSign   -> true
    | ZeroSign,PlusSign   -> false
    | PlusSign,MinusSign  -> false
    | PlusSign,ZeroSign   -> false
    | PlusSign,PlusSign   -> true
    | _                   -> failwith "Evaluation of type evaluate_equal error"

let evaluate_nequal x y =
    match x,y with 
    | MinusSign,MinusSign -> true
    | MinusSign,ZeroSign  -> true
    | MinusSign,PlusSign  -> true
    | ZeroSign,MinusSign  -> true
    | ZeroSign,ZeroSign   -> false
    | ZeroSign,PlusSign   -> true
    | PlusSign,MinusSign  -> true
    | PlusSign,ZeroSign   -> true
    | PlusSign,PlusSign   -> true
    | _                   -> failwith "Evaluation of type evaluate_nequal error"

let evaluate_greater_equal x y =
    match x,y with 
    | MinusSign,MinusSign -> true
    | MinusSign,ZeroSign  -> false
    | MinusSign,PlusSign  -> false
    | ZeroSign,MinusSign  -> true
    | ZeroSign,ZeroSign   -> true
    | ZeroSign,PlusSign   -> false
    | PlusSign,MinusSign  -> true
    | PlusSign,ZeroSign   -> true
    | PlusSign,PlusSign   -> true
    | _                   -> failwith "Evaluation of type evaluate_greater_equal error"

let evaluate_smaller_equal x y =
    match x,y with 
    | MinusSign,MinusSign -> true
    | MinusSign,ZeroSign  -> true
    | MinusSign,PlusSign  -> true
    | ZeroSign,MinusSign  -> false
    | ZeroSign,ZeroSign   -> true
    | ZeroSign,PlusSign   -> true
    | PlusSign,MinusSign  -> false
    | PlusSign,ZeroSign   -> false
    | PlusSign,PlusSign   -> true
    | _                   -> failwith "Evaluation of type evaluate_smaller_equal error"

let evaluate_greater x y =
    match x,y with 
    | MinusSign,MinusSign -> true
    | MinusSign,ZeroSign  -> false
    | MinusSign,PlusSign  -> false
    | ZeroSign,MinusSign  -> true
    | ZeroSign,ZeroSign   -> false
    | ZeroSign,PlusSign   -> false
    | PlusSign,MinusSign  -> true
    | PlusSign,ZeroSign   -> true
    | PlusSign,PlusSign   -> true
    | _                   -> failwith "Evaluation of type evaluate_greater error"

let evaluate_smaller x y =
    match x,y with 
    | MinusSign,MinusSign -> true
    | MinusSign,ZeroSign  -> true
    | MinusSign,PlusSign  -> true
    | ZeroSign,MinusSign  -> false
    | ZeroSign,ZeroSign   -> false
    | ZeroSign,PlusSign   -> true
    | PlusSign,MinusSign  -> false
    | PlusSign,ZeroSign   -> false
    | PlusSign,PlusSign   -> true
    | _                   -> failwith "Evaluation of type evaluate_smaller error"

let rec evaluate_derived_expr arithmetic arg0 arg1 =
    match arithmetic with
    | Times(x,y)        -> evaluate_times arg0 arg1
    | Div(x,y)          -> evaluate_division arg0 arg1
    | Plus(x,y)         -> evaluate_plus arg0 arg1
    | Minus(x,y)        -> evaluate_minus arg0 arg1
    | Pow(x,y)          -> evaluate_pow arg0 arg1
    | _                 -> failwith "Derived expression evaluation error"

let evaluate_derived_bool test arg0 arg1 =
    match test with
    | Equal(x,y)        -> evaluate_equal arg0 arg1
    | Nequal(x,y)       -> evaluate_nequal arg0 arg1
    | GreaterEqual(x,y) -> evaluate_greater_equal arg0 arg1
    | SmallerEqual(x,y) -> evaluate_smaller_equal arg0 arg1
    | Greater(x,y)      -> evaluate_greater arg0 arg1
    | Smaller(x,y)      -> evaluate_smaller arg0 arg1
    | _                 -> failwith "Derived boolean evaluation error"

let rec evaluate_uminus_list value_list =
    match value_list with
    | x::xs -> (evaluate_uminus x)@(evaluate_uminus_list xs)
    | []    -> []
    | _     -> failwith "Error evaluate_uminus_list error"

let rec all_expr_combinations_helper2 expr value value_list =
    match value_list with
    | x::xs -> (evaluate_derived_expr expr value x)@(all_expr_combinations_helper2 expr value xs)
    | []    -> []
    | _     -> failwith "Error all_expr_combinations_helper2 error"

let rec all_expr_combinations_helper1 expr value_list0 value_list1  =
    match value_list0 with
    | x::xs -> (all_expr_combinations_helper2 expr x value_list1)@(all_expr_combinations_helper1 expr xs value_list1)
    | []    -> []
    | _     -> failwith "Error all_expr_combinations_helper1 error"

let all_expr_combinations expr value_list0 value_list1 = 
    remove_duplicates (all_expr_combinations_helper1 expr value_list0 value_list1)

let rec all_abstract_combinations_helper bool value value_list =
    match value_list with
    | x::xs when evaluate_derived_bool bool value x -> true
    | x::xs                                         -> all_abstract_combinations_helper bool value xs
    | []                                            -> false
    | _                                             -> failwith "Error all_abstract_combinations_helper error"

let rec all_abstract_combinations bool value_list0 value_list1  =
    match value_list0 with
    | x::xs when all_abstract_combinations_helper bool x value_list1 -> true
    | x::xs                                                          -> all_abstract_combinations bool xs value_list1
    | []                                                             -> false
    | _                                                              -> failwith "Error all_abstract_combinations error"

//memory -> power_sets -> power_set

let rec evaluate_expr expr mem =
    match expr with
    | Num(x)            -> evaluate_sign x
    | Var(x)            -> evaluate_var x mem
    | Times(x,y)        -> all_expr_combinations expr (evaluate_expr x mem) (evaluate_expr y mem)
    | Div(x,y)          -> all_expr_combinations expr (evaluate_expr x mem) (evaluate_expr y mem)
    | Plus(x,y)         -> all_expr_combinations expr (evaluate_expr x mem) (evaluate_expr y mem)
    | Minus(x,y)        -> all_expr_combinations expr (evaluate_expr x mem) (evaluate_expr y mem)
    | Pow(x,y)          -> all_expr_combinations expr (evaluate_expr x mem) (evaluate_expr y mem)
    | Uminus(x)         -> remove_duplicates (evaluate_uminus_list (evaluate_expr x mem))
    | ArrIndex(x,y)     -> evaluate_var x mem
    | _                 -> failwith "Expression evaluation error"

let rec evaluate_bool bool mem =
    match bool with
    | True              -> true
    | False             -> false
    | Band(x,y)         -> (evaluate_bool x mem) && (evaluate_bool y mem)
    | Bor(x,y)          -> (evaluate_bool x mem) || (evaluate_bool y mem)
    | And(x,y)          -> (evaluate_bool x mem) && (evaluate_bool y mem)
    | Or(x,y)           -> (evaluate_bool x mem) || (evaluate_bool y mem)
    | Equal(x,y)        -> all_abstract_combinations bool (evaluate_expr x mem) (evaluate_expr y mem)
    | Nequal(x,y)       -> all_abstract_combinations bool (evaluate_expr x mem) (evaluate_expr y mem)
    | Not(x)            -> not (evaluate_bool x mem)
    | GreaterEqual(x,y) -> all_abstract_combinations bool (evaluate_expr x mem) (evaluate_expr y mem)
    | SmallerEqual(x,y) -> all_abstract_combinations bool (evaluate_expr x mem) (evaluate_expr y mem)
    | Greater(x,y)      -> all_abstract_combinations bool (evaluate_expr x mem) (evaluate_expr y mem)
    | Smaller(x,y)      -> all_abstract_combinations bool (evaluate_expr x mem) (evaluate_expr y mem)
    | _                 -> failwith "Boolean evaluation error"

let rec valid_power_sets vars test_action =
    match vars with
    | var::varss when evaluate_bool test_action var -> var::(valid_power_sets varss test_action)
    | var::varss                                    -> (valid_power_sets varss test_action)
    | []                                            -> []
    | _                                             -> failwith "Powerset validation error"

(*

let allowed edgeAction mem =
    match edgeAction with
        | Test(x)           -> evaluate_bool x mem
        | _                 -> true

let rec valid_edges pg_structure vars arrs node =
    match pg_structure with
    | (node0,node1,edgeAction)::xs when node0 = node && allowed edgeAction vars arrs -> (node0,node1,edgeAction)::(valid_edges xs vars arrs node)
    | (node0,node1,edgeAction)::xs                                                   -> valid_edges xs vars arrs node
    | []                                                                             -> []
    | _                                                                              -> failwith "Edge validation error"

*)

let rec update_abstract_values power_set var assigned_value =
    match power_set with
    | (x,values)::abstract_values when x = var -> (x,[assigned_value])::abstract_values
    | (x,values)::abstract_values              -> (x,values)::(update_abstract_values abstract_values var assigned_value)
    | []                                       -> []
    | _                                        -> failwith "Value update error"

let rec assigned_power_sets_helper power_set var assigned_values =
    match assigned_values with
    | x::xs -> (update_abstract_values power_set var x)::(assigned_power_sets_helper power_set var xs)
    | []    -> []
    | _     -> failwith "Error  assigned_power_sets_helper error"

let rec assigned_power_sets power_sets var assigned_expr =
    match power_sets with
    | x::xs -> (assigned_power_sets_helper x var (evaluate_expr assigned_expr x))@(assigned_power_sets xs var assigned_expr)
    | []    -> []
    | _     -> failwith "Error  assigned_power_sets error"

let rec add_abstract_values power_set var assigned_value =
    match power_set with
    | (x,values)::abstract_values when x = var && List.contains assigned_value values -> (x,values)::abstract_values
    | (x,values)::abstract_values when x = var                                        -> (x,assigned_value::values)::abstract_values
    | (x,values)::abstract_values                                                     -> (x,values)::(update_abstract_values abstract_values var assigned_value)
    | []                                                                              -> []
    | _                                                                               -> failwith "Value addition error"

let rec assigned_power_sets_arr_helper power_set arr assigned_values =
    match assigned_values with
    | x::xs -> (add_abstract_values power_set arr x)::(assigned_power_sets_helper power_set arr xs)
    | []    -> []
    | _     -> failwith "Error  assigned_power_sets_arr_helper error"

let rec assigned_power_sets_arr power_sets arr assigned_expr =
    match power_sets with
    | x::xs -> (assigned_power_sets_helper x arr (evaluate_expr assigned_expr x))@(assigned_power_sets xs arr assigned_expr)
    | []    -> []
    | _     -> failwith "Error  assigned_power_sets_arr error"

let random n = (new System.Random()).Next(0, n)

let rec interpret_var var value var_list =
    match var_list with
    | (x,n)::xs when x = var  -> (x,value)::xs
    | (x,n)::xs               -> (x,n)::(interpret_var var value xs)
    | _                       -> failwith "Variable interpretation error"

let rec update_arr index value value_list =
    match value_list with
    | x::xs when index = 0    -> value::xs
    | x::xs                   -> x::(update_arr (index-1) value xs)
    | _                       -> failwith "Array update error"

let rec interpret_arr arr index value arr_list =
    match arr_list with
    | (a,xs)::ys when a = arr -> (a,update_arr index value xs)::ys
    | (a,xs)::ys              -> (a,xs)::interpret_arr arr index value ys
    | _                       -> failwith "Array interpretation error"

let arrow x =
    match x with
    | 0  -> "▷"
    | -1 -> "◀"
    | n  -> (string n)

let rec format_vars vars =
    match vars with
    | (x,n)::xs -> (string x) + ": " + (string n) + "\n" + (format_vars xs)
    | []        -> ""

let rec format_arrs arrs =
    match arrs with
    | (a,xs)::ys -> (string a) + ": " + (string xs) + "\n" + (format_arrs ys)
    | []         -> ""

let formatter node vars arrs =
    "Node: q" + (arrow node) + "\n" + (format_vars vars) + (format_arrs arrs)

(*
let rec runner pg_structure vars arrs node_current node_final steps =
    //vars = [("x",2);("y",5)]
    //arrs = [("X",[2;3]]);("Y",[5])]
    let valid_list = valid_edges pg_structure vars arrs node_current
    let length = List.fold (fun s x -> s + 1) 0 valid_list
    let edge =  if length <> 0 then
                    extract_value valid_list (random length)
                else
                    (node_current,node_final,Skip)
    match edge with
    | (-1,-1,action)                            -> "Status: terminated \n" + formatter node_current vars arrs
    | (node0,node1,action) when length = 0      -> "Status: stuck \n" + formatter node_current vars arrs
    | (node0,node1,action) when steps = 0       -> "Status: out of steps \n" + formatter node_current vars arrs
    | (node0,node1,action)                      -> match action with
                                                    | VarAssign(x,y)     -> runner pg_structure (interpret_var x (evaluate_expr y vars arrs) vars) arrs node1 node_final (steps-1)
                                                    | ArrAssign(x,y,z)   -> runner pg_structure vars (interpret_arr x (Convert.ToInt32(evaluate_expr y vars arrs)) (evaluate_expr z vars arrs) arrs) node1 node_final (steps-1)
                                                    | Test(x)            -> runner pg_structure vars arrs node1 node_final (steps-1)
                                                    | Skip               -> runner pg_structure vars arrs node1 node_final (steps-1)
*)

let rec outgoing_edges pg_structure node =
    match pg_structure with
    | (node0,node1,action)::pgss when node0 = node -> (node0,node1,action)::(outgoing_edges pgss node)
    | (node0,node1,action)::pgss                   -> (outgoing_edges pgss node)
    | []                                           -> []
    | _                                            -> failwith "Error outgoing_edges error"

let rec build_difference_list_helper valid_set next_power_sets =
    match next_power_sets with
    | x::xs when x = valid_set -> true
    | x::xs                    -> build_difference_list_helper valid_set xs
    | []                       -> false
    | _                        -> failwith "Error build_difference_list_helper error"

let rec build_difference_list valid_power_sets next_power_sets =
    match valid_power_sets with
    | x::xs when build_difference_list_helper x next_power_sets -> build_difference_list xs next_power_sets
    | x::xs                                                     -> x::(build_difference_list xs next_power_sets)
    | []                                                        -> []
    | _                                                         -> failwith "Error build_difference_list error"

let pop_queue queue =
    match queue with
    | edge::queues -> Some (edge,queues)
    | []           -> None
    | _            -> failwith "Queue popping error"

let valid_combinations memory queue =
    match queue with
    | (node0,node1,VarAssign(x,y))::queues   -> remove_duplicates (assigned_power_sets (node_power_sets memory node0) x y)
    | (node0,node1,ArrAssign(x,y,z))::queues -> remove_duplicates (assigned_power_sets_arr (node_power_sets memory node0) x z)
    | (node0,node1,Test(x))::queues          -> valid_power_sets (node_power_sets memory node0) x
    | (node0,node1,Skip)::queues             -> (node_power_sets memory node0)
    | _                                      -> failwith "Combination validation error"

let rec queue_initializer pg_structure node =
    match pg_structure with
    | (node0,node1,edge_action)::pgss when node0 = node -> (node0,node1,edge_action)::(queue_initializer pgss node)
    | []                                                -> []
    | (node0,node1,edge_action)::pgss                   -> (queue_initializer pgss node)
    | _                                                 -> failwith "Queue initialization error"

let rec abstract_runner pg_structure memory node_final queue =
    //vars = [("x",PlusSign);("y",ZeroSign)]
    //arrs = [("X",[PlusSign;ZeroSign]]);("Y",[MinusSign])]
    let popped_queue = pop_queue queue
    if popped_queue.IsSome then
        let valid_power_sets_list = valid_combinations memory queue
        let edge, queues = popped_queue.Value
        let node0, node1, action = edge
        let difference_list = build_difference_list valid_power_sets_list (node_power_sets memory (node1))
        let new_memory = update_memory difference_list memory node1
        if not (List.isEmpty difference_list) then
            let mutable queues = queues
            queues <- queues@(outgoing_edges pg_structure node1)
        abstract_runner pg_structure new_memory node_final queues
    else 
        //node_power_sets memory node_final
        memory

let abstract_initializer pg_structure memory node_start node_final =
    abstract_runner pg_structure memory node_final (queue_initializer pg_structure node_start)
