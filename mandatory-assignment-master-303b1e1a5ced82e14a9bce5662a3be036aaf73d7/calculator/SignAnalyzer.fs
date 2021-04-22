module SignAnalyzer
open System

//
//Program graph constructor
//

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
//Arithmetic evaluation functions as per the books description
//

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

//
//Boolean evaluation functions as per the books description
//

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

//
//Expression evaluation: given an arithmetic expression type, evaluates two non-list abstract arguments for the specified expression
//

let rec evaluate_abstract_expr arithmetic arg0 arg1 =
    match arithmetic with
    | Times(x,y)        -> evaluate_times arg0 arg1
    | Div(x,y)          -> evaluate_division arg0 arg1
    | Plus(x,y)         -> evaluate_plus arg0 arg1
    | Minus(x,y)        -> evaluate_minus arg0 arg1
    | Pow(x,y)          -> evaluate_pow arg0 arg1
    | _                 -> failwith "Derived expression evaluation error"

//
//Boolean evaluation: given an boolean test type, evaluates two non-list abstract arguments for the specified boolean test
//

let evaluate_abstract_bool test arg0 arg1 =
    match test with
    | Equal(x,y)        -> evaluate_equal arg0 arg1
    | Nequal(x,y)       -> evaluate_nequal arg0 arg1
    | GreaterEqual(x,y) -> evaluate_greater_equal arg0 arg1
    | SmallerEqual(x,y) -> evaluate_smaller_equal arg0 arg1
    | Greater(x,y)      -> evaluate_greater arg0 arg1
    | Smaller(x,y)      -> evaluate_smaller arg0 arg1
    | _                 -> failwith "Derived boolean evaluation error"

//
//  Data structure naming
//
//  memory:     [ (node, [power_sets]) ; (node, [power_sets]) ; ... ]
//  power_sets: [ [power_set] ; [power_set] ; ... ]
//  power_set:  [ ("variable_name", [values]) ; ("variable_name", [values]) ; ... ]
//

//
//Sign evaluator: returns abstract value from decimal input
//

let evaluate_sign x =
    match x with 
    | 0.0            -> ZeroSign::[]
    | x when x<0.0   -> MinusSign::[]
    | x when x>0.0   -> PlusSign::[]
    | _              -> failwith "Evaluation of type evaluate_sign error"

//
//Variable evaluation: returns the list of value(s) for the inputted variable in the inputted power_set
//

let rec evaluate_var var power_set =
    match power_set with
    | (v,vars)::mems when v = var -> vars
    | (v,vars)::mems              -> evaluate_var var mems
    | _                           -> failwith "Variable evaluation error"

//
//all_expr_combinations is a helper function for evaluate_expr that takes lists of abstract values, finds all combinations between these lists, and evaluates them as non-list abstract expression
//

let rec all_expr_combinations_helper2 expr value value_list =
    match value_list with
    | x::xs -> (evaluate_abstract_expr expr value x)@(all_expr_combinations_helper2 expr value xs)
    | []    -> []
    | _     -> failwith "Error all_expr_combinations_helper2 error"

let rec all_expr_combinations_helper1 expr value_list0 value_list1  =
    match value_list0 with
    | x::xs -> (all_expr_combinations_helper2 expr x value_list1)@(all_expr_combinations_helper1 expr xs value_list1)
    | []    -> []
    | _     -> failwith "Error all_expr_combinations_helper1 error"

let all_expr_combinations expr value_list0 value_list1 = 
    remove_duplicates (all_expr_combinations_helper1 expr value_list0 value_list1)

//
//evaluate_uminus_list is similar to but only iterates through a single list
//

let rec evaluate_uminus_list value_list =
    match value_list with
    | x::xs -> (evaluate_uminus x)@(evaluate_uminus_list xs)
    | []    -> []
    | _     -> failwith "Error evaluate_uminus_list error"

//
//all_bool_combinations is a helper function for evaluate_bool that takes lists of abstract values, finds all combinations between these lists, and evaluates them as non-list abstract boolean tests
//

let rec all_bool_combinations_helper bool value value_list =
    match value_list with
    | x::xs when evaluate_abstract_bool bool value x -> true
    | x::xs                                         -> all_bool_combinations_helper bool value xs
    | []                                            -> false
    | _                                             -> failwith "Error all_abstract_combinations_helper error"

let rec all_bool_combinations bool value_list0 value_list1  =
    match value_list0 with
    | x::xs when all_bool_combinations_helper bool x value_list1 -> true
    | x::xs                                                          -> all_bool_combinations bool xs value_list1
    | []                                                             -> false
    | _                                                              -> failwith "Error all_abstract_combinations error"

//
//Expression evaluator that can reduce any decimal value and/or variable expression to sets of single abstract values and send these to be computed by smaller functions
//

let rec evaluate_expr expr power_set =
    match expr with
    | Num(x)            -> evaluate_sign x
    | Var(x)            -> evaluate_var x power_set
    | Times(x,y)        -> all_expr_combinations expr (evaluate_expr x power_set) (evaluate_expr y power_set)
    | Div(x,y)          -> all_expr_combinations expr (evaluate_expr x power_set) (evaluate_expr y power_set)
    | Plus(x,y)         -> all_expr_combinations expr (evaluate_expr x power_set) (evaluate_expr y power_set)
    | Minus(x,y)        -> all_expr_combinations expr (evaluate_expr x power_set) (evaluate_expr y power_set)
    | Pow(x,y)          -> all_expr_combinations expr (evaluate_expr x power_set) (evaluate_expr y power_set)
    | Uminus(x)         -> evaluate_uminus_list (evaluate_expr x power_set)
    | ArrIndex(x,y)     -> evaluate_var x power_set
    | _                 -> failwith "Expression evaluation error"

//
//Boolean evaluator that can reduce boolean tests to combinations of their boolean and/or arithmetic components and find whether it is possible for a combination to evaluate to true
//

let rec evaluate_bool bool power_set =
    match bool with
    | True              -> true
    | False             -> false
    | Band(x,y)         -> (evaluate_bool x power_set) && (evaluate_bool y power_set)
    | Bor(x,y)          -> (evaluate_bool x power_set) || (evaluate_bool y power_set)
    | And(x,y)          -> (evaluate_bool x power_set) && (evaluate_bool y power_set)
    | Or(x,y)           -> (evaluate_bool x power_set) || (evaluate_bool y power_set)
    | Equal(x,y)        -> all_bool_combinations bool (evaluate_expr x power_set) (evaluate_expr y power_set)
    | Nequal(x,y)       -> all_bool_combinations bool (evaluate_expr x power_set) (evaluate_expr y power_set)
    | Not(x)            -> not (evaluate_bool x power_set)
    | GreaterEqual(x,y) -> all_bool_combinations bool (evaluate_expr x power_set) (evaluate_expr y power_set)
    | SmallerEqual(x,y) -> all_bool_combinations bool (evaluate_expr x power_set) (evaluate_expr y power_set)
    | Greater(x,y)      -> all_bool_combinations bool (evaluate_expr x power_set) (evaluate_expr y power_set)
    | Smaller(x,y)      -> all_bool_combinations bool (evaluate_expr x power_set) (evaluate_expr y power_set)
    | _                 -> failwith "Boolean evaluation error"

//
//Power_sets extracter: returns the power_sets from memory for an inputted node
//

let rec power_sets_of_node memory node =
    match memory with
    | (n,vars)::mems when n = node -> vars
    | (n,vars)::mems               -> power_sets_of_node mems node
    | _                            -> failwith "Error power_sets_of_node error"

//
//Memory updator: returns the updated memory where difference_list has been added to the power_sets of a specified node
//

let rec update_memory difference_list memory node =
    match memory with
    | (n,vars)::mems when n = node -> (n,difference_list@vars)::mems
    | (n,vars)::mems               -> (n,vars)::(update_memory difference_list mems node)
    | _                            -> failwith "Memory update error"

//
//Power_sets tester: returns power_sets that passes a boolean test
//

let rec valid_power_sets power_sets bool_test =
    match power_sets with
    | power_set::power_setss when evaluate_bool bool_test power_set -> power_set::(valid_power_sets power_setss bool_test)
    | power_set::power_setss                                          -> (valid_power_sets power_setss bool_test)
    | []                                                              -> []
    | _                                                               -> failwith "Powerset validation error"

//
//Value replacor: replaces the old value of a variable in a power_set with a new one
//

let rec replace_abstract_values power_set var assigned_value =
    match power_set with
    | (x,values)::abstract_values when x = var -> (x,[assigned_value])::abstract_values
    | (x,values)::abstract_values              -> (x,values)::(replace_abstract_values abstract_values var assigned_value)
    | []                                       -> []
    | _                                        -> failwith "Value update error"

//
//Value adder: adds values to an array type variable in a power_set
//

let rec add_abstract_values power_set var assigned_value =
    match power_set with
    | (x,values)::vars when x = var && List.contains assigned_value values -> (x,values)::vars
    | (x,values)::vars when x = var                                        -> (x,assigned_value::values)::vars
    | (x,values)::vars                                                     -> (x,values)::(replace_abstract_values vars var assigned_value)
    | []                                                                   -> []
    | _                                                                    -> failwith "Value addition error"

//
//Variable assigner: evaluates an expression and assigns it to a specified variable in power_sets
//

let rec var_assignment_in_power_sets_helper power_set var assigned_values =
    match assigned_values with
    | x::xs -> (replace_abstract_values power_set var x)::(var_assignment_in_power_sets_helper power_set var xs)
    | []    -> []
    | _     -> failwith "Error  var_assignment_in_power_sets_helper error"

let rec var_assignment_in_power_sets power_sets var assigned_expr =
    match power_sets with
    | x::xs -> (var_assignment_in_power_sets_helper x var (evaluate_expr assigned_expr x))@(var_assignment_in_power_sets xs var assigned_expr)
    | []    -> []
    | _     -> failwith "Error var_assignment_in_power_sets error"

//
//Array assigner: evaluates an expression and assigns it to a specified array in power_sets
//

let rec arr_assignment_in_power_sets_helper power_set arr assigned_values =
    match assigned_values with
    | x::xs -> (add_abstract_values power_set arr x)::(var_assignment_in_power_sets_helper power_set arr xs)
    | []    -> []
    | _     -> failwith "Error  arr_assignment_in_power_sets_helper error"

let rec arr_assignment_in_power_sets power_sets arr assigned_expr =
    match power_sets with
    | x::xs -> (var_assignment_in_power_sets_helper x arr (evaluate_expr assigned_expr x))@(var_assignment_in_power_sets xs arr assigned_expr)
    | []    -> []
    | _     -> failwith "Error  arr_assignment_in_power_sets error"

//
//Outgoing edges returns a list of edges for a node in pg_structure
//

let rec outgoing_edges pg_structure node =
    match pg_structure with
    | (node0,node1,action)::pgss when node0 = node -> (node0,node1,action)::(outgoing_edges pgss node)
    | (node0,node1,action)::pgss                   -> (outgoing_edges pgss node)
    | []                                           -> []
    | _                                            -> failwith "Error outgoing_edges error"

//
//Difference list builder: finds the difference between two power_sets and returns a list with only the difference
//

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

//
//Queue popper: pops the queue ;)
//

let pop_queue queue =
    match queue with
    | edge::queues -> Some (edge,queues)
    | []           -> None
    | _            -> failwith "Queue popping error"

//
//valid_combinations travels an edge and builds a new hypothetical memory for combinations of the data that can succesfully travel the edge
//

let valid_combinations memory edge =
    match edge with
    | (node0,node1,VarAssign(x,y))   -> remove_duplicates (var_assignment_in_power_sets (power_sets_of_node memory node0) x y)
    | (node0,node1,ArrAssign(x,y,z)) -> remove_duplicates (arr_assignment_in_power_sets (power_sets_of_node memory node0) x z)
    | (node0,node1,Test(x))          -> valid_power_sets (power_sets_of_node memory node0) x
    | (node0,node1,Skip)             -> (power_sets_of_node memory node0)
    | _                              -> failwith "Combination validation error"

//
//Formatter: formats the power_sets uotput as per the project description
//

let prettify_sign abstract_type =
    match abstract_type with
    | PlusSign  -> "+"
    | ZeroSign  -> "0"
    | MinusSign -> "-"

let rec prettify abstract_list =
    match abstract_list with
    | x::[] -> (prettify_sign x)
    | x::xs -> (prettify_sign x) + "," + (prettify xs)
    | []    -> ""

let rec variable_formatter_helper power_set =
    match power_set with
    | (name,values)::vars -> " " + name + "      " + (variable_formatter_helper vars)
    | []                  -> "\n"

let variable_formatter power_sets =
    match power_sets with
    | power_set::power_setss -> variable_formatter_helper power_set
    | _                      -> ""

let rec print_spaces num =
    if num > 0 then 
        " " + print_spaces (num-1)
    else
        ""

let rec format_spaces char_list num =
    match char_list with
    | x::xs -> format_spaces xs (num+1)
    | []    -> print_spaces num

let rec value_formatter_helper power_set =
    match power_set with
    | (name,values)::vars -> "{" + (prettify values) + "}" + (format_spaces (Seq.toList ("{" + (prettify values) + "}")) 0)  + (value_formatter_helper vars)
    | []                  -> "\n"

let rec value_formatter power_sets =
    match power_sets with
    | power_set::power_setss -> (value_formatter_helper power_set) + (value_formatter power_setss)
    | _                      -> ""

let formatter power_sets =
    (variable_formatter power_sets) + (value_formatter power_sets)

//
//Main function
//

let rec abstract_runner pg_structure memory node_final queue =
    let popped_queue = pop_queue queue
    if popped_queue.IsSome then
        let edge, queues = popped_queue.Value
        let node0, node1, action = edge
        let valid_power_sets_list = valid_combinations memory edge
        let difference_list = build_difference_list valid_power_sets_list (power_sets_of_node memory (node1))
        let new_memory = update_memory difference_list memory node1
        if not (List.isEmpty difference_list) then
            abstract_runner pg_structure new_memory node_final (queues@(outgoing_edges pg_structure node1))
        else
            abstract_runner pg_structure new_memory node_final queues
    else 
        formatter (power_sets_of_node memory node_final)
        //memory

//
//Initializer: initializes the main function with an initial queue
//

let abstract_initializer pg_structure memory node_start node_final =
    abstract_runner pg_structure memory node_final (outgoing_edges pg_structure node_start)

