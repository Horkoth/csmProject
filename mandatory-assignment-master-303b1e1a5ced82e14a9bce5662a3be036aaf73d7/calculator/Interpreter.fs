module Interpreter
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

let rec evaluate_var var var_list =
    match var_list with
    | (v,n)::vs when v = var  -> n
    | (v,n)::vs               -> evaluate_var var vs
    | _                       -> failwith "Fejl 40"

let rec extract_value x_list index =
    match x_list with
    | x::xs when index = 0    -> x
    | x::xs                   -> extract_value xs (index-1)
    | _                       -> failwith "Fejl 40"

let rec evaluate_arr arr index arr_list =
    match arr_list with
    | (a,xs)::ys when a = arr -> extract_value xs index
    | (a,xs)::ys              -> evaluate_arr arr index ys
    | _                       -> failwith "Fejl 40"

let rec evaluate_expr expr vars arrs =
    match expr with
    | Num(x)            -> x
    | Var(x)            -> evaluate_var x vars
    | Times(x,y)        -> (evaluate_expr x vars arrs) * (evaluate_expr y vars arrs)
    | Div(x,y)          -> (evaluate_expr x vars arrs) / (evaluate_expr y vars arrs)
    | Plus(x,y)         -> (evaluate_expr x vars arrs) + (evaluate_expr y vars arrs)
    | Minus(x,y)        -> (evaluate_expr x vars arrs) - (evaluate_expr y vars arrs)
    | Pow(x,y)          -> (evaluate_expr x vars arrs) ** (evaluate_expr y vars arrs)
    | Uminus(x)         -> -(evaluate_expr x vars arrs)
    | ArrIndex(x,y)     -> evaluate_arr x (Convert.ToInt32(evaluate_expr y)) arrs

let rec evaluate_bool bool vars arrs =
    match bool with
    | True              -> true
    | False             -> false
    | Band(x,y)         -> (evaluate_bool x vars arrs) && (evaluate_bool y vars arrs)
    | Bor(x,y)          -> (evaluate_bool x vars arrs) || (evaluate_bool y vars arrs)
    | And(x,y)          -> (evaluate_bool x vars arrs) && (evaluate_bool y vars arrs)
    | Or(x,y)           -> (evaluate_bool x vars arrs) || (evaluate_bool y vars arrs)
    | Equal(x,y)        -> (evaluate_expr x vars arrs) = (evaluate_expr y vars arrs)
    | Nequal(x,y)       -> (evaluate_expr x vars arrs) <> (evaluate_expr y vars arrs)
    | Not(x)            -> not (evaluate_bool x vars arrs)
    | GreaterEqual(x,y) -> (evaluate_expr x vars arrs) >= (evaluate_expr y vars arrs)
    | SmallerEqual(x,y) -> (evaluate_expr x vars arrs) <= (evaluate_expr y vars arrs)
    | Greater(x,y)      -> (evaluate_expr x vars arrs) > (evaluate_expr y vars arrs)
    | Smaller(x,y)      -> (evaluate_expr x vars arrs) < (evaluate_expr y vars arrs)

let allowed edgeAction vars arrs =
    match edgeAction with
        | Test(x)           -> evaluate_bool x vars arrs
        | _                 -> true

let rec valid_edges pg_structure vars arrs node =
    match pg_structure with
    | (node0,node1,edgeAction)::xs when node0 = node && allowed edgeAction vars arrs -> (node0,node1,edgeAction)::(valid_edges xs vars arrs node)
    | (node0,node1,edgeAction)::xs                                                   -> valid_edges xs vars arrs node
    | []                                                                             -> []
    | _                                                                              -> failwith "Fejl 40"

let random n = (new System.Random()).Next(0, n)

let rec interpret_var var value var_list =
    match var_list with
    | (x,n)::xs when x = var  -> (x,value)::xs
    | (x,n)::xs               -> (x,n)::(interpret_var var value xs)
    | _                       -> failwith "Fejl 40"

let rec update_arr index value value_list =
    match value_list with
    | x::xs when index = 0    -> value::xs
    | x::xs                   -> x::(update_arr (index-1) value xs)
    | _                       -> failwith "Fejl 40"

let rec interpret_arr arr index value arr_list =
    match arr_list with
    | (a,xs)::ys when a = arr -> (a,update_arr index value xs)::ys
    | (a,xs)::ys              -> (a,xs)::interpret_arr arr index value ys
    | _                       -> failwith "Fejl 40"

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

let rec runner pg_structure vars arrs node_current node_final =
    //vars = [("x",2);("y",5)]
    //arrs = [("X",[2;3]]);("Y",[5])]
    let valid_list = valid_edges pg_structure vars arrs node_current
    let length = List.fold (fun s x -> s + 1) 0 valid_list
    let edge = extract_value valid_list (random length)
    match edge with
    | (-1,-1,action)                         -> "Status: terminated \n" + formatter node_current vars arrs
    | (node0,node1,action) when length = 0   -> "Status: stuck \n" + formatter node_current vars arrs
    | (node0,node1,action)                   -> match action with
                                                | VarAssign(x,y)     -> runner pg_structure (interpret_var x (evaluate_expr y vars arrs) vars) arrs node1 node_final
                                                | ArrAssign(x,y,z)   -> runner pg_structure vars (interpret_arr x (Convert.ToInt32(evaluate_expr y vars arrs)) (evaluate_expr z vars arrs) arrs) node1 node_final
                                                | Skip               -> runner pg_structure vars arrs node1 node_final
                                                | _                  -> failwith "Fejl 40"
