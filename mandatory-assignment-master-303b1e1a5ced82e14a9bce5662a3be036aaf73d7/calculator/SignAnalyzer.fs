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

let evaluate_plus x y =
    match x,y with 
    | Minus,Minus -> Minus::[]
    | Minus,Zero  -> Minus::[]
    | Minus,Plus  -> Minus::Zero::Plus::[]
    | Zero,Minus  -> Minus::[]
    | Zero,Zero   -> Zero::[]
    | Zero,Plus   -> Plus::[]
    | Plus,Minus  -> Minus::Zero::Plus::[]
    | Plus,Zero   -> Plus::[]
    | Plus,Plus   -> Plus::[]

let evaluate_minus x y =
    match x,y with 
    | Minus,Minus -> Minus::Zero::Plus::[]
    | Minus,Zero  -> Minus::[]
    | Minus,Plus  -> Minus::[]
    | Zero,Minus  -> Plus::[]
    | Zero,Zero   -> Zero::[]
    | Zero,Plus   -> Minus::[]
    | Plus,Minus  -> Plus::[]
    | Plus,Zero   -> Plus::[]
    | Plus,Plus   -> Minus::Zero::Plus::[]

let evaluate_times x y =
    match x,y with 
    | Minus,Minus -> Plus::[]
    | Minus,Zero  -> Zero::[]
    | Minus,Plus  -> Minus::[]
    | Zero,Minus  -> Zero::[]
    | Zero,Zero   -> Zero::[]
    | Zero,Plus   -> Zero::[]
    | Plus,Minus  -> Minus::[]
    | Plus,Zero   -> Zero::[]
    | Plus,Plus   -> Plus::[]

let evaluate_division x y =
    match x,y with 
    | Minus,Minus -> Plus::[]
    | Minus,Zero  -> []
    | Minus,Plus  -> Minus::[]
    | Zero,Minus  -> Zero::[]
    | Zero,Zero   -> []
    | Zero,Plus   -> Zero::[]
    | Plus,Minus  -> Minus::[]
    | Plus,Zero   -> []
    | Plus,Plus   -> Plus::[]

let evaluate_pow x y =
    match x,y with 
    | Minus,Minus -> Minus::Plus::[]
    | Minus,Zero  -> Plus::[]
    | Minus,Plus  -> Minus::Plus::[]
    | Zero,Minus  -> []
    | Zero,Zero   -> Plus::[]
    | Zero,Plus   -> []
    | Plus,Minus  -> Plus::[]
    | Plus,Zero   -> Plus::[]
    | Plus,Plus   -> Plus::[]

let evaluate_uminus x =
    match x with 
    | Minus -> Plus::[]
    | Zero  -> Zero::[]
    | Plus  -> Minus::[]

let evaluate_sign x =
    match x with 
    | 0            -> Zero::[]
    | x when x<0   -> Minus::[]
    | x when x>0   -> Plus::[]

let evaluate_equal x y =
    match x,y with 
    | Minus,Minus -> true
    | Minus,Zero  -> false
    | Minus,Plus  -> false
    | Zero,Minus  -> false
    | Zero,Zero   -> true
    | Zero,Plus   -> false
    | Plus,Minus  -> false
    | Plus,Zero   -> false
    | Plus,Plus   -> true

let evaluate_nequal x y =
    match x,y with 
    | Minus,Minus -> true
    | Minus,Zero  -> true
    | Minus,Plus  -> true
    | Zero,Minus  -> true
    | Zero,Zero   -> false
    | Zero,Plus   -> true
    | Plus,Minus  -> true
    | Plus,Zero   -> true
    | Plus,Plus   -> true

let evaluate_greater_equal x y =
    match x,y with 
    | Minus,Minus -> true
    | Minus,Zero  -> false
    | Minus,Plus  -> false
    | Zero,Minus  -> true
    | Zero,Zero   -> true
    | Zero,Plus   -> false
    | Plus,Minus  -> true
    | Plus,Zero   -> true
    | Plus,Plus   -> true

let evaluate_smaller_equal x y =
    match x,y with 
    | Minus,Minus -> true
    | Minus,Zero  -> true
    | Minus,Plus  -> true
    | Zero,Minus  -> false
    | Zero,Zero   -> true
    | Zero,Plus   -> true
    | Plus,Minus  -> false
    | Plus,Zero   -> false
    | Plus,Plus   -> true

let evaluate_greater x y =
    match x,y with 
    | Minus,Minus -> true
    | Minus,Zero  -> false
    | Minus,Plus  -> false
    | Zero,Minus  -> true
    | Zero,Zero   -> false
    | Zero,Plus   -> false
    | Plus,Minus  -> true
    | Plus,Zero   -> true
    | Plus,Plus   -> true

let evaluate_smaller x y =
    match x,y with 
    | Minus,Minus -> true
    | Minus,Zero  -> true
    | Minus,Plus  -> true
    | Zero,Minus  -> false
    | Zero,Zero   -> false
    | Zero,Plus   -> true
    | Plus,Minus  -> false
    | Plus,Zero   -> false
    | Plus,Plus   -> true

let rec evaluate_expr expr mem node =
    match expr with
    | Num(x)            -> evaluate_sign x
    | Var(x)            -> evaluate_sign (evaluate_var x mem node)
    | Times(x,y)        -> evaluate_times (evaluate_expr x mem node) (evaluate_expr y mem node)
    | Div(x,y)          -> evaluate_division (evaluate_expr x mem node) (evaluate_expr y mem node)
    | Plus(x,y)         -> evaluate_plus (evaluate_expr x mem node) (evaluate_expr y mem node)
    | Minus(x,y)        -> evaluate_minus (evaluate_expr x mem node) (evaluate_expr y mem node)
    | Pow(x,y)          -> evaluate_pow (evaluate_expr x mem node) (evaluate_expr y mem node)
    | Uminus(x)         -> evaluate_uminus (evaluate_expr x mem node)
    | ArrIndex(x,y)     -> evaluate_sign (evaluate_var x (Convert.ToInt32(evaluate_expr y)) mem node)

let rec evaluate_bool bool mem node =
    match bool with
    | True              -> true
    | False             -> false
    | Band(x,y)         -> (evaluate_bool x mem node) && (evaluate_bool y mem node)
    | Bor(x,y)          -> (evaluate_bool x mem node) || (evaluate_bool y mem node)
    | And(x,y)          -> (evaluate_bool x mem node) && (evaluate_bool y mem node)
    | Or(x,y)           -> (evaluate_bool x mem node) || (evaluate_bool y mem node)
    | Equal(x,y)        -> evaluate_equal (evaluate_expr x mem node) (evaluate_expr y mem node)
    | Nequal(x,y)       -> evaluate_nequal (evaluate_expr x mem node) (evaluate_expr y mem node)
    | Not(x)            -> not (evaluate_bool x mem node)
    | GreaterEqual(x,y) -> evaluate_greater_equal (evaluate_expr x mem node) (evaluate_expr y mem node)
    | SmallerEqual(x,y) -> evaluate_smaller_equal (evaluate_expr x mem node) (evaluate_expr y mem node)
    | Greater(x,y)      -> evaluate_greater (evaluate_expr x mem node) (evaluate_expr y mem node)
    | Smaller(x,y)      -> evaluate_smaller (evaluate_expr x mem node) (evaluate_expr y mem node)

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

let rec queue_initializer pg_structure node =
    match pg_structure with
    | (n,x,y)::pgss when n = node -> (n,x,y)::(queue_initializer pgss node)
    | []                          -> []
    | (n,x,y)::pgss               -> (queue_initializer pgss node)

let rec abstract_runner pg_structure memory node_final queue =
    //vars = [("x",Plus);("y",Zero)]
    //arrs = [("X",[Plus;Zero]]);("Y",[Minus])]
    match queue with
    | egde::queues when not is_valid edge arbstract_vars abstract_arrs -> abstract_runner pg_structure memory node_final queues
    | edge::queues -> abstract_runner pg_structure (update_memory edge memory) node_final (update_queue edge queues memory)

let abstract_initializer pg_structure memory node_start node_final =
    abstract_runner pg_structure memory node_final (queue_initializer pg_structure node_start)
