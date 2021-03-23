module Interpreter
open System

//let mutable counter = 0

let pg input node0 node1 det =
  let mutable counter = 0
  let rec finished input =
    match input with
      | ConditionCmd(x,y) -> Not(x)
      | Brack(x,y) -> And((finished x),(finished y))
  let rec helper input node0 node1 =
      //guarded commands
      match input with
        | ConditionCmd(x,y)   -> counter <- counter + 1
                                 (node0, counter, Test x)::(edges y counter node1)
        | Brack(x,y)          -> (helper x node0 node1)@(helper y node0 node1)
  and edges input node0 node1 =
      //commands
      match input with
        | VarAssignCmd(x,y)   -> (node0, node1, VarAssign (x, y))::[]
        | ArrAssignCmd(x,y,z) -> (node0, node1, ArrAssign input)::[]
        | IfCmd(x)            -> helper x node0 node1
        | DoCmd(x)            -> (node0, node1, finished x)::[]
        | Skip(x)             -> (node0, node1, input)::[]
        | Scolon(x,y)         -> counter <- counter + 1
                                 (edges x node0 counter)@(edges y counter node1)
  let rec cmd input node0 node1 =
    match input with
    | IfCmd(x) -> let (E,d) = gc x node0 node1 (string false)
                  E
    | DoCmd(x) -> let (E,d) = gc x node0 node0 (string false)
                  E::(node0, node1, Not(d))
    | x -> edges x node0 node1
  and gc input node0 node1 d =
    match input with
    | Brack(x,y) -> let (E1,d1) = gc x node0 node1 d
                    let (E2,d2) = gc y node0 node1 d1
                    (E1::E2, d2)
    | ConditionCmd(b,C) -> counter <- counter + 1
                           let E = edges C (string counter) node1
                           ((node0, counter, And(b,Not(d)))::E, Or(b,d))
  if det then
    (cmd input node0 node1)
  else
    (edges input node0 node1)

  //[(q0,[(q1,expr),(q2,expr)]), (q1,[(q0,expr),(q2,expr)])]

  //[(e_node,s_node,edge_action,"t[0]=node,t[1]=node,t[2]=expr,t[3]="t[0]=node,t[1]=node,t[2]=expr,t[3]=""""),(0,2,expr)]
  //[(0,1,a,b,"expr")]
  //VarAssignCmd(x,y)   -> [("q" + (string node0), [("q" + (string node1), input)])]
