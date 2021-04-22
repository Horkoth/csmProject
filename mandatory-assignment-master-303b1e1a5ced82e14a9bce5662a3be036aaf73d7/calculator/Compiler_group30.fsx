// This script implements our interactive calculator

// We need to import a couple of modules, including the generated lexer and parser
#r "FsLexYacc.Runtime.10.0.0/lib/net46/FsLexYacc.Runtime.dll"
open FSharp.Text.Lexing
open System
#load "TypesAST.fs"
open TypesAST
#load "Parser.fs"
open Parser
#load "Lexer.fs"
open Lexer
//#load "Interpreter.fs"
//open Interpreter
#load "SignAnalyzer.fs"
open SignAnalyzer

let startNode = 0
let endNode = -1
let mutable counter = 0

//let converter

(*
let rec stepwise startnode structure memory
  if interpreter edge = true 
    stepwise newnode structure updated mem
  else if no valueid edges
    stuck = true

  if stuck or terminated
    print 

let interpreter =
  match 
*)

let pg input node0 node1 det =
  let mutable counter = 0
  let rec cleanString input =
    match input with 
      | x::xs when x = '"' -> '\\'::'"'::(cleanString xs)
      | x::xs -> x::(cleanString xs)
      | x::[] when x = '"' -> '\\'::'"'::[]
      | x::[] -> x::[]
      | _ -> []
  let transform input =
    (String.Concat(Array.ofList((cleanString (Seq.toList input)))))
  let rec finished input =
    match input with
      | ConditionCmd(x,y) -> Not(x)
      | Brack(x,y) -> And((finished x),(finished y))
  let rec helper input node0 node1 =
      //guarded commands
      match input with
        | ConditionCmd(x,y)   -> counter <- counter + 1
                                 "q" + (string node0) + " -> q" + (string counter) + " [label = \"" + (transform (string x)) + "\"];\n" + (edges y (string counter) node1)
        | Brack(x,y)          -> (helper x node0 node1) + (helper y node0 node1)
  and edges input node0 node1 =
      //commands
      match input with
        | VarAssignCmd(x,y)   -> "q" + (string node0) + " -> q" + (string node1) + " [label = \"" + (transform (string input)) + "\"];\n"
        | ArrAssignCmd(x,y,z) -> "q" + (string node0) + " -> q" + (string node1) + " [label = \"" + (transform (string input)) + "\"];\n"
        | IfCmd(x)            -> helper x node0 node1
        | DoCmd(x)            -> "q" + (string node0) + " -> q" + (string node1) + " [label = \"" + (string (finished x)) + "\"];\n" + (helper x node0 node0)
        | SkipCmd             -> "q" + (string node0) + " -> q" + (string node1) + " [label = \"" + "skip" + "\"];\n"
        | Scolon(x,y)         -> counter <- counter + 1
                                 (edges x node0 (string counter)) + (edges y (string counter) node1) 
  let rec cmd input node0 node1 =
    match input with
    | IfCmd(x) -> let (E,d) = gc x node0 node1 (string false)
                  E
    | DoCmd(x) -> let (E,d) = gc x node0 node0 (string false)
                  E + ("q" + (string node0) + " -> q" + (string node1) + " [label = \"" + "Not (" + d + ")" + "\"];\n")
    | x -> edges x node0 node1
  and gc input node0 node1 d =
    match input with
    | Brack(x,y) -> let (E1,d1) = gc x node0 node1 d
                    let (E2,d2) = gc y node0 node1 d1
                    (E1 + E2, d2)
    | ConditionCmd(b,C) -> counter <- counter + 1
                           let E = edges C (string counter) node1
                           ("q" + (string node0) + " -> q" + (string counter) + " [label = \"" + "And (" + (transform (string b)) + ", Not (" + (string d) + ")) " + "\"];\n" + (string E), "Or (" + (transform (string b)) + ", " + (string d) + ")")
  if det then
    "digraph program_graph {rankdir=LR;\nnode [shape = circle]; q▷;\nnode [shape = doublecircle]; q◀;\nnode [shape = circle]\n" + (cmd input node0 node1) + "}"
  else
    "digraph program_graph {rankdir=LR;\nnode [shape = circle]; q▷;\nnode [shape = doublecircle]; q◀;\nnode [shape = circle]\n" + (edges input node0 node1) + "}"

let rec init_vars i = 
  if i > 0 then
    printf "Enter variable name (string): "
    let var = Console.ReadLine()
    printf "Enter variable value (float): "
    let value = float (Console.ReadLine())
    (var,value)::(init_vars (i-1))
  else
    []

let rec build_array() =
  printf "Enter array value (float), insert nothing to continue: "
  let value = Console.ReadLine()
  match value with
    | "" -> []
    | _  -> (float value)::build_array()

let rec init_arrs i = 
  if i > 0 then
    printf "Enter array name (string): "
    let arr = Console.ReadLine()
    let values = build_array()
    (arr,values)::(init_arrs (i-1))
  else
    []

let interpret_abstract_value i =
  match i with
  | "+" -> PlusSign::[]
  | "-" -> MinusSign::[]
  | "0" -> ZeroSign::[]

let rec insert_var var value memory node =
  match memory with
  | (n,[])::ms when n = node             -> ms@[(n,[(var,value)]::[])]
  | (n,vars::vars_all)::ms when n = node -> (n,(vars@[(var,value)])::vars_all)::ms
  | m::ms                                -> m::(insert_var var value ms node)
  | []                                   -> []

let rec init_abstract_vars i memory node = 
  if i > 0 then
    printf "Enter variable name (string): "
    let var = Console.ReadLine()
    printf "Enter variable value (+,-,0): "
    let value = interpret_abstract_value (Console.ReadLine())
    init_abstract_vars (i-1) (insert_var var value memory node) node
    // [(q0;  [ [(x,[Plus]);(y,[Minus]);(A,[Minus;Plus])] ; [(x,[Zero]);(y,[Minus]);(A,[Minus;Plus])] ]  )]
    // [Plus,Minus]
  else
    memory

let rec build_abstract_array list =
  printf "Enter array value (+,-,0), insert nothing to continue: "
  let value = Console.ReadLine()
  match value with
    | ""                          -> []
    | x when List.contains x list -> build_abstract_array list
    | _                           -> (interpret_abstract_value value)@(build_abstract_array list)

let rec init_abstract_arrs i memory node = 
  if i > 0 then
    printf "Enter array name (string): "
    let arr = Console.ReadLine()
    let values = build_abstract_array []
    init_abstract_arrs (i-1) (insert_var arr values memory node) node
  else
    memory

let parse_bool s =
  match s with
  | "true"  -> true
  | "false" -> false
  | _       -> failwith ("Error: expected bool but recieved: " + s)

let rec nodes_list pg_structure memory = 
  match pg_structure with
  | (n0,n1,x)::structure -> nodes_list structure ((n0,[])::(n1,[])::memory)
  | []                   -> memory 

let init_memory pg_structure =
  remove_duplicates (nodes_list pg_structure [])

// We
let parse input =
  // translate string into a buffer of characters
  let lexbuf = LexBuffer<char>.FromString input
  // translate the buffer into a stream of tokens and parse them
  let res = Parser.start Lexer.tokenize lexbuf
  // return the result of parsing (i.e. value of type "expr")
  res

// We implement here the function that interacts with the user
let rec compute =
  (*
  printf "Enter a command: "
  
  let e = parse (Console.ReadLine())

  printf "Enter deterministic value (true, false): "

  let det = parse_bool (Console.ReadLine())

  printf "Enter number of steps (integer): "

  let steps = Convert.ToInt32(Console.ReadLine())

  printf "Enter number of variables (integer): "

  let i = Convert.ToInt32(Console.ReadLine())

  let vars = init_vars i

  printf "Enter number of arrays (integer): "
  
  let j = Convert.ToInt32(Console.ReadLine())

  let arrs = init_arrs j
  *)

  //printfn "\n%s" (pg e "▷" "◀" det)
    
  //printfn "\n%A\n" e

  //printfn "\n%s" (runner (pg_structure e startNode endNode det) vars arrs startNode endNode steps)

  printf "Enter a command: "
  
  let e = parse (Console.ReadLine())

  printf "Enter deterministic value (true, false): "

  let det = parse_bool (Console.ReadLine())

  //printf "Enter number of steps (integer): "

  //let steps = Convert.ToInt32(Console.ReadLine())

  let structure = (pg_structure e startNode endNode det)

  let mutable memory = init_memory structure

  printf "Enter number of variables (integer): "

  let i = Convert.ToInt32(Console.ReadLine())

  memory <- init_abstract_vars i memory startNode

  printf "Enter number of arrays (integer): "
  
  let j = Convert.ToInt32(Console.ReadLine())

  memory <- init_abstract_arrs j memory startNode

  printfn "\n%s" (abstract_initializer structure memory startNode endNode)

// Start interacting with the user
compute
