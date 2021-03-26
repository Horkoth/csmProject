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
#load "Interpreter.fs"
open Interpreter

let det = true
let startNode = 0
let endNode = -1
let mutable counter = 0

//let converter

(*
let rec stepwise startnode structure memory
  if interpreter edge = true 
    stepwise newnode structure updated mem
  else if no valid edges
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
  printf "Enter a command: "
  
  let e = parse (Console.ReadLine())

  (*

  printf "Enter variables (e.g. [(x,10);(y,5)]: "
  
  let vars = parse (Console.ReadLine())

  printf "Enter arrays (e.g. [(A,[1;2]);(B,[3;4;5])]: "
  
  let arrs = parse (Console.ReadLine())

  *)

  //printfn "\n%s" (pg e "▷" "◀" det)
    
  //printfn "\n%A\n" e

  printfn "\n%A" (runner (pg_structure e startNode endNode det) [(x,10);(y,5)] [(A,[1;2]);(B,[3;4;5])] startNode endNode)

// Start interacting with the user
compute
