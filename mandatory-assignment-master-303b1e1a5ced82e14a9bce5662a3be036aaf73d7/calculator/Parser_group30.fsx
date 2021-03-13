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

let rec cmdToString input =
  match input with 
  | VarAssignCmd(x,y) -> "VarAssignCmd" + "(" + (exprToString x) + "," + (exprToString y) + ")"
  | x -> (string x)
and exprToString input = 
  match input with
  | Var x -> "Var " + "\\\"" + (string x) + "\\\""
  | x -> (string x)

let pg input node0 node1 =
  let mutable counter = 0
  let rec finished input =
    match input with
      | ConditionCmd(x,y) -> Not(x)
      | Brack(x,y) -> And((finished x),(finished y))
  let rec helper input node0 node1 =
    //guarded commands
    match input with
      | ConditionCmd(x,y)   -> counter <- counter + 1
                               //("q%A -> q%A [label = \"%A\"];" node0 counter x) + (edges counter node1 y)
                               "q" + (string node0) + " -> q" + (string counter) + " [label = \"" + (string x) + "\"];\n" + (edges y counter node1)
      | Brack(x,y)          -> (helper x node0 node1) + (helper y node0 node1)
  and edges input node0 node1 =
    //commands
    match input with
      | VarAssignCmd(x,y)   -> //"q%A -> q%A [label = \"%A\"];" node0 node1 input
                               "q" + (string node0) + " -> q" + (string node1) + " [label = \"" + (cmdToString input) + "\"];\n"
      | ArrAssignCmd(x,y,z) -> "q" + (string node0) + " -> q" + (string node1) + " [label = \"" + (string input) + "\"];\n"
      | IfCmd(x)            -> helper x node0 node1
      | DoCmd(x)            -> //("q%A -> q%A [label = \"%A\"];" node0 node1 (finished x)) + (edges node0 node0 x)
                               "q" + (string node0) + " -> q" + (string node1) + " [label = \"" + (string (finished x)) + "\"];\n" + (helper x node0 node0)
      | Skip(x)             -> "q" + (string node0) + " -> q" + (string node1) + " [label = \"" + (string input) + "\"];\n"
      | Scolon(x,y)         -> counter <- counter + 1
                               (edges x node0 counter) + (edges y counter node1)
  (*
  and helper2 input node0 node1
    //expressions
    match input with
      | Num(x)              -> (string input)
      | Var(x)              -> (string input)
      | Times(x,y)          -> (string input)
      | Div(x,y)            -> (string input)
      | Plus(x,y)           -> (string input)
      | Minus(x,y)          -> (string input)
      | Pow(x,y)            -> (string input)
      | Uminus(x)           -> (string input)
      | ArrIndex(x,y)       -> (string input)

  and help3r input node0 node1
    //booleans
    match input with
      | True(x)             -> (string input)
      | False(x)            -> (string input)
      | Band(x,y)           -> (string input)
      | Bor(x,y)            -> (string input)
      | And(x,y)            -> (string input)
      | Or(x,y)             -> (string input)
      | Equal(x,y)          -> (string input)
      | Nequal(x,y)         -> (string input)
      | Not(x)              -> (string input)
      | GreaterEqual(x,y)   -> (string input)
      | SmallerEqual(x,y)   -> (string input)
      | Greater(x,y)        -> (string input)
      | Smaller(x,y)        -> (string input)
  *)
  "digraph program_graph {rankdir=LR;\nnode [shape = circle]; q0;\nnode [shape = doublecircle]; q99;\nnode [shape = circle]\n" + (edges input node0 node1) + "}"

//q▷ -> q◀

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

  printfn "%A" (pg e 0 99)//(pg e 0 99)
  printfn "\n%A" e

// Start interacting with the user
compute
