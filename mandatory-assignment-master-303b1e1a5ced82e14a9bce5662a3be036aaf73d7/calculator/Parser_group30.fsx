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

let rec cleanString input =
  match input with 
    | x::xs when x = '"' -> '\\'::'"'::(cleanString xs)
    | x::xs -> x::(cleanString xs)
    | x::[] when x = '"' -> '\\'::'"'::[]
    | x::[] -> x::[]
    | _ -> []
let transform input =
  (String.Concat(Array.ofList((cleanString (Seq.toList input)))))
  
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
                               "q" + (string node0) + " -> q" + (string counter) + " [label = \"" + (transform (string x)) + "\"];\n" + (edges y (string counter) node1)
      | Brack(x,y)          -> (helper x node0 node1) + (helper y node0 node1)
  and edges input node0 node1 =
    //commands
    match input with
      | VarAssignCmd(x,y)   -> "q" + (string node0) + " -> q" + (string node1) + " [label = \"" + (transform (string input)) + "\"];\n"
      | ArrAssignCmd(x,y,z) -> "q" + (string node0) + " -> q" + (string node1) + " [label = \"" + (transform (string input)) + "\"];\n"
      | IfCmd(x)            -> helper x node0 node1
      | DoCmd(x)            -> "q" + (string node0) + " -> q" + (string node1) + " [label = \"" + (string (finished x)) + "\"];\n" + (helper x node0 node0)
      | Skip(x)             -> "q" + (string node0) + " -> q" + (string node1) + " [label = \"" + (transform (string input)) + "\"];\n"
      | Scolon(x,y)         -> counter <- counter + 1
                               (edges x node0 (string counter)) + (edges y (string counter) node1)
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

  printfn "\n%s" (pg e "▷" "◀")
  printfn "\n%A\n" e

// Start interacting with the user
compute
