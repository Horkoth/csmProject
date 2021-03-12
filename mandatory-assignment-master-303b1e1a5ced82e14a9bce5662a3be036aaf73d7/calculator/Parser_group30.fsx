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

let pg input node0 node1 =
  let mutable counter = 0
  let rec finished input =
    match input with
      | ConditionCmd(x,y) -> Not(x)
      | Brack(x,y) -> And((finished x),(finished y))
  let rec edges input node0 node1 =
    match input with
      //commands
      | VarAssignCmd(x,y)   -> //"q%A -> q%A [label = \"%A\"];" node0 node1 input
                               "q" + (string node0) + " -> q" + (string node1) + " [label = \"" + (string input) + "\"];"
      | ArrAssignCmd(x,y,z) -> "q" + (string node0) + " -> q" + (string node1) + " [label = \"" + (string input) + "\"];"
      | IfCmd(x)            -> edges x node0 node1
      | DoCmd(x)            -> //("q%A -> q%A [label = \"%A\"];" node0 node1 (finished x)) + (edges node0 node0 x)
                               "q" + (string node0) + " -> q" + (string node1) + " [label = \"" + (string (finished x)) + "\"];" + (edges node0 node0 x)
      | Skip(x)             -> "q" + (string node0) + " -> q" + (string node1) + " [label = \"" + (string input) + "\"];"
      | Scolon(x,y)         -> counter = counter + 1
                               (edges node0 counter x) + (edges counter node1 y)
      //guarded commands
      | ConditionCmd(x,y)   -> counter = counter + 1
                               //("q%A -> q%A [label = \"%A\"];" node0 counter x) + (edges counter node1 y)
                               "q" + (string node0) + " -> q" + (string counter) + " [label = \"" + (string x) + "\"];" + (edges counter node1 y)
      | Brack(x,y)          -> (edges node0 node1 x) + (edges node0 node1 y)
      //expressions
      | Num(x)              -> (string input)
      | Var(x)              -> (string input)
      | Times(x,y)          -> (string input)
      | Div(x,y)            -> (string input)
      | Plus(x,y)           -> (string input)
      | Minus(x,y)          -> (string input)
      | Pow(x,y)            -> (string input)
      | Uminus(x)           -> (string input)
      | ArrIndex(x,y)       -> (string input)
      //booleans
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
  "digraph program_graph {rankdir=LR;node [shape = circle]; q▷;node [shape = doublecircle]; q◀;node [shape = circle]" + (edges input node0 node1) + "}"

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
  printfn "%s" (pg e "▷" "◀")

// Start interacting with the user
compute
