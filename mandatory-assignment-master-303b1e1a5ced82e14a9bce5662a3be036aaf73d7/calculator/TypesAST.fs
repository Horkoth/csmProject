// This file implements a module where we define a data type "expr"
// to store represent arithmetic expressions
module TypesAST

type cmd =
  | VarAssignCmd of (string * expr)
  | ArrAssignCmd of (string * expr * expr)
  | IfCmd of (gcmd)
  | DoCmd of (gcmd)
  | SkipCmd
  | Scolon of (cmd * cmd)
and gcmd =
  | ConditionCmd of (bool * cmd)
  | Brack of (gcmd * gcmd)
and expr =
  | Num of float
  | Var of string
  | Times of (expr * expr)
  | Div of (expr * expr)
  | Plus of (expr * expr)
  | Minus of (expr * expr)
  | Pow of (expr * expr)
  | Uminus of (expr)
  | ArrIndex of (string * expr)
and bool =
  | True
  | False
  | Band of (bool * bool)
  | Bor of (bool * bool)
  | And of (bool * bool)
  | Or of (bool * bool)
  | Equal of (expr * expr)
  | Nequal of (expr * expr)
  | Not of (bool)
  | GreaterEqual of (expr * expr)
  | SmallerEqual of (expr * expr)
  | Greater of (expr * expr)
  | Smaller of (expr * expr)

type edge_action =
  | VarAssign of (string * expr)
  | ArrAssign of (string * expr * expr)
  | Skip
  | Test of bool

type sign =
  | PlusSign
  | ZeroSign
  | MinusSign
