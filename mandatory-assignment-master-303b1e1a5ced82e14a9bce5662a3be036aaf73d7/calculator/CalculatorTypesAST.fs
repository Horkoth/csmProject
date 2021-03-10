// This file implements a module where we define a data type "expr"
// to store represent arithmetic expressions
module CalculatorTypesAST

type cmd =
  | VarAssignCmd of (Var * expr)
  | ArrAssignCmd of (Var * expr * expr)
  | IfCmd of (gcmd)
  | DoCmd of (gcmd)

type gcmd =
  | ConditionCmd of (bool * cmd)


type expr =
  | Num of float
  | Unum of (expr)
  | Var of String
  | Times of (expr * expr)
  | Div of (expr * expr)
  | Plus of (expr * expr)
  | Minus of (expr * expr)
  | Pow of (expr * expr)
  | UPlus of (expr)
  | UMinus of (expr)
  | Assign of (expr * expr)
  | ArrIndex of (Var * expr)

type bool =
  | True of String
  | False of String
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
