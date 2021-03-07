// This file implements a module where we define a data type "expr"
// to store represent arithmetic expressions
module CalculatorTypesAST

type expr =
  | Num of float
  | Letter of String
  | TimesExpr of (expr * expr)
  | DivExpr of (expr * expr)
  | PlusExpr of (expr * expr)
  | MinusExpr of (expr * expr)
  | PowExpr of (expr * expr)
  | UPlusExpr of (expr)
  | UMinusExpr of (expr)
  | BorExpr of (expr * expr)
  | BandExpr of (expr * expr)
  | OrExpr of (expr * expr)
  | AndExpr of (expr * expr)
  | EqualExpr of (expr * expr)
  | NequalExpr of (expr * expr)
  | NotExpr of (expr)
  | GreaterEqualExpr of (expr * expr)
  | SmallerEqualExpr of (expr * expr)
  | GreaterExpr of (expr * expr)
  | SmallerExpr of (expr * expr)
  | AssignExpr of (expr * expr)
  | Bool of String
//  | Skip of (expr)
