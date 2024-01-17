module Algebra

open Num

type name = string

type indef = name

type item =
| Num of num
| Ind of indef
| Expr of operation // may contain indefs, otherwise resolved to num

and operation = // allows uncertainty for Ind, unlike Num operations
| OprAdd of item * item
| OprSub of item * item
| OprMul of item * item
| OprDiv of item * item
| OprPow of item * num
| OprSqr of item
| OprSqt of item
| OprNeg of item
| OprEtc_Unary of (item -> item) * item
| OprEtc_Binary of (item -> item -> item) * item * item
| OprEtc_Etc of (item list -> item) * item list

let rec definite (x: item) : bool =
    match x with
    | Ind _ -> false
    | Num _ -> true
    | Expr (opr: operation) ->
        match opr with
        | OprAdd (y, z) | OprSub (y, z) | OprMul (y, z) | OprDiv (y, z) | OprEtc_Binary (_, y, z) -> definite y && definite z
        | OprSqr y | OprSqt y | OprNeg y | OprPow (y, _) | OprEtc_Unary (_, y) -> definite y
        | OprEtc_Etc (_, y) -> List.forall definite y

let comprehensive_numSanitaize (n: num) : num =
    match n with
    | Sqt _ -> sqrtSanitize n
    | Frc _ -> fracSanitize n
    | Add _ -> addSanitize n
    | _ -> n

let rec sanitize (x: item) : item =
    match x with
    | Ind _ -> x
    | Num (n: num) ->
        match n with
        | Sqt _ | Frc _ | Add _ -> Num (comprehensive_numSanitaize n)
        | _ -> x
    | Expr (opr: operation) ->
        match opr with
        | _ -> x // WIP, this line is wrong

//let apply (itm: item) (var: indef) (value: num) = // idiom example: ("x", Int 2) ||> apply expr (* where expr = Expr (...) that contains "x" *)

//let solve (item1: item) (item2: item) (var: indef) : item = // also returns remaining indefs if any, as a pair
    

(* // probably not necessary but just saving for later
type polynomial_func =
| NoInd of (num list -> item)
| UniInd of (num list -> indef -> item)
| MultiInd of (num list -> indef list -> item)

type nonpolynomial_func =
| NoInd of (num list -> item)
| UniInd of (num list -> indef -> item)
| MultiInd of (num list -> indef list -> item)

type operation_func = // note that indef succeeds as variables
| Poly of polynomial_func
| NonPoly of nonpolynomial_func
*)
