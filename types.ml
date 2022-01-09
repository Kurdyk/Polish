(*****************************************************************************)
(** Syntaxe abstraite Polish (types imposés, ne pas changer sauf extensions) *)

(** Position : numéro de ligne dans le fichier, débutant à 1 *)
type position = int

(** Nom de variable *)
type name = string

(** Opérateurs arithmétiques : + - * / % *)
type op = Add | Sub | Mul | Div | Mod

(** Expressions arithmétiques *)
type expr =
    | Num of int
    | Var of name
    | Op of op * expr * expr

(** Opérateurs de comparaisons *)
type comp =
    | Eq (* = *)
    | Ne (* Not equal, <> *)
    | Lt (* Less than, < *)
    | Le (* Less or equal, <= *)
    | Gt (* Greater than, > *)
    | Ge (* Greater or equal, >= *)

(** Condition : comparaison entre deux expressions *)
type cond = expr * comp * expr

(** Instructions *)
type instr =
    | Set of name * expr
    | Read of name
    | Print of expr
    | If of cond * block * block
    | While of cond * block
and block = (position * instr) list

(** Un programme Polish est un bloc d'instructions *)
type program = block

(*type sign = Neg | Zero | Pos | Error*)

module Sign = 
struct
  type t = Neg | Zero | Pos | Error
  let compare t1 t2 = 
    match (t1, t2) with 
      | (Neg, Neg) -> 0
      | (Neg, Zero) -> -1
      | (Neg, Pos) -> -2
      | (Neg, Error) -> -10
      | (Zero, Neg) -> 1
      | (Zero, Zero) -> 0
      | (Zero, Pos) -> -1
      | (Zero, Error) -> -9
      | (Pos, Neg) -> 2
      | (Pos, Zero) -> 1
      | (Pos, Pos) -> 0
      | (Pos, Error) -> -8
      | (Error, Neg) -> 10
      | (Error, Zero) -> 9
      | (Error, Pos) -> 8
      | (Error, Error) -> 0
end 

module VAR_SIGN = Set.Make(Sign)


(***********************************************************************)

module ENV = Map.Make(String);;
module VAR = Set.Make(String)