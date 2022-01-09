open Types
open Printf
open Misc

(** Evalue la représentation Ocaml d'une expression Polish et renvoie sa valeur *)
let rec eval_expr expr env l = match expr with 
  | Num(a) -> a
  | Var(v) -> get_variable v env l
  | Op(operator, expr1, expr2) -> match operator with 
    | Add -> (eval_expr expr1 env l) + (eval_expr expr2 env l)
    | Sub -> (eval_expr expr1 env l) - (eval_expr expr2 env l)
    | Mul -> (eval_expr expr1 env l) * (eval_expr expr2 env l)
    | Div -> let divider = (eval_expr expr2 env l) in if divider = 0 then begin printf "Exception: Line %d, division by 0\n" l; exit 1 end else (eval_expr expr1 env l) / divider
    | Mod -> let divider = (eval_expr expr2 env l) in if divider = 0 then begin printf "Exception: Line %d, division by 0\n" l; exit 1 end else (eval_expr expr1 env l) mod divider
;;

(** Evalue la représentation Ocaml d'une condition et renvoie si elle est vraie ou non *)
let eval_condition (expr1, comparator, expr2) env l = match comparator with 
  | Eq -> (eval_expr expr1 env l) = (eval_expr expr2 env l)
  | Ne -> (eval_expr expr1 env l) <> (eval_expr expr2 env l)
  | Lt -> (eval_expr expr1 env l) < (eval_expr expr2 env l)
  | Le -> (eval_expr expr1 env l) <= (eval_expr expr2 env l)
  | Gt -> (eval_expr expr1 env l) > (eval_expr expr2 env l)
  | Ge -> (eval_expr expr1 env l) >= (eval_expr expr2 env l)


(** Affiche la valeur de la représentation Ocaml d'une expression. Calcule cette valeur au besoin, grace à `eval_expr` *)
let print_expression expr env l = 
  match expr with 
    | Num(n) -> printf "%d\n" n
    | Var(v) -> printf "%d\n" (get_variable v env l)
    | Op(_, _, _) -> printf "%d\n" (eval_expr expr env l)
;;


(** Demande à l'utilisateur de saisir une valeur et l'enregistre dans l'environnement d'execution *)
let read_variable n env l = 
  printf "%s? " n; 
  let saisie = read_int () in 
    ENV.add n saisie env;;


(** Permet de ne pas tenir compte de la valeur de retour d'une fonction *)
let masquer_retour retour = ();;


(** Fonction principale, permet de lancer l'execution d'un programme Polish (en représentation Ocaml) *)
let eval_polish (p:program) =
  let rec process_while condition block env l = 
    if eval_condition condition env l then begin let new_env = parcours_programme block env in process_while condition block new_env l end else env
  and parcours_programme prog env = match prog with 
    | [] -> env
    | (l, Print(expr)) :: suite_prog -> print_expression expr env l; parcours_programme suite_prog env
    | (l, Set(name, expr)) :: suite_prog -> let new_env = set_variable name (eval_expr expr env l) env l in 
          parcours_programme suite_prog new_env
    | (l, Read(n)) :: suite_prog -> let new_env = read_variable n env l in parcours_programme suite_prog new_env
    | (l, If(cond, block1, block2)) :: suite_prog -> let new_env = if eval_condition cond env l then parcours_programme block1 env else parcours_programme block2 env in parcours_programme suite_prog new_env
    | (l, While(cond, block)) :: suite_prog -> let new_env = process_while cond block env l in parcours_programme suite_prog new_env
  in masquer_retour (parcours_programme p ENV.empty)
;;
