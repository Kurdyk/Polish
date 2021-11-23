open Printf
(** Projet Polish -- Analyse statique d'un mini-langage impératif *)

(** Note : cet embryon de projet est pour l'instant en un seul fichier
    polish.ml. Il est recommandé d'architecturer ultérieurement votre
    projet en plusieurs fichiers source de tailles raisonnables *)

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


(***********************************************************************)

module ENV = Map.Make(String);;

let exclusion_names = ["READ"; "PRINT"; "IF"; "ELSE"; "WHILE"; "COMMENT";
                       ":="; "+"; "-"; "*"; "/"; "%"; 
                       "="; "<>"; "<"; "<="; ">"; ">="];;

let operators = ["="; "<>"; "<"; "<="; ">"; ">="]

let is_numeric str = 
  try
    let _ = int_of_string str in
      true;
  with Failure _ -> false
;;


let var_exists name env = ENV.mem name env;;

let get_variable name env l = if ENV.mem name env then ENV.find name env else begin printf "Exception: Line %d, variable %s referenced before assignement" l name; exit 1; end;;

let check_variable_name name l = if List.mem name exclusion_names then begin printf "Exception: Line %d, cannot name variable %s: forbidden name (reserved keyword)\n" l name; exit 1; end else if is_numeric (String.make 1 (String.get name 0)) then begin printf "Exception: Line %d, cannot name variable %s: invalid name\n" l name; exit 1; end;;

let set_variable name value env l = check_variable_name name l; ENV.add name value env;;


let rec read_file channel current = 
  try
    let line = input_line channel in
      (current, line) :: read_file channel (current + 1)
  with End_of_file -> 
    close_in_noerr channel;
    []
;;

let purifier liste = List.filter (fun k -> k <> "") liste;;

let check_expression_validity expression n = if List.length expression = 1 then List.hd expression else match List.hd (List.tl expression) with | Num(a) -> printf "Exception: Line %d, unexpected argument \"%d\"\n" n a; exit 1; | Var(a) -> printf "Exception: Line %d, unexpected argument \"%s\"\n" n a; exit 1; |_ -> printf "Exception: Line %d, cannot parse expression; unknown error\n" n; exit 1;;

let get_expression exp n =
  let rec auxiliaire exp n = match exp with 
    | [] -> []
    | h :: q when is_numeric h  -> Num(int_of_string h) :: auxiliaire q n
    | "+" :: q -> (let retour = auxiliaire q n in match retour with 
                     | [] -> printf "Exception: Line %d, not enought arguments for operator \"+\" (required 2, found 0)\n" n; exit 1
                     | h :: [] -> printf "Exception: Line %d, not enought arguments for operator \"+\" (required 2, found 1)\n" n; exit 1
                     | h1 :: h2 :: [] -> [Op(Add, h1, h2)]
                     | h1 :: h2 :: q -> [Op(Add, h1, h2)] @ q)
    | "-" :: q -> (let retour = auxiliaire q n in match retour with 
                     | [] -> printf "Exception: Line %d, not enought arguments for operator \"-\" (required 2, found 0)\n" n; exit 1
                     | h :: [] -> printf "Exception: Line %d, not enought arguments for operator \"-\" (required 2, found 1)\n" n; exit 1
                     | h1 :: h2 :: [] -> [Op(Sub, h1, h2)]
                     | h1 :: h2 :: q -> [Op(Sub, h1, h2)] @ q)
    | "*" :: q -> (let retour = auxiliaire q n in match retour with 
                     | [] -> printf "Exception: Line %d, not enought arguments for operator \"*\" (required 2, found 0)\n" n; exit 1
                     | h :: [] -> printf "Exception: Line %d, not enought arguments for operator \"*\" (required 2, found 1)\n" n; exit 1
                     | h1 :: h2 :: [] -> [Op(Mul, h1, h2)]
                     | h1 :: h2 :: q -> [Op(Mul, h1, h2)] @ q)
    | "/" :: q -> (let retour = auxiliaire q n in match retour with 
                     | [] -> printf "Exception: Line %d, not enought arguments for operator \"/\" (required 2, found 0)\n" n; exit 1
                     | h :: [] -> printf "Exception: Line %d, not enought arguments for operator \"/\" (required 2, found 1)\n" n; exit 1
                     | h1 :: h2 :: [] -> [Op(Div, h1, h2)]
                     | h1 :: h2 :: q -> [Op(Div, h1, h2)] @ q)
    | "%" :: q -> (let retour = auxiliaire q n in match retour with 
                     | [] -> printf "Exception: Line %d, not enought arguments for operator \"%%\" (required 2, found 0)\n" n; exit 1
                     | h :: [] -> printf "Exception: Line %d, not enought arguments for operator \"%%\" (required 2, found 1)\n" n; exit 1
                     | h1 :: h2 :: [] -> [Op(Mod, h1, h2)]
                     | h1 :: h2 :: q -> [Op(Mod, h1, h2)] @ q)
    | h :: q -> Var(h) :: auxiliaire q n
  in check_expression_validity (auxiliaire exp n) n
;;


let split_on_operator condition = 
  let rec interne cond expr1 = match cond with
    | [] -> ([], "", [])
    | operator :: expr2 when List.mem operator operators -> (expr1, operator, expr2)
    | h :: q -> interne q (expr1 @ [h])
  in interne condition []
;;


let get_condition condition line= let (expr1, operator, expr2) = split_on_operator condition in 
    match operator with 
      | "=" -> (get_expression expr1 line, Eq, get_expression expr2 line)
      | "<>" -> (get_expression expr1 line, Ne, get_expression expr2 line)
      | "<" -> (get_expression expr1 line, Lt, get_expression expr2 line)
      | "<=" -> (get_expression expr1 line, Le, get_expression expr2 line)
      | ">" -> (get_expression expr1 line, Gt, get_expression expr2 line)
      | ">=" -> (get_expression expr1 line, Ge, get_expression expr2 line)
      | _ -> printf "Exception: Line %d, cannot parse condition because no operator was found\n" line; exit 1;
;;


let rec calcul_indent line = match line with 
  | "" :: q -> 1 + calcul_indent q 
  | _ -> 0
;;

let rec search_for_else lines current_indent = match lines with
  | [] -> []
  | (n, l) :: lines_queue -> let line = (String.split_on_char ' ' l) in
      let indent = calcul_indent line in
        if indent >= current_indent then search_for_else lines_queue current_indent
        else if indent = (current_indent - 2) && List.hd (purifier line) = "ELSE" then lines_queue
        else []
;;


let read_lines lines = 
  let rec aux lines current_indent allow_else =
    (match lines with
      | [] -> []
      | (n, l) :: lines_queue ->let line = (String.split_on_char ' ' l) in
          let indent = calcul_indent line in
            if (indent = current_indent && allow_else && List.hd (purifier line) = "ELSE") || List.hd (purifier line) = "COMMENT" then aux lines_queue current_indent false
            else if indent = current_indent then (n, convert_line (String.split_on_char ' ' l) current_indent lines_queue n) :: aux lines_queue current_indent (if List.hd (purifier line) = "IF" then true else false)
            else if indent > current_indent then aux lines_queue current_indent allow_else
            else [])

  and convert_line line current_indent prog_continuation n = 
    (match purifier line with 
      | "PRINT"::r -> Print(get_expression (purifier r) n)
      | "READ" :: n :: [] -> Read(n)
      | "READ" :: q -> printf "Syntax error: Line %d, READ method does not allow multiple parameters\n" n; exit 1;
      | "WHILE" :: q -> While(get_condition q n, aux prog_continuation (current_indent + 2) false)
      | "IF" :: q -> If(get_condition q n, aux prog_continuation (current_indent + 2) false, aux (search_for_else prog_continuation (current_indent + 2)) (current_indent + 2) false)
      | "ELSE" :: q -> printf "Syntax error: Lune %d, found ELSE keyword, but no IF were found before\n" n; exit 1;
      | h :: ":=" :: q -> Set(h, get_expression (purifier q) n) (* cette ligne doit être à la fin du match*)
      | _ -> Read("a"))
  in aux lines 0 false
;;


let read_polish (filename:string) : program =
  let ic = open_in filename in 
  let file = read_file ic 0 in 
    read_lines file 
;;

let print_polish (p:program) : unit = 

  let rec print_indent (current_block:int) : unit =
    if current_block <= 0 then () else begin printf "  "; print_indent (current_block - 1) end; 
  in

  let rec print_expr (expression:expr) : unit =
    match expression with 
      | Num(x) -> printf "%s " (string_of_int x);
      | Var(name) -> printf "%s " (name)
      | Op(op1, expr1, expr2) -> match op1 with
        | Add -> printf("+ "); print_expr expr1; print_expr expr2;
        | Sub -> printf("- "); print_expr expr1; print_expr expr2;
        | Mul -> printf("* "); print_expr expr1; print_expr expr2;
        | Div -> printf("/ "); print_expr expr1; print_expr expr2;
        | Mod -> printf "%s" ("% "); print_expr expr1; print_expr expr2;
  in

  let print_condi condi = 
    match condi with 
      | (expr1, Eq, expr2) -> print_expr expr1; printf "= "; print_expr expr2;
      | (expr1, Ne, expr2) -> print_expr expr1; printf "<> "; print_expr expr2; (* Not equal, <> *)
      | (expr1, Lt, expr2) -> print_expr expr1; printf "< "; print_expr expr2; (* Less than, < *)
      | (expr1, Le, expr2) -> print_expr expr1; printf "<= "; print_expr expr2; (* Less or equal, <= *)
      | (expr1, Gt, expr2) -> print_expr expr1; printf "> "; print_expr expr2; (* Greater than, > *)
      | (expr1, Ge, expr2) -> print_expr expr1; printf ">= "; print_expr expr2; (* Greater or equal, >= *)

  in 

  let rec print_instr (instruc:instr) (current_block:int) : unit = 
    match instruc with
      | Set(name,expr) -> print_indent current_block;
          printf "%s" (name ^ " := "); print_expr expr; 
      | Read(name) -> print_indent current_block;
          printf "%s" ("READ " ^ name);
      | Print(expr) -> print_indent current_block;
          printf "%s" ("PRINT "); print_expr expr;
      | While(cond, block) -> print_indent current_block; printf "WHILE " ;
          print_condi cond; printf "\n" ;interne (current_block + 1) block;
      | If(cond, block1, block2) -> match block2 with 
        | [] -> print_indent current_block;
            printf "%s" "IF "; print_condi cond; printf "\n" ; interne (current_block + 1) block1;
        | block2 -> print_indent current_block;
            printf "%s" "IF "; print_condi cond; printf "\n" ; interne (current_block + 1) block1;
            printf "\n"; print_indent current_block; printf "ELSE\n"; interne (current_block + 1) block2; 
  and interne (current_block:int) (lp:program) : unit =
    match lp with 
      | [] -> ()
      | h::[] -> print_instr (snd h) current_block;
      | h::t -> print_instr (snd h) current_block; printf "\n" ; interne current_block t;
  in interne 0 p;;

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

let eval_condition (expr1, comparator, expr2) env l = match comparator with 
  | Eq -> (eval_expr expr1 env l) = (eval_expr expr2 env l)
  | Ne -> (eval_expr expr1 env l) <> (eval_expr expr2 env l)
  | Lt -> (eval_expr expr1 env l) < (eval_expr expr2 env l)
  | Le -> (eval_expr expr1 env l) <= (eval_expr expr2 env l)
  | Gt -> (eval_expr expr1 env l) > (eval_expr expr2 env l)
  | Ge -> (eval_expr expr1 env l) >= (eval_expr expr2 env l)



let print_expression expr env l = 
  match expr with 
    | Num(n) -> printf "%d\n" n
    | Var(v) -> printf "%d\n" (get_variable v env l)
    | Op(_, _, _) -> printf "%d\n" (eval_expr expr env l)
;;


let read_variable n env l = 
  printf "%s? " n; 
  let saisie = read_int () in 
    ENV.add n saisie env;;

let masquer_retour retour = ();;



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



let simpl_polish (p:program) = 

  let rec no_var expr =
    match expr with 
      | Num(x) -> true
      | Var(name) -> false
      | Op(op, expr1, expr2) -> (no_var expr1) && (no_var expr2)
  in

  let toujours_valide cond =
    match cond with
      | expr1, comp, expr2 when not (no_var expr1) || not (no_var expr2) -> None (* Cas ou l'on a des varibles dans la condition*)
      | Num(x), comp, Num(y) (*Les expressions sont deja simplifiées car on l'appelle sur interne *) 
        -> (match comp with
             | Eq -> Some(x = y)
             | Ne -> Some(x <> y)
             | Lt -> Some(x < y)
             | Le -> Some(x <= y)
             | Gt -> Some(x > y)
             | Ge -> Some(x >= y))
      | _ -> assert(false)

  in 

  let rec code_mort (p:program) (acc:program) = 
    match p with 
      | [] -> acc
      | (pos, instr)::xs -> match instr with 
        | If(cond, block1, block2) -> (match toujours_valide cond with
                                        | None -> code_mort xs (List.append acc [(pos, If(cond, block1, block2))])
                                        | Some(true) -> code_mort xs (List.append acc block1)
                                        | Some(false) -> code_mort xs (List.append acc block2))
        | While(cond, block) -> (match toujours_valide cond with
                                  | None | Some(true) -> code_mort xs (List.append acc [pos, While(cond, block)])
                                  | Some(false) -> code_mort xs acc)
        | instr -> code_mort xs (List.append acc [(pos, instr)])

  in 

  let rec reline (p:program) pos_courante acc=
    match p with
      | [] -> acc
      | (pos,instr)::xs -> reline xs (pos_courante + 1) (List.append acc [pos_courante, instr])  

  in

  let rec simpl_expr_ari(expr_init:expr) =
    match expr_init with 
      | Num(x) -> Num(x)
      | Var(name) -> Var(name)
      | Op(op, Num(x), Num(y)) -> (match op with 
                                    | Add -> Num(x + y)
                                    | Sub -> Num(x - y)
                                    | Mul -> Num(x * y)
                                    | Div -> Num(x / y)
                                    | Mod -> Num(x mod y))
      | Op(op, Var(name1), Num(y)) -> (match op with 
                                        | Add -> if y = 0 then Var(name1) else Op(op, Var(name1), Num(y))
                                        | Mul -> if y = 1 then Var(name1) else 
                                            if y = 0 then Num 0 else Op(op, Var(name1), Num(y))
                                        | Div -> if y = 1 then Var(name1) else Op(op, Var(name1), Num(y))
                                        | _ -> Op(op, Var(name1), Num(y)))
      | Op(op, Num(x), Var(name2)) -> (match op with 
                                        | Add -> if x = 0 then Var(name2) else Op(op, Num(x) , Var(name2))
                                        | Mul -> if x = 1 then Var(name2) else 
                                            if x = 0 then Num 0 else Op(op, Num(x) , Var(name2))
                                        | Div -> if x = 0 then Num 0 else Op(op, Num(x) , Var(name2))
                                        | _ -> Op(op, Num(x) , Var(name2)))
      | Op(op, Var(name1), Var(name2)) -> Op(op, Var(name1), Var(name2))
      | Op(op, expr1, expr2) -> simpl_expr_ari (Op(op, simpl_expr_ari expr1, simpl_expr_ari expr2))
  in

  let simpl_condi cond = match cond with
    | (expr1, Eq, expr2) -> simpl_expr_ari expr1, Eq, simpl_expr_ari expr2;
    | (expr1, Ne, expr2) -> simpl_expr_ari expr1, Ne, simpl_expr_ari expr2; 
    | (expr1, Lt, expr2) -> simpl_expr_ari expr1, Lt, simpl_expr_ari expr2; 
    | (expr1, Le, expr2) -> simpl_expr_ari expr1, Le, simpl_expr_ari expr2;
    | (expr1, Gt, expr2) -> simpl_expr_ari expr1, Gt, simpl_expr_ari expr2; 
    | (expr1, Ge, expr2) -> simpl_expr_ari expr1, Ge, simpl_expr_ari expr2; 

  in

  let rec simpl_instr instruct = match instruct with
    | Set(name, expr) -> Set(name, simpl_expr_ari expr)
    | If(cond, block1, block2) -> If(simpl_condi cond, interne block1 [], interne block2 [])
    | While(cond, block) -> While(simpl_condi cond, interne block [])
    | Print(expr) -> Print(simpl_expr_ari expr)
    | Read(name) -> Read(name)

  and 

    interne (p:program) acc =
    match p with
      | [] -> acc
      | (pos, instruct)::xs -> interne xs (List.append acc [(pos, simpl_instr instruct)])
  in reline(code_mort (interne p []) []) 0 []
;; 


let usage () =
  print_string "Polish : analyse statique d'un mini-langage\n";
  print_string "usage: à documenter (TODO)\n"

let main () =
  match Sys.argv with
    | [|_;"--reprint";file|] -> print_polish (read_polish file)
    | [|_;"--eval";file|] -> eval_polish (read_polish file)
    | [|_;"--simpl";file|] -> print_polish (simpl_polish(read_polish file))
    | _ -> usage ()

(* lancement de ce main *)
let () = main ()
