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
      | (Zero, Pos) -> 1
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
  in interne 0 p; printf "\n" ;;

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

  let rec var_in expr =
    match expr with 
      | Num(x) -> []
      | Var(name) -> [name]
      | Op(op, expr1, expr2) -> List.rev_append (var_in expr1) (var_in expr2)
  in

  let toujours_valide cond = 
    match cond with
      | expr1, comp, expr2 when not (var_in expr1 = []) || not (var_in expr2 = [])
        -> None (* Cas ou l'on a des varibles dans la condition*)
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
      | Op(op, expr1, Num(y)) -> (match op with 
                                   | Add -> if y = 0 then simpl_expr_ari expr1 else Op(op, simpl_expr_ari expr1, Num(y))
                                   | Mul -> if y = 1 then simpl_expr_ari expr1 else 
                                       if y = 0 then Num 0 else Op(op, simpl_expr_ari expr1, Num(y))
                                   | Div -> if y = 1 then simpl_expr_ari expr1 else Op(op, simpl_expr_ari expr1, Num(y))
                                   | _ -> Op(op, simpl_expr_ari expr1, Num(y)))
      | Op(op, Num(x), expr2) -> (match op with 
                                   | Add -> if x = 0 then simpl_expr_ari expr2 else Op(op, Num(x) , simpl_expr_ari expr2)
                                   | Mul -> if x = 1 then simpl_expr_ari expr2 else 
                                       if x = 0 then Num 0 else Op(op, Num(x) ,simpl_expr_ari expr2)
                                   | Div -> if x = 0 then Num 0 else Op(op, Num(x) , simpl_expr_ari expr2)
                                   | _ -> Op(op, Num(x) , simpl_expr_ari expr2))
      | Op(op, Var(name1), Var(name2)) -> Op(op, Var(name1), Var(name2))
      | Op(op, expr1, expr2) -> Op(op, simpl_expr_ari expr1, simpl_expr_ari expr2)

  in

  let simpl_cond cond = match cond with
    | (expr1, comp, expr2) -> simpl_expr_ari expr1, comp, simpl_expr_ari expr2;

  in

  let rec simpl_with_const expr env = 
    match expr with 
      | Var(name) when ENV.mem name env -> ENV.find name env
      | Op(op, Var(name1), Num(y)) when ENV.mem name1 env -> simpl_expr_ari (Op(op, ENV.find name1 env, Num(y)))

      | Op(op, Num(x), Var(name2)) when ENV.mem name2 env ->  simpl_expr_ari (Op(op, Num(x), ENV.find name2 env))

      | Op(op, Var(name1), Var(name2)) when ENV.mem name1 env && ENV.mem name2 env
        ->  simpl_expr_ari (Op(op, ENV.find name1 env, ENV.find name2 env))

      | Op(op, Var(name1), Var(name2)) when ENV.mem name1 env && not (ENV.mem name2 env)
        ->  simpl_expr_ari (Op(op, ENV.find name1 env, Var(name2)))

      | Op(op, Var(name1), Var(name2)) when not (ENV.mem name1 env) && ENV.mem name2 env
        ->  simpl_expr_ari (Op(op, Var(name1), ENV.find name2 env))

      | Op(op, Var(name1), Var(name2)) when not (ENV.mem name1 env && ENV.mem name2 env)
        ->  simpl_expr_ari (Op(op, Var(name1), Var(name2)))

      | Op(op, expr1, expr2) -> simpl_expr_ari (Op(op, simpl_with_const expr1 env, simpl_with_const expr2 env))
      | expr -> expr

  in

  let simpl_cond_with_const cond env = 
    match cond with 
      | (expr1, comp, expr2) -> simpl_with_const expr1 env, comp, simpl_with_const expr2 env
  in 

  let maj_env env_init env_maj = 
    ENV.mapi (fun key _ -> ENV.find key env_maj) (ENV.filter (fun key _ -> ENV.mem key env_maj) env_init) 

  in 

  let stability env_init env_post = 
    ENV.filter (fun key value -> ENV.find key env_post = value) (ENV.filter (fun key _ -> ENV.mem key env_post) env_init) 
  in 



  let rec find_const (p:program) env_const acc in_while =
    match p with
      | [] -> acc, env_const
      | (pos, instr)::t -> match instr with 

        | Set(name, expr) -> let expr_s = simpl_expr_ari expr in 
              (match var_in expr_s with
                | [] -> find_const
                          t 
                          (ENV.add name expr_s env_const) 
                          (List.append acc [pos, Set(name, expr_s)]) 
                          in_while
                | l ->let expr_final = simpl_with_const expr_s env_const in 
                      if List.for_all (fun x -> ENV.mem x env_const) l && not in_while
                      then find_const
                             t 
                             (ENV.add name expr_final env_const) 
                             (List.append acc [pos, Set(name, expr_final)]) 
                             in_while
                      else if List.mem name l then
                        find_const
                          t
                          (ENV.remove name env_const)
                          (List.append acc [pos, Set(name, simpl_with_const expr_s (ENV.remove name env_const))]) 
                          in_while
                      else
                        find_const
                          t
                          (ENV.add name expr_s env_const) 
                          (List.append acc [pos, Set(name, expr_final)]) 
                          in_while)

        | Read(name) -> find_const 
                          t
                          (ENV.remove name env_const) 
                          (List.append acc [pos, Read(name)]) 
                          in_while
        | Print(expr) -> find_const 
                           t env_const
                           (List.append acc [pos, Print(simpl_with_const expr env_const)])
                           in_while

        | If(cond, block1, block2) -> 
            let b1, env1 = find_const block1 env_const [] in_while in
            let b2, env2 = find_const block2 env_const [] in_while in 
              (match toujours_valide (simpl_cond_with_const cond env_const) with
                | None -> find_const 
                            t
                            (stability env1 env2)
                            (List.append acc [pos, If(simpl_cond_with_const cond env_const, b1, b2)])
                            in_while
                | Some(true) -> find_const 
                                  t
                                  (maj_env env_const env1)
                                  (List.append acc b1)
                                  in_while
                | Some(false) -> find_const 
                                   t
                                   (maj_env env_const env2)
                                   (List.append acc b2)
                                   in_while)


        | While(cond, block) -> let b, env = find_const block env_const [] true in
              match toujours_valide (simpl_cond_with_const cond (maj_env env_const env)) with 
                | None | Some(true) -> find_const
                                         t 
                                         (stability env_const env)
                                         (List.append acc [pos, While(simpl_cond cond, b)])
                                         in_while
                | Some(false) -> find_const
                                   t 
                                   (stability env_const env)
                                   acc
                                   in_while



  in reline(fst (find_const p ENV.empty [] false)) 0 []
;; 



let vars (p:program) =

  let fst_t triplet = 
    match triplet with
      | a, b, c -> a
  in 

  let snd_t triplet = 
    match triplet with
      | a, b, c -> b
  in 

  let trd_t triplet = 
    match triplet with
      | a, b, c -> c
  in 


  let rec check_var names env =
    match names with 
      | [] -> [], []
      | x::xs -> let couple = check_var xs env in
            if VAR.mem x env 
            then x::(fst couple), snd couple
            else x::(fst couple), x::(snd couple)
  in 

  let rec find_var_expr expr =
    match expr with 
      | Var(name) -> [name]
      | Num(_) -> []
      | Op(op, expr1, expr2) -> List.append (find_var_expr expr1) (find_var_expr expr2)
  in

  let find_var_condi cond = 
    match cond with
      | (expr1, comp, expr2) -> List.append (find_var_expr expr1) (find_var_expr expr2)

  in

  let print_env env = 
    masquer_retour (VAR.map (fun name -> let () = printf "%s " name in name) env) 
  in

  let rec interne (p:program) env_tot env_bad_access env_well_declared =
    match p with
      | [] -> env_tot, env_bad_access, env_well_declared
      | (_, instr)::xs -> match instr with
        | Read(name) -> interne xs (VAR.add name env_tot) env_bad_access (VAR.add name env_well_declared)
        | Set(name, expr) -> let couple = check_var (find_var_expr expr) env_well_declared
            in interne 
                 xs 
                 (VAR.union (VAR.add name env_tot) (VAR.of_list (fst couple)))
                 (VAR.union env_bad_access (VAR.of_list (snd couple))) 
                 (VAR.add name env_well_declared)
        | Print(expr) -> let couple = check_var (find_var_expr expr) env_well_declared
            in interne 
                 xs 
                 (VAR.union env_tot (VAR.of_list (fst couple)))
                 (VAR.union env_bad_access (VAR.of_list (snd couple)))
                 env_well_declared
        | If(cond, block1, block2) -> 
            let couple_cond = check_var (find_var_condi cond) env_well_declared
            in let b1 = interne block1 VAR.empty VAR.empty env_well_declared
            in let b2 = interne block2 VAR.empty VAR.empty env_well_declared
            in let env_vars = VAR.union (fst_t b1) (fst_t b2)
            in let env_vars_bad = VAR.union (snd_t b1) (snd_t b2)
            in let env_vars_well = VAR.inter (trd_t b1) (trd_t b2)
            in interne 
                 xs
                 (VAR.union env_vars (VAR.union env_tot (VAR.of_list (fst couple_cond))))
                 (VAR.union env_vars_bad (VAR.union env_bad_access (VAR.of_list ( (snd couple_cond) ))))
                 (VAR.union env_well_declared env_vars_well)
        | While(cond, block) -> let couple = check_var (find_var_condi cond) env_well_declared
            in let b = interne block VAR.empty VAR.empty env_well_declared
            in interne 
                 xs
                 (VAR.union (fst_t b) (VAR.union env_tot (VAR.of_list (fst couple))))
                 (VAR.union (snd_t b) (VAR.union env_bad_access (VAR.of_list (snd couple))))
                 env_well_declared


  in let env_triplet = interne p VAR.empty VAR.empty VAR.empty
  in print_env (fst_t env_triplet); printf "\n"; print_env (snd_t env_triplet); printf "\n"
;;



let ajouter_dans_set varname value env = ENV.update varname (fun x -> match x with | None -> None | Some a -> Some(VAR_SIGN.union value a)) env
let get_possible_signs varname env = ENV.find varname env;;
let nswoe element = (VAR_SIGN.add element (VAR_SIGN.empty))

let combine_possibilities operation expr1 expr2 = 
  let compute_comb operation sign1 sign2 = match (operation, sign1, sign2) with 
    | (Add, _, Sign.Error) | (Add, Sign.Error, _) -> VAR_SIGN.(empty |> add(Error))
    | (Add, Sign.Neg, Sign.Neg) | (Add, Sign.Neg, Sign.Zero) | (Add, Sign.Zero, Sign.Neg) -> VAR_SIGN.(empty |> add(Neg))
    | (Add, Sign.Pos, Sign.Pos) | (Add, Sign.Pos, Sign.Zero) | (Add, Sign.Zero, Sign.Pos) -> VAR_SIGN.(empty |> add(Pos))
    | (Add, Sign.Zero, Sign.Zero) -> VAR_SIGN.(empty |> add(Zero))
    | (Add, _, _) -> VAR_SIGN.(empty |> add(Neg) |> add(Zero) |> add(Pos))

    | (Sub, _, Sign.Error) | (Sub, Sign.Error, _) -> VAR_SIGN.(empty |> add(Error))
    | (Sub, Sign.Neg, Sign.Pos) | (Sub, Sign.Neg, Sign.Zero) | (Sub, Sign.Zero, Sign.Pos) -> VAR_SIGN.(empty |> add(Neg))
    | (Sub, Sign.Pos, Sign.Neg) | (Sub, Sign.Pos, Sign.Zero) | (Sub, Sign.Zero, Sign.Neg) -> VAR_SIGN.(empty |> add(Pos))
    | (Sub, Sign.Zero, Sign.Zero) -> VAR_SIGN.(empty |> add(Zero))
    | (Sub, _, _) -> VAR_SIGN.(empty |> add(Neg) |> add(Zero) |> add(Pos))

    | (Mul, _, Sign.Error) | (Mul, Sign.Error, _) -> VAR_SIGN.(empty |> add(Error))
    | (Mul, Sign.Pos, Sign.Neg) | (Mul, Sign.Neg, Sign.Pos) -> VAR_SIGN.(empty |> add(Neg))
    | (Mul, Sign.Pos, Sign.Pos) | (Mul, Sign.Neg, Sign.Neg) -> VAR_SIGN.(empty |> add(Pos))
    | (Mul, Sign.Zero, _) | (Mul, _, Sign.Zero) -> VAR_SIGN.(empty |> add(Zero))

    | (Div, _, Sign.Error) | (Div, Sign.Error, _) | (Div, _, Sign.Zero) -> VAR_SIGN.(empty |> add(Error))
    | (Div, Sign.Pos, Sign.Neg) | (Div, Sign.Neg, Sign.Pos) -> VAR_SIGN.(empty |> add(Neg))
    | (Div, Sign.Pos, Sign.Pos) | (Div, Sign.Neg, Sign.Neg) -> VAR_SIGN.(empty |> add(Pos))
    | (Div, Sign.Zero, _) -> VAR_SIGN.(empty |> add(Zero))

    | (Mod, _, Sign.Error) | (Mod, Sign.Error, _) | (Mod, _, Sign.Zero) -> VAR_SIGN.(empty |> add(Error))
    | (Mod, _, _) -> VAR_SIGN.(empty |> add(Pos))

  in let rec comb2 operation sign1 sign2_list env = 
       match (sign1, sign2_list) with
         | (_, []) -> env
         | (_, h :: q) -> comb2 operation sign1 q (VAR_SIGN.union env (compute_comb operation sign1 h))
  in let rec comb1 operation sign1_list sign2_list env = 
       match (sign1_list, sign2_list) with 
         | ([], _) -> env
         | (h :: q, _) -> comb1 operation q sign2_list (comb2 operation h sign2_list env)
  in comb1 operation (VAR_SIGN.elements expr1) (VAR_SIGN.elements expr2) VAR_SIGN.empty
;;

let rec detect_sign expr env = match expr with 
  | Num(a) -> if a < 0 then VAR_SIGN.(empty |> add(Neg))
      else if a = 0 then VAR_SIGN.(empty |> add(Zero))
      else VAR_SIGN.(empty |> add(Pos))
  | Var(v) -> get_possible_signs v env
  | Op(operation, expr1, expr2) -> combine_possibilities operation (detect_sign expr1 env) (detect_sign expr2 env)
;;

let merge_maps map1 map2 = 
  let get_keys map = 
    let rec interne bindings = match bindings with 
      | [] -> []
      | (k, v) :: q -> k :: interne q
    in interne (ENV.bindings map)
  in let rec aux keys env = match keys with
       | [] -> env 
       | k :: q -> aux q (match (ENV.mem k env, ENV.mem k map1, ENV.mem k map2) with
                           | (_, false, false) -> env
                           | (true, false, true) -> ENV.add k (VAR_SIGN.union (ENV.find k env) (ENV.find k map2)) env
                           | (false, false, true) -> ENV.add k (ENV.find k map2) env 
                           | (true, true, false) -> ENV.add k (VAR_SIGN.union (ENV.find k env) (ENV.find k map1)) env
                           | (false, true, false) -> ENV.add k (ENV.find k map1) env 
                           | (true, true, true) -> ENV.add k (VAR_SIGN.union (VAR_SIGN.union (ENV.find k env) (ENV.find k map2)) (ENV.find k map1)) env
                           | (false, true, true) -> ENV.add k (VAR_SIGN.union (ENV.find k map1) (ENV.find k map2)) env)
  in aux ((get_keys map1) @ (get_keys map2)) ENV.empty
;;


let neg_condition (expr1,comparator, expr2) = match comparator with 
  | Eq -> (expr1, Ne, expr2)
  | Ne -> (expr1, Eq, expr2)
  | Lt -> (expr1, Ge, expr2)
  | Ge -> (expr1, Lt, expr2)
  | Le -> (expr1, Gt, expr2)
  | Gt -> (expr1, Le, expr2)
;;


let satisfaisable (expr1, comp, expr2) env =
  let rec deux_egaux signs1_elements signs2 = 
    match signs1_elements with 
      | [] -> false
      | h :: q when VAR_SIGN.mem h signs2 -> true
      | h :: q -> deux_egaux q signs2
  in let rec lt signs1_elements signs2 = 
       let superieur_exist sign signs2 = 
         match sign with 
           | Sign.Neg -> not (VAR_SIGN.is_empty (VAR_SIGN.inter signs2 (VAR_SIGN.(empty |> add Neg |> add Zero |> add Pos))))
           | Sign.Zero -> not (VAR_SIGN.is_empty (VAR_SIGN.inter signs2 (VAR_SIGN.(empty |> add Pos))))
           | Sign.Pos -> not (VAR_SIGN.is_empty (VAR_SIGN.inter signs2 (VAR_SIGN.(empty |> add Pos))))
           | Sign.Error -> false
       in match signs1_elements with 
         | [] -> false
         | h :: q  when (superieur_exist h signs2) -> true
         | h :: q -> lt q signs2
  in let rec ge signs1_elements signs2 = 
       let aux sign signs2 = 
         match sign with 
           | Sign.Neg -> not (VAR_SIGN.is_empty (VAR_SIGN.inter signs2 (VAR_SIGN.(empty |> add Neg))))
           | Sign.Zero -> not (VAR_SIGN.is_empty (VAR_SIGN.inter signs2 (VAR_SIGN.(empty |> add Neg |> add Zero))))
           | Sign.Pos -> not (VAR_SIGN.is_empty (VAR_SIGN.inter signs2 (VAR_SIGN.(empty |> add Neg |> add Zero |> add Pos))))
           | Sign.Error -> false
       in match signs1_elements with 
         | [] -> false
         | h :: q  when (aux h signs2) -> true
         | h :: q -> ge q signs2
  in let rec le signs1_elements signs2 = 
       let aux sign signs2 = 
         match sign with 
           | Sign.Neg -> not (VAR_SIGN.is_empty (VAR_SIGN.inter signs2 (VAR_SIGN.(empty |> add Neg |> add Zero |> add Pos))))
           | Sign.Zero -> not (VAR_SIGN.is_empty (VAR_SIGN.inter signs2 (VAR_SIGN.(empty |> add Zero |> add Pos))))
           | Sign.Pos -> not (VAR_SIGN.is_empty (VAR_SIGN.inter signs2 (VAR_SIGN.(empty |> add Pos))))
           | Sign.Error -> false
       in match signs1_elements with 
         | [] -> false
         | h :: q  when (aux h signs2) -> true
         | h :: q -> le q signs2
  in let rec gt signs1_elements signs2 = 
       let aux sign signs2 = 
         match sign with 
           | Sign.Neg -> not (VAR_SIGN.is_empty (VAR_SIGN.inter signs2 (VAR_SIGN.(empty |> add Neg))))
           | Sign.Zero -> not (VAR_SIGN.is_empty (VAR_SIGN.inter signs2 (VAR_SIGN.(empty |> add Neg))))
           | Sign.Pos -> not (VAR_SIGN.is_empty (VAR_SIGN.inter signs2 (VAR_SIGN.(empty |> add Neg |> add Zero |> add Pos))))
           | Sign.Error -> false
       in match signs1_elements with 
         | [] -> false
         | h :: q  when (aux h signs2) -> true
         | h :: q -> gt q signs2
  in match comp with 
    | Eq -> deux_egaux (VAR_SIGN.elements (detect_sign expr1 env)) (detect_sign expr2 env)
    | Ne -> not (deux_egaux (VAR_SIGN.elements (detect_sign expr1 env)) (detect_sign expr2 env))
    | Lt -> lt (VAR_SIGN.elements (detect_sign expr1 env)) (detect_sign expr2 env)
    | Ge -> ge (VAR_SIGN.elements (detect_sign expr1 env)) (detect_sign expr2 env)
    | Le -> le (VAR_SIGN.elements (detect_sign expr1 env)) (detect_sign expr2 env)
    | Gt -> gt (VAR_SIGN.elements (detect_sign expr1 env)) (detect_sign expr2 env)
;;


let isoler_variable (expr1, comparator, expr2) var_name env = 
  let operation_inverse operateur = match operateur with 
    | Add -> Sub
    | Sub -> Add
    | Mul -> Div
    | Div -> Mul
    | Mod -> failwith "Not Supposed to simplify mod"
  in let rec var_in_expr expr var_name = match expr with 
       | Num(n) -> false
       | Var(a) when a = var_name -> true
       | Var(a) -> false
       | Op(operateur, expr1, expr2) -> (var_in_expr expr1 var_name) || (var_in_expr expr2 var_name)
  in let variable_isolee expr var_name = match expr with 
       | Var(a) when a = var_name -> true
       | _ -> false
  in let rec is_modulo_in_expr expr = match expr with
       | Num(a) -> false
       | Var(a) -> false
       | Op(Mod, _, _) -> true
       | Op(operateur, expr1, expr2) -> (is_modulo_in_expr expr1) || (is_modulo_in_expr expr2)
  in let is_processable expr1 expr2 var_name = 
       if ((var_in_expr expr1 var_name) && (is_modulo_in_expr expr1)) || ((var_in_expr expr2 var_name) && (is_modulo_in_expr expr2)) then false
       else true
  (*in let rec passer_op expr var_name env*)
  and isoler (expr1, comparator, expr2) var_name env = 
    if (variable_isolee expr1 var_name) || (variable_isolee expr2 var_name) then (expr1, comparator, expr2, env) 
    else (match comparator with 
           | _ -> if (var_in_expr expr1 var_name) then (expr1, comparator, expr2, env) else (expr1, comparator, expr2, env)
         )
  in if not (is_processable expr1 expr2 var_name) then None else Some (isoler (expr1, comparator, expr2) var_name)
;;

let sign_evaluate_condition (expr1, comparator, expr2) env =
  let rec initialise_env condition env = 
    match condition with 
      | Num(a) -> env
      | Var(name) -> ENV.add name (VAR_SIGN.empty) env
      | Op(operation, expr1, expr2) -> initialise_env expr2 (initialise_env (expr1) env)
  in initialise_env expr2 (initialise_env expr1 ENV.empty);;



let check_sign prog =
  let print_var_signs name signs = 
    let rec aux signs_list = match signs_list with 
      | [] -> printf "\n" 
      | Sign.Neg :: q -> printf "-"; aux q
      | Sign.Zero :: q -> printf "0" ; aux q
      | Sign.Pos :: q -> printf "+" ; aux q
      | Sign.Error :: q -> printf "!" ; aux q
    in printf "%s " name; aux (VAR_SIGN.elements signs)
  in let rec interne prog env = match prog with 
       | [] -> env
       | (l, Read(name)) :: suite_prog -> interne suite_prog (ENV.add name VAR_SIGN.(empty |> add(Neg) |> add(Zero) |> add(Pos)) env)
       | (l, Set(name, expr)) :: suite_prog -> interne suite_prog (ENV.add name (detect_sign expr env) env)
       (*| (l, If(cond, block1, block2)) :: suite_prog -> interne suite_prog (process_if cond block1 block2 env)*)
       | (l, If(cond, block1, block2)) :: suite_prog -> interne suite_prog (interne block2 (interne block1 env))
       | (l, While(cond, block)) :: suite_prog -> interne suite_prog (interne block env)
       | (l, Print(expr)) :: suite_prog -> interne suite_prog env
  and process_if cond blockIF blockELSE env = 
    merge_maps (if (satisfaisable cond env) 
                then (interne blockIF (sign_evaluate_condition cond env)) else ENV.empty) 
      (if (satisfaisable (neg_condition cond)env) 
       then (interne blockELSE (sign_evaluate_condition (neg_condition cond) env)) else ENV.empty)

  in ENV.iter print_var_signs (interne prog ENV.empty)

let usage () =
  print_string "Polish : analyse statique d'un mini-langage\n";
  print_string "	      usage: -option nom_fichier.p\nLes options sont :\n";
  print_string "-reprint : affiche le programme polish.\n";
  print_string "-eval : fait tourner le programme polish. Les READ du programme sont demandés dans le terminal.\n";
  print_string "-simpl : affiche le programme polish avec calculs simplifiés et propagation des constantes (et simplifications éventuelles de bloc.\n";
  print_string "-vars : affiche les variables du programme polish sur la première ligne et les varibales mal initialisées sur une seconde ligne.\n";
  print_string "-sign : affiche le signe attendu de chaque variable du programme polish après analyse statique.\n";;

let main () =
  match Sys.argv with
    | [|_;"-reprint";file|] -> print_polish (read_polish file)
    | [|_;"-eval";file|] -> eval_polish (read_polish file)
    | [|_;"-simpl";file|] -> print_polish (simpl_polish(read_polish file))
    | [|_;"-vars";file|] -> vars(read_polish file)
    | [|_; "-sign"; file|] -> check_sign(read_polish file)
    | _ -> usage ()

(* lancement de ce main *)
let () = main ()
