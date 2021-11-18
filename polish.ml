open Format
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
let env = ref ENV.empty

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

let var_exists name = ENV.mem name !env;;

let get_variable name = if ENV.mem name !env then ENV.find name !env else begin printf "Variable %s referenced before assignement" name; exit 1; end;;

let check_variable_name name = if List.mem name exclusion_names then begin printf "Cannot name variable %s: forbidden name (reserved keyword)" name; exit 1; end else if is_numeric (String.make 1 (String.get name 0)) then begin printf "Cannot name variable %s: invalid name" name; exit 1; end;;

let set_variable name value = check_variable_name name; env := ENV.add name value !env;;


let rec read_file channel current = 
  try
    let line = input_line channel in
      (current, line) :: read_file channel (current + 1)
  with End_of_file -> 
    close_in_noerr channel;
    []
;;

let purifier liste = List.filter (fun k -> k <> "") liste;;

let check_expression_validity expression = if List.length expression = 1 then List.hd expression else match List.hd (List.tl expression) with | Num(a) -> printf "Exception: Unexpected argument %d" a; exit 1; |_ -> printf "Exception: Unknown error"; exit 1;;

let get_expression exp =
  let rec auxiliaire exp = match exp with 
    | [] -> []
    | h :: q when is_numeric h  -> Num(int_of_string h) :: auxiliaire q
    | "+" :: q -> (let retour = auxiliaire q in match retour with 
                     | [] -> printf "Exception: Not enought arguments for operator + (required 2, found 0)"; exit 1
                     | h :: [] -> printf "Exception: Not enought arguments for operator + (required 2, found 1)"; exit 1
                     | h1 :: h2 :: [] -> [Op(Add, h1, h2)]
                     | h1 :: h2 :: q -> [Op(Add, h1, h2)] @ q)
    | "-" :: q -> (let retour = auxiliaire q in match retour with 
                     | [] -> printf "Exception: Not enought arguments for operator - (required 2, found 0)"; exit 1
                     | h :: [] -> printf "Exception: Not enought arguments for operator - (required 2, found 1)"; exit 1
                     | h1 :: h2 :: [] -> [Op(Sub, h1, h2)]
                     | h1 :: h2 :: q -> [Op(Sub, h1, h2)] @ q)
    | "*" :: q -> (let retour = auxiliaire q in match retour with 
                     | [] -> printf "Exception: Not enought arguments for operator * (required 2, found 0)"; exit 1
                     | h :: [] -> printf "Exception: Not enought arguments for operator * (required 2, found 1)"; exit 1
                     | h1 :: h2 :: [] -> [Op(Mul, h1, h2)]
                     | h1 :: h2 :: q -> [Op(Mul, h1, h2)] @ q)
    | "/" :: q -> (let retour = auxiliaire q in match retour with 
                     | [] -> printf "Exception: Not enought arguments for operator / (required 2, found 0)"; exit 1
                     | h :: [] -> printf "Exception: Not enought arguments for operator / (required 2, found 1)"; exit 1
                     | h1 :: h2 :: [] -> [Op(Div, h1, h2)]
                     | h1 :: h2 :: q -> [Op(Div, h1, h2)] @ q)
    | "%" :: q -> (let retour = auxiliaire q in match retour with 
                     | [] -> printf "Exception: Not enought arguments for operator %% (required 2, found 0)"; exit 1
                     | h :: [] -> printf "Exception: Not enought arguments for operator %% (required 2, found 1)"; exit 1
                     | h1 :: h2 :: [] -> [Op(Mod, h1, h2)]
                     | h1 :: h2 :: q -> [Op(Mod, h1, h2)] @ q)
    | h :: q -> Var(h) :: auxiliaire q
  in check_expression_validity (auxiliaire exp)
;;


let split_on_operator condition = 
  let rec interne cond expr1 = match cond with
    | [] -> ([], "", [])
    | operator :: expr2 when List.mem operator operators -> (expr1, operator, expr2)
    | h :: q -> interne q (expr1 @ [h])
  in interne condition []
;;


let rec get_condition condition line= let (expr1, operator, expr2) = split_on_operator condition in 
    match operator with 
      | "=" -> (get_expression expr1, Eq, get_expression expr2)
      | "<>" -> (get_expression expr1, Ne, get_expression expr2)
      | "<" -> (get_expression expr1, Lt, get_expression expr2)
      | "<=" -> (get_expression expr1, Le, get_expression expr2)
      | ">" -> (get_expression expr1, Gt, get_expression expr2)
      | ">=" -> (get_expression expr1, Ge, get_expression expr2)
      | _ -> printf "Exception: cannot parse condition on line %d, no operator found" line; exit 1;
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
      | "PRINT"::r -> Print(get_expression (purifier r))
      | "READ" :: n :: [] -> Read(n)
      | "READ" :: q -> printf "Syntax error: READ method does not allow multiple parameters"; exit 1;
      | "WHILE" :: q -> While(get_condition q n, aux prog_continuation (current_indent + 2) false)
      | "IF" :: q -> If(get_condition q n, aux prog_continuation (current_indent + 2) false, aux (search_for_else prog_continuation (current_indent + 2)) (current_indent + 2) false)
      | "ELSE" :: q -> printf "Syntax error, line %d: found ELSE keyword, but no IF were found before" n; exit 1;
      | h :: ":=" :: q -> Set(h, get_expression (purifier q)) (* cette ligne doit être à la fin du match*)
      | _ -> Read("a"))
  in aux lines 0 false
;;


let read_polish (filename:string) : program =
  let ic = open_in filename in 
  let file = read_file ic 0 in 
    read_lines file 
;;





let print_polish (p:program) : unit = failwith "TODO"

let eval_polish (p:program) : unit = failwith "TODO"

let usage () =
  print_string "Polish : analyse statique d'un mini-langage\n";
  print_string "usage: à documenter (TODO)\n"

let main () =
  match Sys.argv with
    | [|_;"--reprint";file|] -> print_polish (read_polish file)
    | [|_;"--eval";file|] -> eval_polish (read_polish file)
    | _ -> usage ()

(* lancement de ce main *)
let () = main ()
