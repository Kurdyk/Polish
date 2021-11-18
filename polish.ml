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
                       "="; "<>"; "<"; "<="; ">"; ">="]

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
    | h :: q -> if not (var_exists h) then begin printf "Variable %s referenced before assignment" h; exit 1; end else Var(h) :: auxiliaire q
  in check_expression_validity (auxiliaire exp)
;;


let rec convert_line line = match line with 
  | "PRINT"::r -> Print(get_expression (purifier r))
  | "READ" :: n :: [] -> Read(n)
  | "READ" :: q -> printf "Syntax error: READ method does not allow multiple parameters"; exit 1;
  | h :: ":=" :: q -> Set(h, get_expression (purifier q)) (* cette ligne doit être à la fin du match*)
  | _ -> Read("a")
;;


let rec read_lines lines = match lines with
  | [] -> []
  | (n, l) :: lines_queue -> convert_line (String.split_on_char ' ' l) :: read_lines lines_queue
;;


let read_polish (filename:string) : program =
  let ic = open_in filename in 
    read_file ic 0;;




let print_polish (p:program) : unit = 

  let rec print_indent (current_block:int) : unit =
    if current_block <= 0 then () else begin printf "  "; print_indent (current_block - 1) end; 
  in

  let rec print_expr (expression:expr) : unit =
    match expression with 
      | Num(x) -> printf "%s" (string_of_int x);
      | Var(name) -> printf "%s" (name)
      | Op(op1, expr1, expr2) -> match op1 with
        | Add -> printf(" + "); print_expr expr1; print_expr expr2;
        | Sub -> printf(" - "); print_expr expr1; print_expr expr2;
        | Mul -> printf(" * "); print_expr expr1; print_expr expr2;
        | Div -> printf(" / "); print_expr expr1; print_expr expr2;
        | Mod -> printf "%s" (" % "); print_expr expr1; print_expr expr2;
  in

  let print_condi condi = 
    match condi with 
      | (expr1, Eq, expr2) -> print_expr expr1; printf " = "; print_expr expr2;
      | (expr1, Ne, expr2) -> print_expr expr1; printf " <> "; print_expr expr2; (* Not equal, <> *)
      | (expr1, Lt, expr2) -> print_expr expr1; printf " < "; print_expr expr2; (* Less than, < *)
      | (expr1, Le, expr2) -> print_expr expr1; printf " <= "; print_expr expr2; (* Less or equal, <= *)
      | (expr1, Gt, expr2) -> print_expr expr1; printf " > "; print_expr expr2; (* Greater than, > *)
      | (expr1, Ge, expr2) -> print_expr expr1; printf " >= "; print_expr expr2; (* Greater or equal, >= *)

  in 

  let rec print_instr (instruc:instr) (current_block:int) : unit = 
    match instruc with
      | Set(name,expr) -> print_indent current_block;
          printf "%s" (name ^ " := "); print_expr expr; 
      | Read(name) -> print_indent current_block;
          printf "%s" ("READ " ^ name);
      | Print(expr) -> print_indent current_block;
          printf "%s" ("PRINT "); print_expr expr;
      | If(cond, block1, block2) -> print_indent current_block;
          printf "%s" "IF "; print_condi cond; interne (current_block + 1) block1;
          printf "%s\n" "ELSE"; interne (current_block + 1) block2; 
      | While(cond, block) -> print_indent current_block;
          print_condi cond; interne (current_block + 1) block;

  and interne (current_block:int) (lp:program) : unit =
    match lp with 
      | [] -> ()
      | h::t -> print_instr (snd h) current_block; printf "\n" ; interne current_block t;
  in interne 0 p;;

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
