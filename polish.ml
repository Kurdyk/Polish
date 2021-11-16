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

let is_numeric str = 
  try
    let _ = int_of_string str in
      true;
  with Failure _ -> false
;;

let var_exists name = ENV.mem name !env;;

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
                     | h1 :: h2 :: [] -> [Op(Mul, h1, h2)]
                     | h1 :: h2 :: q -> [Op(Div, h1, h2)] @ q)
    | "%" :: q -> (let retour = auxiliaire q in match retour with 
                     | [] -> printf "Exception: Not enought arguments for operator %% (required 2, found 0)"; exit 1
                     | h :: [] -> printf "Exception: Not enought arguments for operator %% (required 2, found 1)"; exit 1
                     | h1 :: h2 :: [] -> [Op(Mul, h1, h2)]
                     | h1 :: h2 :: q -> [Op(Mod, h1, h2)] @ q)
    | h :: q -> if not (var_exists h) then begin printf "Variable %s referenced before assignment" h; exit 1; end else Var(h) :: auxiliaire q
  in check_expression_validity (auxiliaire exp)
;;

let rec convert_line line = match line with 
  | "PRINT"::r -> Print(get_expression (purifier r))
;;


let rec read_lines lines = match lines with
  | [] -> []
  | (n, l) :: lines_queue -> convert_line (String.split_on_char ' ' l) :: read_lines lines_queue
;;


let read_polish (filename:string) : program =
  let ic = open_in filename in 
    read_file ic 0;;
read_polish "/Users/victor/Documents/Cours L3/PF5/pf5-projet/exemples/fact.p";;


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
