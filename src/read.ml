open Types
open Printf




(** Renvoie `true` si la chaine de caractère passée en paramètre représente une donnée numérique *)
let is_numeric str = 
  try
    let _ = int_of_string str in
      true;
  with Failure _ -> false
;;

(** Retire d'une liste de chaines de caractères toutes les chaines vides *)
let purifier liste = List.filter (fun k -> k <> "") liste;;

(** S'assure de la validité d'une expression Polish sous la forme d'une liste de chaines de caractères avant de la parser *)
let check_expression_validity expression n = 
if List.length expression = 1 
then List.hd expression 
else match List.hd (List.tl expression) with 
| Num(a) -> printf "Exception: Line %d, unexpected argument \"%d\"\n" n a; exit 1; 
| Var(a) -> printf "Exception: Line %d, unexpected argument \"%s\"\n" n a; exit 1; 
|_ -> printf "Exception: Line %d, cannot parse expression; unknown error\n" n; exit 1;;

(** Parse une expression Polish sous la forme d'une liste de chaines de caractères en sa représentation Ocaml.
Permet de détecter les erreurs de syntaxe dans les expressions Polish*)
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

(** Liste des opérateurs de comparaison Polish *)
let operators = ["="; "<>"; "<"; "<="; ">"; ">="]


(** Permet de séparer une conditon Polish sous la forme d'une liste de chaines de caractères en fonction de l'opérateur de comparaison. *)
let split_on_operator condition = 
  let rec interne cond expr1 = match cond with
    | [] -> ([], "", [])
    | operator :: expr2 when List.mem operator operators -> (expr1, operator, expr2)
    | h :: q -> interne q (expr1 @ [h])
  in interne condition []
;;


(** Prend en paramètre une chaine de caractères et retourne une représentation Ocaml de la condition Polish contenue dedans *)
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


(** Calcule l'indentation d'une ligne *) 
let rec calcul_indent line = match line with
  | "" :: q -> 1 + calcul_indent q 
  | _ -> 0
;;

(** Renvoie le bloc `ELSE` associé à un bloc `IF` si il existe *)
let rec search_for_else lines current_indent = match lines with
  | [] -> []
  | (n, l) :: lines_queue -> let line = (String.split_on_char ' ' l) in
      let indent = calcul_indent line in
        if indent >= current_indent then search_for_else lines_queue current_indent
        else if indent = (current_indent - 2) && List.hd (purifier line) = "ELSE" then lines_queue
        else []
;;


(** Prend en paramètre une liste (numero de ligne, contenu de la ligne) et renvoie la représentation du programme en Ocaml*)
let read_lines lines = 
  (* Parcours la liste de ligne et demande la conversion de la ligne à `convert_line` en s'assurant de la cohérence de l'indentation.
  S'assure également de la légalité du mot clé `ELSE` (y a-t-il un `IF` juste avant) et filtre les commentaires *)
  let rec aux lines current_indent allow_else =
    (match lines with
      | [] -> []
      | (n, l) :: lines_queue ->let line = (String.split_on_char ' ' l) in
          let indent = calcul_indent line in
            if (indent = current_indent && allow_else && List.hd (purifier line) = "ELSE") || List.hd (purifier line) = "COMMENT" then aux lines_queue current_indent false
            else if indent = current_indent then (n, convert_line (String.split_on_char ' ' l) current_indent lines_queue n) :: aux lines_queue current_indent (if List.hd (purifier line) = "IF" then true else false)
            else if indent > current_indent then aux lines_queue current_indent allow_else
            else [])

  (* Converti une chaine de caractères en représentation Ocaml de l'instruction Polish *)
  and convert_line line current_indent prog_continuation n = 
    (match purifier line with 
      | "PRINT"::r -> Print(get_expression (purifier r) n)
      | "READ" :: n :: [] -> Read(n)
      | "READ" :: q -> printf "Syntax error: Line %d, READ method does not allow multiple parameters\n" n; exit 1;
      | "WHILE" :: q -> While(get_condition q n, aux prog_continuation (current_indent + 2) false)
      | "IF" :: q -> If(get_condition q n, aux prog_continuation (current_indent + 2) false, aux (search_for_else prog_continuation (current_indent + 2)) (current_indent + 2) false)
      (* Le ELSE n'est pas traité ici mais dans la fonction search_for_else pour s'assurer que sa présence n'est pas illégale*)
      | "ELSE" :: q -> printf "Syntax error: Line %d, found ELSE keyword, but no IF were found before\n" n; exit 1;
      | h :: ":=" :: q -> Set(h, get_expression (purifier q) n) (* cette ligne doit être à la fin du match*)
      | _ -> Read("a"))
  in aux lines 0 false
;;


(** Prend en paramètre un channel et renvoie une liste de (numero de ligne, contenu de la ligne) de ce channel*)
let rec read_file channel current = 
  try
    let line = input_line channel in
      (current, line) :: read_file channel (current + 1)
  with End_of_file -> 
    close_in_noerr channel;
    []
;;

(** Prend un paramètre un nom de fichier et renvoie la représentation du programme polish en Ocaml*)
let read_polish (filename:string) : program =
  let ic = open_in filename in 
  let file = read_file ic 0 in 
    read_lines file 
;;