open Types
open Printf


(** Permet de savoir à quelle ligne une division par 0 risque de se produire. 
Utilisation d'une référence car c'est déjà bien le bordel et je ne me voyais pas rajouter
une valeur de retour supplémentaire à chaque fonction pour garder trace de ce numéro de ligne. *)
let first_division_by_0 = ref (-1) ;;

(** Enregistre qu'une division par 0 peut avoir lieu à la ligne `l` *)
let tell_division_by_zero l = if !first_division_by_0 = (-1) then first_division_by_0 := l else ();;


let ajouter_dans_set varname value env = ENV.update varname (fun x -> match x with | None -> None | Some a -> Some(VAR_SIGN.union value a)) env
let get_possible_signs varname env = ENV.find varname env;;
let nswoe element = (VAR_SIGN.add element (VAR_SIGN.empty))

(** Renvoie un set de tous les signes que peut prendre une opération arithmétique `operation`
entre deux expressions dont les signes possibles sont `expr1` et `expr2` *)
let combine_possibilities operation expr1 expr2 l = 
  let compute_comb operation sign1 sign2 = match (operation, sign1, sign2) with 
    | (Add, _, Sign.Error) | (Add, Sign.Error, _) -> tell_division_by_zero l; VAR_SIGN.(empty |> add(Error))
    | (Add, Sign.Neg, Sign.Neg) | (Add, Sign.Neg, Sign.Zero) | (Add, Sign.Zero, Sign.Neg) -> VAR_SIGN.(empty |> add(Neg))
    | (Add, Sign.Pos, Sign.Pos) | (Add, Sign.Pos, Sign.Zero) | (Add, Sign.Zero, Sign.Pos) -> VAR_SIGN.(empty |> add(Pos))
    | (Add, Sign.Zero, Sign.Zero) -> VAR_SIGN.(empty |> add(Zero))
    | (Add, _, _) -> VAR_SIGN.(empty |> add(Neg) |> add(Zero) |> add(Pos))

    | (Sub, _, Sign.Error) | (Sub, Sign.Error, _) -> tell_division_by_zero l; VAR_SIGN.(empty |> add(Error))
    | (Sub, Sign.Neg, Sign.Pos) | (Sub, Sign.Neg, Sign.Zero) | (Sub, Sign.Zero, Sign.Pos) -> VAR_SIGN.(empty |> add(Neg))
    | (Sub, Sign.Pos, Sign.Neg) | (Sub, Sign.Pos, Sign.Zero) | (Sub, Sign.Zero, Sign.Neg) -> VAR_SIGN.(empty |> add(Pos))
    | (Sub, Sign.Zero, Sign.Zero) -> VAR_SIGN.(empty |> add(Zero))
    | (Sub, _, _) -> VAR_SIGN.(empty |> add(Neg) |> add(Zero) |> add(Pos))

    | (Mul, _, Sign.Error) | (Mul, Sign.Error, _) -> tell_division_by_zero l; VAR_SIGN.(empty |> add(Error))
    | (Mul, Sign.Pos, Sign.Neg) | (Mul, Sign.Neg, Sign.Pos) -> VAR_SIGN.(empty |> add(Neg))
    | (Mul, Sign.Pos, Sign.Pos) | (Mul, Sign.Neg, Sign.Neg) -> VAR_SIGN.(empty |> add(Pos))
    | (Mul, Sign.Zero, _) | (Mul, _, Sign.Zero) -> VAR_SIGN.(empty |> add(Zero))

    | (Div, _, Sign.Error) | (Div, Sign.Error, _) | (Div, _, Sign.Zero) -> tell_division_by_zero l; VAR_SIGN.(empty |> add(Error))
    | (Div, Sign.Pos, Sign.Neg) | (Div, Sign.Neg, Sign.Pos) -> VAR_SIGN.(empty |> add(Neg))
    | (Div, Sign.Pos, Sign.Pos) | (Div, Sign.Neg, Sign.Neg) -> VAR_SIGN.(empty |> add(Pos))
    | (Div, Sign.Zero, _) -> VAR_SIGN.(empty |> add(Zero))

    | (Mod, _, Sign.Error) | (Mod, Sign.Error, _) | (Mod, _, Sign.Zero) -> tell_division_by_zero l; VAR_SIGN.(empty |> add(Error))
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

(** Calcule le signe d'une expression. *)
let rec detect_sign expr env l = match expr with 
  | Num(a) -> if a < 0 then VAR_SIGN.(empty |> add(Neg))
      else if a = 0 then VAR_SIGN.(empty |> add(Zero))
      else VAR_SIGN.(empty |> add(Pos))
  | Var(v) -> get_possible_signs v env
  | Op(operation, expr1, expr2) -> combine_possibilities operation (detect_sign expr1 env l) (detect_sign expr2 env l) l
;;


(** Fusionne deux environnements de signes, en conservant chaque signe possible pour chaque variable *)
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


(** Nie une condition (renvoie la condition inverse) *)
let neg_condition (expr1,comparator, expr2) = match comparator with 
  | Eq -> (expr1, Ne, expr2)
  | Ne -> (expr1, Eq, expr2)
  | Lt -> (expr1, Ge, expr2)
  | Ge -> (expr1, Lt, expr2)
  | Le -> (expr1, Gt, expr2)
  | Gt -> (expr1, Le, expr2)
;;


(** Renvoie true si et seulement si la condition donnée en paramètres a une chance d'être vraie. *)
let satisfaisable (expr1, comp, expr2) env l =
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
    | Eq -> deux_egaux (VAR_SIGN.elements (detect_sign expr1 env l)) (detect_sign expr2 env l)
    | Ne -> not (VAR_SIGN.equal (detect_sign expr1 env l) VAR_SIGN.(empty |> add Zero) && VAR_SIGN.equal (detect_sign expr2 env l) VAR_SIGN.(empty |> add Zero))
    | Lt -> lt (VAR_SIGN.elements (detect_sign expr1 env l)) (detect_sign expr2 env l)
    | Ge -> ge (VAR_SIGN.elements (detect_sign expr1 env l)) (detect_sign expr2 env l)
    | Le -> le (VAR_SIGN.elements (detect_sign expr1 env l)) (detect_sign expr2 env l)
    | Gt -> gt (VAR_SIGN.elements (detect_sign expr1 env l)) (detect_sign expr2 env l)
;;

(** Enorme bordel... Permet de mettre en évidence des contraintes sur une variable en considérant que la condition est vraie. *)
let  isoler_variable (expr1, comparator, expr2) var_name env l = 
  let operation_inverse operateur = match operateur with 
    | Add -> Sub
    | Sub -> Add
    | Mul -> Div
    | Div -> Mul
    | Mod -> failwith "Not Supposed to simplify mod"
  in let comparateur_negatif comparator = match comparator with 
       | Eq -> Eq 
       | Ne -> Ne
       | Le -> Ge
       | Lt -> Gt
       | Gt -> Lt
       | Ge -> Le
  (* Vérifie si la variable sur laquelle nous travaillons se trouve bien dans l'expression donnée en paramètre *)
  in let rec var_in_expr expr var_name = match expr with 
       | Num(n) -> false
       | Var(a) when a = var_name -> true
       | Var(a) -> false
       | Op(operateur, expr1, expr2) -> (var_in_expr expr1 var_name) || (var_in_expr expr2 var_name)
  (* Vérifie si l'expression passée en paramètre ne contient que la variable sur laquelle on travaille. *)
  in let variable_isolee expr var_name = match expr with 
       | Var(a) when a = var_name -> true
       | _ -> false
  in let is_processable expr1 expr2 var_name = 
       ((var_in_expr expr1 var_name)  || (var_in_expr expr2 var_name))
  (* Permet de s'assurer que la variable sur laquelle on travaille se trouve bien dans la partie gauche de la condition. 
  Transforme églament la partie droite de la condition en un set de signes. Pour que l'extraction de contraintes soit réalisable, 
  nous avons fait le choix de cette simplification*)
  in let preformat_condition (expr1, comparator, expr2) var_name = 
       if var_in_expr expr1 var_name then (expr1, comparator, (detect_sign expr2 env l))
       else if var_in_expr expr2 var_name then (expr2, (comparateur_negatif comparator), (detect_sign expr1 env l))
       else failwith "Unable to find variable in expression"
  (* Simplification de la tache. Sans cela c'est mission impossible. Transforme n'importe quel 
  triplet (expression, operateur de comparaison, set de signes) en une condition d'égalité (ou eventuellement d'inégalité). 
  Exemple : (expr, <, {-, 0}) devient (expr, =, {-}) *)
  in let simplify_comparator comparator signs = 
       let rec aux comparator l = 
         match (l, comparator) with 
           | ([], _) -> VAR_SIGN.empty

           | (Sign.Pos :: q, Gt) | (Sign.Pos :: q, Ge) -> (aux comparator q) |> VAR_SIGN.add(Pos)
           | (Sign.Pos :: q, Le) | (Sign.Pos :: q, Lt)-> (aux comparator q) |> VAR_SIGN.add(Neg) |> VAR_SIGN.add(Zero) |> VAR_SIGN.add(Pos)

           | (Sign.Zero :: q, Lt) -> (aux comparator q) |> VAR_SIGN.add(Neg)
           | (Sign.Zero :: q, Le) -> (aux comparator q) |> VAR_SIGN.add(Neg) |> VAR_SIGN.add(Zero)
           | (Sign.Zero :: q, Gt) -> (aux comparator q) |> VAR_SIGN.add(Pos)
           | (Sign.Zero :: q, Ge) -> (aux comparator q) |> VAR_SIGN.add(Zero) |> VAR_SIGN.add(Pos)

           | (Sign.Neg :: q, Lt) | (Sign.Neg :: q, Le) -> (aux comparator q) |> VAR_SIGN.add(Neg)
           | (Sign.Neg :: q, Ge) | (Sign.Neg :: q, Gt) -> (aux comparator q) |> VAR_SIGN.add(Neg) |> VAR_SIGN.add(Zero) |> VAR_SIGN.add(Pos)

           | (Error :: q, _) -> aux comparator q

           | (_, _) -> failwith "Une valeur incorrecte dans simplify_comparator"
       in match comparator with 
         | Eq | Ne -> (comparator, signs)
         | _ -> (Eq, aux comparator (VAR_SIGN.elements signs))
  (* Transforme une operation  pour qu'elle respecte le critère suivant : 
  Si la représentation Ocaml de l'opération est (operateur, sous-expression1, sous-expression2),
  alors la variable sur laquelle on travaille doit impérativement se trouver dans la sous-expression1. 
  En particulier, elle n'autorise pas certaines soustraction/division :
  Si l'opération est 3 - variable, elle est remplacée par (variable * (-1)) + 3 
  Si l'opération est 3/variable, elle est replacée par variable * (1/3) (passage à l'inverse conserve le signe) *) 
  in let reformat_expression expr signs var_name = match expr with
       | Op(Sub, sexpr1, sexpr2) -> if var_in_expr sexpr1 var_name then (expr, signs) else (Op(Add, Op(Mul, sexpr2, Num(-1)), sexpr1), signs)
       | Op(Div, sexpr1, sexpr2) -> if var_in_expr sexpr1 var_name then (expr, signs) else (Op(Mul, sexpr2, Op(Div, Num(1), sexpr1)), VAR_SIGN.remove Zero signs)
       | Op(op, sexpr1, sexpr2) -> if var_in_expr sexpr1 var_name then (expr, signs) else (Op(op, sexpr2, sexpr1), signs)
       | _ -> failwith "Autre chose qu'une operation dans reformat_expression"

  (* Fonction d'isolement de la variable du coté gauche de la condition *)
  in let rec isoler (expr1, comparator, signs) var_name =
       if variable_isolee expr1 var_name then (expr1, comparator, signs)
       else (
         match reformat_expression expr1 signs var_name with 
           | (Num(a), _) -> failwith "Erreur : expression innatendue"
           | (Var(a), _) -> failwith "Erreur : expression innatendue"
           | (Op(Mod, _, _), _) -> (Var(var_name), Eq, VAR_SIGN.(empty |> add Neg |> add Zero |> add Pos))
           | (Op(operator, sexpr1, sexpr2), nsigns) -> 
               let possible = detect_sign sexpr2 env l in 
                 isoler (sexpr1, comparator, (combine_possibilities (operation_inverse operator) nsigns possible l)) var_name
       )
  (* Extrait une contrainte sur une variable en fonction de la condition simplifiée.
  Compare les signes possibles si la condition est vraie et les signes que pouvait prendre la variable dans le reste du programme. 
  Ne retiens que les signes commus aux deux.*)
  in let extract_constraint comparator signs env var_name = 
       let rec aux signs bsigns = 
         match signs with 
           | [] -> VAR_SIGN.empty
           | h :: q when VAR_SIGN.mem h bsigns -> (aux q bsigns) |> VAR_SIGN.add h
           | h :: q -> aux q bsigns
       in match comparator with 
         | Eq -> aux (VAR_SIGN.elements signs) (ENV.find var_name env)
         | Ne -> aux (VAR_SIGN.elements (if VAR_SIGN.equal signs (VAR_SIGN.(empty |> add Zero)) then VAR_SIGN.(empty |> add Neg |> add Pos) else VAR_SIGN.(empty |> add Neg |> add Zero |> add Pos))) (ENV.find var_name env)
         | _ -> failwith "Please simplify condition"
  in let (pexpr1, pcomp, psigns) = preformat_condition (expr1, comparator, expr2) var_name in
  let (scomp, ssigns) = simplify_comparator pcomp psigns in
  let (_, fcomp, fsigns) = isoler (pexpr1, scomp, ssigns) var_name
  in extract_constraint fcomp fsigns env var_name
;;


(** Affiche un enviromment de signes comme demandé par le sujet. Exemple : 
{"a": [Neg Pos]; "b": [Zero Error]} affiche : 
a -+
b 0! *)
let print_env_sign env = 
  let get_keys map = 
    let rec interne bindings = match bindings with 
      | [] -> []
      | (k, v) :: q -> k :: interne q
    in interne (ENV.bindings map)
  in let rec af l = match l with 
       | [] -> printf "\n"
       | Sign.Neg :: q -> printf "-"; af q
       | Sign.Zero :: q  -> printf "0"; af q
       | Sign.Pos :: q -> printf "+"; af q
       | Sign.Error :: q -> printf "!"; af q
  in let rec pr l = match l with 
       | [] -> ()
       | h :: q -> printf "%s " h; af (VAR_SIGN.elements (ENV.find h env)); pr q
  in pr (get_keys env)


(** Renvoie un environnement dans lequel on a changé tous les signes possibles des variables présentes dans la condition.
Ces nouveaux signes sont donnés par la fonction `isoler_variable` *)
let sign_evaluate_condition (expr1, comparator, expr2) env_o l =
  let rec initialise_env condition env = 
    match condition with 
      | Num(a) -> env
      | Var(name) -> ENV.add name (isoler_variable (expr1, comparator, expr2) name env_o l) env
      | Op(operation, expr1, expr2) -> initialise_env expr2 (initialise_env (expr1) env)
  in ENV.union (fun key elm1 elm2 -> Some(elm2)) env_o (initialise_env expr2 (initialise_env expr1 ENV.empty)) 
;;

let print_first_division_by_zero () = if !first_division_by_0 = (-1) then
 print_string "safe\n"
 else (printf "divbyzero %d\n" (!first_division_by_0));;


(** Fonction principale pour évaluer le signe des variables d'un programme. *)
let check_sign prog =
  let rec interne prog env = match prog with 
       | [] -> env
       | (l, Read(name)) :: suite_prog -> interne suite_prog (ENV.add name VAR_SIGN.(empty |> add(Neg) |> add(Zero) |> add(Pos)) env)
       | (l, Set(name, expr)) :: suite_prog -> interne suite_prog (ENV.add name (detect_sign expr env l) env)
       | (l, If(cond, block1, block2)) :: suite_prog -> interne suite_prog (process_if cond block1 block2 env l)
       | (l, While(cond, block)) :: suite_prog -> interne suite_prog (process_while cond block env env l)
       | (l, Print(expr)) :: suite_prog -> interne suite_prog env
  (* Calcule, si possible, les contraintes sur la condition d'un IF en condidérant qu'elle est vraie.
  Propage ces contraintes au corps du IF. Fais de meme pour le bloc ELSE (en niant la condition) 
  et merge les deux environnements obtenus *)
  and process_if cond blockIF blockELSE env l = 
    let envIF = if (satisfaisable cond env l) then interne blockIF (sign_evaluate_condition cond env l) else ENV.empty
    in let envELSE = if (satisfaisable (neg_condition cond) env l) then interne blockELSE (sign_evaluate_condition (neg_condition cond) env l) else ENV.empty
    in merge_maps envIF envELSE
  (* Calcul de l'environnement de signes après l'execution d'un bloc WHILE. 
  Procède par un calcul de point-fixe. A la fin propage les contraintes de la négation de la condition d'arrêt. *)
  and process_while cond corp env env_o l =
    let propage_cond = sign_evaluate_condition cond env l in
    let propage_corp = interne corp propage_cond in
    let propage_join = ENV.union (fun key elm1 elm2 -> Some(elm2)) env propage_corp in 
      if ENV.equal (VAR_SIGN.equal) env propage_join then ENV.union (fun key elm1 elm2 -> Some(elm2)) propage_join (sign_evaluate_condition (neg_condition cond) env_o l)
      else process_while cond corp propage_join env_o l

  in print_env_sign (interne prog ENV.empty); print_first_division_by_zero ();;
