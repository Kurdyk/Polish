open Types
open Printf

(**La fonction d'analyse statique appelée par l'option -vars.
   Affiche sur la première ligne toutes les variables trouvées dans le fichier polish.
   Affiche sur le seconde ligne les variables pouvant être accédées avant d'être définie.
*)
let vars (p:program) =

  let fst_t triplet = 
    (*Renvoie le premier élément d'un triplet*)
    match triplet with
      | a, b, c -> a
  in 

  let snd_t triplet = 
    (*Renvoie le deuxième élément d'un triplet*)
    match triplet with
      | a, b, c -> b
  in 

  let trd_t triplet = 
    (*Renvoie le troisième élément d'un triplet*)
    match triplet with
      | a, b, c -> c
  in 


  let rec check_var names env =
    (*Permet de construite la liste des variables accédées avant définition*)
    match names with 
      | [] -> [], []
      | x::xs -> let couple = check_var xs env in
            if VAR.mem x env 
            then x::(fst couple), snd couple
            else x::(fst couple), x::(snd couple)
  in 

  let rec find_var_expr expr =
    (*Trouve toutes les variables dans une expression*)
    match expr with 
      | Var(name) -> [name]
      | Num(_) -> []
      | Op(op, expr1, expr2) -> List.append (find_var_expr expr1) (find_var_expr expr2)
  in

  let find_var_condi cond = 
    (*Trouve toutes les variables dans une condition*)
    match cond with
      | (expr1, comp, expr2) -> List.append (find_var_expr expr1) (find_var_expr expr2)

  in

  let print_set set = 
    (*Affiche un ensemble*)
    Eval.masquer_retour (VAR.map (fun name -> let () = printf "%s " name in name) set) 
  in

  let rec interne (p:program) env_tot env_bad_access env_well_declared =
    (*Fonction principale : parcours le programme et construit des ensembles pour les variables bien et mal accédé*)
    match p with
      | [] -> env_tot, env_bad_access, env_well_declared
      | (_, instr)::xs -> match instr with
        (*Ne peut qu'ajouter une variable bien déclarée ou la redéclarer*)
        | Read(name) -> interne xs (VAR.add name env_tot) env_bad_access (VAR.add name env_well_declared)
        (*Ajoute la variable du SET à celles bien déclarées et vérifie l'expression utilisée*)
        | Set(name, expr) -> let couple = check_var (find_var_expr expr) env_well_declared
            in interne 
                 xs 
                 (VAR.union (VAR.add name env_tot) (VAR.of_list (fst couple)))
                 (VAR.union env_bad_access (VAR.of_list (snd couple))) 
                 (VAR.add name env_well_declared)
        (*Vérifie l'expression a PRINT*)
        | Print(expr) -> let couple = check_var (find_var_expr expr) env_well_declared
            in interne 
                 xs 
                 (VAR.union env_tot (VAR.of_list (fst couple)))
                 (VAR.union env_bad_access (VAR.of_list (snd couple)))
                 env_well_declared
        (*Ajouter les variables trouvées et mal déclarées dans les deux blocs aux ensembles, intersecte les variables bien décalrées*)
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
        (*Ajouter les variables trouvées et mal déclarées dans le bloc aux ensembles*)
        | While(cond, block) -> let couple = check_var (find_var_condi cond) env_well_declared
            in let b = interne block VAR.empty VAR.empty env_well_declared
            in interne 
                 xs
                 (VAR.union (fst_t b) (VAR.union env_tot (VAR.of_list (fst couple))))
                 (VAR.union (snd_t b) (VAR.union env_bad_access (VAR.of_list (snd couple))))
                 env_well_declared


  in let env_triplet = interne p VAR.empty VAR.empty VAR.empty
  in print_set (fst_t env_triplet); printf "\n"; print_set (snd_t env_triplet); printf "\n"
;;
