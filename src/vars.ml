open Types
open Printf

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
    Eval.masquer_retour (VAR.map (fun name -> let () = printf "%s " name in name) env) 
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
