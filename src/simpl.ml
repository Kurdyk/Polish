open Types

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
                | l -> let expr_final = simpl_with_const expr_s env_const in 
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