open Types
open Printf

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