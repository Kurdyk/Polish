open Types
open Printf

let exclusion_names = ["READ"; "PRINT"; "IF"; "ELSE"; "WHILE"; "COMMENT";
                       ":="; "+"; "-"; "*"; "/"; "%"; 
                       "="; "<>"; "<"; "<="; ">"; ">="];;

let var_exists name env = ENV.mem name env;;

let get_variable name env l = if ENV.mem name env then ENV.find name env else begin printf "Exception: Line %d, variable %s referenced before assignement" l name; exit 1; end;;

let check_variable_name name l = if List.mem name exclusion_names then begin printf "Exception: Line %d, cannot name variable %s: forbidden name (reserved keyword)\n" l name; exit 1; end else if Read.is_numeric (String.make 1 (String.get name 0)) then begin printf "Exception: Line %d, cannot name variable %s: invalid name\n" l name; exit 1; end;;

let set_variable name value env l = check_variable_name name l; ENV.add name value env;;