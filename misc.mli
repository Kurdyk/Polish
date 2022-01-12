open Types

val exclusion_names : string list

val var_exists : ENV.key -> 'a ENV.t -> bool

val get_variable : ENV.key -> 'a ENV.t -> int -> 'a 

val check_variable_name : string -> int -> unit

val set_variable : ENV.key -> 'a -> 'a ENV.t -> int -> 'a ENV.t