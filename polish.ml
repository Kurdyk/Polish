open Printf
open Types
open Read
open Print
open Eval
open Misc
open Simpl
open Vars
open Signs
(** Projet Polish -- Analyse statique d'un mini-langage impératif *)

(** Note : cet embryon de projet est pour l'instant en un seul fichier
    polish.ml. Il est recommandé d'architecturer ultérieurement votre
    projet en plusieurs fichiers source de tailles raisonnables *)


let usage () =
  print_string "Polish : analyse statique d'un mini-langage\n";
  print_string "	      usage: -option nom_fichier.p\nLes options sont :\n";
  print_string "-reprint : affiche le programme polish.\n";
  print_string "-eval : fait tourner le programme polish. Les READ du programme sont demandés dans le terminal.\n";
  print_string "-simpl : affiche le programme polish avec calculs simplifiés et propagation des constantes (et simplifications éventuelles de bloc.\n";
  print_string "-vars : affiche les variables du programme polish sur la première ligne et les varibales mal initialisées sur une seconde ligne.\n";
  print_string "-sign : affiche le signe attendu de chaque variable du programme polish après analyse statique.\n";;

let main () =
  match Sys.argv with
    | [|_;"-reprint";file|] -> print_polish (read_polish file)
    | [|_;"-eval";file|] -> eval_polish (read_polish file)
    | [|_;"-simpl";file|] -> print_polish (simpl_polish(read_polish file))
    | [|_;"-vars";file|] -> vars(read_polish file)
    | [|_; "-sign"; file|] -> check_sign(read_polish file)
    | _ -> usage ()

(* lancement de ce main *)
let () = main ()
