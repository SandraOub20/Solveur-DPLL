(* MP1 2024/2025 - dpll.ml *)

open List

(* fonctions utilitaires *)
(* ----------------------------------------------------------- *)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien y ajouter.
   Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   afficher le résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
     let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
     List.iter (fun i -> print_int i; print_string " ") modele2;
     print_string "0\n"

(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [
  [1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];
  [19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];
  [-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];
  [-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];
  [-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];
  [-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];
  [-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];
  [-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];
  [-14;-17];[-15;-18]]

(* ----------------------------------------------------------- *)




(* simplifie : int -> int list list -> int list option list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral l à vrai *)
 
   (*la fonction simplifie utilise une fonction auxiliaire qui va représenter le paramétre filter de la fonction filter_map qui va revoyer None si la liste contient l sinon va revoyer la liste en supprimant les occurences de -l dans cette liste  en utilisant la fonction List.filter *)


  let simplifie l clauses =
      let aux clause = if List.mem l clause then None 
        else Some ( List.filter (fun x -> x <> -l) clause )  in 
          rev (filter_map aux clauses) ;;


            

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
  (* la clause vide n'est jamais satisfiable *)
  if mem [] clauses then None else
  (* branchement *) 
  let l = hd (hd clauses) in
  let branche = solveur_split (simplifie l clauses) (l::interpretation) in
  match branche with
  | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
  | _    -> branche


(* tests *)
(* let () = print_modele (solveur_split systeme []) *)
(* let () = print_modele (solveur_split coloriage []) *)

(* solveur dpll récursif *)
(* ----------------------------------------------------------- *)

(* pur : int list list -> int option
    - si `clauses' contient au moins un littéral pur, retourne le premier  littéral pur (c-a-d Some littéral) ;
    - sinon elle retourne None c-a-d rien *)

(*
* La fonction prend en paramétres une liste de clauses
* On commence par aplatir la liste de liste pour avoir une simple liste de littéraux. 

* Ensuite , on utilise une fonction auxiliaire : int list -> int option , elle parcourt la liste de littéraux si elle trouve un littéral l et sa négation -l dans la liste  elle continue son parcours sur cette liste privée de toutes les occurrences de l et de -l. Sinon elle renvoie (Some l)
* Enfin on appelle cette fonction auxiliaire sur notre liste de clauses applatie .
*)

(*Nous avons décidé de transformer le type de retour en int option pour simplifier l'implémentation du solveur_dpll_rec *)

let  pur clauses =
    let tout_litteraux = List.flatten clauses in 
    let rec aux liste_literaux = 
      match liste_literaux with 
      | [] -> None (*raise (Failure "pas de littéral pur")*)
      | l::reste -> 
        if (List.mem (-l) reste) then aux (filter (fun x ->  x <> x && x <> -l ) reste) else Some (l) 
        in aux tout_litteraux 

        
(* unitaire : int list list -> int option
    - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire  (c-a-d Some l);
    - sinon, retourne None *)
(*Nous avons décidé de transformer le type de retour en int option pour simplifier l'implémentation du solveur_dpll_rec *)
(*

* La fonction prend en paramétres une liste de clauses
* La fonction parcours la liste de clauses et vérifie d'abord que notre liste de clauses n'est pas vide sinon elle renvoie None. 
* Ensuite pour chaque clause dans clauses la fonction vérifie si elle est un singleton [l] si c'est le cas elle renvoie (Some l)  sinon elle continue son parcours sur le reste des clauses (récursivement)
*)


    let rec unitaire clauses =
      (* à compléter *)
      match  clauses with
      [] ->  None(*raise Not_found*)
      | [l] :: _ -> Some l 
      | _ :: l' -> unitaire l'

(* solveur_dpll_rec : int list list -> int list -> int list option *)
(*
* La fonction prends une liste de clauses et une interpretation  ( liste d'entiers initialement vide) . 
* Si l'ensemble de clauses est vide, alors la formule est satisfiable et on retourne l'interprétation courante.
* Si l'ensemble de clauses contient une clause vide ça veut dire  que la formule est insatisfiable avec l'interpretation courante donc on retourne rien (None)
* La fonction recherche ensuite une clause unitaire (qui contient un seul littéral l_unitaire), si elle en trouve elle simplifie les clauses en appelant simplifie avec ce l_unitaire et l'ensemble des clauses puis appelle récursivement solveur_dpll_rec sur cet ensemble de clauses simplifiées et elle ajoute l_unitaire à l'interpretation.

* si aucune clause unitaire n'est trouvé la fonction cherche un littéral pur en appelant la fonction pur sur l'ensemble de clauses , si elle trouve un littéral pur l_pur elle simplifie les clauses en appelant simplifie avec ce l_pur et l'ensemble des clauses puis appelle récursivement solveur_dpll_rec sur cet ensemble de clauses simplifiées et  l_pur  rejouté à l'interpretation.

* Si aucun littéral pur ni unitaire n'est trouvé , on fait un split c'est a dire on choisit un littéral l et on applique solveur_dpll_rec sur l et l'ensembles de clauses. Si c'est pas satisfiable avec l on applique solveur_dpll_rec sur sa négation.

*)

let rec solveur_dpll_rec clauses interpretation = 
  if  clauses = [] then Some interpretation
  else if List.exists (fun x -> x=[]) clauses then None 
  else
    match unitaire clauses with 
    | Some l_unitaire -> 
      let clauses_simplifiees = simplifie l_unitaire clauses in 
      solveur_dpll_rec  clauses_simplifiees (l_unitaire::interpretation)
    | None -> match  pur clauses with 
            | Some l_pur -> let clauses_simplifiees = simplifie l_pur clauses in 
                            solveur_dpll_rec clauses_simplifiees (l_pur :: interpretation)
            |None  -> 
              (*Nous avons décidé de ne pas appeler solveur_split mais d'utiliser une partie de son code réadaptée à solveur_dpll_rec car la compléxité en temps est meilleure  *)
              let l = List.hd (List.hd clauses) in (*on prend toujour le premier littéral de la premiére clause *)
              let branche = solveur_dpll_rec (simplifie l clauses) (l::interpretation) in (*on applique solveur_dpll_rec en simplifiant les clauses par l (premiére branche ) *)
              match branche with
                | None -> solveur_dpll_rec (simplifie (-l) clauses) ((-l)::interpretation) (* si c'est pas satisfiable avec l on réapplique  solveur_dpll_rec en simplifiant avec -l *)
                | _    -> branche  (*si l satisfait la proposition on renvoie l'interpretation (branche)*)    

 
(* tests *)
(* ----------------------------------------------------------- *)
(*let () = print_modele (solveur_dpll_rec systeme []) 
let () = print_modele (solveur_dpll_rec coloriage []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  print_modele (solveur_dpll_rec clauses [])

 
  



     

