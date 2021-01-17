(*SUBMITTED BY AAYUSH KUMAR SINGH 2020MCS2444*)

type variable = string;;

type symbol = (string * int);;

type term = V of variable | Node of symbol*(term list);;

(*1. Given a signature consisting of symbols with their arities (>= 0) in any suitable form -- either
 *  as a list of (symbol, arity) pairs, or as a function from strings to non-negative integer 
 *  arities, write a function check_sig that checks whether the signature is a valid signature 
*  (no repeated symbols, arities are non-negative etc.)*)

let rec member m signature = match signature with
    [] -> false
  |(x,y)::xs -> if m = x then true else member m xs
;;

let rec nonRepeated signature = match signature with
    [] -> true
  |(x,y)::xs -> if member x xs then false else nonRepeated xs
;;

let rec nonNegative signature = match signature with
    [] -> true
  |(x,y)::xs -> if y < 0 then false else nonNegative xs
;;

let check_sig signature = nonRepeated signature && nonNegative signature;;

(*2. Given a valid signature (checked using check_sig), define a function wfterm that checks 
 * that a given preterm is well-formed according to the signature, i.e., every node labelled 
 * by a symbol has exactly as many subterms as specified by the arity.*)

(* example input : wfterm (Node (("g",2),[V "X";Node(("h",2),[Node(("f",1),[V "X"]);V "Y"])])) ;; *)

let rec check_term y signature = match y with
    []-> true
  |x::xs -> check_wellformed x signature && check_term xs signature
and
  check_wellformed term signature = match term with
    Node((x,u),y) -> if  u = List.length y && List.mem (x,u) signature
      then check_term y signature
      else false
  | V x -> true
;;

let wfterm term = check_wellformed term;;

(* 3. Define functions ht, size and vars that given a well-formed term, return its height, the 
 * number of nodes in it, and the set of variables appearing in it respectively.  Use map, 
 * foldl and other such functions as far as possible wherever you use lists. 
*)
  
  (*Size *) 
let rec size_t term = match term with
    [] -> 0
  |y::ys -> size y + size_t ys
and
  size term = match term with
    Node((x,u),y) -> 1 + size_t y
  |V x -> 1
;;
(*Height*)
let rec ht_t term = match term with
    [] -> 0
  | x::xs -> max (ht x) (ht_t xs)
and
  ht term = match term with
    Node((x,0),y) -> 0
  |Node((x,u),y) -> 1 + ht_t y
  |V x -> 0
;;

(*Vars*)
let rec union l1 l2 = match l2 with
    [] -> l1
  | x::xs -> if List.mem x l1 then union l1 xs else x::(union l1 xs)
;;
let rec vars_t term = match term with
    [] -> []
  |x::xs -> union (vars x) (vars_t xs)
and
  vars term = match term with
    Node(x,y) -> vars_t y
  |V x -> [x]
;;

(*4. Define a suitable representation for substitutions. *)
type substitution = (string * term ) list;;

(*5. Define the function subst that given a term t and a substitution s, applies the (Unique Homomorphic Extension of) s to t. Ensure that subst is efficiently implemented. *)

let rec findsub m s = match s with
    [] -> V m
  | (x,v)::xs -> if m = x then v else findsub m xs;;

let rec substitution_t y s = match y with
    [] -> []
  |x::xs -> (substitution x s)::(substitution_t xs s)
and
  substitution t s = match t with
  | V x -> findsub x s   (*find and subst x in s*)
  |Node((x,u),y) -> Node((x,u),substitution_t y s);;

let subst t s = substitution t s;;


(*6.Come up with an efficient representation of composition of substitutions. *)
type composition = substitution list;;

(*7. Define the function mgu that given two terms t1 and t2, returns their most general unifier, if it exists and otherwise raises an exception NOT_UNIFIABLE.*)
(*Exception NOT_UNIFIABLE*)
exception NOT_UNIFIABLE;;


(*performs occurs check that is used to know if a variable occurs inside a term*)
let rec occurs_check_t x u = match u with
    V y -> x=y
  |Node((a,b),c) -> occurs_check x c
and
  occurs_check x w = match w with
    [] -> false
  |u::us -> occurs_check_t x u && occurs_check x us
;;

(*function compose_subst is used to perform composition of substitution*)
let rec compMember m l = match l with
    [] -> false
  |(u,V v)::us -> if(m = v) then true else compMember m us;;

let rec compRepl (u,v) l = match l with 
    [] -> []
  |(x,V y)::xs -> if  y = u then (x,V v)::(compRepl (u,v) xs) else (x, V y)::(compRepl (u,v)  xs)
;;
let rec compose l1 l2 l3= match l2 with
    []-> l1@l3
  |(u, V v)::xs ->if compMember u l1 then compose (compRepl (u,v) l1) xs l3 else compose l1 xs l3
;;

let rec compose_subst l1 l2 = compose l1 l2 l2;;


(*MGU function that return appropriate substitution given 2 terms*)
(*function to apply substitution*)
let rec apply_subst l t = match l with 
    [] -> t
  |x::xs -> (apply_subst xs (subst t [x]))
;; 

(*function to find MGU of 2 terms*)
let rec mgu_t term1 term2 l3= match (term1, term2) with
    ([], []) -> l3
  |(x::xs, y::ys) -> mgu_t xs ys (mostGenU (apply_subst l3 x) (apply_subst l3 y) l3)
and
  mostGenU term1 term2 l3 = match (term1, term2) with 
  |  (V x, V y) -> if x = y then []@l3 else mostGenU (subst term1 [(x, V y)]) term2 (compose_subst l3 [(x, V y)])
  |(V x, Node((u, 0),[])) -> mostGenU (subst term1 [(x, Node((u,0),[]))]) term2 (l3@[(x, Node((u,0),[]))])
  |(Node((u,0),[]), V x)->  mostGenU term1 (subst term2 [(x, Node((u,0),[]))] ) (l3@[(x, Node((u,0),[]))])(*Map variable to constant*)
  |(V x, Node((u,v),w)) -> if occurs_check x w  (*If variable x appears in symbol we raise exception *)
      then
        raise NOT_UNIFIABLE
      else mostGenU (subst term1 [(x, Node((u,v),w))] ) term2 (l3@[(x, Node((u,v),w))]) 
        
  | (Node((u,v),w), V x) -> if occurs_check x w  (*If variable x appears in symbol we raise exception *)
      then
        raise NOT_UNIFIABLE
      else mostGenU term1 (subst term2 [(x, Node((u,v),w))]) (l3@[(x, Node((u,v),w))])
        
  |(Node((u,0),[]), Node((v,0),[])) -> if u = v then ([]@l3) else raise NOT_UNIFIABLE (*If different constants they cant be unified else we return identity*)
  |(Node((u,0),[]),y) | (y, Node((u,0),[]))-> raise NOT_UNIFIABLE (*As constant at roots are different*)
  |(Node((u,v),y), Node((w,x),z)) -> if u = w && v = x then mgu_t y z l3 else raise NOT_UNIFIABLE

let mgu term1 term2 = mostGenU term1 term2 [];;

