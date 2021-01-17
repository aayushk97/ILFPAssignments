(*Assignment 2, 25th October, 2020MCS2444, Aayush Kumar Singh*)

type prop = T
           |F
           | Letter of string
           | Not of prop
           | And of prop * prop
           | Or of prop * prop
           | Impl of prop * prop
           | Iff of prop * prop
           ;;


let rec nnfpos p = match p with
              T -> T
              | F -> F
              | Letter s -> p
              | Not p1 -> nnfneg p1
              | And (p1, p2) -> And (nnfpos p1, nnfpos p2)
              | Or (p1, p2) -> Or(nnfpos p1, nnfpos p2)
              | Impl (p1, p2) -> Or(nnfneg p1, nnfpos p2)
              | Iff (p1, p2) -> Or(And(nnfneg p1, nnfpos p2), And(nnfpos p1, nnfneg p2))
      and
        nnfneg p = match p with
              T -> F
             | F -> T
             | Letter s -> Not(Letter s)
             | Not p1 -> nnfpos p1
             | And (p1, p2) -> Or(nnfneg p1, nnfneg p2)
             | Or (p1, p2) -> And(nnfneg p1, nnfneg p2)
             | Impl(p1,p2) -> And(nnfpos p1, nnfneg p2)
             | Iff(p1, p2) -> And(Or(nnfpos p1, nnfpos p2),Or(nnfneg p1, nnfneg p2))
        ;;
(*1.vars: prop -> string set, which returns the set of propositional letters that appear in a proposition.*)
(* We check while union if the element is present in other list then we include else exclude *)
(* Here we consider s = size of prop and n = no of unique letters in prop *)

(*Time Complexity of vars p : O(s*(n^2))
 * Space Complexity: O(s)*)

let rec union l1 l2 = match l1 with 
                      [] -> l2
                     | x::xs -> if(List.mem x l2) then union xs l2 else x::(union xs l2);;


let rec vars p = match p with
                T | F -> []
               |Letter s -> [s]
               |Not(p1) ->  vars p1
               | And(p1, p2) -> union (vars p1) (vars p2)
               | Or(p1, p2) -> union (vars p1) (vars p2)
               | Impl(p1, p2) -> union (vars p1) (vars p2)
               | Iff(p1, p2) -> union (vars p1) (vars p2)
;;

(*2. cnf: prop -> prop set set, which converts a proposition into conjunctive normal form (POS) as a set of clauses, each of which is a set of literals (a special subset of prop, comprising only letters and negations of letters).
*)

(* To distribute Or over And for converting of cnf to dnf *)
(*Time complexity: O(no of nodes * time to append at each node) = O(s*(2^l))
 * Space Complexity: O(2^n) *)

let rec distributeOr p1 p2 = match (p1, p2) with
                           (p1, And(p2, p3)) -> And( distributeOr p1 p2, distributeOr p1 p3)
               |(And(p1, p2), p3) -> And( distributeOr p1 p3, distributeOr p2 p3)
               |(p1, p2) -> Or(p1, p2)
;;



let rec nnfTocnf p =
       let q = nnfpos p in
       match q with
         T -> T
       | F -> F
       | Letter s -> q
       | Not p1 -> q
       | And(p1, p2) -> And(nnfTocnf p1, nnfTocnf p2)
       | Or(p1, p2) -> distributeOr (nnfTocnf p1) (nnfTocnf p2)
       | Impl(p1, p2) -> q
       | Iff(p1, p2) -> q

;;


(* To convert the cnf form to appropriate set form where each maxterm is seperated by semicolon matching the dnf in pairs*)
let rec fixCnf m =
  match m with
  Letter s -> [[Letter s]]
  | Or(F,F) -> [[]]
  |  Or(_, T ) | Or(T, _) -> []
  | Or(Letter s, F) | Or(F, Letter s) -> [[Letter s]]
  |Or(Not(Letter s),F) | Or(F, Not(Letter s)) -> [[Not(Letter s)]]
  | Or(p1, F) | Or(F,p1) -> fixCnf p1
  | Or(Not(Letter s), Not(Letter b)) -> [[Not(Letter s); Not(Letter b)]]
  | Or(Not(Letter s), Letter b) -> [[Not(Letter s); Letter b]]
  | Or(Letter s, Not(Letter b)) -> [[Letter s; Not(Letter b)]]
  | Or(Letter s, Letter b) -> [[Letter s ; Letter b ]]
  |And(Letter s, Not(Letter b)) -> [[Letter s]]@[[Not(Letter b)]]
  |And(Not(Letter s), Letter b) -> [[Not(Letter s)]]@[[Letter b]]
  |And(Not(Letter s), Not(Letter b)) -> [[Not(Letter s)]]@[[Not(Letter b)]]
  |And(Letter s, Letter b) -> [[Letter s]]@[[Letter b]]
  |And(p1, F) | And(F, p1) ->[[]]
  |And(p1, T) | Or(T,p1) -> fixCnf p1
  |And(p1, Letter s) -> (fixCnf p1)@[[Letter s]]
  |And(Letter s, p1) -> [[Letter s]]@(fixCnf p1)
  |And(p1, Not(Letter s)) -> (fixCnf p1)@[[Not(Letter s)]]
  |And(Not(Letter s), p1) -> [[Not(Letter s)]]@(fixCnf p1)
  |And(p1, p2) -> fixCnf p1@ fixCnf p2
  | Or(Letter s, p1) -> (let n = fixCnf p1 in
                         match n with
                           [] -> []
                         |[[]] -> [[]]
                         | x::xs -> [Letter s::x] )
  | Or(Not(Letter s), p1) -> (let n = fixCnf p1 in
                              match n with
                                [] -> []
                              |[[]] -> [[]]
                              | x::xs -> [Not(Letter s)::x] )
  |Or(p1, p2) -> (let m = fixCnf p1 and n = fixCnf p2 in
                   match m, n with
                     [],[] -> []
                   |[[]],_ -> n
                   | x::xs, y::ys -> [x@y] )
  |Impl(p1, p2) -> fixCnf m
  | Iff(p1, p2) -> fixCnf m
  | T -> []
  | F -> [[]]
  | Not(p1) -> fixCnf m
;;

let cnf p = fixCnf (nnfTocnf p);;

(* 3. dnf: prop -> prop set set,  which converts a proposition into disjunctive normal form (SOP) as a set of terms, each of which is a set of literals.*)

(*To convert nnf to dnf by distributing And over Or *)
(*Time complexity: O(n*2^l)
 * Space Complexity: O(2^l)
 * *)
let rec distributeAnd p1 p2 = match(p1, p2) with
                        (p1, Or(p2, p3)) -> Or( distributeAnd p1 p2, distributeAnd p1 p3)
       | (Or(p1, p2), p3) -> Or( distributeAnd p1 p2, distributeAnd p1 p3)
       | ( p1, p2 ) -> And(p1, p2)
;;

let rec nnfTodnf p =
         let q = nnfpos p in
           match q with
         T -> T
        | F -> F
        | Letter s -> q
        | Not p1 -> q
        | Or(p1, p2) -> Or(nnfTodnf p1, nnfTodnf p2)
        | And(p1, Or(p2, p3)) -> Or(nnfTodnf (And(nnfTodnf p1, nnfTodnf p2)), nnfTodnf(And(nnfTodnf p1,nnfTodnf p3)))
        | And(Or(p1,p2), p3) -> Or( nnfTodnf(And(nnfTodnf p1, nnfTodnf p3)), nnfTodnf(And(nnfTodnf p1, nnfTodnf p2)))
        | And(p1, p2) -> And(nnfTodnf p1, nnfTodnf p2)
        | Impl(p1, p2) -> q
        | Iff(p1, p2) -> q;;
;;
(*Convert dnf generated to approriate list form with each minterm sepearted by semicoln by match input cnf in pairs *)
let rec fixDnf m =
  match m with
  |Letter s -> [[Letter s]]
  | And(T,T) -> [[]]
  |  And(_, F ) | And(F, _) -> []
  | And(Letter s, T) | And(T, Letter s) -> [[Letter s]]
  |And(Not(Letter s),T) | And(T, Not(Letter s)) -> [[Not(Letter s)]]
  | And(p1, T) | And(T,p1) -> fixDnf p1
  | And(Not(Letter s), Not(Letter b)) -> [[Not(Letter s); Not(Letter b)]]
  | And(Not(Letter s), Letter b) -> [[Not(Letter s); Letter b]]
  | And(Letter s, Not(Letter b)) -> [[Letter s; Not(Letter b)]]
  |And(Letter s, Letter b) -> [[Letter s ; Letter b ]]
  |Or(Letter s, Not(Letter b)) -> [[Letter s]]@[[Not(Letter b)]]
  |Or(Not(Letter s), Letter b) -> [[Not(Letter s)]]@[[Letter b]]
  |Or(Not(Letter s), Not(Letter b)) -> [[Not(Letter s)]]@[[Not(Letter b)]]
  |Or(Letter s, Letter b) -> [[Letter s]]@[[Letter b]]
  |Or(p1, T) | Or(T, p1) -> [[]]
  |Or(p1, F) | Or(F,p1) -> fixDnf p1
  |Or(p1, Letter s) -> (fixDnf p1)@[[Letter s]]
  |Or(Letter s, p1) -> [[Letter s]]@(fixDnf p1)
  |Or(p1, Not(Letter s)) -> (fixDnf p1)@[[Not(Letter s)]]
  |Or(Not(Letter s), p1) -> [[Not(Letter s)]]@(fixDnf p1)
  |Or(p1, p2) -> fixDnf p1@ fixDnf p2
  | And(Letter s, p1) -> (let n = fixDnf p1 in
                          match n with
                            [] -> []
                          |[[]] -> [[]]
                          | x::xs -> [Letter s::x] )
  | And(Not(Letter s), p1) -> (let n = fixDnf p1 in
                               match n with
                                 [] -> []
                               |[[]] -> [[]]
                               | x::xs -> [Not(Letter s)::x] )
  | And(p1, p2) -> (let m = fixDnf p1 and n = fixDnf p2 in
                                  match m,n with
                                  [],[] -> []
                                |[[]],_-> n
                                |x::xs, y::ys -> [x@y])
  |Impl(p1, p2) -> fixDnf m
  | Iff(p1, p2) -> fixDnf m
  | T -> [[]]
  | F -> []
  | Not(p1) -> fixDnf m
;;

let dnf p = fixDnf(nnfTodnf p);;
 

(*6. isTautology: prop -> bool, which checks if a proposition is a tautology.*)
(* A proposition is tautology if the set returned by cnf is empty or each sublist has an element and it's inverse*)
(*Time Complexity: O(l*2^l+n*2^n)
 * Space Complexity: O(2^l)
 *)

let rec compExist l = match l with
    [] -> false
  | x::xs -> match x with
      Not(k) -> if(List.mem k l) then true else false
    | k -> if(List.mem (Not(k)) l) then true else false;;


let rec taut n = match n with
    [[]] -> true
  |[]::xs -> taut xs
  | [] -> true
  |x ::xs -> compExist x && taut xs   
;;

let isTautology p =let n = cnf p in
  (match n with
     [] -> true
   |[[]] -> false
   | _ -> taut n)
;;

(*7. isContradiction: prop -> bool, which checks if a proposition is a tautology.*)
(* A proposition is a contradiction if its dnf is empty or each sublist has an element and it's inverse*)
(*Time Complexity: O((l^2)*(2^l))
 * Space Complexity: O(2^l)
 *)

let rec cont n = match n with
    [[]] -> true
  |[]::xs -> cont xs
  | [] -> true            
  |x ::xs -> compExist x && cont xs 
;;

let isContradiction p =let n = dnf p in
  (match n with
     [] -> false
   |[[]] -> true
   | _ -> cont n);;

(*1. isSatisfiable: prop -> bool, which checks if a proposition is satisfiable*)
(* Since, tautology + contingency = satisfiable so we negate the output of isContradiction*)
(*Time Complexity = Time Complexity of isContradiction *)
(*Space Complexity = Space Complexity of isContradiction *)

let isSatisfiable p = not(isContradiction p);;

(*3. isFalsifiable: prop -> bool, which checks if a proposition is satisfiable*)
(* Since, contingeny + contradiction = falsifiable set so we contradict the output of tautology*)
(*Time Complexity = Time Complexity of isTautology *)
(*Space Complexity = Space Complexity of isFalsifiable *)

let isFalsifiable p = not(isTautology p);;

(*8. isEquivalent: prop -> prop -> bool, which checks if two propositions are logically equivalent.*)
(*Two propositions p and q are logically equivalent if p <-> q is a tautology*)
(* Time Complexity= Time Complexity of isTautology *)
(*Space Complexity = Space Complexity of isTautology*)

let isEquivalent p1 p2 = isTautology(Impl(p1,p2))&&isTautology(Impl(p2,p1));;


(*9. entails: prop set -> prop -> bool, which checks if a given proposition is a logical consequence of a given set of propositions.*)
(*We check if each proposition in proposition set implies the given proposition*)
(*Time Complexity = O(k*TC of isTautology) where k is size of prop set
 * Space Complexity = O(k + SC of isTautology
 *)

let rec entails ps p = match ps with
                  [] -> true
                 | x::xs -> isTautology(Impl(x,p))&& entails xs p
                ;;


(* 2. satisfier: prop -> valuation, which returns a satisfying truth assignment if it exists. *)
(* We output the first set of non empty literals of dnf and set them appropriately to make the proposition satisfiable. Since, in dnf form atleast one min term has to be true for the entire prop to be true*)
(*TC = O((n*2^l)+l) where l is no of unique letters *)
(*SC = O(2^l)*)
let rec makeValuation l = match l with
                [] -> []
                 |x::xs ->( match x with
                 Not(k) -> (k, false)::makeValuation xs
                 | k-> (k, true)::makeValuation xs
                )
;;


let rec valuSatis m = match m with 
                   [] -> []
                  | x::xs -> if(x=[]) then valuSatis xs else makeValuation x;;


let satisfier p = let m = dnf p in valuSatis m;;

(*4. falsifier: prop -> valuation, which returns a falsifying truth assignment if it exists.*)
(* Instead of setting appropriate values in cnf terms here we set the appropraite value of maxterm to make entire prop false. We choose the first set and assign them values so that they are false*)
(*TC = O((n*2^l) + l) 
 * SC = O(2^l)
 *)

let rec makeValuationf l = match l with
                [] -> []
                 |x::xs ->( match x with
                 Not(k) -> (k, true)::makeValuationf xs
                 | k-> (k, false)::makeValuationf xs
                )
;;

let rec valuSatisf m = match m with
                   [] -> []
                  | x::xs -> if(x=[]) then valuSatisf xs else makeValuationf x;;




let falsifier p = let n = cnf p in valuSatisf n;;


(*5. models: prop -> valuation set, which returns the set of ``all valuations'' that satisfy a given prop. The models of set are formed by forming valuation using cnf terms and using allValuationSet to take power set of this valuation set so we get all valuations and then exclude the empty set of power set by using List.tl function *)
(* TC = O(2^(n*2^l))
 * SC = O(2^(2^l))
 *) 
let rec makeModelSet m = match m with
    [] -> []
  | x::xs -> if(x=[]) then makeModelSet xs else (makeValuation x)::(makeModelSet xs);;

let rec allValuationSet = function
  | [] -> [[]]
  | x :: xs ->
      let rest = allValuationSet xs in
      rest @ List.map (fun ss -> x @ ss) rest
;;

let models p = (let n = dnf p in List.tl (allValuationSet (makeModelSet n)));;

(*Tests:
 * let p1 = Or(Letter "p", Not(And(Letter "p", Letter "q")));;
let p2 = And(Impl(Letter "p", Letter "q"),Impl(Letter "q", Letter "r"));;
*)
