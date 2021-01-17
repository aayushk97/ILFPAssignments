(*ASSIGNMENT 3*)
(*Submitted By: Aayush Kumar Singh*)


(* Given: *)
type atom = Letter of string;;

(* The head is a positive atom, i.e, a propositional Letter *)
type head = atom;;

(*A body is a sequence of (1 or more) positive atoms, i.e, propositional letters.*)
type body = atom list;;

(*A goal is a sequence of positive atomic formulas.*)
type goal = atom list;;

(* A clause can either be a fact or a rule. *)
type clause = Fact of head | Rule of head * body;;

(* A program is a sequence of clauses. *)
type program = clause list;;

(* Given test program is represented as: 
let program =  [Rule(Letter "A",[Letter "B"; Letter "C"]);
                Rule(Letter "A",[Letter "D"]);
                Fact(Letter "B");
                Rule(Letter "C",[Letter "E"; Letter "F"]);
                Rule(Letter "C",[Letter "G"]);
                Rule(Letter "D",[Letter "E"; Letter "G"]);
                Fact(Letter "E");
                Rule(Letter "G",[Letter "H"; Letter "B"]);
                Fact(Letter "H")];;

A test goal is represented as:
let goal = [Letter "A"; Letter "B"; Letter "C"; Letter "D"];;
*)

(*These below will replace the goal term by body of rule or a fact*)

let rec union l1 l2 = match l1 with
    [] -> l2
  | x::xs ->
      if List.mem x l2 then
        union xs l2
      else
        x:: (union xs l2)
;;
 
 
 
let rec findf x goal = match goal with
    [] -> []
  |z::zs -> if (x = z) then findf x zs else (z::findf x zs)
;;
 
let rec findR u v goal = match goal with
    [] -> []
  |y::ys -> if (u = y) then (findR u v (union v ys)) else (y::findR u v ys)
;;
 
let rec replace clauseUsed goal term = match term with
    Fact(x) -> findf x goal
  |Rule(u,v) -> findR u v goal
;;
 
(*Finding in a program the one which matches the given literal*)
let find literal clause = match clause with
  |Fact(x) -> if(x = literal) then true else false
  |Rule(x,y) -> if(x = literal) then true else false
;;
 
let rec clauseex program x clauseUsed goals= match program with
    [] -> clauseUsed
  |p::ps -> if(find x p && not(List.mem p clauseUsed)) then p::clauseUsed else clauseex ps x clauseUsed goals
 
(*Function to find the clause which will be used for next resolution*) 
let rec programex program x clauseUsed goals= match program with
    [] -> goals
  |p::ps -> if(find x p && not(List.mem p clauseUsed)) then replace (p::clauseUsed) goals p else programex ps x clauseUsed goals
 
(*To check if 2 lists are equal *)  
let rec subset l1 l2 = match l1 with 
    [] -> true
  |x::xs -> if( List.mem x l2) then subset xs l2 else false;; 
 
let equal l1 l2 = subset l1 l2 && subset l2 l1;;
 

(*DFS Horn clause resolution engine*) 
let rec goalex program clauseListTwo goals =
  let clauseList = []  
  in recGoal program goals clauseList clauseListTwo
and 
  recGoal program g clauseList clauseListTwo=
  let newGoal = programex program (List.hd g) clauseList g 
  in
  if(not(newGoal = [])) then 
    (let newGoalTwo = programex program (List.hd newGoal) clauseListTwo newGoal
     in if(not(newGoalTwo = [])) then (if(not(equal newGoalTwo newGoal))
                                       then (if(goalex program [] newGoal) then true 
                                             else (recGoal program g (clauseListTwo@clauseList) [])) 
                                       else( if(List.length clauseListTwo = 0) then false
                                             else recGoal program g (clauseList@clauseListTwo) []
                                           ))
 
     else true
 
    ) else
    true
 
;;
 
(*Main function*)
let hornClauseGenerator program goals = goalex program [] goals;;
 

