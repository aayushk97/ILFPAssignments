(*SUBMITTED BY: AAYUSH KUMAR SINGH 2020MCS2444*)

type variable = string;;

type symbol = (string * int);;

type term = V of variable | Node of symbol*(term list);;

type atomicFormula = Pred of symbol*(term list);;

(*A head is a single atomic formula.*)
type head = atomicFormula;;

(*A body is a sequence of atomic formulas.*)
type body = atomicFormula list;;

(*A goal is a set of atomic formulas*)
type goal = atomicFormula list;;

(*A clause can either be a fact or rule.*)
(*A fact has a head but no body.*)
(*A rule has a head and a body.*)
type clause = Fact of head | Rule of head * body;;

(*A program is a set(list) of clauses*)
type program = clause list;;


type substitution = (string * term ) list;;

type composition = substitution list;;

exception NOT_UNIFIABLE;;


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

let predvl term = match term with
    [] -> []
  |[Pred(l,x)]-> vars_t x;;
(*4. Define a suitable representation for substitutions. *)


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

let subst s t = substitution t s;;


(*6.Come up with an efficient representation of composition of substitutions. *)


(*7. Define the function mgu that given two terms t1 and t2, returns their most general unifier, if it exists and otherwise raises an exception NOT_UNIFIABLE.*)
(*Exception NOT_UNIFIABLE*)

(*performs occurs check that is used to know if a variable occurs inside a term*)
let rec occurs_check_t x u = match u with
    V y -> x=y
  |Node((a,b),c) -> occurs_check x c
and
  occurs_check x w = match w with
    [] -> false
  |u::us -> occurs_check_t x u || occurs_check x us
;;

(*function compose_subst is used to perform composition of substitution*)
let rec compMember m l = match l with
    [] -> false
  |(u,V v)::us -> if(m = v) then true else compMember m us
  |t::us -> compMember m us
;;

let rec compRepl (u,v) l = match l with 
    [] -> []
  |(x,V y)::xs -> if  y = u then (x,V v)::(compRepl (u,v) xs) else (x, V y)::(compRepl (u,v)  xs) 
;;
let rec compose l1 l2 l3= match l2 with
    []-> l1@l3
  |(u, V v)::xs ->if compMember u l1 then compose (compRepl (u,v) l1) xs l3 else compose l1 xs l3
  |(u, x)::xs -> compose l1 xs l3  
;;

let rec compose_subst l1 l2 = compose l1 l2 l2;;

let id = fun x -> x;;
(*MGU function that return appropriate substitution given 2 terms*)
(*function to apply substitution*)
let rec apply_subst l t = match l with 
    [] -> t
  |x::xs -> (apply_subst xs (subst [x] t))
;; 

(*function to find MGU of 2 terms*)
let rec mgu_t term1 term2 l3= match (term1, term2) with
    ([], []) -> l3
  |(x::xs, y::ys) -> mgu_t xs ys (mostGenU (apply_subst l3 x) (apply_subst l3 y) l3)
  |_-> []
and
  mostGenU term1 term2 l3 = match (term1, term2) with 
  |(V x, V y) -> if x = y then []@l3 else mostGenU (subst [(x, V y)] term1) term2 (compose_subst l3 [(x, V y)])
  |(V x, Node((u, 0),[])) -> mostGenU (subst [(x, Node((u,0),[]))] term1) term2 (l3@[(x, Node((u,0),[]))])
  |(Node((u,0),[]), V x)->  mostGenU term1 (subst [(x, Node((u,0),[]))]  term2) (l3@[(x, Node((u,0),[]))])(*Map variable to constant*)
  |(V x, Node((u,v),w)) -> if occurs_check x w  (*If variable x appears in symbol we raise exception *)
      then
        raise NOT_UNIFIABLE
      else mostGenU (subst [(x, Node((u,v),w))] term1) term2 (l3@[(x, Node((u,v),w))]) 
        
  | (Node((u,v),w), V x) -> if occurs_check x w  (*If variable x appears in symbol we raise exception *)
      then
        raise NOT_UNIFIABLE
      else mostGenU term1 (subst [(x, Node((u,v),w))] term2) (l3@[(x, Node((u,v),w))])
        
  |(Node((u,0),[]), Node((v,0),[])) -> if u = v then ([]@l3) else raise NOT_UNIFIABLE (*If different constants they cant be unified else we return identity*)
  |(Node((u,0),[]),y) | (y, Node((u,0),[]))-> raise NOT_UNIFIABLE (*As constant at roots are different*)
  |(Node((u,v),y), Node((w,x),z)) -> if u = w && v = x then mgu_t y z l3 else raise NOT_UNIFIABLE
          
let mgu term1 term2 = mostGenU term1 term2 [];;

let replace l r = match l with
    [] -> l
  |h::tail -> r::tail
;;


let rec changePN term = match term with
    [] -> []
  |Pred(x,t)::preds -> Node(x,t)::(changePN preds)
;;

let rec andOnList l = match l with
    [] -> true
  |h::tail -> h && (andOnList tail)
;;

let rec and_on_list list = match list with
    [] -> true
  |x::xs -> x && (and_on_list xs)
;;

let rec goThrough s fprogram goal goalRest mguAns boolAns rprogram goalc = match rprogram with
    [] -> ( match s with
        [] -> (mguAns, boolAns)
(*Solve for the rest*)
      |(prgPart, mguPart, goalPart, boolPart)::ss -> recursolve(ss, prgPart, fprogram, goalPart, mguPart, boolPart)
    )
  |Fact(Pred(t,x))::programxs -> (
      try 
        let unif = (mgu (Node(t,x)) goalc) in
        recursolve((programxs, mguAns, goal, boolAns)::s, fprogram, fprogram, (List.map (subst unif) goalRest), compose_subst mguAns unif, false::(replace boolAns (true)))
          
      with
      | _ -> goThrough s fprogram goal goalRest mguAns boolAns programxs goalc
    )
  |Rule(Pred(t1,x),subGoal)::programxs ->(
      try
        let unif = (mgu (Node(t1,x)) goalc) in
        let unifiedSubGoal = List.map (subst unif) (changePN subGoal) in
        let answer = recursolve(s, fprogram, fprogram, unifiedSubGoal, compose_subst mguAns unif,[false]) in
        let bRes = match answer with
            (funn,bool_l) -> funn,[(and_on_list bool_l)]
        in
        let a_unif,b=bRes in
        if b=[true] then
          let unifiedGoalc = List.map (subst a_unif) goalRest in
          recursolve((programxs, mguAns, goal, boolAns)::s, fprogram, fprogram, unifiedGoalc, compose_subst mguAns a_unif, false::(replace boolAns (true)))
        else
          (
            goThrough s fprogram goal goalRest mguAns boolAns programxs goalc
          )
          
      with
      |_ -> goThrough s fprogram goal goalRest mguAns boolAns programxs goalc
    )
and
  recursolve (d, rprogram, fprogram, goal, mguAns, boolAns) = match (d, rprogram, goal) with
    (_,_,[]) -> ( match boolAns with
      (*Remove the first false and return mguAns and bool list*)
        false::boolxs -> mguAns, boolxs 
    )
(*When d and rprogram are empty*)
  |([],[],g::goalxs) -> (mguAns, boolAns)
(*If both the conditions fails*)
  |(s, rprogram, goalc::goalxs ) -> goThrough s fprogram goal goalxs mguAns boolAns rprogram goalc 
                                      
;;                      

let rec getMem answer x l= match answer with
    [] -> l
  |(y,z)::ys -> if y=x then (getMem ys x ((y,z)::l)) else getMem ys x l
;;

let rec getCorrespondingVal answer list l = match list with
    [] -> l
  |x::xs -> getMem answer x l;;

let rec printValues list = match list with
    [] -> Printf.printf "true.\n"
  |(x,u)::xs -> (match u with 
        Node((a,0),[]) -> Printf.printf "%s = %s\n" x a 
      |V s -> Printf.printf "%s = %s\n" x s
      |_-> Printf.printf "Wrong term was output. Check Again.\n");
      printValues xs
;;


let interpret program goals = 
  let answer, bool = (recursolve ([], (List.rev program), (List.rev program), (changePN goals), [], [false])) in
  match (getCorrespondingVal answer (vars_t (changePN goals)) []),bool with
    [],(bval::rest) -> (if bval = false then Printf.printf "false.\n" else Printf.printf "true.\n")
  |(x::xs),(bval::rest) -> (if bval = false then Printf.printf "false.\n"
                            else printValues (x::xs))
                            ;;

(*
let program1 = [Fact(Pred(("male",1),[Node(("Arjun",0),[])]));
  Fact(Pred(("male",1),[Node(("Karan",0),[])]));
  Fact(Pred(("male",1),[Node(("Dad",0),[])]));
Fact(Pred(("child",2),[Node(("Dad",0),[]); Node(("Karan",0),[])]));
Fact(Pred(("child",2),[Node(("Dad",0),[]); Node(("Ajun",0),[])]));
  Rule(Pred(("brother",2),[V "X"; V "Y"]),[Pred(("child",2),[V "Z"; V "X"]); Pred(("child",2),[V "Z"; V "Y"])])
];;

let goals = [Pred(("brother",2),[Node(("Karan",0),[]); V "W"])] ;;

interpret program1 goals;;
*)

(*Example2:
    
let program1 = [Fact(Pred(("male",1),[Node(("Arjun",0),[])]));
  Fact(Pred(("male",1),[Node(("Karan",0),[])]));
  Fact(Pred(("male",1),[Node(("Dad",0),[])]));
Fact(Pred(("child",2),[Node(("Dad",0),[]); Node(("Karan",0),[])]));
Fact(Pred(("child",2),[Node(("Dad",0),[]); Node(("Ajun",0),[])]));
  Rule(Pred(("brother",2),[V "X"; V "Y"]),[Pred(("child",2),[Node(("Dad",0),[]); V "X"]); Pred(("child",2),[Node(("Dad",0),[]); V "Y"])])
  ]
    Nodes and variables are inside Predicate 
  Goal i.e, query is written as:
  let goals = [Pred(("brother",2),[Node(("Karan",0),[]); V "Z"])]
*)

