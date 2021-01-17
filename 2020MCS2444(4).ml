module Ls = struct
        
    (*1. emptyset, which represents the empty set.*)

        let emptyset = [];;

    (*2.  member x s, which returns true if and only if x is in s. *)

        let rec member m l = match l with
                        [] -> false
                        | x::xs -> m = x || member m xs
                      ;;

        (* Test case used: 
                * member 27 [2;7;7;2;9]; ;;
                - : bool = false

                * member 0 [0;1;2;3;4];;
                - : bool = true

                * member 'a' ['a';'b';'c';'d'];;
                - : bool = true

         *)
    
       
     (*3. subset s1 s2, which returns true if and only if s1 is a subset of s2 *)
     (* Uses the List function mem for finding if a particular element of l1
      * is present in l2*) 

       let rec subset l1 l2 = match l1 with 
                         [] -> true
                        | x::xs -> List.mem x l2 && subset xs l2
                       ;; 
                          
          
          (* Test cases used:
                  * subset [3;6;9] [1;2;3;4;5;6;7;8;9] ;;
                  - : bool = true

                  * subset [21;25;27;30] [9;12;15;18;21];;
                  - : bool = false
                  
                  * subset ['o';'c';'a';'m';'l'] ['o';'h';'c';'a';'m';'e';'l'];;
                  - : bool = true
          *)


    (*4. equal s1 s2, which returns true if and only if  set s1 is equal to set s2.*)
    (* Implementation follows the def that for 2 sets to be equal one has to be subset
     * of other and vice versa*)    

 
        let equal l1 l2 = subset l1 l2 && subset l2 l1;;

        (*Test cases used:
                * equalset ['r';'a';'t';'s'] ['s';'t';'a';'r'];;
                - : bool = true
                
                * equalset [] [];;
                - : bool = true

                equalset [23;45;99] [2;3;4;5;9] ;;
                - : bool = false
        *)

       (*5. union s1 s2, which returns the union of sets s1 and s2*)
       (* Implementation follows that if an element is not a member of other list then we
        * insert the element to make list 2 union of l1 l2*)

        let rec union l1 l2 = match l1 with
                        [] -> l2
                        | x::xs -> if(not(List.mem x l2)) 
                                   then union xs (x::l2) 
                                   else union xs l2 
                         ;;
 
        (* Test cases: 
                * union [] [];;
                - : 'a list = []
                
                * union ['m';'a';'r';'s'] ['c';'a';'r';'s'];;
                - : char list = ['m'; 'c'; 'a'; 'r'; 's']
                
                * union [5;10;15;20;25][30;35;40;45;50];;
                - : int list = [25; 20; 15; 10; 5; 30; 35; 40; 45; 50]
        *)

        (*6. intersection s1 s2, which returns the intersection of s1 and s2*)
        (*Uses List function filter to filter out elements not part of l1 as 
         * a means to make list 2 an intersection of both lists*)

        let intersection l1 l2 = List.filter (fun x -> List.mem x l1) l2;;

        (* Test cases: 
                * intersection [5;10;15;20;25] [10;20];;
                - : int list = [10; 20]

                * intersection [1;2][] ;;
                - : int list = []

                * intersection(intersection ['e';'n';'g';'i';'n';'e']['n';'i';'n';'e']) ['o';'n';'e'];;
                - : char list = ['n'; 'e']
        *)

        (*7. difference s1 s2, which returns the set consisting of elements of s1 
         * which are not in s2*)
        (* Uses List function filter to remove/filter elements from list1 present in l2*)

        let difference l1 l2 = List.filter (fun x -> not(List.mem x l2)) l1;;

        (*Test cases: 
                * difference [2;3;4] [2;3];;
                - : int list = [4]

                * difference [] [1;5;15;20;25];;
                - : int list = []

                * difference ['o';'h';'c';'a';'m';'l'] ['c';'a';'m';'l'];;
                - : char list = ['o'; 'h']
        *)

        (*8. power s, which returns the set of subsets of s*)
        (* Uses list function map to sequentially create sets from smaller sets*)
        (* The result of which is appended to list created our list of lists*)

        let rec power l = match l with 
                         [] -> [[]]
                        | x::xs -> power xs @ List.map( fun y -> x::y ) (power xs);;

        (*Test cases:
                * power [1;2;3];;
                - : int list list = [[]; [3]; [2]; [2; 3]; [1]; [1; 3]; [1; 2]; [1; 2; 3]]

                * power [[]];;
                - : 'a list list list = [[]; [[]]]
                
                * power power [[1;3;5];[2;4;6]];;
                - : int list list list = [[]; [[2; 4; 6]]; [[1; 3; 5]]; [[1; 3; 5]; [2; 4; 6]]]

                *)


        (*9. product s1 s2, which returns the cartesian product of s1 and s2. *)
        (* Uses map to create ordered pairs with each element under considereation from l2 with x*)
        (* where x is an element of l1 *)

        let rec product l1 l2 = match l1 with
                                  [] -> []
                                 | x::xs -> 
                                         List.map (fun y -> (x,y)) l2 @(product xs l2) 
                                ;;
        
        (*Test cases: 
                * product [1;3;5][2;4;6];;
                - : (int * int) list =[(1, 2); (1, 4); (1, 6); (3, 2); (3, 4); (3, 6); (5, 2); (5, 4); (5, 6)]
                
                * product ['a';'b';'c']['d';'e';'f'];;
                 - : (char * char) list =[('a', 'd'); ('a', 'e'); ('a', 'f'); ('b', 'd'); ('b', 'e');                           ('b', 'f');('c', 'd'); ('c', 'e'); ('c', 'f')]

                * product [[1;2];[3;4]] [4;5] ;;
                - : (int list * int) list =[([1; 2], 4); ([1; 2], 5); ([3; 4], 4); ([3; 4], 5)]
         *)
end
(*-----------------------------------------------------------------------------------*)

 

module Cf = struct
        
        (* 1. emptyset, which represents the empty set.*)
        
        let emptyset x = false;;
        
        (* 2. member x s, which returns true if and only if x is in s. *)
        (* uses conditional statements to check if element x belongs to set s*)

        let member x s = if(s x) then true else false;;
        
        (* 3. union s1 s2, which returns the union of sets s1 and s2*)
        (* From def of union, if either of s1 and s2 or both has an element x in it's 
         * set then resulant set will have x as element and characteristic function will 
         * return true else false*) 

        let union f1 f2 = fun x -> if( f1 x || f2 x) then true else false;;

        (* 4. intersection s1 s2, which returns the intersection of s1 and s2 *)
        (* From def of intersection, both of s1 and s2 should have the element x in it's
         * resultant set function will return true *)

        let intersection f1 f2 = fun x -> if( f1 x && f2 x) then true else false;;

        (*5. difference s1 s2, which returns the set consisting of elements of s1 
         * which are not in s2*)
        (* From def of difference above we return the resulant set*) 

        let difference f1 f2 = fun x -> if(f1 x && not(f2 x)) then true else false;;
        

        (*6. product s1 s2, which returns the cartesian product of s1 and s2.*)
        (*The cartesian product of s1 and s2 will contain ordered pairs (a,b) where 
         * a belongs to s1 and b belongs to s2. Here we used an helper function to help
         * with forming of ordered pairs so it can be checked again respective functions*)

        let product f1 f2 = let pairHelper s1 s2 (x, y) = f1 x && f2 y in pairHelper f1 f2;;       

end

 


(*-------------------------------------------------------------------------------*)


