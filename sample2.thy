theory sample2
  imports Main begin
type_synonym string = "char list"

datatype 
  'a tree = Leaf |
  Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree\<Rightarrow>'a tree" where
  "mirror Leaf = Leaf" |
  (*left and right is swapped*)
  "mirror (Node left a right) = Node (mirror right) a (mirror left)"

lemma "mirror (mirror t) = t"
  apply(induction t)
   apply(auto)
  done

datatype 'a option = None | Some 'a

(* t1 * t2 is the type of pairs*)
fun lookup :: "('a * 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "lookup Nil x = None" |
  "lookup ((a, b) # ps) x = (
    if a = x then 
      Some b 
    else 
    lookup ps x
)"

(*
  Pairs can be taken apart either by pattern
  matching(as above) or with the projection
  functions fst and snd (first, second)
  Tuples are simulated by pairs nested to the
  right: (a, b, c) is short for (a, (b, c))
  and t1 * t2 * t3 is short for 
  t1 * (t2 * t3)
*)

(*non-recursive function*)
definition sq :: "nat\<Rightarrow>nat" where
  "sq n = n * n"

(*abbreviations*)
abbreviations sq' :: "nat\<Rightarrow>nat" where
  "sq' n = n * n"

(*
  the key difference is that sq' is only
  syntactic suger, sq' t is replaced by
  t * t; 
  before printing, every occurrence
  of u * u is replaced by sq' u.
  Internally, sq' does not exist
*)

(*recursive functions: defined with fun
  by pattern matching over datatype 
  constructors
  The order of equations matters! ! !
  (as in functional programming languages)
  However, all HOL functions must be total.
  This simplifies the logic - 
  terms are always defined - 
  but means that recursive functions must
  terminate.
  Otherwise one could define a function
  f n = f n + 1 and conclude 0 = 1 by
  subtracting f n on both sides.
*)
(*
  Isabelle's automatic termination checker
  requires that arguments of ercursive calls
  on the right-hand side must be strictly
  smaller than the arguments on the left-hand
  side.
  This means that one fixed argument position
  decreases in size with each recursive call.
  The size is measured as the number of  
  constructor(excluding 0-ary ones, e.g. Nil)
  Lexicographic combinations are also 
  recognized.
*)

(*functions defined with fun come with their
  own induction schema that mirrors the 
  recursion schema and is derived from the 
  termination order.*)

fun div2 :: "nat\<Rightarrow>nat" where
  "div2 0 = 0" | (* 0 *)
  "div2 (Suc 0) = 0" | (* 1 *)
  "div2 (Suc (Suc n)) = Suc(div2 n)" (* 2~ *)
  (*e.g.: div2 (Suc (Suc 2)) = Suc (div2 2)
   Suc (Suc 2) \<Rightarrow> 4 *)

(*it does not just define div2 but also proves
  a customized induction rule
  P 0  P (Suc 0)  \<forall>n. P n \<Longrightarrow> P (Suc (Suc n))
  -------------------------------------------
              P m

  This induction rule can simplify inductive
  proofs.
*)

lemma "div2(n) = n div 2"
  apply(induction n rule: div2.induct)
  apply(auto)
  done

(*
  Function rev has quadratic worst-case 
  running time because it calls append 
  for each element of the list and append 
  is linear in its first argument. A linear 
  time version of rev requires an extra 
  argument where the result is accumulated 
  gradually, using only #
*)

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev Nil ys = ys" |
  "itrev (x # xs) ys = itrev xs (x # ys)"

thm itrev.induct

(*
  it reverses its first argument by stacking 
  its elements onto the second argument, and 
  it returns that second argument when the 
  first one becomes empty. Note that itrev 
  is tail-recursive: it can be compiled 
  into a loop; no stack is necessary 
  for executing it.
*)


lemma "itrev xs Nil = rev xs"
  apply(induction xs)
   apply(auto)
  (* IH is too weak to remove subgoal*)
  sorry

(*xs @ ys = app xs ys*)
lemma "itrev xs ys = rev xs @ ys"
  (*apply(induction xs)*)
  (*apply(auto)*)
  (*IH is still too weak, use this instead*)
  apply(induction xs arbitrary: ys)
  apply(auto)
  done
  
  







