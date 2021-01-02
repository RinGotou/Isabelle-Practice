theory homework2
  imports Main begin

(* isabelle part exercise 1 *)
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count x Nil = 0" |
  "count x (y#xs) = (
  if x = y then
    Suc (count x xs)
  else
    count x xs)"

value "count (1::nat) (1#2#3#[])"

lemma occurrence: "count x xs \<le> length xs"
  apply(induction xs)
  apply(auto)
  done

(* isabelle part exercise 2 *)
datatype 'a tree2 = Leaf 'a | Node "'a tree2" 'a "'a tree2"

fun mirror2 :: "'a tree2 \<Rightarrow> 'a tree2" where
  "mirror2 (Leaf x) = Leaf x" | (* don't miss the parenthness! *)
  "mirror2 (Node lhs x rhs) = Node (mirror2 rhs) x (mirror2 lhs)"

thm mirror2.induct

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
  "pre_order (Leaf x) = x # Nil" |
  (* be careful of constructor of tree2! *)
  "pre_order (Node lhs x rhs) = x # (pre_order(lhs)) @ (pre_order(rhs))"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
  "post_order (Leaf x) = x # Nil" |
  "post_order (Node lhs x rhs) = (post_order(lhs)) @ (post_order(rhs)) @ [x]"

lemma mirror_order: "pre_order (mirror2 t) = rev (post_order t)"
  apply(induction t) 
  apply(auto)
  done
end

