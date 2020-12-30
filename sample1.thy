theory sample1
  imports Main begin

(*for chapter 2.2*)

fun conj :: "bool\<Rightarrow>bool\<Rightarrow>bool" where
  "conj True True = True" |
  "conj _ _ = False"

thm conj.induct

fun add :: "nat\<Rightarrow>nat\<Rightarrow>nat" where
  "add 0 n = n" |
  "add (Suc m) n = Suc(add m n)"

thm add.induct

lemma add_02 [simp]: "add m 0 = m" (*reversed fist rule of add()*)
  apply(induction m)
  (* 1: base case
     2: induction step
  *)
  apply(auto)
  done

(*inspect this lemma*)
thm add_02

(* datatype 'a list = Nil | Cons 'a "'a list" *)

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app Nil ys = ys" |
  "app (Cons x xs) ys = Cons x (app xs ys)"

thm app.induct
value "[] = Nil" (* True  *)

fun rev :: "'a list \<Rightarrow> 'a list" where
  "rev Nil = Nil" |
  "rev (Cons x xs) = app (rev xs) (Cons x Nil)"

thm rev.induct

value "rev(Cons True (Cons False Nil))"
value "rev(Cons a(Cons b Nil))"

(*third lemma for rev_app's second subgoal*)
(*[] = Nil*)
lemma app_assoc [simp]: 
  "app (app xs ys) zs = app xs (app ys zs)"
  apply(induction xs)
  apply(auto)
  done

(*second lemma for rev_app*)
lemma app_Nil2[simp]: "app xs Nil = xs"
  apply(induction xs)
  apply(auto)
  done

(*first lemma for rev_rev*)
lemma rev_app[simp]:
  "rev(app xs ys) = app (rev ys) (rev xs)"
  apply(induction xs)
(*
 1. sample1.rev (app [] ys) =
    app (sample1.rev ys) (sample1.rev [])
*)
   apply(auto)
  (*can't resolve subgoals*)
  (*for 1: xs is Nil, deal with app_Nil2*)
  (* 1. \<And>a xs.
       sample1.rev (app xs ys) =
       app (sample1.rev ys) (sample1.rev xs) \<Longrightarrow>
       app (app (sample1.rev ys) (sample1.rev xs)) [a] =
       app (sample1.rev ys) (app (sample1.rev xs) [a])
  *)
  (*for 2: take care of last two line, 
    deal with app_assoc*)
  done

theorem rev_rev [simp]: "rev(rev xs) = xs"
  apply(induction xs)
  apply(auto) (*one subgoal remains*)
  (*need to define some lemmas for next step*)
  (*based on proof state below*)
  done

(*apply a function to all elements inside list*)
fun map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map f Nil = Nil" |
  "map f (Cons x xs) = Cons (f x) (map f xs)"

thm map.induct

(*head of list*)
fun hd :: "'a list\<Rightarrow>'a" where
  "hd (x # xs) = x"

(*rest part of list*)
fun tl :: "'a list \<Rightarrow> 'a list" where
  "tl Nil = Nil" |
  "tl (x # xs) = xs"

(*need to finish: exercise 2.3*)





  









