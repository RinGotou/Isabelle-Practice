theory homework3
  imports "HOL-IMP.Hoare_Examples"
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  for r where
  refl:  "star r x x"
| step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

(* Problem 1 *)

inductive palindrome :: "'a list \<Rightarrow> bool" where
  "palindrome []"  |
  "palindrome [x]" |
(* If xs is a palindrome, so is a#xs@[a]. *)
  "palindrome xs \<Longrightarrow> palindrome (x#xs@[x])"

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply(induction xs rule: palindrome.induct)
  apply(simp_all)
  done

(*qed*)

(* Problem 2 *)

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl': "star' r x x"
| step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma star_step2 :"star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
  by (auto intro: star.intros)

(* forward proof *)
lemma star_equal1 :"star' r x y \<Longrightarrow> star r x y"
  apply(induction rule: star'.induct)
  apply(rule star.refl)
  apply(simp add: star_step2)
  done

lemma star2_one: "r x y \<Longrightarrow> star' r x y"
  apply(rule star'.step')
  apply(rule star'.refl')
  apply auto
  done

lemma star2_step2: "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
  apply(induction rule: star'.induct)
  apply(simp add: star2_one)
  apply(simp add: star'.step')
  done

(* backward proof *)
lemma "star r x y \<Longrightarrow> star' r x y"
  apply(induction rule: star.induct)
  apply(simp add: star'.refl')
  apply(simp add: star2_step2)
  done

(*qed*)

(* Problem 3 *)

lemma
  "\<turnstile> {\<lambda>s. s ''x'' = x \<and> s ''y'' = y \<and> 0 \<le> x}
     WHILE Less (N 0) (V ''x'') DO (
       ''x'' ::= Plus (V ''x'') (N (-1));;
       ''y'' ::= Plus (V ''y'') (N (-1))
     )
     {\<lambda>t. t ''y'' = y - x}"  
  apply(rule strengthen_pre[where P="\<lambda>s. s ''y'' = y - (x - s ''x'') \<and> s ''x'' \<ge> 0 \<and> 0 \<le> x"])
   apply(simp)
  apply(rule While')
   prefer 2
   apply(simp)
  apply(rule Seq)
   prefer 2
   apply(rule Assign)
  apply(rule Assign')
  apply(simp)
  done
(*qed*)

(* Problem 4 *)

lemma
  "\<turnstile> { \<lambda>s. s ''x'' = i \<and> 0 \<le> i}
     ''r'' ::= N 0;; ''r2'' ::= N 1;;
     WHILE (Not (Less (V ''x'') (V ''r2'')))
     DO (''r'' ::= Plus (V ''r'') (N 1);;
            ''r2'' ::= Plus (V ''r2'') (Plus (Plus (V ''r'') (V ''r'')) (N 1)))
     {\<lambda>s. (s ''r'')^2 \<le> i \<and> i < (s ''r'' + 1)^2}"
  apply(rule Seq)
   prefer 2
  apply(rule While'[where P= "\<lambda>s. s ''x'' = i \<and> (s ''r'')^2 \<le> i \<and> s ''r2'' = ((s ''r'') + 1)^2 \<and> 0 \<le> (s ''r'')"])
    apply(rule Seq)
     prefer 2
     apply(rule Assign)
    apply(simp add: power2_eq_square algebra_simps)
    apply(rule Assign')
    apply(simp add: algebra_simps)
   apply(simp)
  apply(rule Seq)
   prefer 2
   apply(rule Assign)
  apply(simp)
  apply(rule Assign')
  apply(auto)
  done

(*qed*)
end
